module Provable3 where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.Star
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Expressions for a simple language.
--------------------------------------------------------------------------------

data Type : Set where
  BOOL : Type
  NAT : Type

data Val : Type → Set where
  v-bool : Bool → Val BOOL
  v-nat : ℕ → Val NAT

data Exp : Type → Set where
  e-val :        ∀ {T} → Val T → Exp T
  e-add :        (e₁ e₂ : Exp NAT) → Exp NAT
  e-ifthenelse : ∀ {T} → Exp BOOL → (e₁ e₂ : Exp T) → Exp T
  e-throw :      ∀ {T} → Exp T
  e-catch :      ∀ {T} → Exp T → Exp T → Exp T


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Evaluation of expressions
--------------------------------------------------------------------------------

add-values : Val NAT → Val NAT → Val NAT
add-values (v-nat x₁) (v-nat x₂) = v-nat (x₁ + x₂)

eval : ∀ {T} → Exp T → Maybe (Val T)
eval (e-val x) = just x
eval (e-add e₁ e₂) with eval e₁ | eval e₂
... | just v₁ | just v₂ = just (add-values v₁ v₂)
... | _ | _ = nothing
eval (e-ifthenelse c e₁ e₂) with eval c
... | just (v-bool true) = eval e₁
... | just (v-bool false) = eval e₂
... | nothing = nothing
eval e-throw = nothing
eval (e-catch e h) with eval e
... | just x = just x
... | nothing = eval h


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Virtual stack machine
--------------------------------------------------------------------------------

data StackItem : Set where
  val : Type → StackItem
  hnd : Type → StackItem
  skp : Type → StackItem

Shape : Set
Shape = List StackItem

mutual
  data Instr : Shape → Shape → Set where
    PUSH :   ∀ {T s} → Val T → Instr s (val T ∷ s)
    ADD :    ∀ {s} → Instr (val NAT ∷ val NAT ∷ s) (val NAT ∷ s)
    COND :   ∀ {s₁ s₂} → Code s₁ s₂ → Code s₁ s₂ → Instr (val BOOL ∷ s₁) s₂
    MARK :   ∀ {s T} → Instr s (hnd T ∷ skp T ∷ s)
    HANDLE : ∀ {s T} → Instr (val T ∷ hnd T ∷ skp T ∷ s) (skp T ∷ s)
    UNMARK : ∀ {s T} → Instr (val T ∷ skp T ∷ s) (val T ∷ s)
    THROW :  ∀ {s T} → Instr s (val T ∷ s)

  Code : Shape → Shape → Set
  Code = Star Instr -- Use Star to use transitive property of Instr. Cool library!

infixr 50 _>>_ hnd>>_ skp>>_
data Stack : Shape → Set where
  ε :      Stack []
  _>>_ :   ∀ {S T} → Val T → Stack S → Stack (val T ∷ S)
  hnd>>_ : ∀ {S} → {T : Type} → Stack S → Stack (hnd T ∷ S)
  skp>>_ : ∀ {S} → {T : Type} → Stack S → Stack (skp T ∷ S)


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Execution of code
--------------------------------------------------------------------------------

-- Some routines for unwinding the stack up to the n-th handle tag:
unwindShape : Shape → ℕ → Shape
unwindShape [] _ = []
unwindShape (hnd x ∷ s) zero = s
unwindShape (hnd x ∷ s) (suc n) = unwindShape s n
unwindShape (_ ∷ s) n = unwindShape s n

unwind : ∀ {s} → Stack s → (n : ℕ) → Stack (unwindShape s n)
unwind ε n = ε
unwind (x >> st) n = unwind st n
unwind (hnd>> st) zero = st
unwind (hnd>> st) (suc n) = unwind st n
unwind (skp>> st) n = unwind st n

skipShape : Shape → ℕ → Shape
skipShape [] _ = []
skipShape (skp x ∷ s) zero = val x ∷ s
skipShape (skp x ∷ s) (suc n) = skipShape s n
skipShape (_ ∷ s) n = skipShape s n

-- Execution state encodes how many nested exceptions need to be handled:
data State (s : Shape) : Set where
  ✓[_] : Stack s → State s
  x[_,_] : (n : ℕ) → (st : Stack (unwindShape s n)) → State s
  ⇝[_,_] : (n : ℕ) → (st : Stack (skipShape s n)) → State s

mutual
  -- Actual execution, split up by state:
  execInstr : ∀ {s₁ s₂} → Instr s₁ s₂ → State s₁ → State s₂
  -- Normal operation
  execInstr (PUSH x)   ✓[ st ]                  = ✓[ x >> st ]
  execInstr ADD        ✓[ x₁ >> x₂ >> st ]      = ✓[ add-values x₁ x₂ >> st ]
  execInstr (COND t f) ✓[ v-bool true >> st ]   = exec t ✓[ st ]
  execInstr (COND t f) ✓[ v-bool false >> st ]  = exec f ✓[ st ]
  execInstr MARK       ✓[ st ]                  = ✓[ hnd>> skp>> st ]
  execInstr HANDLE     ✓[ x >> hnd>> skp>> st ] = ⇝[ zero , x >> st ] -- Skip handler code
  execInstr UNMARK     ✓[ x >> skp>> st ]       = ✓[ x >> st ]
  execInstr THROW      ✓[ st ]                  = x[ zero , unwind st zero ] -- Throw first exception
  -- Catching state
  execInstr (PUSH x)   x[ n , st ]              = x[ n , st ]
  execInstr ADD        x[ n , st ]              = x[ n , st ]
  execInstr (COND t f) x[ n , st ]              = exec t x[ n , st ]
  execInstr MARK       x[ n , st ]              = x[ suc n , st ]
  execInstr HANDLE     x[ zero , st ]           = ✓[ st ] -- Handle exception
  execInstr HANDLE     x[ suc n , st ]          = x[ n , st ]
  execInstr UNMARK     x[ n , st ]              = x[ n , st ]
  execInstr THROW      x[ n , st ]              = x[ n , st ]
  -- Skipping handle code state
  execInstr (PUSH x)   ⇝[ n , st ]              = ⇝[ n , st ]
  execInstr ADD        ⇝[ n , st ]              = ⇝[ n , st ]
  execInstr (COND t f) ⇝[ n , st ]              = exec t ⇝[ n , st ]
  execInstr MARK       ⇝[ n , st ]              = ⇝[ suc n , st ]
  execInstr HANDLE     ⇝[ n , st ]              = ⇝[ n , st ]
  execInstr UNMARK     ⇝[ zero , st ]           = ✓[ st ] -- All marked sections skipped
  execInstr UNMARK     ⇝[ suc n , st ]          = ⇝[ n , st ]
  execInstr THROW      ⇝[ n , st ]              = ⇝[ n , st ]


  exec : ∀ {s₁ s₂} → Code s₁ s₂ → State s₁ → State s₂
  exec ε st = st
  exec (i ◅ is) st = exec is (execInstr i st)


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Compilation of expressions into code
--------------------------------------------------------------------------------

⟦_⟧ : ∀ {s t} → Instr s t → Code s t
⟦_⟧ i = i ◅ ε

compile : ∀ {T s} → Exp T → Code s (val T ∷ s)
compile (e-val x) = ⟦ PUSH x ⟧
compile (e-add e₁ e₂) = compile e₂ ◅◅ compile e₁ ◅◅ ⟦ ADD ⟧
compile (e-ifthenelse c e₁ e₂) = compile c ◅◅ ⟦ COND (compile e₁) (compile e₂) ⟧
compile e-throw = ⟦ THROW ⟧
compile (e-catch e h) = ⟦ MARK ⟧ ◅◅ compile e ◅◅ ⟦ HANDLE ⟧ ◅◅ compile h ◅◅ ⟦ UNMARK ⟧


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Correctness proof
--------------------------------------------------------------------------------

-- Distribution lemma
distr : ∀ {s₁ s₂ s₃} (st : State s₁) (c₁ : Code s₁ s₂) (c₂ : Code s₂ s₃) → exec (c₁ ◅◅ c₂) st ≡ exec c₂ (exec c₁ st)
distr st ε d = refl
distr st (i ◅ is) d = distr _ is d

-- Combine evaluation result with stateful stack:
infixr 5 _:~:_
_:~:_ : ∀ {s T} → Maybe (Val T) → State s → State (val T ∷ s)
_:~:_ (just x) ✓[ st ]     = ✓[ x >> st ]
_:~:_ nothing  ✓[ st ]     = x[ zero , unwind st zero ]
_:~:_ _        x[ n , st ] = x[ n , st ]
_:~:_ _        ⇝[ n , st ] = ⇝[ n , st ]

mutual

  -- Some lemma's:

  lemma-add : ∀ {s} (e₁ e₂ : Exp NAT) (st : State s) → execInstr ADD (eval e₁ :~: eval e₂ :~: st) ≡ eval (e-add e₁ e₂) :~: st
  lemma-add e₁ e₂ st with eval e₁ | eval e₂
  lemma-add e₁ e₂ ✓[ st ]     | just x₁ | just x₂ = refl
  lemma-add e₁ e₂ x[ n , st ] | just x₁ | just x₂ = refl
  lemma-add e₁ e₂ ⇝[ n , st ] | just x₁ | just x₂ = refl
  lemma-add e₁ e₂ ✓[ st ]     | just x  | nothing = refl
  lemma-add e₁ e₂ x[ n , st ] | just x  | nothing = refl
  lemma-add e₁ e₂ ⇝[ n , st ] | just x  | nothing = refl
  lemma-add e₁ e₂ ✓[ st ]     | nothing | just x  = refl
  lemma-add e₁ e₂ x[ n , st ] | nothing | just x  = refl
  lemma-add e₁ e₂ ⇝[ n , st ] | nothing | just x  = refl
  lemma-add e₁ e₂ ✓[ st ]     | nothing | nothing = refl
  lemma-add e₁ e₂ x[ n , st ] | nothing | nothing = refl
  lemma-add e₁ e₂ ⇝[ n , st ] | nothing | nothing = refl

  lemma-:~:combination-maintains-xstate : ∀ {s T} (e : Exp T) (n : ℕ) (st : Stack (unwindShape s n)) → (_:~:_) {s} (eval e) x[ n , st ] ≡ x[ n , st ]
  lemma-:~:combination-maintains-xstate e n st with eval e
  ... | just x = refl
  ... | nothing = refl
  
  lemma-:~:combination-maintains-⇝state : ∀ {s T} (e : Exp T) (n : ℕ) (st : Stack (skipShape s n)) → (_:~:_) {s} (eval e) ⇝[ n , st ] ≡ ⇝[ n , st ]
  lemma-:~:combination-maintains-⇝state e n st with eval e
  ... | just x = refl
  ... | nothing = refl

  lemma-compiled-expr-maintains-xstate : ∀ {s T} (e : Exp T) (n : ℕ) (st : Stack (unwindShape s n)) → exec {s} (compile e) x[ n , st ] ≡ x[ n , st ]
  lemma-compiled-expr-maintains-xstate e n st = let open ≡-Reasoning in begin
    exec (compile e) x[ n , st ]
      ≡⟨ correct e x[ n , st ] ⟩
    eval e :~: x[ n , st ]
      ≡⟨ lemma-:~:combination-maintains-xstate e n st ⟩
    x[ n , st ]
      ∎

  lemma-compiled-expr-maintains-⇝state : ∀ {s T} (e : Exp T) (n : ℕ) (st : Stack (skipShape s n)) → exec {s} (compile e) ⇝[ n , st ] ≡ ⇝[ n , st ]
  lemma-compiled-expr-maintains-⇝state e n st = let open ≡-Reasoning in begin
    exec (compile e) ⇝[ n , st ]
      ≡⟨ correct e ⇝[ n , st ] ⟩
    eval e :~: ⇝[ n , st ]
      ≡⟨ lemma-:~:combination-maintains-⇝state e n st ⟩
    ⇝[ n , st ]
      ∎

  lemma-ite : ∀ {s T} (c : Exp BOOL) (e₁ e₂ : Exp T) (st : State s) → execInstr (COND (compile e₁) (compile e₂)) (eval c :~: st) ≡ eval (e-ifthenelse c e₁ e₂) :~: st
  lemma-ite c e₁ e₂ st with eval c | eval e₁ | eval e₂
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool true)  | just x₁ | just x₂ = correct e₁ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool true)  | just x₁ | just x₂ = correct e₁ x[ n , st ]
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool true)  | just x₁ | just x₂ = correct e₁ ⇝[ n , st ]
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool true)  | just x  | nothing = correct e₁ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool true)  | just x  | nothing = correct e₁ x[ n , st ]
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool true)  | just x  | nothing = correct e₁ ⇝[ n , st ]
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool true)  | nothing | just x  = correct e₁ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool true)  | nothing | just x  = correct e₁ x[ n , st ]
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool true)  | nothing | just x  = correct e₁ ⇝[ n , st ]
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool true)  | nothing | nothing = correct e₁ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool true)  | nothing | nothing = correct e₁ x[ n , st ]
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool true)  | nothing | nothing = correct e₁ ⇝[ n , st ]
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool false) | just x₁ | just x₂ = correct e₂ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool false) | just x₁ | just x₂ = let open ≡-Reasoning in begin
    exec (compile e₁) x[ n , st ]
      ≡⟨ lemma-compiled-expr-maintains-xstate e₁ n st ⟩
    x[ n , st ]
      ≡⟨ {!lemma-:~:combination-maintains-xstate e₂ n st!} ⟩
    eval e₂ :~: x[ n , st ] ∎
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool false) | just x₁ | just x₂ = {!!}
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool false) | just x  | nothing = correct e₂ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool false) | just x  | nothing = {!!}
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool false) | just x  | nothing = {!!}
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool false) | nothing | just x  = correct e₂ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool false) | nothing | just x  = {!!}
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool false) | nothing | just x  = {!!}
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool false) | nothing | nothing = correct e₂ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool false) | nothing | nothing = {!!}
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool false) | nothing | nothing = {!!}
  lemma-ite c e₁ e₂ ✓[ st ]     | nothing             | just x₁ | just x₂ = lemma-compiled-expr-maintains-xstate e₁ zero (unwind st zero)
  lemma-ite c e₁ e₂ x[ n , st ] | nothing             | just x₁ | just x₂ = lemma-compiled-expr-maintains-xstate e₁ n st
  lemma-ite c e₁ e₂ ⇝[ n , st ] | nothing             | just x₁ | just x₂ = lemma-compiled-expr-maintains-⇝state e₁ n st
  lemma-ite c e₁ e₂ ✓[ st ]     | nothing             | just x  | nothing = lemma-compiled-expr-maintains-xstate e₁ zero (unwind st zero)
  lemma-ite c e₁ e₂ x[ n , st ] | nothing             | just x  | nothing = lemma-compiled-expr-maintains-xstate e₁ n st
  lemma-ite c e₁ e₂ ⇝[ n , st ] | nothing             | just x  | nothing = lemma-compiled-expr-maintains-⇝state e₁ n st
  lemma-ite c e₁ e₂ ✓[ st ]     | nothing             | nothing | just x  = lemma-compiled-expr-maintains-xstate e₁ zero (unwind st zero)
  lemma-ite c e₁ e₂ x[ n , st ] | nothing             | nothing | just x  = lemma-compiled-expr-maintains-xstate e₁ n st
  lemma-ite c e₁ e₂ ⇝[ n , st ] | nothing             | nothing | just x  = lemma-compiled-expr-maintains-⇝state e₁ n st
  lemma-ite c e₁ e₂ ✓[ st ]     | nothing             | nothing | nothing = lemma-compiled-expr-maintains-xstate e₁ zero (unwind st zero)
  lemma-ite c e₁ e₂ x[ n , st ] | nothing             | nothing | nothing = lemma-compiled-expr-maintains-xstate e₁ n st
  lemma-ite c e₁ e₂ ⇝[ n , st ] | nothing             | nothing | nothing = lemma-compiled-expr-maintains-⇝state e₁ n st

  lemma-catch : ∀ {s T} (e h : Exp T) (st : State s) → execInstr UNMARK (eval h :~: execInstr HANDLE (eval e :~: execInstr MARK st)) ≡ eval (e-catch e h) :~: st
  lemma-catch e h st with eval e
  lemma-catch e h st | just x with eval h
  lemma-catch e h ✓[ st ]     | just x₁ | just x₂ = refl
  lemma-catch e h x[ n , st ] | just x₁ | just x₂ = refl
  lemma-catch e h ⇝[ n , st ] | just x₁ | just x₂ = refl
  lemma-catch e h ✓[ x₁ ]     | just x  | nothing = refl
  lemma-catch e h x[ n , st ] | just x  | nothing = refl
  lemma-catch e h ⇝[ n , st ] | just x  | nothing = refl
  lemma-catch e h st | nothing with eval h
  lemma-catch e h ✓[ st ]     | nothing | just x  = refl
  lemma-catch e h x[ n , st ] | nothing | just x  = refl
  lemma-catch e h ⇝[ n , st ] | nothing | just x  = refl
  lemma-catch e h ✓[ st ]     | nothing | nothing = refl
  lemma-catch e h x[ n , st ] | nothing | nothing = refl
  lemma-catch e h ⇝[ n , st ] | nothing | nothing = refl


  -- The correctness proof:

  correct : ∀ {s T} (e : Exp T) (st : State s) → exec (compile e) st ≡ (eval e :~: st)
  correct (e-val x) ✓[ st ] = refl
  correct (e-val x) x[ n , st ] = refl
  correct (e-val x) ⇝[ n , st ] = refl

  correct (e-add e₁ e₂) st = let open ≡-Reasoning in begin
    exec (compile e₂ ◅◅ compile e₁ ◅◅ ADD ◅ ε) st
      ≡⟨ distr _ (compile e₂) _ ⟩
    exec (compile e₁ ◅◅ ADD ◅ ε) (exec (compile e₂) st)
      ≡⟨ distr _ (compile e₁) _ ⟩
    execInstr ADD (exec (compile e₁) (exec (compile e₂) st))
      ≡⟨ cong (λ x → execInstr ADD (exec (compile e₁) x)) (correct e₂ st) ⟩
    execInstr ADD (exec (compile e₁) (eval e₂ :~: st))
      ≡⟨ cong (λ x → execInstr ADD x) (correct e₁ (eval e₂ :~: st)) ⟩
    execInstr ADD (eval e₁ :~: eval e₂ :~: st)
      ≡⟨ lemma-add e₁ e₂ st ⟩
    eval (e-add e₁ e₂) :~: st
      ∎

  correct (e-ifthenelse c e₁ e₂) st = let open ≡-Reasoning in begin
    exec (compile c ◅◅ COND (compile e₁) (compile e₂) ◅ ε) st
      ≡⟨ distr _ (compile c) _ ⟩
    execInstr (COND (compile e₁) (compile e₂)) (exec (compile c) st)
      ≡⟨ cong (λ x → execInstr (COND (compile e₁) (compile e₂)) x) (correct c st) ⟩
    execInstr (COND (compile e₁) (compile e₂)) (eval c :~: st)
      ≡⟨ lemma-ite c e₁ e₂ st ⟩
    eval (e-ifthenelse c e₁ e₂) :~: st
      ∎

  correct e-throw ✓[ x ] = refl
  correct e-throw x[ n , st ] = refl
  correct e-throw ⇝[ n , st ] = refl

  correct (e-catch e h) st = let open ≡-Reasoning in begin
    exec (compile e ◅◅ HANDLE ◅ compile h ◅◅ UNMARK ◅ ε) (execInstr MARK st)
      ≡⟨ distr _ (compile e) _ ⟩
    exec (compile h ◅◅ UNMARK ◅ ε) (execInstr HANDLE (exec (compile e) (execInstr MARK st)))
      ≡⟨ distr _ (compile h) _ ⟩
    execInstr UNMARK (exec (compile h) (execInstr HANDLE (exec (compile e) (execInstr MARK st))))
      ≡⟨ cong (λ x → execInstr UNMARK (exec (compile h) (execInstr HANDLE x))) (correct e (execInstr MARK st)) ⟩
    execInstr UNMARK (exec (compile h) (execInstr HANDLE (eval e :~: execInstr MARK st)))
      ≡⟨ cong (λ x → execInstr UNMARK x) (correct h (execInstr HANDLE (eval e :~: execInstr MARK st))) ⟩
    execInstr UNMARK (eval h :~: execInstr HANDLE (eval e :~: execInstr MARK st))
      ≡⟨ lemma-catch e h st ⟩
    eval (e-catch e h) :~: st
      ∎
