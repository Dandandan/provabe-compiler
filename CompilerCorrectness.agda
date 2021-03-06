module CompilerCorrectness where

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

data BinOp : Type -> Type -> Type -> Set where
  o-plus : BinOp NAT NAT NAT
  o-minus  : BinOp NAT NAT NAT
  o-times : BinOp NAT NAT NAT

data Exp : Type → Set where
  e-val :        ∀ {T} → Val T → Exp T
  e-bin :        ∀ {T U V} → BinOp T U V → Exp T → Exp U → Exp V
  e-ifthenelse : ∀ {T} → Exp BOOL → (e₁ e₂ : Exp T) → Exp T
  e-throw :      ∀ {T} → Exp T
  e-catch :      ∀ {T} → Exp T → Exp T → Exp T


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Evaluation of expressions
--------------------------------------------------------------------------------

add-values : Val NAT → Val NAT → Val NAT
add-values (v-nat x₁) (v-nat x₂) = v-nat (x₁ + x₂)

subtract-values : Val NAT → Val NAT → Val NAT
subtract-values (v-nat x₁) (v-nat x₂) = v-nat (x₁ ∸ x₂)

mult-values : Val NAT → Val NAT → Val NAT
mult-values (v-nat x₁) (v-nat x₂) = v-nat (x₁ * x₂)

bin-op : ∀ {T U V} -> BinOp T U V -> Val T -> Val U -> Val V
bin-op o-plus x x₁ = add-values x x₁  
bin-op o-minus x x₁ = subtract-values x x₁ 
bin-op o-times x x₁ = mult-values x₁ x₁
eval : ∀ {T} → Exp T → Maybe (Val T)
eval (e-val x) = just x
eval (e-bin o e₁ e₂) with eval e₁ | eval e₂
... | just v₁ | just v₂ = just (bin-op o v₁ v₂)
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

data StackItemType : Set where
  val : Type → StackItemType
  hnd : Type → StackItemType
  skp : Type → StackItemType

Shape : Set
Shape = List StackItemType

mutual
  data Instr : Shape → Shape → Set where
    PUSH :   ∀ {T s} → Val T → Instr s (val T ∷ s)
    BIN : ∀ {s t u v} → BinOp t u v → Instr (val t ∷ val u ∷ s) (val v ∷ s)
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
  _>>_ :   ∀ {s T} → Val T → Stack s → Stack (val T ∷ s)
  hnd>>_ : ∀ {s} → {T : Type} → Stack s → Stack (hnd T ∷ s)
  skp>>_ : ∀ {s} → {T : Type} → Stack s → Stack (skp T ∷ s)


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
  execInstr (BIN o)    ✓[ x₁ >> x₂ >> st ]      = ✓[ bin-op o x₁ x₂ >> st ]  
  execInstr (COND t f) ✓[ v-bool true >> st ]   = exec t ✓[ st ]
  execInstr (COND t f) ✓[ v-bool false >> st ]  = exec f ✓[ st ]
  execInstr MARK       ✓[ st ]                  = ✓[ hnd>> skp>> st ]
  execInstr HANDLE     ✓[ x >> hnd>> skp>> st ] = ⇝[ zero , x >> st ] -- Skip handler code
  execInstr UNMARK     ✓[ x >> skp>> st ]       = ✓[ x >> st ]
  execInstr THROW      ✓[ st ]                  = x[ zero , unwind st zero ] -- Throw first exception
  -- Catching state
  execInstr (PUSH x)   x[ n , st ]              = x[ n , st ]
  execInstr (BIN o)    x[ n , st ]              = x[ n , st ]
  execInstr (COND t f) x[ n , st ]              = exec t x[ n , st ]
  execInstr MARK       x[ n , st ]              = x[ suc n , st ]
  execInstr HANDLE     x[ zero , st ]           = ✓[ st ] -- Handle exception
  execInstr HANDLE     x[ suc n , st ]          = x[ n , st ]
  execInstr UNMARK     x[ n , st ]              = x[ n , st ]
  execInstr THROW      x[ n , st ]              = x[ n , st ]
  -- Skipping handle code state
  execInstr (PUSH x)   ⇝[ n , st ]              = ⇝[ n , st ]
  execInstr (BIN o)    ⇝[ n , st ]              = ⇝[ n , st ]
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

op-instr : ∀ {t u v w} -> BinOp t u v → Instr (val t ∷ val u ∷ w) (val v ∷ w)
op-instr o = BIN o
compile : ∀ {T s} → Exp T → Code s (val T ∷ s)
compile (e-val x) = ⟦ PUSH x ⟧
compile (e-bin o e₁ e₂) = compile e₂ ◅◅ compile e₁ ◅◅ ⟦ op-instr o ⟧
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

  lemma-op : ∀ {s t u v} (e₁ : Exp t) (e₂ : Exp u) (op : BinOp t u v) → (st : State s) → execInstr (op-instr op) (eval e₁ :~: eval e₂ :~: st) ≡ eval (e-bin op e₁ e₂) :~: st
  lemma-op e₁ e₂ o s with eval e₁ | eval e₂
  lemma-op e₁ e₂ o-plus ✓[ st ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-minus ✓[ st ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-plus x[ n , st ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-minus x[ n , st ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-plus ⇝[ n , st ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-minus ⇝[ n , st ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-plus ✓[ x₁ ] | just x | nothing = refl
  lemma-op e₁ e₂ o-minus ✓[ x₁ ] | just x | nothing = refl
  lemma-op e₁ e₂ o-plus x[ n , st ] | just x | nothing = refl
  lemma-op e₁ e₂ o-minus x[ n , st ] | just x | nothing = refl
  lemma-op e₁ e₂ o-plus ⇝[ n , st ] | just x | nothing = refl
  lemma-op e₁ e₂ o-minus ⇝[ n , st ] | just x | nothing = refl
  lemma-op e₁ e₂ o-plus ✓[ st ] | nothing | just x = refl
  lemma-op e₁ e₂ o-minus ✓[ st ] | nothing | just x = refl
  lemma-op e₁ e₂ o-plus x[ n , st ] | nothing | just x = refl
  lemma-op e₁ e₂ o-minus x[ n , st ] | nothing | just x = refl
  lemma-op e₁ e₂ o-plus ⇝[ n , st ] | nothing | just x = refl
  lemma-op e₁ e₂ o-minus ⇝[ n , st ] | nothing | just x = refl
  lemma-op e₁ e₂ o-plus ✓[ x ] | nothing | nothing = refl
  lemma-op e₁ e₂ o-minus ✓[ x ] | nothing | nothing = refl
  lemma-op e₁ e₂ o-plus x[ n , st ] | nothing | nothing = refl
  lemma-op e₁ e₂ o-minus x[ n , st ] | nothing | nothing = refl
  lemma-op e₁ e₂ o-plus ⇝[ n , st ] | nothing | nothing = refl
  lemma-op e₁ e₂ o-minus ⇝[ n , st ] | nothing | nothing = refl
  lemma-op e₁ e₂ o-times ✓[ x₂ ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-times x[ n , st ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-times ⇝[ n , st ] | just x | just x₁ = refl
  lemma-op e₁ e₂ o-times ✓[ x₁ ] | just x | nothing = refl
  lemma-op e₁ e₂ o-times x[ n , st ] | just x | nothing = refl
  lemma-op e₁ e₂ o-times ⇝[ n , st ] | just x | nothing = refl
  lemma-op e₁ e₂ o-times ✓[ x₁ ] | nothing | just x = refl
  lemma-op e₁ e₂ o-times x[ n , st ] | nothing | just x = refl
  lemma-op e₁ e₂ o-times ⇝[ n , st ] | nothing | just x = refl
  lemma-op e₁ e₂ o-times ✓[ x ] | nothing | nothing = refl
  lemma-op e₁ e₂ o-times x[ n , st ] | nothing | nothing = refl
  lemma-op e₁ e₂ o-times ⇝[ n , st ] | nothing | nothing = refl

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

  lemma-compiled-expr-:~:combination-xequivalency : ∀ {s T} (e₁ e₂ : Exp T) (n : ℕ) (st : Stack (unwindShape s n)) → exec {s} (compile e₁) x[ n , st ] ≡ (_:~:_) {s} (eval e₂) x[ n , st ]
  lemma-compiled-expr-:~:combination-xequivalency e₁ e₂ n st = let open ≡-Reasoning in begin
    exec (compile e₁) x[ n , st ]
      ≡⟨ lemma-compiled-expr-maintains-xstate e₁ n st ⟩
    x[ n , st ]
      ≡⟨ sym (lemma-:~:combination-maintains-xstate e₂ n st) ⟩
    eval e₂ :~: x[ n , st ]
      ∎

  lemma-compiled-expr-:~:combination-⇝equivalency : ∀ {s T} (e₁ e₂ : Exp T) (n : ℕ) (st : Stack (skipShape s n)) → exec {s} (compile e₁) ⇝[ n , st ] ≡ (_:~:_) {s} (eval e₂) ⇝[ n , st ]
  lemma-compiled-expr-:~:combination-⇝equivalency e₁ e₂ n st = let open ≡-Reasoning in begin
    exec (compile e₁) ⇝[ n , st ]
      ≡⟨ lemma-compiled-expr-maintains-⇝state e₁ n st ⟩
    ⇝[ n , st ]
      ≡⟨ sym (lemma-:~:combination-maintains-⇝state e₂ n st) ⟩
    eval e₂ :~: ⇝[ n , st ]
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
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool false) | just x₁ | just x₂ = lemma-compiled-expr-:~:combination-xequivalency e₁ e₂ n st
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool false) | just x₁ | just x₂ = lemma-compiled-expr-:~:combination-⇝equivalency e₁ e₂ n st
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool false) | just x  | nothing = correct e₂ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool false) | just x  | nothing = lemma-compiled-expr-:~:combination-xequivalency e₁ e₂ n st
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool false) | just x  | nothing = lemma-compiled-expr-:~:combination-⇝equivalency e₁ e₂ n st
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool false) | nothing | just x  = correct e₂ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool false) | nothing | just x  = lemma-compiled-expr-:~:combination-xequivalency e₁ e₂ n st
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool false) | nothing | just x  = lemma-compiled-expr-:~:combination-⇝equivalency e₁ e₂ n st
  lemma-ite c e₁ e₂ ✓[ st ]     | just (v-bool false) | nothing | nothing = correct e₂ ✓[ st ]
  lemma-ite c e₁ e₂ x[ n , st ] | just (v-bool false) | nothing | nothing = lemma-compiled-expr-:~:combination-xequivalency e₁ e₂ n st
  lemma-ite c e₁ e₂ ⇝[ n , st ] | just (v-bool false) | nothing | nothing = lemma-compiled-expr-:~:combination-⇝equivalency e₁ e₂ n st
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
  -- 
  correct (e-bin o e₁ e₂) st = let open ≡-Reasoning in begin
    exec (compile e₂ ◅◅ compile e₁ ◅◅ op-instr o ◅ ε) st
      ≡⟨ distr _ (compile e₂) _ ⟩
    exec (compile e₁ ◅◅ op-instr o ◅ ε) (exec (compile e₂) st)
      ≡⟨ distr _ (compile e₁) _ ⟩
    execInstr (op-instr o) (exec (compile e₁) (exec (compile e₂) st))
      ≡⟨ cong (λ x → execInstr (op-instr o) (exec (compile e₁) x)) (correct e₂ st) ⟩
       execInstr (op-instr o) (exec (compile e₁) (eval e₂ :~: st))
      ≡⟨ cong (λ x → execInstr (op-instr o) x) (correct e₁ (eval e₂ :~: st)) ⟩
    execInstr (op-instr o) (eval e₁ :~: eval e₂ :~: st)
      ≡⟨ lemma-op e₁ e₂ o st ⟩
    eval (e-bin o e₁ e₂) :~: st
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
