module Provable3 where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.Star

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

-- Execution state encodes how many nested exceptions need to be handled:
data State (s : Shape) : Set where
  ✓[_] : Stack s → State s
  x[_,_] : (n : ℕ) → (st : Stack (unwindShape s n)) → State s

mutual
  -- Actual execution, split up by state:
  execInstr : ∀ {s₁ s₂} → Instr s₁ s₂ → State s₁ → State s₂
  -- Normal operation
  execInstr (PUSH x)   ✓[ st ]                  = ✓[ x >> st ]
  execInstr ADD        ✓[ x₁ >> x₂ >> st ]      = ✓[ add-values x₁ x₂ >> st ]
  execInstr (COND t f) ✓[ v-bool true >> st ]   = exec t ✓[ st ]
  execInstr (COND t f) ✓[ v-bool false >> st ]  = exec f ✓[ st ]
  execInstr MARK       ✓[ st ]                  = ✓[ hnd>> skp>> st ]
  execInstr HANDLE     ✓[ x >> hnd>> skp>> st ] = ✓[ skp>> st ]
  execInstr UNMARK     ✓[ x >> skp>> st ]       = ✓[ x >> st ]
  execInstr THROW      ✓[ st ]                  = x[ zero , unwind st zero ]
  -- Catching state
  execInstr (PUSH x)   x[ n , st ]              = x[ n , st ]
  execInstr ADD        x[ n , st ]              = x[ n , st ]
  execInstr (COND t f) x[ n , st ]              = exec t x[ n , st ]
  execInstr MARK       x[ n , st ]              = x[ suc n , st ]
  execInstr HANDLE     x[ zero , st ]           = ✓[ st ]
  execInstr HANDLE     x[ suc n , st ]          = x[ n , st ]
  execInstr UNMARK     x[ n , st ]              = x[ n , st ]
  execInstr THROW      x[ n , st ]              = x[ n , st ]


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

