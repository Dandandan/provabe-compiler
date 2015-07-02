module Provable3 where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.Star

----------------------------------------
----------------------------------------
-- Expressions for a simple language.
----------------------------------------

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


----------------------------------------
----------------------------------------
-- Evaluation
----------------------------------------

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


----------------------------------------
----------------------------------------
-- Virtual stack machine
----------------------------------------

data StackItem : Set where
  val : Type → StackItem
  hnd : Type → StackItem
  skp : Type → StackItem

Shape : Set
Shape = List StackItem

data Instr : Shape → Shape → Set where
  PUSH :   ∀ {T S} → Val T → Instr S (val T ∷ S)
  ADD :    ∀ {S} → Instr (val NAT ∷ val NAT ∷ S) (val NAT ∷ S)
  COND :   ∀ {S₁ S₂} → Instr S₁ S₂ → Instr S₁ S₂ → Instr (val BOOL ∷ S₁) S₂
  MARK :   ∀ {S T} → Instr S (hnd T ∷ skp T ∷ S)
  HANDLE : ∀ {S T} → Instr (val T ∷ hnd T ∷ skp T ∷ S) (skp T ∷ S)
  UNMARK : ∀ {S T} → Instr (val T ∷ skp T ∷ S) (val T ∷ S)
  THROW :  ∀ {S T} → Instr S (val T ∷ S)

Code : Shape → Shape → Set
Code = Star Instr -- Use Star to use transitive property of Instr. Cool library!

infixr 50 _>>_ hnd>>_ skp>>_
data Stack : Shape → Set where
  ε :      Stack []
  _>>_ :   ∀ {S T} → Val T → Stack S → Stack (val T ∷ S)
  hnd>>_ : ∀ {S} → {T : Type} → Stack S → Stack (hnd T ∷ S)
  skp>>_ : ∀ {S} → {T : Type} → Stack S → Stack (skp T ∷ S)
