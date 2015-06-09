module Provable where

-- paragraph 3.1
data TyExp : Set where
    nat : TyExp
    bool : TyExp

data Type : Set where
    NAT : Type
    BOOL : Type

data Nat : Set where
    Zero : Nat
    Succ : Nat -> Nat

data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL

  vnat : Nat -> Value NAT

typeOf : ∀ {x} -> Value x -> Type
typeOf {NAT} x = NAT
typeOf {BOOL} x = BOOL
