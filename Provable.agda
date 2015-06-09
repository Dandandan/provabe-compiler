module Provable where

-- paragraph 3.1
data TyExp : Set where
    nat : TyExp
    bool : TyExp

data Nat : Set where
    Zero : Nat
    Succ : Nat -> Nat

data Val : TyExp -> Set where
  vtrue : Val bool
  vfalse : Val bool

  vnat : Nat -> Val nat

cond : ∀ {ty} -> Val bool -> Val ty -> Val ty -> Val ty 
cond vtrue x x₁ = x
cond vfalse x x₁ = x₁

typeOf : ∀ {x} -> Val x -> Set
typeOf {nat} x = Nat
typeOf {bool} x = Val bool

data Exp : TyExp -> Set where
    val : {v : TyExp} -> Val v -> Exp v
