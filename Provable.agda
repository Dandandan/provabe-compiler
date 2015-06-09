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

cond : ∀ {t} -> Val bool -> Val t -> Val t -> Val t
cond vtrue x x₁ = x
cond vfalse x x₁ = x₁

typeOf : ∀ {x} -> Val x -> Set
typeOf {nat} x = Nat
typeOf {bool} x = Val bool

data Exp : TyExp -> Set where
    val : ∀ {t} -> Val t -> Exp t
    plus : (e1 e2 : Exp nat) -> Exp nat
    if : ∀ {t} -> (b : Exp bool) (e1 e2 : Exp t) -> Exp t

_+_ : Val nat -> Val nat -> Val nat
_+_ = {!!}

eval : ∀ {t} -> Exp t -> Val t
eval (val x) = x
eval (plus e1 e2) = eval e1 + eval e2
eval (if b e1 e2) = cond (eval b) (eval e1) (eval e2)
