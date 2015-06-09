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

cond : ∀ {T} -> Val bool -> Val T -> Val T -> Val T
cond vtrue x _ = x
cond vfalse _ x₁ = x₁

typeOf : ∀ {T} -> Val T -> Set
typeOf {nat} _ = Nat
typeOf {bool} _ = Val bool

data Exp : TyExp -> Set where
    val : ∀ {T} -> Val T -> Exp T
    plus : (e1 e2 : Exp nat) -> Exp nat
    if : ∀ {T} -> (b : Exp bool) (e1 e2 : Exp T) -> Exp T

_+_ : Val nat -> Val nat -> Val nat
_+_ = {!!}

eval : ∀ {T} -> Exp T -> Val T
eval (val x) = x
eval (plus e1 e2) = eval e1 + eval e2
eval (if b e1 e2) = cond (eval b) (eval e1) (eval e2)

-- Paragraph 4.1 Typing stacks
data List : Set -> Set₁ where
    []   : {A : Set} -> List A
    _::_ : {A : Set} (x : A) (xs : List A) -> List A


StackType : Set₁
StackType = List TyExp

data Stack : StackType -> Set₁ where
  ε : Stack []
  _>_ : ∀ {T S} (v : Val T) (s : Stack S) -> Stack (T :: S)

top : ∀ {T S} (s : Stack (T :: S)) -> Val T
top (v > s) = v
