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

data Code : (S S′  : StackType) -> Set₁ where
    skip : ∀ {S} -> Code S S
    _++_ : ∀ {S₀ S₁ S₂} (c₁ : Code S₀ S₁) (c₂ : Code S₁ S₂) -> Code S₀ S₂
    PUSH : ∀ {T S} (v : Val T) -> Code S (T :: S)
    ADD : ∀ {S} -> Code (nat :: (nat :: S)) (nat :: S)
    IF  : ∀ {S S′} (c₁ c₂ : Code S S′) -> Code (bool :: S) S′

exec : ∀ {S S′} (c : Code S S′) -> (s : Stack S) -> (Stack S′)
exec skip s = s
exec (c ++ c₁) s = exec c₁ (exec c s)
exec (PUSH v) s = v > s
exec ADD (v > (v₁ > s)) = (v + v₁) > s 
exec (IF c c₁) (vtrue > s) = exec c s
exec (IF c c₁) (vfalse > s) = exec c₁ s

compile : ∀ {T S} (e : Exp T) -> Code S (T :: S)
compile (val x) = PUSH x
compile (plus e₁ e₂) = compile e₂ ++ (compile e₁ ++ ADD) 
compile (if b e₁ e₂) = {!compile b ++ (IF (compile e₁) (compile e₂))!}
