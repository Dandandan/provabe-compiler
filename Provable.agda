module Provable where

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Expressions for a simple language.
--------------------------------------------------------------------------------


data TyExp : Set where
    nat : TyExp
    bool : TyExp

data Nat : Set where
    Zero : Nat
    Succ : Nat -> Nat

data Bool : Set where
    True : Bool
    False : Bool

data Val : TyExp -> Set where
  VBool : Bool -> Val bool
  VNat : Nat -> Val nat

cond : {T : Set} -> Val bool -> T -> T -> T
cond (VBool True) x _ = x
cond _ _ x₁ = x₁

data Exp : TyExp -> Set where
    val : ∀ {T} -> Val T -> Exp T
    plus : Exp nat -> Exp nat -> Exp nat
    if : ∀ {T} -> Exp bool -> Exp T -> Exp T -> Exp T

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Evaluation of expressions
--------------------------------------------------------------------------------

_+_ : Val nat -> Val nat -> Val nat
(VNat Zero) + b = b
VNat (Succ x) + VNat b =  VNat x + VNat (Succ b)

eval : ∀ {T} -> Exp T -> Val T
eval (val x) = x
eval (plus e1 e2) = eval e1 + eval e2
eval (if b e1 e2) = cond (eval b) (eval e1) (eval e2)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Virtual stack machine
--------------------------------------------------------------------------------

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

StackType : Set
StackType = List TyExp

data Stack : StackType -> Set where
  ε : Stack []
  _>_ : ∀ {T S} -> Val T -> Stack S -> Stack (T :: S)

infixr 10 _>_ _::_ _++_
infixr 9 _≡_ 

data Code : (S S′  : StackType) -> Set where
    skip : ∀ {S} -> Code S S
    _++_ : ∀ {S₀ S₁ S₂} -> Code S₀ S₁ -> Code S₁ S₂ -> Code S₀ S₂
    PUSH : ∀ {T S} -> Val T -> Code S (T :: S)
    ADD : ∀ {S} -> Code (nat :: nat :: S) (nat :: S)
    IF  : ∀ {S S′} (c₁ c₂ : Code S S′) -> Code (bool :: S) S′

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Execution of code
--------------------------------------------------------------------------------

exec : ∀ {S S′} -> Code S S′ -> Stack S -> Stack S′
exec skip s = s
exec (c ++ c₁) s = exec c₁ (exec c s)
exec (PUSH v) s = v > s
exec ADD (v > v₁ > s) = v₁ + v > s 
exec (IF c c₁) (VBool True > s) = exec c s
exec (IF c c₁) (_ > s) = exec c₁ s

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Compilation of expressions into code
--------------------------------------------------------------------------------

compile : ∀ {T S} -> Exp T -> Code S (T :: S)
compile (val x) = PUSH x
compile (plus e₁ e₂) = compile e₁ ++ compile e₂ ++ ADD
compile (if b e₁ e₂) = compile b ++ IF (compile e₁) (compile e₂)


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Compiler correctness
--------------------------------------------------------------------------------

mutual
  correctPlus : ∀ {S} (e e₁ : Exp nat) (s : Stack S) -> eval e + eval e₁ > s ≡ exec ADD (exec (compile e₁) (exec (compile e) s))
  correctPlus e e₁ s with correct e s
  ... | x with eval e | exec (compile e) s
  correctPlus e e₁ s | refl | x | .(x > s) with correct e₁ (x > s)
  ... | y with eval e₁ | exec (compile e₁) (x > s)
  correctPlus e e₁ s | refl | x | .(x > s) | refl | m | .(m > x > s) = refl

  correctIf : ∀ {S T} (b : Exp bool) (e₁ e₂ : Exp T) (s : Stack S) -> cond (eval b) (eval e₁) (eval e₂) > s ≡ exec (IF (compile e₁) (compile e₂)) (exec (compile b) s)
  correctIf b e₁ e₂ s with correct b s
  ... | _ with eval b | exec (compile b) s 
  correctIf b e₁ e₂ s | refl | VBool True | .(VBool True > s) = correct e₁ s
  correctIf b e₁ e₂ s | refl | VBool False | .(VBool False > s) = correct e₂ s

  correct : ∀ {T S} -> (e : Exp T) -> (s : Stack S) -> eval e > s ≡ exec (compile e) s
  correct (val x) s = refl
  correct (plus e e₁) s = correctPlus e e₁ s 
  correct (if b e₁ e₂) s = correctIf b e₁ e₂ s
