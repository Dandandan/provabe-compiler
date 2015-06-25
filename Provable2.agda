module Provable2 where

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

data TyExp : Set where
    nat : TyExp
    bool : TyExp

data Bool : Set where
    False : Bool
    True : Bool

data Nat : Set where
    Zero : Nat
    Succ : Nat -> Nat

data Val : TyExp -> Set where
  vtrue : Val bool
  vfalse : Val bool
  vnat : Nat -> Val nat

data Exp : TyExp -> Set where
    val : ∀ {T} -> Val T -> Exp T
    plus : (e1 e2 : Exp nat) -> Exp nat
    if : ∀ {T} -> Exp bool -> (e1 e2 : Exp T) -> Exp T

    throw : ∀ {T} -> Exp T
    catch : ∀ {T} -> Exp T -> Exp T -> Exp T

_:+_ : Nat -> Nat -> Nat
Zero :+ b = b
Succ a :+ b = Succ (a :+ b)

_+_ : Val nat -> Val nat -> Val nat
vnat Zero + b = b
vnat (Succ x) + vnat b = vnat (x :+ b)

data Maybe {a} (A : Set a) : Set a where
    Nothing : Maybe A
    Just : A -> Maybe A

eval : ∀ {T} -> Exp T -> Maybe (Val T)
eval (val x) = Just x
eval (plus e1 e2) with eval e1 | eval e2
eval (plus e1 e2) | Just x | Just x₁ = Just (x + x₁)
eval (plus e1 e2) | _ | _ = Nothing
eval (if b e1 e2) with eval b | eval e1 | eval e2
eval (if b e1 e2) | Just vtrue | Just e | _ = Just e
eval (if b e1 e2) | Just vfalse | _ | Just e = Just e
...| x | y | z = Nothing
eval (catch e h) with eval e
eval (catch e h) | Nothing = eval h
eval (catch e h) | Just x = Just x
eval throw = Nothing

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

data Item : Set where
    IVal : TyExp -> Item
    Han : TyExp -> Item
    Skip : TyExp -> Item

StackType : Set
StackType = List Item

data Stack : StackType -> Set where
  ε : Stack []
  _>_ : ∀ {S T} ->  Val T -> Stack S -> Stack (IVal T :: S)
  han> : ∀ {S} -> {T : TyExp} -> Stack S -> Stack (Han T :: S)
  skip> : ∀ {S} -> {T : TyExp} -> Stack S -> Stack (Skip T :: S)

infixr 10 _++_  _::_

data Code : (S S′  : StackType) -> Set where
    skip : ∀ {S} -> Code S S
    _++_ : ∀ {S₀ S₁ S₂} -> Code S₀ S₁ -> Code S₁ S₂ -> Code S₀ S₂
    PUSH : ∀ {T S} -> Val T -> Code S (IVal T :: S)
    ADD : ∀ {S} -> Code (IVal nat :: IVal nat :: S) (IVal nat :: S)
    IF  : ∀ {S S′} (c₁ c₂ : Code S S′) -> Code (IVal bool :: S) S′

    MARK : ∀ {S S′} -> Code S (Han S′ :: Skip S′ :: S)
    HANDLE : ∀ {S S′} -> Code (IVal S′ :: Han S′ :: Skip S′ :: S) (Skip S′ :: S)
    UNMARK : ∀ {S S′} -> Code (IVal S′ :: Skip S′ :: S) (IVal S′ :: S)
    THROW : ∀ {S S′} -> Code S (IVal S′ :: S)


unwindI : StackType -> StackType
unwindI [] = []
unwindI (IVal x :: s) = unwindI s
unwindI (Han x :: s) =  s
unwindI (Skip x :: s) = unwindI s
mutual 
 unwind : ∀ {S S′} -> Code S S′ -> Stack S -> Stack (unwindI S)
 unwind c ε = ε
 unwind c (x > s) = unwind (PUSH x ++ c) s
 unwind c (han> s) = s
 unwind c (skip> s) = unwind skip s

 exec : ∀ {S S′} -> Code S S′ -> Stack S -> Stack S′
 exec skip s = s
 exec (c ++ c₁) s = exec c₁ (exec c s)
 exec (PUSH v) s = v > s
 exec ADD (v > (v₁ > s)) = (v + v₁) > s 
 exec (IF c c₁) (vtrue > s) = exec c s
 exec (IF c c₁) (vfalse > s) = exec c₁ s
 exec MARK y = han> (skip> y)
 exec HANDLE (v > han> y) = y
 exec UNMARK (x > skip> y) = x > y
 exec THROW y = unwind skip {!!}

compile : ∀ {T S} -> Exp T -> Code S (IVal T :: S)
compile (val x) = PUSH x
compile (plus e₁ e₂) = compile e₂ ++ compile e₁ ++ ADD
compile (if b e₁ e₂) = compile b ++ IF (compile e₁) (compile e₂)
compile throw = THROW
compile (catch x x₁) with compile x | compile x₁
... | y | z = MARK ++ y ++ HANDLE ++ z ++ UNMARK

cond : ∀ {T} -> Val bool -> Val T -> Val T -> Val T
cond vtrue x _ = x
cond vfalse _ x₁ = x₁


--mutual
  {-
  correctPlus : ∀ {S} (e e₁ : Exp nat) (s : Stack S) -> ((eval e + eval e₁) > s) ≡ exec ADD (exec (compile e) (exec (compile e₁) s))
  correctPlus e e₁ s = {!!} 

  correctIf : ∀ {S T} (b : Exp bool) (e₁ e₂ : Exp T) (s : Stack S) -> (cond (eval b) (eval e₁) (eval e₂) > s) ≡ exec (IF (compile e₁) (compile e₂)) (exec (compile b) s)
  correctIf b e₁ e₂ s with correct b s
  ... | _ with eval b | exec (compile b) s 
  correctIf b e₁ e₂ s | refl | vtrue | .(vtrue > s) = correct e₁ s
  correctIf b e₁ e₂ s | refl | vfalse | .(vfalse > s) = correct e₂ s
  -}

  --correct : ∀ {T S} (e : Exp T) -> (s : Stack S) -> (eval e > s) ≡ exec (compile e) s
  --correct (val x) s = refl
  --correct (plus e e₁) s = ? --correctPlus e e₁ s
  --correct (if b e₁ e₂) s = ? -- correctIf b e₁ e₂ s
  
