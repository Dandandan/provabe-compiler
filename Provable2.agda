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
    VBool : Bool -> Val bool
    VNat : Nat -> Val nat

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
VNat Zero + b = b
VNat (Succ x) + VNat b = VNat (x :+ b)

data Maybe {a} (A : Set a) : Set a where
  Just    : (x : A) → Maybe A
  Nothing : Maybe A

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

infixr 10 _++_  _::_ han> skip>

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
unwindI (Han x :: s) =  s
unwindI (_ :: s) = unwindI s

-- Excecution state:
data State (t : StackType) : Set where
    -- Normal operation
    ✓⟦_⟧ : (s : Stack t) -> State t
    -- Exceptional state (TODO: add index label)
    !⟦_⟧ : (s : Stack (unwindI t)) -> State t

mutual 
 unwind : ∀ {S} -> Stack S -> Stack (unwindI S)
 unwind ε = ε
 unwind (x > s) =  unwind s
 unwind (han> s) = s
 unwind (skip> s) = unwind s

 exec : ∀ {S S′} -> Code S S′ -> State S -> State S′
 -- Cruft:
 exec skip       x = x
 exec (x₀ ++ x₁) s = exec x₁ (exec x₀ s)
 -- Normal operation:
 exec (PUSH x)   ✓⟦ s ⟧                  = ✓⟦ x > s ⟧
 exec ADD        ✓⟦ x₀ > (x₁ > s) ⟧      = ✓⟦ (x₀ + x₁) > s ⟧
 exec (IF x₀ x₁) ✓⟦ VBool True > s ⟧     = exec x₀ ✓⟦ s ⟧
 exec (IF x₀ x₁) ✓⟦ VBool False > s ⟧    = exec x₁ ✓⟦ s ⟧
 exec MARK       ✓⟦ s ⟧                  = ✓⟦ han> (skip> s) ⟧
 exec HANDLE     ✓⟦ x > han> (skip> s) ⟧ = ✓⟦ skip> s ⟧
 exec UNMARK     ✓⟦ x > skip> s ⟧        = ✓⟦ x > s ⟧
 exec THROW      ✓⟦ s ⟧                  = !⟦ unwind s ⟧
 -- Exception handling:
 exec (PUSH x)   !⟦ s ⟧                  = !⟦ s ⟧
 exec ADD        !⟦ s ⟧                  = !⟦ s ⟧
 exec (IF x₀ x₁) !⟦ s ⟧                  = exec x₀ !⟦ s ⟧
 exec MARK       !⟦ s ⟧                  = !⟦ {!!} ⟧
 exec HANDLE     !⟦ s ⟧                  = ✓⟦ s ⟧
 exec UNMARK     !⟦ s ⟧                  = !⟦ s ⟧
 exec THROW      !⟦ s ⟧                  = !⟦ s ⟧

compile : ∀ {T S} -> Exp T -> Code S (IVal T :: S)
compile (val x) = PUSH x
compile (plus e₁ e₂) = compile e₂ ++ compile e₁ ++ ADD
compile (if b e₁ e₂) = compile b ++ IF (compile e₁) (compile e₂)
compile throw = THROW
compile (catch x h) with compile x | compile h
... | xcode | hcode = MARK ++ xcode ++ HANDLE ++ hcode ++ UNMARK

cond : ∀ {T} -> Val bool -> Val T -> Val T -> Val T
cond (VBool True) x _ = x
cond _ _ x₁ = x₁

{--
maybeStack : forall {T : Item} -> Maybe {!!}  -> StackType
maybeStack Nothing =  []
maybeStack {t} (Just x) =  t :: []

conv : forall {T} (m : Maybe (Val T)) -> Stack (maybeStack m)
conv (Just x) = x > ε
conv Nothing = ε
--}
{--
mutual
  correct : ∀ {T S} (e : Exp T) -> (s : Stack S) -> (conv (eval e) > s) ≡ exec (compile e) s
  correct (val x) s = refl
  correct (plus e e₁) s = ? --correctPlus e e₁ s
  correct (if b e₁ e₂) s = ? -- correctIf b e₁ e₂ s
--}