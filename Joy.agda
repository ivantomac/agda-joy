{-# OPTIONS --cubical --exact-split #-}

-- Tested with Agda 2.6.2.1 and agda-stdlib 1.7.1.

module Joy where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.FromString

open import Category.Functor
open import Data.Bool hiding (T)
  renaming (true to agda-true; false to agda-false)

open import Data.Integer hiding (Negative)
open import Data.Nat
open import Data.Product hiding (swap)
open import Data.String
open import Data.Unit

open import Function

open import Relation.Binary.PropositionalEquality

import Data.Nat.Literals     as ℕ
import Data.Integer.Literals as ℤ

instance
  numberNat : Number ℕ
  numberNat = ℕ.number

instance
  numberInt : Number ℤ
  numberInt = ℤ.number

instance
  negativeInt : Negative ℤ
  negativeInt = ℤ.negative

------------------------------------------- Quotations ----

data Qt (S A B : Set) : Set where
  qt : S → (A → B) → Qt S A B

open RawFunctor ⦃ ... ⦄ public

instance
  qtFunctor : ∀ {S A} → RawFunctor (Qt S A)
  _<$>_ ⦃ qtFunctor ⦄ f (qt s g) = qt s $ f ∘ g

---------------------------------------- Continuations ----

Cont : Set → Set → Set
Cont R A = (A → R) → R

record LiftCont (F : Set → Set) : Set₁ where
  field
    liftCont : ∀ {A B R} → (A → B) → F A → Cont R (F B)

open LiftCont ⦃ ... ⦄ public

instance
  qtLiftCont : ∀ {S A} → LiftCont (Qt S A)
  liftCont ⦃ qtLiftCont ⦄ f (qt s g) k = k $ qt s $ f ∘ g

infix 0 _⇒_

_⇒_ : Set → Set → Set₁
A ⇒ B = ∀ {F R} ⦃ lift : LiftCont F ⦄ → F A → Cont R (F B)

------------------------------------- Quotation Syntax ----

⟦ : ∀ {R S A} → S → Cont R (Qt S A A)
⟦ s = _$ qt s id

⟧ : ∀ {R S A B} {F : Set → Set} ⦃ _ : RawFunctor F ⦄
  → Qt (F S) A B → Cont R (F ((A → B) × S))

⟧ (qt s f) = _$ (f ,_) <$> s

:⟦ : ∀ {R A} → Cont R (Qt ⊤ A A)
:⟦ = ⟦ tt

⟧:
  : ∀ {A B F R} ⦃ lift : LiftCont F ⦄
  → Qt ⊤ A B → F A → Cont R (F B)

⟧: (qt _ f) = liftCont f

⟧· : ∀ {A} → Qt ⊤ ⊤ A → A
⟧· (qt x f) = f x

---------------------------------- Primitive Functions ----

module _ where
  private
    variable A B C R S T : Set

  record Interface (F : Set → Set → Set) : Set₁ where

    infix 0 _⇢_

    _⇢_ : Set → Set → Set
    _⇢_ = F

    field
      true    : S               ⇢ Bool × S
      false   : S               ⇢ Bool × S
      dup     : A × S           ⇢ A × A × S
      pop     : A × S           ⇢ S
      swap    : A × B × S       ⇢ B × A × S
      over    : A × B × S       ⇢ B × A × B × S
      rot     : A × B × C × S   ⇢ C × A × B × S
      i       : (S → T) × S     ⇢ T
      dip     : (S → T) × A × S ⇢ A × T
      stack   : S               ⇢ S × S
      unstack : T × S           ⇢ T

      branch  : (S → T) × (S → T) × Bool × S ⇢ T
      ifte    : (S → T) × (S → T) × (S → Bool × R) × S ⇢ T

open Interface ⦃ ... ⦄ public

instance
  lib : Interface (λ A B → A → B)
  true    ⦃ lib ⦄                 = agda-true  ,_
  false   ⦃ lib ⦄                 = agda-false ,_
  dup     ⦃ lib ⦄ (s @ (x , _))   = x , s
  pop     ⦃ lib ⦄                 = proj₂
  swap    ⦃ lib ⦄ (x , y , s)     = y , x , s
  over    ⦃ lib ⦄ (x , y , s)     = y , x , y , s
  rot     ⦃ lib ⦄ (x , y , z , s) = z , x , y , s
  i       ⦃ lib ⦄ (f , s)         = f s
  dip     ⦃ lib ⦄ (f , x , s)     = x , f s
  stack   ⦃ lib ⦄ s               = s , s
  unstack ⦃ lib ⦄                 = proj₁

  branch ⦃ lib ⦄ (f , t , cond , s) with cond
  ... | agda-true  = t s
  ... | agda-false = f s

  ifte ⦃ lib ⦄ (f , t , test , s) with proj₁ $ test s
  ... | agda-true  = t s
  ... | agda-false = f s

instance
  impl
    : ∀ {F R} ⦃ lift : LiftCont F ⦄
    → Interface (λ A B → F A → Cont R (F B))
  true    ⦃ impl ⦄ = liftCont true
  false   ⦃ impl ⦄ = liftCont false
  dup     ⦃ impl ⦄ = liftCont dup
  pop     ⦃ impl ⦄ = liftCont pop
  swap    ⦃ impl ⦄ = liftCont swap
  over    ⦃ impl ⦄ = liftCont over
  rot     ⦃ impl ⦄ = liftCont rot
  i       ⦃ impl ⦄ = liftCont i
  dip     ⦃ impl ⦄ = liftCont dip
  stack   ⦃ impl ⦄ = liftCont stack
  unstack ⦃ impl ⦄ = liftCont unstack
  branch  ⦃ impl ⦄ = liftCont branch
  ifte    ⦃ impl ⦄ = liftCont ifte

instance
  joyNat
    : ∀ {F R S} ⦃ lift : LiftCont F ⦄
    → Number (F S → Cont R (F (ℕ × S)))
  joyNat .Number.Constraint _ = ⊤
  joyNat .Number.fromNat    n = liftCont $ n ,_

instance
  joyNeg
    : ∀ {F R S} ⦃ lift : LiftCont F ⦄
    → Negative (F S → Cont R (F (ℤ × S)))
  joyNeg .Negative.Constraint _ = ⊤
  joyNeg .Negative.fromNeg    n = liftCont $ fromNeg n ,_

instance
  joyStr
    : ∀ {F R S} ⦃ lift : LiftCont F ⦄
    → IsString (F S → Cont R (F (String × S)))
  joyStr .IsString.Constraint _ = ⊤
  joyStr .IsString.fromString s = liftCont $ s ,_

------------------------------------ Derived Functions ----

popd  : ∀ {A B S}   → A × B × S     ⇒ A × S
dupd  : ∀ {A B S}   → A × B × S     ⇒ A × B × B × S
swapd : ∀ {A B C S} → A × B × C × S ⇒ A × C × B × S

popd  = :⟦ ⟦ pop  ⟧ dip ⟧:
dupd  = :⟦ ⟦ dup  ⟧ dip ⟧:
swapd = :⟦ ⟦ swap ⟧ dip ⟧:

------------------------------------------------ Tests ----

test-define-dup : ∀ {A B S} → A × B × S ⇒ A × B × B × S
test-define-dup = :⟦ dupd ⟧:

test-string : String × ⊤
test-string = :⟦ "blorf" ⟧·

test-empty : ⊤
test-empty = :⟦ ⟧·

test-bool-nat-dupd : ℕ × Bool × Bool × ⊤
test-bool-nat-dupd = :⟦ true 1 dupd ⟧·

test-eq : :⟦ 2 1 dupd ⟧· ≡ (1 , 2 , 2 , tt)
test-eq = refl

test-quote : ∀ {A} → (A → A) × ⊤
test-quote = :⟦ ⟦ ⟧ ⟧·

test-i : Bool × ⊤
test-i = :⟦ ⟦ true ⟧ i ⟧·
