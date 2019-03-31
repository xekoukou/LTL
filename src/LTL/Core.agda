module LTL.Core where

open import Agda.Primitive
open import Data.Nat 
open import Data.Fin as F using (Fin)
open import Data.Empty
open import Data.Nat.Properties
open import Data.Product
open import Relation.Nullary
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

-- Homogeneous FRP

_ʷ : ∀ {α} → Set α → Set α
A ʷ =  ℕ → A

_ʷ∥_ : ∀{ℓ} → Set ℓ → ℕ → Set ℓ
A ʷ∥ m = Fin m → A

⟨_⟩ : ∀ {α} {A : Set α} → A → (A ʷ)
⟨ x ⟩ n = x

!ₛ : ∀ {α} {A : Set α} → (Aₛ : A ʷ) → A
!ₛ x = x zero

○ₛ : ∀ {α} {A : Set α} → (Aₛ : A ʷ) → A ʷ
○ₛ xs n = xs (suc n)

○ᶠₛ : ∀ {α} {A : Set α} → ∀{m} → (Aₛ : A ʷ∥ (suc m)) → A ʷ∥ m
○ᶠₛ xs n = xs (F.suc n)


○ₙₛ : ∀ {α} {A : Set α} → (Aₛ : A ʷ) → ℕ → A ʷ
○ₙₛ xs m n = xs (m + n)

-- Heterogeneous FRP

[_] : ∀ {α} → (Set α) ʷ → Set α
[ Aₛ ] = ∀ n → Aₛ n

[_]∥ : ∀{ℓ m} → (Set _) ʷ∥ m → Set ℓ
[ Aₛ ]∥ = (fn : Fin _) → Aₛ fn

! : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → !ₛ Aₛ
! xs = xs 0

○ : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → [ ○ₛ Aₛ ]
○ xs n = xs (suc n)

○ᶠ : ∀ {α m} {Aₛ : (Set α) ʷ∥ (suc m)} → [ Aₛ ]∥ → [ ○ᶠₛ Aₛ ]∥
○ᶠ xs n = xs (F.suc n)

○ₙ : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → (m : ℕ) → [ ○ₙₛ Aₛ m ]
○ₙ xs m n = xs (m + n)

_∷ₛ_ : ∀ {α} {Aₛ : (Set α) ʷ} → ! Aₛ → [ ○ Aₛ ] → [ Aₛ ]
(x ∷ₛ xs) 0 = x
(x ∷ₛ xs) (suc n) = xs n



_⟨_,,_] : ∀ {α} → (Set α)ʷ → ℕ → ℕ → (Set α)
As ⟨ ℓ ,, n ] = (∀ m → (ℓ < m) → (m ≤ n) → As(m))

_[_,,_] : ∀ {α} → (Set α)ʷ → ℕ → ℕ → (Set α)
As [ ℓ ,, n ] = (∀ m → (ℓ ≤ m) → (m ≤ n) → As(m))

_[_,,_⟩ : ∀ {α} → (Set α)ʷ → ℕ → ℕ → (Set α)
As [ ℓ ,, n ⟩ = (∀ m → (ℓ ≤ m) → (m < n) → As(m))


_beforeˡ_ : ∀{ℓ} {A : (Set ℓ) ʷ} → ∀{s u v} → (A [ s ,, v ⟩) → (u ≤ v) → A [ s ,, u ⟩
(σ beforeˡ u≤v) t s≤t t<u = σ t s≤t w where
  w = ≤-trans t<u u≤v


_beforeʳ_ : ∀{ℓ} {A : (Set ℓ) ʷ} → ∀{s u v} → A [ s ,, v ⟩ → (u < v) → A [ s ,, u ]
(σ beforeʳ u<v) t s≤t t≤u = σ t s≤t w where
  w = ≤-trans (s≤s t≤u) u<v


[]-extₛ : ∀ {α l} → {A : Set α} → ⟨ A ⟩ [ 0 ,, l ] → A ʷ → A ʷ
[]-extₛ {l = l} ln as n
  = case (n ≤? l) of
     λ { (yes p) → ln n z≤n p
       ; (no ¬p) → as (n ∸ l)}


[]-ext : ∀ {α l} → {A : (Set α) ʷ} → {B : (Set α) ʷ} → A [ 0 ,, l ] → [ B ] → [ []-extₛ {l = l} (λ m _ _ → A m) B ]
[]-ext {l = l} ln as n with (n ≤? l)
[]-ext {l = l} ln as n | yes p = ln n z≤n p
[]-ext {l = l} ln as n | no ¬p = as (n ∸ l)

[⟩-extₛ : ∀ {α l} → {A : Set α} → ⟨ A ⟩ [ 0 ,, l ⟩ → A ʷ → A ʷ
[⟩-extₛ {l = l} ln as n
  = case (n <? l) of
     λ { (yes p) → ln n z≤n p
       ; (no ¬p) → as (n ∸ l)}



-- _∈_ : ∀ {α β} {A : Set α} → A → (A → Set β) → Set β
-- x ∈ A = A x

-- _∉_ : ∀ {α β} {A : Set α} → A → (A → Set β) → Set β
-- _∉_ {α} {β} x A = (A x) → ⊥



-- -- Well ordering of < on an interval

-- _≮[_]_ : ℕ → ℕ → ℕ → Set
-- s ≮[ zero  ] u = ⊥
-- s ≮[ suc n ] u = ∀ {t} → (s ≤ t) → (t < u) → (s ≮[ n ] t)


-- <-wo′ : ∀ n {s u} → (s ≤ u) → (u ≤ s + n) → (s ≮[ suc n ] u)
-- <-wo′ zero s≤u u≤s+n s≤t t<u with w where
--   w = leq-antisym {{OrdℕLaws}} s≤u (transport (λ z → _ < suc z) (add-zero-r _) u≤s+n)
-- <-wo′ zero s≤u u≤s+n s≤t t<u | refl = ⊥-elim (leq-less-antisym {{OrdℕLaws}} s≤t t<u)
-- <-wo′ (suc n) {s} s≤u u≤s+n {t} s≤t t<u = <-wo′ n s≤t (transport (λ z → t < z) (add-suc-r s n) w) where
--   w = inv-suc-monotone (leq-trans {{OrdℕLaws}} (suc-monotone t<u) u≤s+n)


-- <-wo : ∀ {s u} → (s ≤ u) → ∃ λ n → (s ≮[ n ] u)
-- <-wo (diff k eq) = suc k , <-wo′ k (diff k eq) (diff zero (sym (trans eq (cong suc (add-commute k _)))))

