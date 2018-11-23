module LTL.Core where

open import Agda.Primitive
open import Data.Nat public hiding (_⊔_)
open import Data.Empty public
open import Data.Nat.Properties public
open import Data.Product public
open import Relation.Binary.PropositionalEquality hiding ([_]) public

-- Homogeneous FRP

_ʷ : ∀ {α} → Set α → Set α
A ʷ =  ℕ → A

⟨_⟩ : ∀ {α} {A : Set α} → A → (A ʷ)
⟨ x ⟩ n = x

!ₛ : ∀ {α} {A : Set α} → (Aₛ : A ʷ) → A
!ₛ x = x zero

○ₛ : ∀ {α} {A : Set α} → (Aₛ : A ʷ) → A ʷ
○ₛ xs n = xs (suc n)

-- Heterogeneous FRP

[_] : ∀ {α} → (Set α) ʷ → Set α
[ Aₛ ] = ∀ n → Aₛ n


lemma1 : ∀{a} {A : Set a} → A ʷ ≡ [ ⟨ A ⟩ ]
lemma1 = refl


! : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → !ₛ Aₛ
! xs = xs 0

lemma2 : ∀ {α} → {Aₛ : (Set α) ʷ } → !ₛ Aₛ ≡ ! {Aₛ = ⟨ Set α ⟩ } Aₛ
lemma2 = refl


○ : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → [ ○ₛ Aₛ ]
○ xs n = xs (suc n)

lemma3 : ∀ {α} {Aₛ : (Set α) ʷ} → ○ₛ Aₛ ≡ ○ Aₛ
lemma3 = refl

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

