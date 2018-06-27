module Core where

open import Agda.Primitive public
open import Prelude.Nat public
open import Prelude.Semiring public
open import Prelude.Nat.Properties public
open import Prelude.Ord public
open import Prelude.Unit
open import Prelude.Function using (_∘′_ ; id)
open import Prelude.Equality public
open import Prelude.Empty
open import Prelude.Product

-- Homogeneous FRP

_ʷ : ∀ {α} → Set α → Set α
A ʷ =  Nat → A

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


⟦_⟧ : ∀ {α} → (Set α) ʷ → Set α
⟦ Aₛ ⟧ = ∀ {n} → Aₛ n

to-⟦ :  ∀{α} → {Aₛ : (Set α) ʷ} → (F : [ Aₛ ]) → ⟦ Aₛ ⟧
to-⟦ F {n} = F n

to-[ :  ∀{α} → {Aₛ : (Set α) ʷ} → (F : ⟦ Aₛ ⟧) → [ Aₛ ]
to-[ F n = F {n}

! : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → !ₛ Aₛ
! xs = xs 0

lemma2 : ∀ {α} → {Aₛ : (Set α) ʷ } → !ₛ Aₛ ≡ ! {Aₛ = ⟨ Set α ⟩ } Aₛ
lemma2 = refl


○ : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → [ ○ₛ Aₛ ]
○ xs n = xs (suc n)

lemma3 : ∀ {α} {Aₛ : (Set α) ʷ} → ○ₛ Aₛ ≡ ○ Aₛ
lemma3 = refl

_∷_ : ∀ {α} {Aₛ : (Set α) ʷ} → ! Aₛ → [ ○ Aₛ ] → [ Aₛ ]
(x ∷ xs) 0 = x
(x ∷ xs) (suc n) = xs n



_⟨_,,_] : ∀ {α} → (Set α)ʷ → Nat → Nat → (Set α)
As ⟨ ℓ ,, n ] = (∀ m → (ℓ < m) → (m ≤ n) → As(m))

_[_,,_] : ∀ {α} → (Set α)ʷ → Nat → Nat → (Set α)
As [ ℓ ,, n ] = (∀ m → (ℓ ≤ m) → (m ≤ n) → As(m))

_[_,,_⟩ : ∀ {α} → (Set α)ʷ → Nat → Nat → (Set α)
As [ ℓ ,, n ⟩ = (∀ m → (ℓ ≤ m) → (m < n) → As(m))


_beforeˡ_ : ∀{ℓ} {A : (Set ℓ) ʷ} → ∀{s u v} → (A [ s ,, v ⟩) → (u ≤ v) → A [ s ,, u ⟩
(σ beforeˡ u≤v) t s≤t t<u = σ t s≤t (inv-suc-monotone w) where
  w = leq-trans {{OrdNatLaws}} (suc-monotone t<u) u≤v


_beforeʳ_ : ∀{ℓ} {A : (Set ℓ) ʷ} → ∀{s u v} → A [ s ,, v ⟩ → (u < v) → A [ s ,, u ]
(σ beforeʳ diff k1 eq1) t s≤t (diff k eq) = σ t s≤t (diff (k1 + k) a) where
  w = trans eq1 (sym (add-suc-r k1 _))
  q = trans w (cong (_+_ k1) eq)
  e = trans q (add-suc-r _ _)
  a = trans e (cong suc (add-assoc k1 k _))


_∈_ : ∀ {α β} {A : Set α} → A → (A → Set β) → Set β
x ∈ A = A x

_∉_ : ∀ {α β} {A : Set α} → A → (A → Set β) → Set β
_∉_ {α} {β} x A = (A x) → ⊥′ {β}


∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _
