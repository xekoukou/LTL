module LTL.Globally where

open import LTL.Core public
open import LTL.Stateless



-- □ A is "A holds globally in the future"

□ᶠ : ∀{ℓ} → (Set ℓ) ʷ → (Set ℓ) ʷ
□ᶠ A t = ∀ u → (t ≤ u) → A u


map□ᶠ : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ] → [ □ᶠ Aₛ ⇒ □ᶠ Bₛ ]
map□ᶠ f s a u s≤u = f u (a u s≤u)



-- Comonad structure of □

extend□ᶠ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ A ⇒ B ] → [ □ᶠ A ⇒ □ᶠ B ]
extend□ᶠ f s a u s≤t = f u (a u s≤t)  

extract□ᶠ : ∀{ℓ} {A : (Set ℓ) ʷ} → [ □ᶠ A ⇒ A ]
extract□ᶠ n a = a n ≤-refl

duplicate□ᶠ : ∀{ℓ} {A : (Set ℓ) ʷ} → [ □ᶠ A ⇒ □ᶠ (□ᶠ A) ]
duplicate□ᶠ s a t s≤t u t≤u = a u (≤-trans s≤t t≤u)


-- Applicative structure of □

pureᶠ : ∀{ℓ} {A : (Set ℓ) ʷ} → [ A ] → [ □ᶠ A ]
pureᶠ a s t s≤t = a t


_⟨*⟩ᶠ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ □ᶠ (A ⇒ B) ] → [ □ᶠ A ] → [ □ᶠ B ]
(f ⟨*⟩ᶠ a) s t s≤t = f s t s≤t (a s t s≤t)

-- Not useful
-- _⟨*⟩ᶠ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → ∀{s} → ( □ᶠ (A ⇒ B) ⇒ □ᶠ A ⇒  □ᶠ B ) s
-- (f ⟨*⟩ᶠ a) t s≤t = f t s≤t (a t s≤t)
