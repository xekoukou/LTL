module Globally where

open import Stateless



-- □ A is "A holds globally in the future"

□ᶠ : ∀{ℓ} → (Set ℓ) ʷ → (Set ℓ) ʷ
□ᶠ A t = ∀ u → (t ≤ u) → A u

-- Comonad structure of □

extend : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ A ⇒ B ] → [ □ᶠ A ⇒ □ᶠ B ]
extend f s a u s≤t = f u (a u s≤t)  

extract : ∀{ℓ} {A : (Set ℓ) ʷ} → [ □ᶠ A ⇒ A ]
extract n a = a n (diff! zero)

duplicate : ∀{ℓ} {A : (Set ℓ) ʷ} → [ □ᶠ A ⇒ □ᶠ (□ᶠ A) ]
duplicate s a t s≤t u t≤u = a u (leq-trans {{OrdNatLaws}} s≤t t≤u)

-- Applicative structure of □

pureᶠ : ∀{ℓ} {A : (Set ℓ) ʷ} → [ A ] → [ □ᶠ A ]
pureᶠ a s t s≤t = a t


_⟨*⟩ᶠʷ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ □ᶠ (A ⇒ B) ] → [ □ᶠ A ] → [ □ᶠ B ]
(f ⟨*⟩ᶠʷ a) s t s≤t = f s t s≤t (a s t s≤t)

-- Pointwise stronger version
_⟨*⟩ᶠ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → ∀{s} → ( □ᶠ (A ⇒ B) ⇒ □ᶠ A ⇒  □ᶠ B ) s
(f ⟨*⟩ᶠ a) t s≤t = f t s≤t (a t s≤t)