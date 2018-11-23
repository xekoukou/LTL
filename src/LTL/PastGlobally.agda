module LTL.PastGlobally where

open import LTL.Core public
open import LTL.Stateless
open import LTL.CatHetSt
open import Data.Product

□ₚ : ∀ {α} → (Set α) ʷ → (Set α) ʷ
(□ₚ As)(n) = (∀ m → (m ≤ n) → As(m))


map□ₚ : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ] → [ □ₚ Aₛ ⇒ □ₚ Bₛ ]
map□ₚ f s a u s≤u = f u (a u s≤u)


-- Applicative Structure of □ₚ


pureᵖ : ∀{ℓ} {A : (Set ℓ) ʷ} → [ A ] → [ □ₚ A ]
pureᵖ a s t t≤s = a t


_⟨*⟩ᵖ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ □ₚ (A ⇒ B) ] → [ □ₚ A ] → [ □ₚ B ]
(f ⟨*⟩ᵖ a) s t t≤s = f s t t≤s (a s t t≤s)



-- Comonadic Structure of Streams


extract□ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ □ₚ Aₛ ⇒ Aₛ ]
extract□ₚ s a = a s ≤-refl


duplicate□ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ □ₚ Aₛ ⇒ □ₚ (□ₚ Aₛ) ]
duplicate□ₚ s a u u≤s t t≤u = a t (≤-trans t≤u u≤s)

extend□ₚ : ∀{α} → {Aₛ Bₛ : (Set α) ʷ} → [ □ₚ Aₛ ⇒ Bₛ ] → [ □ₚ Aₛ ] → [ □ₚ Bₛ ]
extend□ₚ f a t s s≤t = f s (a s)

-- For the properties of Commonads , check http://hackage.haskell.org/package/comonad-5.0.4#readme
-- If necessary , they can be proven.

-- For a proof check the archive for a different definition of □ₚ .
postulate
  exdp-proof : ∀{α} → {Aₛ : (Set α) ʷ} → ∀ n → (extract□ₚ {Aₛ = □ₚ Aₛ} · (duplicate□ₚ {Aₛ = Aₛ})) n ≡ ids {Aₛ = □ₚ Aₛ} n
  mexdp-proof : ∀{α} → {Aₛ : (Set α) ʷ} → ∀ n xs → (map□ₚ (extract□ₚ {Aₛ = Aₛ}) · duplicate□ₚ {Aₛ = Aₛ}) n xs ≡ ids {Aₛ = □ₚ Aₛ} n xs




-- Is this useful?
-- _⟨*⟩ᵖ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → ∀{s} → ( □ₚ (A ⇒ B) ⇒ □ₚ A ⇒  □ₚ B ) s
-- (f ⟨*⟩ᵖ a) t t≤s = f t t≤s (a t t≤s)
