module LTL.PastGlobally where

open import LTL.Core public
open import LTL.Stateless
open import LTL.CatHetSt
open import Prelude.Product

□ₚ : ∀ {α} → (Set α) ʷ → (Set α) ʷ
(□ₚ As)(n) = (∀ m → (m ≤ n) → As(m))


-- Comonadic Structure of Streams

map□ₚ : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ] → [ □ₚ Aₛ ⇒ □ₚ Bₛ ]
map□ₚ f s a u s≤u = f u (a u s≤u)


extract□ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ □ₚ Aₛ ⇒ Aₛ ]
extract□ₚ s a = a s (diff! zero)


duplicate□ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ □ₚ Aₛ ⇒ □ₚ (□ₚ Aₛ) ]
duplicate□ₚ s a u u≤s t t≤u = a t (leq-trans {{OrdNatLaws}} t≤u u≤s)

-- For a proof check the archive for a different definition of □ₚ .
postulate
  exdp-proof : ∀{α} → {Aₛ : (Set α) ʷ} → ∀ n → (extract□ₚ {Aₛ = □ₚ Aₛ} · (duplicate□ₚ {Aₛ = Aₛ})) n ≡ ids {Aₛ = □ₚ Aₛ} n
  mexdp-proof : ∀{α} → {Aₛ : (Set α) ʷ} → ∀ n xs → (map□ₚ (extract□ₚ {Aₛ = Aₛ}) · duplicate□ₚ {Aₛ = Aₛ}) n xs ≡ ids {Aₛ = □ₚ Aₛ} n xs


-- Applicative Structure of □ₚ


pureᵖ : ∀{ℓ} {A : (Set ℓ) ʷ} → [ A ] → [ □ₚ A ]
pureᵖ a s t t≤s = a t


_⟨*⟩ᵖʷ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ □ₚ (A ⇒ B) ] → [ □ₚ A ] → [ □ₚ B ]
(f ⟨*⟩ᵖʷ a) s t t≤s = f s t t≤s (a s t t≤s)

-- Pointwise stronger version
_⟨*⟩ᵖ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → ∀{s} → ( □ₚ (A ⇒ B) ⇒ □ₚ A ⇒  □ₚ B ) s
(f ⟨*⟩ᵖ a) t t≤s = f t t≤s (a t t≤s)
