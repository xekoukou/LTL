module LTL.Future where

open import LTL.Core public
open import LTL.Stateless
open import Prelude.Product

◇ᶠ : ∀{ℓ} → (Set ℓ) ʷ → (Set ℓ) ʷ
◇ᶠ A t = ∃ λ u → (t ≤ u) × A u



-- Monadic Structure of Streams

map◇ᶠ : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ] → [ ◇ᶠ Aₛ ⇒ ◇ᶠ Bₛ ]
map◇ᶠ fs s (u , s≤u , a) = u , s≤u , fs u a

return◇ᶠ : ∀{α} → {Aₛ : (Set α) ʷ} → [ Aₛ ⇒ ◇ᶠ Aₛ ]
return◇ᶠ s a = s , diff! zero , a

join◇ᶠ : ∀{α} → {Aₛ : (Set α) ʷ} → [ ◇ᶠ (◇ᶠ Aₛ ) ⇒ ◇ᶠ Aₛ ]
join◇ᶠ s (u , s≤u , t , u≤t , a) = t , leq-trans {{OrdNatLaws}} s≤u u≤t , a


-- For the comonadic laws , see the archive LTL.agda for ◇ₚ
