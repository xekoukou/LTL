module LTL.Future where

open import LTL.Core public
open import LTL.Stateless
open import Data.Product

◇ᶠ : ∀{ℓ} → (Set ℓ) ʷ → (Set ℓ) ʷ
◇ᶠ A t = ∃ λ u → (t ≤ u) × A u

-- Functor Structure of Streams

map◇ᶠ : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ] → [ ◇ᶠ Aₛ ⇒ ◇ᶠ Bₛ ]
map◇ᶠ fs s (u , s≤u , a) = u , s≤u , fs u a


-- Not Applicative because there is no synchronization between the input and the function.
-- _⟨*⟩◇ᶠ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ ◇ᶠ (A ⇒ B) ] → [ ◇ᶠ A ] → [ ◇ᶠ B ]
-- (f ⟨*⟩◇ᶠ a) t = let (s , t≤s , ff) = f t in {!!} , ({!!} , {!!})

-- Monadic Structure of Streams

pure◇ᶠ : ∀{α} → {Aₛ : (Set α) ʷ} → [ Aₛ ⇒ ◇ᶠ Aₛ ]
pure◇ᶠ s a = s , (≤-refl , a)

join◇ᶠ : ∀{α} → {Aₛ : (Set α) ʷ} → [ ◇ᶠ (◇ᶠ Aₛ ) ⇒ ◇ᶠ Aₛ ]
join◇ᶠ s (u , s≤u , t , u≤t , a) = t , ((≤-trans s≤u u≤t) , a)

_>>=◇ᶠ_ : ∀{α} → {Aₛ Bₛ : (Set α) ʷ} → [ ◇ᶠ Aₛ ] → [ Aₛ ⇒ ◇ᶠ Bₛ ] → [ ◇ᶠ Bₛ ]
(ma >>=◇ᶠ f) t
  = let (s , t≤s , a) = ma t
        (u , s≤u , b) = f s a
    in u , ≤-trans t≤s s≤u , b


-- For the monadic laws , see the archive LTL.agda for ◇ₚ
