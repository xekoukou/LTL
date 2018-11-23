module LTL.Past where

open import LTL.Core public
open import Data.Product
open import LTL.Stateless

◇ₚ : ∀ {α} → (Set α)ʷ → (Set α)ʷ
(◇ₚ As) n = (∃ λ m → (m ≤ n) × As(m))


-- Monadic Structure of Streams

map◇ₚ : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ] → [ ◇ₚ Aₛ ⇒ ◇ₚ Bₛ ]
map◇ₚ fs s (m , m≤s , a) = m , m≤s , fs m a

return◇ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ Aₛ ⇒ ◇ₚ Aₛ ]
return◇ₚ s a = s , ≤-refl , a

join◇ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ ◇ₚ (◇ₚ Aₛ ) ⇒ ◇ₚ Aₛ ]
join◇ₚ s (m , m≤s , t , t≤m , a) = t , ≤-trans t≤m m≤s , a

-- Implement this
-- _>>=◇ₚ_ = 
-- For the monadic laws , check the archive.
