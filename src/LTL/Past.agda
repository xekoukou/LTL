module LTL.Past where

open import Data.Product
open import Data.Nat 
open import Data.Nat.Properties

open import LTL.Core
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

_>>=◇ₚ_ : ∀{α} → {Aₛ Bₛ : (Set α) ʷ} → [ ◇ₚ Aₛ ] → [ Aₛ ⇒ ◇ₚ Bₛ ] → [ ◇ₚ Bₛ ]
(ma >>=◇ₚ f) t
  = let (s , s≤t , a) = ma t
        (u , u≤s , b) = f s a
    in u , (≤-trans u≤s s≤t) , b


-- For the monadic laws , check the archive.
