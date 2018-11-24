module LTL.Since where


open import Data.Product
open import Data.Nat 

open import LTL.Core



_S_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
(As S Bs) n = (∃ λ ℓ → (ℓ ≤ n) × (As ⟨ ℓ ,, n ]) × Bs ℓ)

_▷ₚ_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
(As ▷ₚ Bs)(n) = (∀ ℓ → (ℓ ≤ n) → As ⟨ ℓ ,, n ] → Bs ℓ)
