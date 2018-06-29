module LTL.Since where

open import LTL.Core public
open import Prelude.Product



_S_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
(As S Bs) n = (∃ λ ℓ → (ℓ ≤ n) × (As ⟨ ℓ ,, n ]) × Bs ℓ)

_▷ₚ_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
(As ▷ₚ Bs)(n) = (∀ ℓ → (ℓ ≤ n) → As ⟨ ℓ ,, n ] → Bs ℓ)
