module LTL.Until where

open import LTL.Core public
open import Agda.Primitive
open import Prelude.Product

infixr 2 _U_

_U_ : ∀{ℓ m} → (Set ℓ) ʷ → (Set m) ʷ → (Set (ℓ ⊔ m)) ʷ
(A U B) t = ∃ λ u → (t ≤ u) × (A [ t ,, u ⟩) × B u
