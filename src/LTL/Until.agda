module LTL.Until where

open import Agda.Primitive
open import Data.Product
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties


open import LTL.Core

infixr 2 _U_

_U_ : ∀{ℓ m} → (Set ℓ) ʷ → (Set m) ʷ → (Set (ℓ ⊔ m)) ʷ
(A U B) t = ∃ λ u → (t ≤ u) × (A [ t ,, u ⟩) × B u


_Uₛ_ : ∀{ℓ m} → (Set ℓ) ʷ → (Set m) ʷ → (Set (ℓ ⊔ m)) ʷ
(A Uₛ B) t = ∃ λ u → (t ≤ u) × (A [ t ,, u ]) × B u
