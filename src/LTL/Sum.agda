module Sum where

open import Core


open import Prelude.Sum renaming (Either to _⊎_)

infix 30 _∨_
_∨_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
(xs ∨ ys) n = (xs n) ⊎ (ys n)
