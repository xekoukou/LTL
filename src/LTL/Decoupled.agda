module Decoupled where

open import Core
open import Stateless
open import Causal
open import Globally

infixr 2 _▻_
-- infixr 3 _⋙ˡ_ _⋙ʳ_ _⋙ˡʳ_


-- Decoupled function space

_▻_ : ∀{ℓ m} → (Set ℓ) ʷ → (Set m) ʷ → (Set (ℓ ⊔ m)) ʷ
(A ▻ B) t = ∀ u → (t ≤ u) → (A [ t ,, u ⟩) → B u

-- Upcast a decoupled function to a causal function

couple : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ (A ▻ B) ⇒ (A ⊵ B) ]
couple {_} {_} {A} {B} s f u s≤u σ = f u s≤u σ′ where
  σ′ : A [ s ,, u ⟩
  σ′ t s≤t t<u = σ t s≤t (lt-to-leq {{OrdNat}} t<u)

-- Variants on composition which produce decoupled functions


_$ᵈˡ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → ∀{s u} → (A ▻ B) s → (A [ s ,, u ⟩) → (B [ s ,, u ])
(f $ᵈˡ σ) t s≤t t≤u = f t s≤t (σ beforeˡ t≤u)

_·ᵈˡ_ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → ⟦ (A ▻ B) ⇒ (B ⊵ C) ⇒ (A ▻ C) ⟧
(f ·ᵈˡ g) t s≤t σ = g t s≤t (f $ᵈˡ σ)


_·ᵈʳ_ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → ⟦ (A ⊵ B) ⇒ (B ▻ C) ⇒ (A ▻ C) ⟧
(f ·ᵈʳ g) t s≤t σ = g t s≤t (f $ᶜʳ σ) 

_·ᵈˡʳ_ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → ⟦ (A ▻ B) ⇒ (B ▻ C) ⇒ (A ▻ C) ⟧
(f ·ᵈˡʳ g) = f ·ᵈˡ couple _ g


-- fix : ∀ {A} → ⟦ (A ▻ A) ⇒ □ᶠ A ⟧ 
-- fix {A} {s} f u s≤u = f u s≤u (σ u) where
--   σ : (u : Nat) → A [ s ,, u ⟩
--   σ u t s≤t t<u = f t s≤t (σ t)
