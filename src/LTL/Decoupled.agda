module LTL.Decoupled where

open import Agda.Primitive
open import LTL.Core public
open import LTL.Stateless
open import LTL.Causal
open import LTL.Globally
open import LTL.CatHetSt
open import Prelude.Product

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

_·ᵈˡ_ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → ⟦ (B ⊵ C) ⇒ (A ▻ B) ⇒ (A ▻ C) ⟧
(g ·ᵈˡ f) t s≤t σ = g t s≤t (f $ᵈˡ σ)


_·ᵈʳ_ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → ⟦ (B ▻ C) ⇒ (A ⊵ B) ⇒ (A ▻ C) ⟧
(g ·ᵈʳ f) t s≤t σ = g t s≤t (f $ᶜʳ σ) 

_·ᵈˡʳ_ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → ⟦ (B ▻ C) ⇒ (A ▻ B) ⇒ (A ▻ C) ⟧
(g ·ᵈˡʳ f) = couple _ g ·ᵈˡ f

