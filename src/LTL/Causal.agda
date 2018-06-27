module Causal where

open import Core
open import Stateless
open import Globally
open import CatHetSt

infixr 2 _⊵_
infixr 3 _$ᶜ_
infixr 3 _$ᶜʷ_


-- A ⊵ B is the causal function space from A to B

_⊵_ : ∀{ℓ m} → (Set ℓ) ʷ → (Set m) ʷ → (Set (ℓ ⊔ m)) ʷ 
(A ⊵ B) t = ∀ u → (t ≤ u) → (A [ t ,, u ]) → B u

-- Categorical structure

arr : ∀{ℓ m} {Aₛ : (Set ℓ) ʷ} {Bₛ : (Set m) ʷ} → [ □ᶠ (Aₛ ⇒ Bₛ) ⇒ (Aₛ ⊵ Bₛ) ]
arr s f u s≤t σ = f _ s≤t (σ _ s≤t (diff! zero)) 

identity : ∀{ℓ} {Aₛ : (Set ℓ) ʷ} → [ Aₛ ⊵ Aₛ ]
identity {_} {Aₛ} = arr $ʷ pureᶠ ids

_before_ : ∀{ℓ} {A : (Set ℓ) ʷ} → ∀{s u v} → (A [ s ,, v ]) → (u ≤ v) → (A [ s ,, u ])
(σ before u≤v) t s≤t t≤u = σ t s≤t (leq-trans {{OrdNatLaws}} t≤u u≤v)

_after_ : ∀{ℓ} {A : (Set ℓ) ʷ} → ∀{s t v} → (A [ s ,, v ]) → (s ≤ t) → (A [ t ,, v ])
(σ after s≤t) t t≤u u≤v = σ t (leq-trans {{OrdNatLaws}} s≤t t≤u) u≤v

_$ᶜ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → ∀{s u} → (A ⊵ B) s → A [ s ,, u ] → B [ s ,, u ]
(f $ᶜ σ) t s≤t t≤u = f t s≤t (σ before t≤u) 

-- Weaker version of the previous one.
_$ᶜʷ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ (A ⊵ B) ] → ∀{s u} → A [ s ,, u ] → B [ s ,, u ]
(f $ᶜʷ σ) t s≤t t≤u = f _ t s≤t (σ before t≤u)


_$ᶜʳ_ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → ∀{s u} → (A ⊵ B) s → (A [ s ,, u ⟩) → (B [ s ,, u ⟩)
(f $ᶜʳ σ) t s≤t t<u = f t s≤t (σ beforeʳ t<u)

_·ᶜ_ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → ∀{s} → ((A ⊵ B) ⇒ (B ⊵ C) ⇒ (A ⊵ C)) s
(f ·ᶜ g ) t s≤t σ = g t s≤t (f $ᶜ σ) 

-- weaker version of the previous one.
_·ᶜʷ_ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → [ A ⊵ B ] → [ B ⊵ C ] → [ A ⊵ C ]
(f ·ᶜʷ g ) s t s≤t σ = g s t s≤t (f $ᶜʷ σ)
