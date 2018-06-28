module LTL.PolConsts where

open import LTL.Stateless
open import LTL.Core public

-- Polymorphic Constants

const₁ : ∀ {α β} → {Aₛ : (Set α) ʷ} → {F : Set α → Set β} → (∀{A} → F A) → [ ⟨ F ⟩ $ʷ Aₛ ]
const₁ {Aₛ = Aₛ} k = ⟨ (λ A → k {A}) ⟩ $ʷ Aₛ

const₂ : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} →  {F : Set α → Set β → Set γ} →  (∀{A B} → F A B) → [ ⟨ F ⟩ $ʷ Aₛ $ʷ Bₛ ]
const₂ {Aₛ = Aₛ} {Bₛ = Bₛ} k = ⟨ (λ A B → k {A} {B}) ⟩ $ʷ Aₛ $ʷ Bₛ

const₃ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {F : Set α → Set β → Set γ → Set δ} →  (∀{A B C} → F A B C) → [ ⟨ F ⟩ $ʷ Aₛ $ʷ Bₛ $ʷ Cₛ ] 
const₃ {Aₛ = Aₛ} {Bₛ = Bₛ} {Cₛ = Cₛ} k = ⟨ (λ A B C → k {A} {B} {C}) ⟩ $ʷ Aₛ $ʷ Bₛ $ʷ Cₛ

const₄ : ∀ {α β γ δ ε} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → {F : Set α → Set β → Set γ → Set δ → Set ε} →  (∀{A B C D} → F A B C D) → [ ⟨ F ⟩ $ʷ Aₛ $ʷ Bₛ $ʷ Cₛ $ʷ Dₛ ] 
const₄ {Aₛ = Aₛ} {Bₛ = Bₛ} {Cₛ = Cₛ} {Dₛ = Dₛ} k = ⟨ (λ A B C D → k {A} {B} {C} {D} ) ⟩ $ʷ Aₛ $ʷ Bₛ $ʷ Cₛ $ʷ Dₛ
