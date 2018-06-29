module LTL.Product where

open import LTL.Core public
open import Agda.Primitive
open import Prelude.Product
open import LTL.Stateless
open import LTL.Causal
open import LTL.Decoupled
open import LTL.Globally
open import LTL.CatHetSt
open import LTL.PolConsts

open import Prelude.Empty



infix 30 _∧_

_∧_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
_∧_ xs ys n = (xs n) × (ys n)


_⇔_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
xs ⇔ ys = (xs ⇐ ys) ∧ (ys ⇒ xs)

infixr 30 _∧ᵈ_ 

_∧ᵈ_ : ∀ {α β} → (Aₛ : (Set α) ʷ ) → (Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ] ) → (Set (α ⊔ β)) ʷ
_∧ᵈ_ xs ys n = Σ (xs n) (ys n)


-- Product Structure of Streams with Stateless morphisms

fsts : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ∧ Bₛ ⇒ Aₛ ]
fsts = const₂ {F = λ A B → A × B → A} fst

snds : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ∧ Bₛ ⇒ Bₛ ]
snds = const₂ {F = λ A B → A × B → B} snd

boths : ∀ {α β γ}  → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ (Aₛ ⇒ Bₛ) ⇒ (Aₛ ⇒ Cₛ) ⇒ Aₛ ⇒ (Bₛ ∧ Cₛ) ]
boths = const₃ {F = λ A B C → (A → B) → (A → C) → A → (B × C)} _&&&_

map∧ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → [ (Aₛ ⇒ Bₛ) ⇒ (Cₛ ⇒ Dₛ) ⇒ (Aₛ ∧ Cₛ) ⇒ (Bₛ ∧ Dₛ) ]
map∧ = const₄ {F = λ A B C D → (A → B) → (C → D) → (A × C) → (B × D)} (λ fs gs → fs *** gs)

lpd-proof : ∀ {α β γ}  → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → (gs : [ Aₛ ⇒ Cₛ ]) → fs ≡ fsts · boths $ʷ fs $ʷ gs
lpd-proof fs gs = refl

rpd-proof : ∀ {α β γ}  → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → (gs : [ Aₛ ⇒ Cₛ ]) → gs ≡ snds · boths $ʷ fs $ʷ gs
rpd-proof fs gs = refl


uv-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ } → (hs : [ Aₛ ⇒ Bₛ ∧ Cₛ ] ) → hs ≡ boths $ʷ (fsts · hs) $ʷ (snds · hs)
uv-proof hs = refl 

uv2-proof : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ] ) → (gs : [ Cₛ ⇒ Dₛ ]) → map∧ $ʷ fs $ʷ gs ≡ boths $ʷ (fs · fsts) $ʷ (gs · snds)
uv2-proof fs gs = refl





-- Product Structure of Streams with Causal morphisms

fstsᶜ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ (A ∧ B) ⊵ A ]
fstsᶜ {_} {_} {A} {B} = arr $ʷ (pureᶠ fsts)

sndsᶜ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ (A ∧ B) ⊵ B ]
sndsᶜ {_} {_} {A} {B} = arr $ʷ (pureᶠ snds)

bothsᶜ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → [ (A ⊵ B) ⇒ (A ⊵ C) ⇒ (A ⊵ (B ∧ C)) ]
bothsᶜ s f g t s≤t σ = (f t s≤t σ) , (g t s≤t σ)
