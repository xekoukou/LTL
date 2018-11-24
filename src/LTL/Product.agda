module LTL.Product where

open import Agda.Primitive
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import LTL.Core
open import LTL.Stateless
open import LTL.Causal
open import LTL.Decoupled
open import LTL.Globally
open import LTL.CatHetSt
open import LTL.PolConsts

open import Relation.Nullary



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
boths = const₃ {F = λ A B C → (A → B) → (A → C) → A → (B × C)} <_,_>

map∧ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → [ (Aₛ ⇒ Bₛ) ⇒ (Cₛ ⇒ Dₛ) ⇒ (Aₛ ∧ Cₛ) ⇒ (Bₛ ∧ Dₛ) ]
map∧ = const₄ {F = λ A B C D → (A → B) → (C → D) → (A × C) → (B × D)} (λ fs gs → map fs gs)

lpd-proof : ∀ {α β γ}  → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → (gs : [ Aₛ ⇒ Cₛ ]) → fs ≡ fsts · boths $ fs $ gs
lpd-proof fs gs = refl

rpd-proof : ∀ {α β γ}  → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → (gs : [ Aₛ ⇒ Cₛ ]) → gs ≡ snds · boths $ fs $ gs
rpd-proof fs gs = refl


uv-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ } → (hs : [ Aₛ ⇒ Bₛ ∧ Cₛ ] ) → hs ≡ boths $ (fsts · hs) $ (snds · hs)
uv-proof hs = refl 

uv2-proof : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ] ) → (gs : [ Cₛ ⇒ Dₛ ]) → map∧ $ fs $ gs ≡ boths $ (fs · fsts) $ (gs · snds)
uv2-proof fs gs = refl





-- Product Structure of Streams with Causal morphisms

fstsᶜ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ (A ∧ B) ⊵ A ]
fstsᶜ {_} {_} {A} {B} = arr $ (pureᶠ fsts)

sndsᶜ : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ (A ∧ B) ⊵ B ]
sndsᶜ {_} {_} {A} {B} = arr $ (pureᶠ snds)

bothsᶜ : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → [ (A ⊵ B) ⇒ (A ⊵ C) ⇒ (A ⊵ (B ∧ C)) ]
bothsᶜ s f g t s≤t σ = (f t s≤t σ) , (g t s≤t σ)





-- Probably not useful.

-- -- Dependent Functions

-- _⇒ₚ_ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → (Cₛ : [ Aₛ ⇒ ⟨ Set γ ⟩ ]) → (Dₛ : [ Bₛ ⇒ ⟨ Set δ ⟩ ])
--         → [ (Aₛ ⇒ Bₛ) ⇒ ⟨ Set (α ⊔ γ ⊔ δ) ⟩ ]
-- _⇒ₚ_ {Aₛ = Aₛ} {Bₛ} Cₛ Dₛ n f = {a : Aₛ n} → Cₛ _ a → Dₛ _ (f a)

-- map∧ᵈ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : [ Aₛ ⇒ ⟨ Set γ ⟩ ]} → {Dₛ : [ Bₛ ⇒ ⟨ Set δ ⟩ ] }
--         → [ ((Aₛ ⇒ Bₛ) ∧ᵈ (Cₛ ⇒ₚ Dₛ)) ⇒ (Aₛ ∧ᵈ Cₛ) ⇒ (Bₛ ∧ᵈ Dₛ) ]
-- map∧ᵈ n (f , g) = map f g -- f *** g


-- _∧↑ᵈ_ : ∀ {α β γ} → {Cₛ : (Set γ) ʷ } → (Aₛ : (Set α) ʷ ) → (Bₛ : [ Cₛ ⇒ Aₛ ⇒ ⟨ Set β ⟩ ] ) → [ Cₛ ⇒ ⟨ Set (α ⊔ β) ⟩ ]
-- _∧↑ᵈ_ xs ys n c = Σ (xs n) (ys n c)


-- fstsᵈ : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ] } → [ Aₛ ∧ᵈ Bₛ ⇒ Aₛ ]
-- fstsᵈ n (x , y) = x

-- sndsᵈ : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ] } → ∀ n → (p : (Aₛ ∧ᵈ Bₛ) n) → Bₛ n (fst p)
-- sndsᵈ n (x , y) = y


-- sndsᵈʷ : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ] } → (p : [ Aₛ ∧ᵈ Bₛ ] ) → [ Bₛ $ (fstsᵈ $ p) ]
-- sndsᵈʷ p n = snd (p n)
