module LTL.Sum where

open import LTL.Core public
open import LTL.Stateless
open import LTL.CatHetSt
open import LTL.PolConsts
open import Agda.Primitive


open import Prelude.Sum renaming (Either to _⊎_)

infix 30 _∨_
_∨_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
(xs ∨ ys) n = (xs n) ⊎ (ys n)


-- Coproduct Structure on Streams

inls : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ (Aₛ ∨ Bₛ) ]
inls = const₂ {F = λ A B → A → A ⊎ B} left

inrs : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Bₛ ⇒ (Aₛ ∨ Bₛ) ]
inrs = const₂ {F = λ A B → B → A ⊎ B} right

cases : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ (Aₛ ⇒ Cₛ) ⇒ (Bₛ ⇒ Cₛ) ⇒ (Aₛ ∨ Bₛ) ⇒ Cₛ ]
cases = const₃ {F = λ A B C → (A → C) → (B → C) → (A ⊎ B) → C} either

map∨ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → [ (Aₛ ⇒ Bₛ) ⇒ (Cₛ ⇒ Dₛ) ⇒ (Aₛ ∨ Cₛ) ⇒ (Bₛ ∨ Dₛ) ]
map∨ = const₄ {F = λ A B C D →  (A → B) → (C → D) → A ⊎ C → B ⊎ D } mapEither 

csl-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ (Aₛ ⇒ Cₛ) ]) → (gs : [ (Bₛ ⇒ Cₛ) ]) → fs ≡ (cases $ʷ fs $ʷ gs) · inls
csl-proof fs gs = refl

csr-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ (Aₛ ⇒ Cₛ) ]) → (gs : [ (Bₛ ⇒ Cₛ) ]) → gs ≡ (cases $ʷ fs $ʷ gs) · inrs
csr-proof fs gs = refl

-- With Cubical we could use functional extensionality here.
csb-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (hs : [ Aₛ ∨ Bₛ ⇒ Cₛ ]) → (vs : [ Aₛ ∨ Bₛ ]) → ∀ n → (hs $ʷ vs) n ≡ (cases $ʷ (hs · inls) $ʷ (hs · inrs) $ʷ vs) n
csb-proof hs vs n with vs n
csb-proof hs vs n | left x = refl
csb-proof hs vs n | right x = refl

mcs-proof : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → ( fs : [ Aₛ ⇒ Bₛ ] ) → ( gs : [ Cₛ ⇒ Dₛ ] ) → map∨ $ʷ fs $ʷ gs ≡ cases $ʷ (inls · fs) $ʷ (inrs · gs)
mcs-proof fs gs = refl
