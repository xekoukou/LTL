module LTL.Sum where


open import Agda.Primitive
open import Relation.Binary.PropositionalEquality hiding ([_])


open import LTL.Core
open import LTL.Stateless
open import LTL.CatHetSt
open import LTL.PolConsts


open import Data.Sum 

infix 30 _∨_
_∨_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
(xs ∨ ys) n = (xs n) ⊎ (ys n)


-- Coproduct Structure on Streams

inls : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ (Aₛ ∨ Bₛ) ]
inls = const₂ {F = λ A B → A → A ⊎ B} inj₁

inrs : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Bₛ ⇒ (Aₛ ∨ Bₛ) ]
inrs = const₂ {F = λ A B → B → A ⊎ B} inj₂

cases : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ (Aₛ ⇒ Cₛ) ⇒ (Bₛ ⇒ Cₛ) ⇒ (Aₛ ∨ Bₛ) ⇒ Cₛ ]
cases = const₃ {F = λ A B C → (A → C) → (B → C) → (A ⊎ B) → C} [_,_]

map∨ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → [ (Aₛ ⇒ Bₛ) ⇒ (Cₛ ⇒ Dₛ) ⇒ (Aₛ ∨ Cₛ) ⇒ (Bₛ ∨ Dₛ) ]
map∨ = const₄ {F = λ A B C D →  (A → B) → (C → D) → A ⊎ C → B ⊎ D } Data.Sum.map

csl-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ (Aₛ ⇒ Cₛ) ]) → (gs : [ (Bₛ ⇒ Cₛ) ]) → fs ≡ (cases $ fs $ gs) · inls
csl-proof fs gs = refl

csr-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ (Aₛ ⇒ Cₛ) ]) → (gs : [ (Bₛ ⇒ Cₛ) ]) → gs ≡ (cases $ fs $ gs) · inrs
csr-proof fs gs = refl

-- With Cubical we could use functional extensionality here.
csb-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (hs : [ Aₛ ∨ Bₛ ⇒ Cₛ ]) → (vs : [ Aₛ ∨ Bₛ ]) → ∀ n → (hs $ vs) n ≡ (cases $ (hs · inls) $ (hs · inrs) $ vs) n
csb-proof hs vs n with vs n
csb-proof hs vs n | inj₁ x = refl
csb-proof hs vs n | inj₂ x = refl

mcs-proof : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → ( fs : [ Aₛ ⇒ Bₛ ] ) → ( gs : [ Cₛ ⇒ Dₛ ] ) → map∨ $ fs $ gs ≡ cases $ (inls · fs) $ (inrs · gs)
mcs-proof fs gs = refl
