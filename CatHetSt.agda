module CatHetSt where


open import PolConsts public
open import Stateless public
open import Prelude.Function using (_∘′_ ; id)



-- Categorical Structure of Heterogeneous Streams
-- Objects are in (Set α) ʷ , morphisms in [ Aₛ ⇒ Bₛ ]

ids : ∀{α} → {Aₛ : (Set α) ʷ} → [ Aₛ ⇒ Aₛ ]
ids = const₁ {F = λ A → A → A} id

_!!_·_ : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ (Bₛ ⇒ Cₛ) ⇒ (Aₛ ⇒ Bₛ) ⇒ (Aₛ ⇒ Cₛ) ]
s !! fₛ · gₛ = λ z → fₛ (gₛ z)

-- Weaker version of the previous statement.
_·_ : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ Bₛ ⇒ Cₛ ] → [ Aₛ ⇒ Bₛ ] → [ Aₛ ⇒ Cₛ ]
fₛ · gₛ =  const₃ {F = λ A B C → ((B → C) → (A → B) → (A → C))} _∘′_ $ʷ fₛ $ʷ gₛ

lid-proof : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → fs · ids ≡ fs
lid-proof fs = refl

rid-proof : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → ids · fs ≡ fs
rid-proof fs = refl

assoc-proof : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → (fs : [ Bₛ ⇒ Cₛ ]) → (gs : [ Aₛ ⇒ Bₛ ]) → (ds : [ Dₛ ⇒ Aₛ ]) → fs · (gs · ds) ≡ (fs · gs) · ds
assoc-proof fs gs ds = refl

