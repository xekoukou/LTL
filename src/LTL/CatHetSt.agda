module LTL.CatHetSt where


open import LTL.PolConsts
open import LTL.Core public
open import LTL.Stateless
open import Function using (_∘′_ ; id)




-- Categorical Structure of Heterogeneous Streams
-- Objects are in (Set α) ʷ , morphisms in [ Aₛ ⇒ Bₛ ]

ids : ∀{α} → {Aₛ : (Set α) ʷ} → [ Aₛ ⇒ Aₛ ]
ids = const₁ {F = λ A → A → A} id


_·_ : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ Bₛ ⇒ Cₛ ] → [ Aₛ ⇒ Bₛ ] → [ Aₛ ⇒ Cₛ ]
fₛ · gₛ =  const₃ {F = λ A B C → ((B → C) → (A → B) → (A → C))} _∘′_ $ fₛ $ gₛ

lid-proof : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → fs · ids ≡ fs
lid-proof fs = refl

rid-proof : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → ids · fs ≡ fs
rid-proof fs = refl

assoc-proof : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → (fs : [ Bₛ ⇒ Cₛ ]) → (gs : [ Aₛ ⇒ Bₛ ]) → (ds : [ Dₛ ⇒ Aₛ ]) → fs · (gs · ds) ≡ (fs · gs) · ds
assoc-proof fs gs ds = refl


-- Is this useful ? Not really.
_!!_·_ : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ (Bₛ ⇒ Cₛ) ⇒ (Aₛ ⇒ Bₛ) ⇒ (Aₛ ⇒ Cₛ) ]
s !! fₛ · gₛ = λ z → fₛ (gₛ z)
