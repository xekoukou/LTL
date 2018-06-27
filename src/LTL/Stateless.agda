module Stateless where

open import Core public


infixr 20 _⇒_

_⇒_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
(xs ⇒ ys) n = xs n → ys n

_⇐_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
xs ⇐ ys = ys ⇒ xs


infixr 20 _⇒ᵈ_


_⇒ᵈ_ : ∀ {α β} (As : (Set α) ʷ) → [ As ⇒ ⟨ Set β ⟩ ] → (Set (α ⊔ β)) ʷ
(as ⇒ᵈ bs) n = (a : as n) → bs n a 








_$ₛʷ_ : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → (fₛ : [ Aₛ ⇒ Bₛ ] ) → (xs : [ Aₛ ]) → [ Bₛ ]
(fs $ₛʷ xs) n = fs n (xs n)

infixl 30 _$ʷ_

_$ʷ_ : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ] } → [ Aₛ ⇒ᵈ Bₛ ] → (xs : [ Aₛ ]) → [ Bₛ $ₛʷ xs ]
(fs $ʷ xs) n = (fs n) (xs n)

lemma4 : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {fs : [ Aₛ ⇒ᵈ (λ n _ → Bₛ n) ]} → {xs : [ Aₛ ]} → fs $ₛʷ xs ≡ (fs $ʷ xs)
lemma4 = refl


_$ₛ_ : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → ⟦ ( Aₛ ⇒ Bₛ ) ⇒ Aₛ ⇒ Bₛ ⟧
(fs $ₛ xs) = fs xs 

infixl 30 _$_

_$_ : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ] } → ∀{s} → (Aₛ ⇒ᵈ Bₛ) s → (xs : Aₛ s) → _$ₛ_ {Aₛ = Aₛ} (Bₛ s) xs
(fs $ xs) = fs xs


lemma5 : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ } → ∀{s} → (fs : (Aₛ ⇒ᵈ (λ n _ → Bₛ n)) s) → (xs : Aₛ s)
         → _$ₛ_ {Aₛ = Aₛ} {Bₛ = Bₛ} fs xs ≡ _$_ {Aₛ = Aₛ} {Bₛ = λ n _ → Bₛ n} fs xs
lemma5 fs xs = refl


indn : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ⇒ ○ Aₛ ] → ! Aₛ → [ Aₛ ]
indn fs x zero = x
indn fs x (suc n) = fs n (indn fs x n)



