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











-- □ₚ : ∀ {α} → (Set α)ʷ → (Set α)ʷ
-- (□ₚ As)(n) = (∀ m → (m ≤ n) → As(m))

-- ◇ₚ : ∀ {α} → (Set α)ʷ → (Set α)ʷ
-- (◇ₚ As) n = (∃ λ m → (m ≤ n) × As(m))

-- _S_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
-- (As S Bs) n = (∃ λ ℓ → (ℓ ≤ n) × (As ⟨ ℓ , n ]) × Bs ℓ)

-- _▷ₚ_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
-- (As ▷ₚ Bs)(n) = (∀ ℓ → (ℓ ≤ n) → As ⟨ ℓ , n ] → Bs ℓ)

-- front : ∀ {α} {Aₛ : (Set α)ʷ} {ℓ n} → Aₛ ⟨ ℓ , suc n ] → Aₛ ⟨ ℓ , n ]
-- front f m p (diff x y) = f m p (diff (suc x) (cong suc y))

-- last : ∀ {α} {As : (Set α)ʷ} {ℓ n} → (ℓ < n) → As ⟨ ℓ , n ] → As(n)
-- last {n = n} p f = f n p (diff! zero)

-- empty : ∀ {α} {Aₛ : (Set α)ʷ} {n} → Aₛ ⟨ n , n ]
-- empty {n = n} m (diff k eq) (diff k1 eq1) = ⊥-elim (less-antirefl ⦃ OrdNatLaws ⦄ g) where
--   q = trans eq (sym (add-suc-r k n))
--   t = trans eq1 (cong (λ z → (suc (k1 +N z))) q)
--   h = trans t (cong suc (add-assoc k1 k (suc n)))
--   g = diff (k1 +N k) h

-- snoc : ∀ {α} {Aₛ : (Set α)ʷ} {ℓ n} → Aₛ ⟨ ℓ , n ] → Aₛ (suc n) → Aₛ ⟨ ℓ , suc n ]
-- snoc {n = n} f x .(suc n) p (diff! zero) = x
-- snoc {n = n} f x m p (diff (suc k) refl) = f m p (diff k refl)


-- last-snoc : ∀ {α} {Aₛ : (Set α)ʷ} {ℓ n} (xs : Aₛ ⟨ ℓ , n ]) (p : ℓ < suc n) (x : Aₛ (suc n)) → last (p) (snoc (xs) (x)) ≡ x
-- last-snoc p xs x = refl

-- -- Simplification with functional extensionality
-- front-snoc : ∀ {α} {As : (Set α)ʷ } {ℓ n} (xs : As ⟨ ℓ , n ]) (x : As (suc n)) → ∀ m p q → front (snoc xs x) m p q ≡ xs m p q
-- front-snoc xs x m p (diff! k) = refl where

-- -- Prove this
-- postulate
--   lessNatUnique : ∀ {n q} → (a : LessNat n q) → (b : LessNat n q) → a ≡  b

-- -- Simplification with functional extensionality
-- ⟨]-eta : ∀ {α} {As : (Set α)ʷ} {ℓ n} (p : (ℓ < suc n)) (xs : As ⟨ ℓ , suc n ]) → ∀ m q r → snoc (front (xs)) (last (p) (xs)) m q r ≡ xs m q r
-- ⟨]-eta {n = n} p xs m q (diff zero refl) = cong (λ X → xs (suc n) X (diff zero refl)) (lessNatUnique p q)
-- ⟨]-eta p xs m q (diff! (suc k)) = refl


-- -- Isomorphisms

-- hd : ∀ {α} {Aₛ : (Set α)ʷ} → [ □ₚ Aₛ ⇒ Aₛ ]
-- hd n f = f n (diff! zero)

-- tl : ∀ {α} {Aₛ : (Set α)ʷ} → [ ○ (□ₚ Aₛ) ⇒ □ₚ Aₛ ]
-- tl n f m m≤n = f m (lt-to-leq {A = Nat} m≤n)



-- -- data Fork : Set where
-- --   fork51 : Fork
-- --   fork12 : Fork
-- --   fork23 : Fork
-- --   fork34 : Fork
-- --   fork45 : Fork
  

-- -- data Philosopher : Set where
-- --   phil1 phil2 phil3 phil4 phil5 : Philosopher


-- -- data Availability (frk : Fork) : Set ʷ where
-- --   unAv : ∀ {t} → Availability frk t
-- --   av : ∀ {t} → Availability frk t


-- -- data IsAv {frk : Fork} : [ Availability frk ⇒ ⟨ Set ⟩ ] where
-- --   isAv : ∀{t aval} → aval ≡ av {frk} {t} → IsAv t aval


-- -- data IsUnAv {frk : Fork} : [ Availability frk ⇒ ⟨ Set ⟩ ] where
-- --   isUnAv : ∀{t aval} → aval ≡ unAv {frk} {t} → IsUnAv t aval


-- -- data Hunger (phil : Philosopher) : Set ʷ where
-- --   hungry : ∀{t} → Hunger phil t  
-- --   notHungry : ∀{t} → Hunger phil t  

-- -- data IsHungry {phil : Philosopher} : [ Hunger phil ⇒ ⟨ Set ⟩ ] where
-- --   isHungry : ∀{t hungr} → hungr ≡ hungry {phil} {t} → IsHungry t hungr


-- -- data IsNotHungry {phil : Philosopher} : [ Hunger phil ⇒ ⟨ Set ⟩ ] where
-- --   isNotHungry : ∀{t hungr} → hungr ≡ notHungry {phil} {t} → IsNotHungry t hungr

-- -- data Action (phil : Philosopher) : Set ʷ where
-- --   eating : ∀{t} → Action phil t
-- --   thinking : ∀{t} → Action phil t

-- -- data IsEating {phil : Philosopher} : [ Action phil ⇒ ⟨ Set ⟩ ] where
-- --   isEating : ∀{t act} → act ≡ eating {phil} {t} → IsEating t act

-- -- data IsThinking {phil : Philosopher} : [ Action phil ⇒ ⟨ Set ⟩ ] where
-- --   isThinking : ∀{t act} → act ≡ thinking {phil} {t} → IsThinking t act



-- -- eatWhenYouCan : (frk1 : Fork) → (frk2 : Fork) → (phil : Philosopher) → Set ʷ 
-- -- eatWhenYouCan frk1 frk2 phil = {!Availability frk1 ⇒ᵈ lift (Availability frk2 ⇒ᵈ ?)!}

-- -- -- (((Availability frk1 ∧ Availability frk2) ∧ Hunger phil) ∧ᵈ {!(boths $ (IsAv · (fsts · fsts))) $ (IsAv · (snds · fsts))!})
-- -- -- {!boths $ (boths $ (IsAv · (fsts · fsts)) $ (IsAv · ?)) $ (IsHungry · ?)!}) -- λ n dv → ((IsAv $ {!fst dv!}) ∧ {!!}) {!!}) ⇒ {!!} -- (RIsAv frk1 ∧ RIsAv frk2 ∧ RIsHn phil) ▻ RIsUnAv frk1 ∧ RIsUnAv frk2 ∧ RIsEat phil


-- -- -- thinkWhenNotHungry : (phil : Philosopher) → RSet
-- -- -- thinkWhenNotHungry phil = RIsNtHn phil ▻ RIsTh phil


-- -- -- thinkingMakesYouHungry : (phil : Philosopher) → RSet
-- -- -- thinkingMakesYouHungry phil = RIsTh phil ▻ ◇ (RIsHn phil)


-- -- -- EatingSatisfiesHunger : (phil : Philosopher) → RSet
-- -- -- EatingSatisfiesHunger phil = RIsTh phil ▻ ◇ (RIsNtHn phil)

