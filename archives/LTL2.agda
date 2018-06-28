module LTL2 where

open import Agda.Primitive
open import Prelude.Nat
open import Prelude.Nat.Properties
open import Prelude.Ord
open import Prelude.Product
open import Prelude.Equality
open import Prelude.Equality.Inspect
open import Prelude.Sum renaming (Either to _⊎_)
open import Prelude.Unit
open import Prelude.Function using (_∘′_ ; id)
open import Prelude.Empty

-- Homogeneous FRP

_ʷ : ∀ {α} → Set α → Set α
A ʷ =  Nat → A

⟨_⟩ : ∀ {α} {A : Set α} → A → (A ʷ)
⟨ x ⟩ n = x

!ₛ : ∀ {α} {A : Set α} → (Aₛ : A ʷ) → A
!ₛ x = x zero

○ₛ : ∀ {α} {A : Set α} → (Aₛ : A ʷ) → A ʷ
○ₛ xs n = xs (suc n)

-- Heterogeneous FRP

[_] : ∀ {α} → (Set α) ʷ → Set α
[ Aₛ ] = ∀ n → Aₛ n

lemma1 : ∀{a} {A : Set a} → A ʷ ≡ [ ⟨ A ⟩ ]
lemma1 = refl


! : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → !ₛ Aₛ
! xs = xs 0

lemma2 : ∀ {α} → {Aₛ : (Set α) ʷ } → !ₛ Aₛ ≡ ! {Aₛ = ⟨ Set α ⟩ } Aₛ
lemma2 = refl


○ : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ] → [ ○ₛ Aₛ ]
○ xs n = xs (suc n)

lemma3 : ∀ {α} {Aₛ : (Set α) ʷ} → ○ₛ Aₛ ≡ ○ Aₛ
lemma3 = refl

_∷_ : ∀ {α} {Aₛ : (Set α) ʷ} → ! Aₛ → [ ○ Aₛ ] → [ Aₛ ]
(x ∷ xs) 0 = x
(x ∷ xs) (suc n) = xs n

infixr 20 _⇒_

_⇒_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
(xs ⇒ ys) n = xs n → ys n

_⇐_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
xs ⇐ ys = ys ⇒ xs


infixr 20 _⇒ᵈ_


-- TODO We need to allow multiple ⇒ᵈ on a single line.
_⇒ᵈ_ : ∀ {α β} (As : (Set α) ʷ) → [ As ⇒ ⟨ Set β ⟩ ] → (Set (α ⊔ β)) ʷ
(as ⇒ᵈ bs) n = (a : as n) → bs n a 


infix 30 _∧_ _∨_

_∧_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
_∧_ xs ys n = (xs n) × (ys n)




_⇔_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
xs ⇔ ys = (xs ⇐ ys) ∧ (ys ⇒ xs)

_∨_ : ∀ {α β} → (Set α) ʷ → (Set β) ʷ → (Set (α ⊔ β)) ʷ
(xs ∨ ys) n = (xs n) ⊎ (ys n)


infixr 30 _∧ᵈ_ 

_∧ᵈ_ : ∀ {α β} → (Aₛ : (Set α) ʷ ) → (Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ] ) → (Set (α ⊔ β)) ʷ
_∧ᵈ_ xs ys n = Σ (xs n) (ys n)



_$ₛ_ : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → (fₛ : [ Aₛ ⇒ Bₛ ] ) → (xs : [ Aₛ ]) → [ Bₛ ]
(fs $ₛ xs) n = fs n (xs n)

infixl 30 _$_

_$_ : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ] } → [ Aₛ ⇒ᵈ Bₛ ] → (xs : [ Aₛ ]) → [ Bₛ $ₛ xs ]
(fs $ xs) n = (fs n) (xs n)

lemma4 : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {fs : [ Aₛ ⇒ᵈ (λ n _ → Bₛ n) ]} → {xs : [ Aₛ ]} → fs $ₛ xs ≡ (fs $ xs)
lemma4 = refl



indn : ∀ {α} {Aₛ : (Set α) ʷ} → [ Aₛ ⇒ ○ Aₛ ] → ! Aₛ → [ Aₛ ]
indn fs x zero = x
indn fs x (suc n) = fs n (indn fs x n)



_∈_ : ∀ {α β} {A : Set α} → A → (A → Set β) → Set β
x ∈ A = A x

_∉_ : ∀ {α β} {A : Set α} → A → (A → Set β) → Set β
_∉_ {α} {β} x A = (A x) → ⊥′ {β}


∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _


_⟨_,_] : ∀ {α} → (Set α)ʷ → Nat → Nat → (Set α)
As ⟨ ℓ , n ] = (∀ m → (ℓ < m) → (m ≤ n) → As(m))

□ₚ : ∀ {α} → (Set α)ʷ → (Set α)ʷ
(□ₚ As)(n) = (∀ m → (m ≤ n) → As(m))

◇ₚ : ∀ {α} → (Set α)ʷ → (Set α)ʷ
(◇ₚ As) n = (∃ λ m → (m ≤ n) × As(m))

_S_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
(As S Bs) n = (∃ λ ℓ → (ℓ ≤ n) × (As ⟨ ℓ , n ]) × Bs ℓ)

_▷ₚ_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
(As ▷ₚ Bs)(n) = (∀ ℓ → (ℓ ≤ n) → As ⟨ ℓ , n ] → Bs ℓ)

front : ∀ {α} {Aₛ : (Set α)ʷ} {ℓ n} → Aₛ ⟨ ℓ , suc n ] → Aₛ ⟨ ℓ , n ]
front f m p (diff x y) = f m p (diff (suc x) (cong suc y))
last : ∀ {α} {As : (Set α)ʷ} {ℓ n} → (ℓ < n) → As ⟨ ℓ , n ] → As(n)
last {n = n} p f = f n p (diff! zero)

empty : ∀ {α} {Aₛ : (Set α)ʷ} {n} → Aₛ ⟨ n , n ]
empty {n = n} m (diff k eq) (diff k1 eq1) = ⊥-elim (less-antirefl ⦃ OrdNatLaws ⦄ g) where
  q = trans eq (sym (add-suc-r k n))
  t = trans eq1 (cong (λ z → (suc (k1 +N z))) q)
  h = trans t (cong suc (add-assoc k1 k (suc n)))
  g = diff (k1 +N k) h

snoc : ∀ {α} {Aₛ : (Set α)ʷ} {ℓ n} → Aₛ ⟨ ℓ , n ] → Aₛ (suc n) → Aₛ ⟨ ℓ , suc n ]
snoc {n = n} f x .(suc n) p (diff! zero) = x
snoc {n = n} f x m p (diff (suc k) refl) = f m p (diff k refl)


last-snoc : ∀ {α} {Aₛ : (Set α)ʷ} {ℓ n} (xs : Aₛ ⟨ ℓ , n ]) (p : ℓ < suc n) (x : Aₛ (suc n)) → last (p) (snoc (xs) (x)) ≡ x
last-snoc p xs x = refl

-- Simplification with functional extensionality
front-snoc : ∀ {α} {As : (Set α)ʷ } {ℓ n} (xs : As ⟨ ℓ , n ]) (x : As (suc n)) → ∀ m p q → front (snoc xs x) m p q ≡ xs m p q
front-snoc xs x m p (diff! k) = refl where

-- Prove this
postulate
  lessNatUnique : ∀ {n q} → (a : LessNat n q) → (b : LessNat n q) → a ≡  b

-- Simplification with functional extensionality
⟨]-eta : ∀ {α} {As : (Set α)ʷ} {ℓ n} (p : (ℓ < suc n)) (xs : As ⟨ ℓ , suc n ]) → ∀ m q r → snoc (front (xs)) (last (p) (xs)) m q r ≡ xs m q r
⟨]-eta {n = n} p xs m q (diff zero refl) = cong (λ X → xs (suc n) X (diff zero refl)) (lessNatUnique p q)
⟨]-eta p xs m q (diff! (suc k)) = refl


-- Isomorphisms

hd : ∀ {α} {Aₛ : (Set α)ʷ} → [ □ₚ Aₛ ⇒ Aₛ ]
hd n f = f n (diff! zero)

tl : ∀ {α} {Aₛ : (Set α)ʷ} → [ ○ (□ₚ Aₛ) ⇒ □ₚ Aₛ ]
tl n f m m≤n = f m (lt-to-leq {A = Nat} m≤n)



-- data Fork : Set where
--   fork51 : Fork
--   fork12 : Fork
--   fork23 : Fork
--   fork34 : Fork
--   fork45 : Fork
  

-- data Philosopher : Set where
--   phil1 phil2 phil3 phil4 phil5 : Philosopher


-- data Availability (frk : Fork) : Set ʷ where
--   unAv : ∀ {t} → Availability frk t
--   av : ∀ {t} → Availability frk t


-- data IsAv {frk : Fork} : [ Availability frk ⇒ ⟨ Set ⟩ ] where
--   isAv : ∀{t aval} → aval ≡ av {frk} {t} → IsAv t aval


-- data IsUnAv {frk : Fork} : [ Availability frk ⇒ ⟨ Set ⟩ ] where
--   isUnAv : ∀{t aval} → aval ≡ unAv {frk} {t} → IsUnAv t aval


-- data Hunger (phil : Philosopher) : Set ʷ where
--   hungry : ∀{t} → Hunger phil t  
--   notHungry : ∀{t} → Hunger phil t  

-- data IsHungry {phil : Philosopher} : [ Hunger phil ⇒ ⟨ Set ⟩ ] where
--   isHungry : ∀{t hungr} → hungr ≡ hungry {phil} {t} → IsHungry t hungr


-- data IsNotHungry {phil : Philosopher} : [ Hunger phil ⇒ ⟨ Set ⟩ ] where
--   isNotHungry : ∀{t hungr} → hungr ≡ notHungry {phil} {t} → IsNotHungry t hungr

-- data Action (phil : Philosopher) : Set ʷ where
--   eating : ∀{t} → Action phil t
--   thinking : ∀{t} → Action phil t

-- data IsEating {phil : Philosopher} : [ Action phil ⇒ ⟨ Set ⟩ ] where
--   isEating : ∀{t act} → act ≡ eating {phil} {t} → IsEating t act

-- data IsThinking {phil : Philosopher} : [ Action phil ⇒ ⟨ Set ⟩ ] where
--   isThinking : ∀{t act} → act ≡ thinking {phil} {t} → IsThinking t act



-- eatWhenYouCan : (frk1 : Fork) → (frk2 : Fork) → (phil : Philosopher) → Set ʷ 
-- eatWhenYouCan frk1 frk2 phil = {!Availability frk1 ⇒ᵈ lift (Availability frk2 ⇒ᵈ ?)!}

-- -- (((Availability frk1 ∧ Availability frk2) ∧ Hunger phil) ∧ᵈ {!(boths $ (IsAv · (fsts · fsts))) $ (IsAv · (snds · fsts))!})
-- -- {!boths $ (boths $ (IsAv · (fsts · fsts)) $ (IsAv · ?)) $ (IsHungry · ?)!}) -- λ n dv → ((IsAv $ {!fst dv!}) ∧ {!!}) {!!}) ⇒ {!!} -- (RIsAv frk1 ∧ RIsAv frk2 ∧ RIsHn phil) ▻ RIsUnAv frk1 ∧ RIsUnAv frk2 ∧ RIsEat phil


-- -- thinkWhenNotHungry : (phil : Philosopher) → RSet
-- -- thinkWhenNotHungry phil = RIsNtHn phil ▻ RIsTh phil


-- -- thinkingMakesYouHungry : (phil : Philosopher) → RSet
-- -- thinkingMakesYouHungry phil = RIsTh phil ▻ ◇ (RIsHn phil)


-- -- EatingSatisfiesHunger : (phil : Philosopher) → RSet
-- -- EatingSatisfiesHunger phil = RIsTh phil ▻ ◇ (RIsNtHn phil)

