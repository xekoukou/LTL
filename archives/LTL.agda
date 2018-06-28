module LTL where

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


---------------------------------
-- Scan functions

scan : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ⇒ ○ Bₛ ] → ! Bₛ → [ Aₛ ] → [ Bₛ ]
scan fs y xs = indn (fs $ xs) y

scan₁ : ∀ {α} {Aₛ : (Set α) ʷ} → [ ○ Aₛ ⇒ Aₛ ⇒ ○ Aₛ ] → [ Aₛ ] → [ Aₛ ]
scan₁ fs xs = scan fs (! xs) (○ xs)

scan₂ : ∀ {α β} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ ○ Bₛ ⇒ ○ Aₛ ⇒ Bₛ ⇒ ○ Bₛ ] → [ Aₛ ] → [ Bₛ ] → [ Bₛ ]
scan₂ fs xs ys = scan (fs $ ○ ys) (! ys) (○ xs)

------------------------
-- Past LTL

○ₚ : ∀ {α} → (Set α) ʷ → (Set α) ʷ
○ₚ Aₛ = ⊤′ ∷ Aₛ

□ₚ : ∀ {α} → (Set α) ʷ → (Set α) ʷ
□ₚ = scan₁ ⟨ _×_ ⟩


◇ₚ :  ∀ {α} → (Set α) ʷ → (Set α) ʷ
◇ₚ = scan₁ ⟨ _⊎_ ⟩

-- Here the lifting of the second argument to the (α + β) universe might cause problems in the future.

_S_ : ∀ {α} → (Set α) ʷ → (Set α) ʷ → (Set α) ʷ
_S_ = scan₂ ⟨ (λ ○b ○a aSb → ○b ⊎ (○a × aSb)) ⟩

-- TODO I do not get this ?
_▻ₚ_ : ∀ {α} → (Set α) ʷ → (Set α) ʷ → (Set α) ʷ
_▻ₚ_ = scan₂ ⟨ (λ B A I → B × (A → I) ) ⟩




-- Polymorphic Constants

const₁ : ∀ {α β} → {Aₛ : (Set α) ʷ} → {F : Set α → Set β} → (∀{A} → F A) → [ ⟨ F ⟩ $ Aₛ ]
const₁ {Aₛ = Aₛ} k = ⟨ (λ A → k {A}) ⟩ $ Aₛ

const₂ : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} →  {F : Set α → Set β → Set γ} →  (∀{A B} → F A B) → [ ⟨ F ⟩ $ Aₛ $ Bₛ ]
const₂ {Aₛ = Aₛ} {Bₛ = Bₛ} k = ⟨ (λ A B → k {A} {B}) ⟩ $ Aₛ $ Bₛ

const₃ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {F : Set α → Set β → Set γ → Set δ} →  (∀{A B C} → F A B C) → [ ⟨ F ⟩ $ Aₛ $ Bₛ $ Cₛ ] 
const₃ {Aₛ = Aₛ} {Bₛ = Bₛ} {Cₛ = Cₛ} k = ⟨ (λ A B C → k {A} {B} {C}) ⟩ $ Aₛ $ Bₛ $ Cₛ

const₄ : ∀ {α β γ δ ε} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → {F : Set α → Set β → Set γ → Set δ → Set ε} →  (∀{A B C D} → F A B C D) → [ ⟨ F ⟩ $ Aₛ $ Bₛ $ Cₛ $ Dₛ ] 
const₄ {Aₛ = Aₛ} {Bₛ = Bₛ} {Cₛ = Cₛ} {Dₛ = Dₛ} k = ⟨ (λ A B C D → k {A} {B} {C} {D} ) ⟩ $ Aₛ $ Bₛ $ Cₛ $ Dₛ


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



-- ???
constᵈ₂ : ∀ {α β γ δ} {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → (fs1 : [ Aₛ ⇒ Bₛ ]) → (fs2 : [ Aₛ ⇒ Cₛ ]) → (gs : [ Bₛ ⇒ Cₛ ⇒ Dₛ ]) → [ Aₛ ⇒ Dₛ ]
constᵈ₂ fs1 fs2 gs = const₄ {F = λ A B C D → (A → B) → (A → C) → (B → C → D) → (A → D)} (λ f1 f2 g x → g (f1 x) (f2 x) ) $ fs1 $ fs2 $ gs


-- Product Structure of Streams

fsts : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ∧ Bₛ ⇒ Aₛ ]
fsts = const₂ {F = λ A B → A × B → A} fst

snds : ∀ {α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ∧ Bₛ ⇒ Bₛ ]
snds = const₂ {F = λ A B → A × B → B} snd

boths : ∀ {α β γ}  → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ (Aₛ ⇒ Bₛ) ⇒ (Aₛ ⇒ Cₛ) ⇒ Aₛ ⇒ (Bₛ ∧ Cₛ) ]
boths = const₃ {F = λ A B C → (A → B) → (A → C) → A → (B × C)} _&&&_

map∧ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → [ (Aₛ ⇒ Bₛ) ⇒ (Cₛ ⇒ Dₛ) ⇒ (Aₛ ∧ Cₛ) ⇒ (Bₛ ∧ Dₛ) ]
map∧ = const₄ {F = λ A B C D → (A → B) → (C → D) → (A × C) → (B × D)} (λ fs gs → fs *** gs)

lpd-proof : ∀ {α β γ}  → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → (gs : [ Aₛ ⇒ Cₛ ]) → fs ≡ fsts · boths $ fs $ gs
lpd-proof fs gs = refl

rpd-proof : ∀ {α β γ}  → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ]) → (gs : [ Aₛ ⇒ Cₛ ]) → gs ≡ snds · boths $ fs $ gs
rpd-proof fs gs = refl


uv-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ } → (hs : [ Aₛ ⇒ Bₛ ∧ Cₛ ] ) → hs ≡ boths $ (fsts · hs) $ (snds · hs)
uv-proof hs = refl 

uv2-proof : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → (fs : [ Aₛ ⇒ Bₛ ] ) → (gs : [ Cₛ ⇒ Dₛ ]) → map∧ $ fs $ gs ≡ boths $ (fs · fsts) $ (gs · snds)
uv2-proof fs gs = refl


-- Coproduct Structure on Streams

inls : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ (Aₛ ∨ Bₛ) ]
inls = const₂ {F = λ A B → A → A ⊎ B} left

inrs : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Bₛ ⇒ (Aₛ ∨ Bₛ) ]
inrs = const₂ {F = λ A B → B → A ⊎ B} right

cases : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → [ (Aₛ ⇒ Cₛ) ⇒ (Bₛ ⇒ Cₛ) ⇒ (Aₛ ∨ Bₛ) ⇒ Cₛ ]
cases = const₃ {F = λ A B C → (A → C) → (B → C) → (A ⊎ B) → C} either

map∨ : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → [ (Aₛ ⇒ Bₛ) ⇒ (Cₛ ⇒ Dₛ) ⇒ (Aₛ ∨ Cₛ) ⇒ (Bₛ ∨ Dₛ) ]
map∨ = const₄ {F = λ A B C D →  (A → B) → (C → D) → A ⊎ C → B ⊎ D } mapEither 

csl-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ (Aₛ ⇒ Cₛ) ]) → (gs : [ (Bₛ ⇒ Cₛ) ]) → fs ≡ (cases $ fs $ gs) · inls
csl-proof fs gs = refl

csr-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (fs : [ (Aₛ ⇒ Cₛ) ]) → (gs : [ (Bₛ ⇒ Cₛ) ]) → gs ≡ (cases $ fs $ gs) · inrs
csr-proof fs gs = refl

-- With Cubical we could use functional extensionality here.
csb-proof : ∀ {α β γ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → (hs : [ Aₛ ∨ Bₛ ⇒ Cₛ ]) → (vs : [ Aₛ ∨ Bₛ ]) → ∀ n → (hs $ vs) n ≡ (cases $ (hs · inls) $ (hs · inrs) $ vs) n
csb-proof hs vs n with vs n
csb-proof hs vs n | left x = refl
csb-proof hs vs n | right x = refl

mcs-proof : ∀ {α β γ δ} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → {Cₛ : (Set γ) ʷ} → {Dₛ : (Set δ) ʷ} → ( fs : [ Aₛ ⇒ Bₛ ] ) → ( gs : [ Cₛ ⇒ Dₛ ] ) → map∨ $ fs $ gs ≡ cases $ (inls · fs) $ (inrs · gs)
mcs-proof fs gs = refl

-- Comonadic Structure of Streams

map□ₚ : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ] → [ □ₚ Aₛ ⇒ □ₚ Bₛ ]
map□ₚ fs = scan map∧ (! fs) (○ fs)

extract□ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ □ₚ Aₛ ⇒ Aₛ ]
extract□ₚ = id ∷ fsts


duplicate□ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ □ₚ Aₛ ⇒ □ₚ (□ₚ Aₛ) ]
duplicate□ₚ {_} {Aₛ} = indn (const₃ {Aₛ = ○ Aₛ} {Bₛ = □ₚ Aₛ} {Cₛ = □ₚ (□ₚ Aₛ)} {F = λ A B C → (B → C) → A × B → ( A × B ) × C} (λ g → id &&& g ∘′ snd)) id

-- Functional extensionality is needed here as well.
exdp-proof : ∀{α} → {Aₛ : (Set α) ʷ} → ∀ n → (extract□ₚ {Aₛ = □ₚ Aₛ} · (duplicate□ₚ {Aₛ = Aₛ})) n ≡ ids {Aₛ = □ₚ Aₛ} n
exdp-proof zero = refl
exdp-proof (suc n) = refl

mexdp-proof : ∀{α} → {Aₛ : (Set α) ʷ} → ∀ n xs → (map□ₚ (extract□ₚ {Aₛ = Aₛ}) · duplicate□ₚ {Aₛ = Aₛ}) n xs ≡ ids {Aₛ = □ₚ Aₛ} n xs
mexdp-proof zero xs = refl
mexdp-proof {Aₛ = Aₛ} (suc n) (x , xs) = cong (λ y → x , y) (mexdp-proof {Aₛ = Aₛ} n xs) 


-- Monadic Structure of Streams

map◇ₚ : ∀{α β} → {Aₛ : (Set α) ʷ} → {Bₛ : (Set β) ʷ} → [ Aₛ ⇒ Bₛ ] → [ ◇ₚ Aₛ ⇒ ◇ₚ Bₛ ]
map◇ₚ fs = scan map∨ (! fs) (○ fs)

return◇ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ Aₛ ⇒ ◇ₚ Aₛ ]
return◇ₚ = id ∷ inls

join◇ₚ : ∀{α} → {Aₛ : (Set α) ʷ} → [ ◇ₚ (◇ₚ Aₛ ) ⇒ ◇ₚ Aₛ ]
join◇ₚ {Aₛ = Aₛ} = indn (const₃ {Aₛ = ○ Aₛ} {Bₛ = ◇ₚ (◇ₚ Aₛ)} {Cₛ = ◇ₚ Aₛ} {F = λ A B C → (B → C) → ((A ⊎ C) ⊎ B) → (A ⊎ C)} (λ g → either id (right ∘′ g))) id

-- functional extensionality here.
jr-proof : ∀{α} → {Aₛ : (Set α) ʷ} →  (vs : [ ◇ₚ Aₛ ] ) → ∀ n → (join◇ₚ {Aₛ = Aₛ} $ (return◇ₚ $ vs)) n ≡ (ids $ vs) n
jr-proof vs zero = refl
jr-proof vs (suc n) = refl


mr-proof : ∀{α} → {Aₛ : (Set α) ʷ} → ∀ n vs → (join◇ₚ {Aₛ = Aₛ} · (map◇ₚ {Aₛ = Aₛ} return◇ₚ)) n vs ≡ ids {Aₛ = ◇ₚ Aₛ} n vs
mr-proof zero vs = refl
mr-proof (suc n) (left x) = refl
mr-proof {Aₛ = Aₛ} (suc n) (right x) = cong right (mr-proof {Aₛ = Aₛ} n x)

jjm-proof : ∀{α} → {Aₛ : (Set α) ʷ} → ∀ n vs → (join◇ₚ {Aₛ = Aₛ} · (join◇ₚ {Aₛ = ◇ₚ Aₛ})) n vs ≡ (join◇ₚ {Aₛ = Aₛ} · (map◇ₚ (join◇ₚ {Aₛ = Aₛ}))) n vs
jjm-proof zero vs = refl
jjm-proof (suc n) (left x) = refl
jjm-proof {Aₛ = Aₛ} (suc n) (right x) = cong right (jjm-proof {Aₛ = Aₛ} n x)



-------------------------------------

ℙ : ∀ {α} → Set α → Set (lsuc α)
ℙ{α}(A) = A → Set α

Σʷ : ∀ {α} {Σ : Set α} → ℙ (Σ ʷ)
Σʷ x = ⊤′

∅ : ∀ {α} {A : Set α} → ℙ(A)
∅ x = ⊥′

_ᶜ : ∀ {α} {A : Set α} → ℙ(A) → ℙ(A)
_ᶜ {α} S x = (S x) → (⊥′ {α})

_∩_ : ∀ {α} {A : Set α} → ℙ(A) → ℙ(A) → ℙ(A)
(S ∩ T) x = (S x) × (T x)

_∪_ : ∀ {α} {A : Set α} → ℙ(A) → ℙ(A) → ℙ(A)
(S ∪ T) x = (S x) ⊎ (T x)

_⊆_ : ∀ {α} {A : Set α} → ℙ(A) → ℙ(A) → Set α
(S ⊆ T) = ∀ x → (S x) → (T x)


Id : ∀ {α} {A : Set α} → A → A
Id x = x
syntax Id (λ x → A) = ⟅ x ∣ A ⟆


_∈_ : ∀ {α β} {A : Set α} → A → (A → Set β) → Set β
x ∈ A = A x

_∉_ : ∀ {α β} {A : Set α} → A → (A → Set β) → Set β
_∉_ {α} {β} x A = (A x) → ⊥′ {β}


∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _


-- Classical proofs

ExcludedMiddle : ∀ {α} → Set (lsuc α)
ExcludedMiddle {α} = ∀ (A : Set α) → (A ⊎ (A → ⊥′ {α}))

_⊆^*_ : ∀ {α} {A : Set α} → ℙ(A) → ℙ(A) → Set (lsuc α)
_⊆^*_ {α} S T = ExcludedMiddle {α} → (S ⊆ T)

CCS⊆*S : ∀ {α} {A : Set α} (S : ℙ(A)) → ((S ᶜ) ᶜ) ⊆^* S
CCS⊆*S S xclm x ¬x∉S with xclm (S x)
CCS⊆*S S xclm x ¬x∉S | left x∈S = x∈S
CCS⊆*S S xclm x ¬x∉S | right x∉S = ⊥′-elim (¬x∉S x∉S)



data pLTL {α} (Σ : Set α) : Set (lsuc α) where
  true : pLTL Σ
  false : pLTL Σ
  _and_ : pLTL Σ → pLTL Σ → pLTL Σ
  _or_ : pLTL Σ → pLTL Σ → pLTL Σ
  box : pLTL Σ → pLTL Σ
  dia : pLTL Σ → pLTL Σ
  _since_ : pLTL Σ → pLTL Σ → pLTL Σ
  _constrain_ : pLTL Σ → pLTL Σ → pLTL Σ
  atom : ℙ Σ → pLTL Σ

⟦_⟧ : ∀ {α} {Σ : Set α} → pLTL Σ → Nat → ℙ ( Σ ʷ )
⟦ true ⟧ n = Σʷ
⟦ false ⟧ n = ∅
⟦ x and y ⟧ n = (⟦ x ⟧ n) ∩ (⟦ y ⟧ n)
⟦ x or y ⟧ n = (⟦ x ⟧ n) ∪ (⟦ y ⟧ n)
⟦ box x ⟧ n = ⟅ w ∣ (∀ m → (m ≤ n) → (w ∈ ⟦ x ⟧ m)) ⟆
⟦ dia x ⟧ n = ⟅ w ∣ (∃ λ m → (m ≤ n) × (w ∈ ⟦ x ⟧ m )) ⟆ 
⟦ x since y ⟧ n =  ⟅ w ∣ (∃ λ ℓ → (ℓ ≤ n) × (∀ m → (ℓ < m) → (m ≤ n) → (w ∈ ⟦ x ⟧ m )) × (w ∈ ⟦ y ⟧ ℓ )) ⟆ 
⟦ x constrain y ⟧ n = ⟅ w ∣ (∀ ℓ → (ℓ ≤ n) → (∀ m → (ℓ < m) → (m ≤ n) → (w ∈ ⟦ x ⟧ m )) → (w ∈ ⟦ y ⟧ ℓ)) ⟆ 
⟦ atom S ⟧ n =  ⟅ w ∣ (w n  ∈ S) ⟆

infix 40 not

not : ∀ {α} {Σ : Set α} → pLTL Σ → pLTL Σ
not true = false
not false = true
not (x and y) = not x or not y
not (x or y) = not x and not y
not (box x) = dia (not x)
not (dia x) = box (not x)
not (x since y) = x constrain not y
not (x constrain y) = x since not y
not (atom S) = atom (S ᶜ)

not-⊆-^C : ∀ {α} {Σ : Set α} (φ : pLTL Σ) n → (⟦ not φ ⟧ n) ⊆ (⟦ φ ⟧ n ᶜ)
not-⊆-^C true n x () 
not-⊆-^C false n x y ()
not-⊆-^C (x and y) n z (left w) q = not-⊆-^C x n z w (fst q)
not-⊆-^C (x and y) n z (right w) q = not-⊆-^C y n z w (snd q)
not-⊆-^C (x or y) n z w (left q) = not-⊆-^C x n z (fst w) q
not-⊆-^C (x or y) n z w (right q) = not-⊆-^C y n z (snd w) q
not-⊆-^C (box x) n z (m , m≤n , notx) q = not-⊆-^C x m z notx (q m m≤n) 
not-⊆-^C (dia x) n z w (m , m≤n , isx) = not-⊆-^C x m z (w m m≤n) isx
not-⊆-^C (x since y) n z w (l , l≤n , f , isyl) = not-⊆-^C y l z (w l l≤n f) isyl
not-⊆-^C (x constrain y) n z (l , l≤n , f , notyl) q = not-⊆-^C y l z notyl (q l l≤n f)
not-⊆-^C (atom x) n z w = w

-- This function is not constructive because it uses the excluded middle. It should not be used in executable code.

not-⊇-^C : ∀ {α} {Σ : Set α} (φ : pLTL Σ) n → (⟦ φ ⟧ n ᶜ) ⊆^* (⟦ not φ ⟧ n)
not-⊇-^C true n xclm w x = x unit
not-⊇-^C false n xclm w x = unit
not-⊇-^C (phi and psi) n xclm w x with xclm (w ∈ ⟦ phi ⟧ n) | xclm (w ∈ ⟦ psi ⟧ n)
not-⊇-^C (phi and psi) n xclm w x | left x₁ | left x₂ = ⊥′-elim (x (x₁ , x₂))
not-⊇-^C (phi and psi) n xclm w x | right no | _ = left (not-⊇-^C phi n xclm w no)
not-⊇-^C (phi and psi) n xclm w x | left _ | right no = right (not-⊇-^C psi n xclm w no)
not-⊇-^C (phi or psi) n xclm w x = (not-⊇-^C phi n xclm w (x ∘′ left) , not-⊇-^C psi n xclm w (x ∘′ right))
not-⊇-^C (box phi) n xclm w x with xclm (∃ λ m → (m ≤ n) × (w ∉ ⟦ phi ⟧(m)))
not-⊇-^C (box phi) n xclm w x | left (m , p , y) = m , (p , (not-⊇-^C phi m xclm w y))
not-⊇-^C (box phi) n xclm w x | right no = ⊥′-elim (x λ m p → CCS⊆*S (⟦ phi ⟧ m) xclm w (λ z → no (m , p , z)))
not-⊇-^C (dia phi) n xclm w x = λ m p → not-⊇-^C phi m xclm w (λ z → x (m , p , z))
not-⊇-^C (phi since psi) n xclm w x = λ ℓ p xs → not-⊇-^C psi ℓ xclm w λ z → x (ℓ , p , xs , z)
not-⊇-^C (phi constrain psi) n xclm w x with xclm (∃ λ ℓ → (ℓ ≤ n) × (∀ m → (ℓ < m) → (m ≤ n) → (w ∈ ⟦ phi ⟧(m))) × (w ∉ ⟦ psi ⟧(ℓ)))
not-⊇-^C (phi constrain psi) n xclm w x | left (ℓ , p , xs ,  y) = ℓ , (p , (xs , not-⊇-^C psi ℓ xclm w y))
not-⊇-^C (phi constrain psi) n xclm w x | right no = ⊥′-elim (x λ ℓ p xs → CCS⊆*S (⟦ psi ⟧ ℓ) xclm w (λ z → no (ℓ , p , xs , z)))
not-⊇-^C (atom x₁) n xclm w x = x


-- Isomorphism

_≈_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)
(As ≈ Bs) = (∃ λ f → ∃ λ g → ((f · g) ≡ ids {Aₛ = Bs}) × ((g · f) ≡ ids {Aₛ = As}))


_⟨_,_] : ∀ {α} → (Set α)ʷ → Nat → Nat → (Set α)
As ⟨ ℓ , n ] = (∀ m → (ℓ < m) → (m ≤ n) → As(m))

□ₚ′ : ∀ {α} → (Set α)ʷ → (Set α)ʷ
(□ₚ′ As)(n) = (∀ m → (m ≤ n) → As(m))

◇ₚ′ : ∀ {α} → (Set α)ʷ → (Set α)ʷ
(◇ₚ′ As) n = (∃ λ m → (m ≤ n) × As(m))

_S′_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
(As S′ Bs) n = (∃ λ ℓ → (ℓ ≤ n) × (As ⟨ ℓ , n ]) × Bs ℓ)

_▷ₚ′_ : ∀ {α} → (Set α)ʷ → (Set α)ʷ → (Set α)ʷ
(As ▷ₚ′ Bs)(n) = (∀ ℓ → (ℓ ≤ n) → As ⟨ ℓ , n ] → Bs ℓ)

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

hd′ : ∀ {α} {Aₛ : (Set α)ʷ} → [ □ₚ′ Aₛ ⇒ Aₛ ]
hd′ n f = f n (diff! zero)

tl′ : ∀ {α} {Aₛ : (Set α)ʷ} → [ ○ (□ₚ′ Aₛ) ⇒ □ₚ′ Aₛ ]
tl′ n f m m≤n = f m (lt-to-leq {A = Nat} m≤n)

□ₚ′impl□ₚ : ∀ {α} {Aₛ : (Set α)ʷ} → [ □ₚ′ Aₛ ⇒ □ₚ Aₛ ]
□ₚ′impl□ₚ zero f = hd′ zero f
□ₚ′impl□ₚ (suc n) f = hd′ (suc n) f , (□ₚ′impl□ₚ n (tl′ n f))

□ₚimpl□ₚ′ : ∀ {α} {Aₛ : (Set α)ʷ} → [ □ₚ Aₛ ⇒ □ₚ′ Aₛ ]
□ₚimpl□ₚ′ zero f .0 (diff! zero) = f
□ₚimpl□ₚ′ zero f m (diff (suc k) ())
□ₚimpl□ₚ′ (suc n) (x , xs) .(suc n) (diff! zero) = x
□ₚimpl□ₚ′ {Aₛ = Aₛ} (suc .(k +N m)) (x , xs) m (diff! (suc k)) = □ₚimpl□ₚ′ {Aₛ = Aₛ} (k +N m) xs m (diff! k)


-- %□-to-□′ : ∀ {α} (As : (Set α)^ω) %n %f %m %m≤n →
--   (□|impl|□′ {/As = As} · □′|impl|□ {/As = As}) %n %f %m %m≤n
--     ≡ & |ids| {/As = □′ As} %n %f %m %m≤n
--       \\
-- %□-to-□′ As .0 f 0 (0 , *) = & * \\
-- %□-to-□′ As .(m +1) f (m +1) (0 , *) = & * \\
-- %□-to-□′ As .((ℓ + 0) +1) f 0 (ℓ +1 , *) = & %□-to-□′ As (ℓ + 0) (|tl|′ (ℓ + 0) f) 0 (ℓ , *) \\
-- %□-to-□′ As .((ℓ + (m +1)) +1) f (m +1) (ℓ +1 , *) = & %□-to-□′ As (ℓ + (m +1)) (|tl|′ (ℓ + (m +1)) f) (m +1) (ℓ , *) \\[1ex]
-- %□′-to-□ : ∀ {α} (As : (Set α)^ω) %n %xs →
--   (□′|impl|□ {/As = As} · □|impl|□′ {/As = As}) %n %xs
--     ≡ & |ids| {/As = □ As} %n %xs
--       \\
-- %□′-to-□ As 0 x = *
-- %□′-to-□ As (n +1) (x , xs) = cong (_,_ x) (trans (%ext n (%lemma n x xs)) (%□′-to-□ As n xs)) where
--   %tl : ∀ n {f g : □′ As (n +1)} → (∀ m m≤n → f m m≤n ≡ g m m≤n) → (∀ m m≤n → |tl|′ n f m m≤n ≡ |tl|′ n g m m≤n) 
--   %tl .(ℓ + m) f=g m (ℓ , *) = f=g m (ℓ +1 , *)
--   %ext : ∀ n {f g : □′ As n} → (∀ m m≤n → f m m≤n ≡ g m m≤n) → (□′|impl|□ n f ≡ □′|impl|□ n g)
--   %ext 0 f=g = f=g 0 (0 , *)
--   %ext (n +1) f=g = cong₂ _,_ (f=g (n +1) (0 , *)) (%ext n (%tl n f=g))
--   %lemma : ∀ n x xs m m≤n → (|tl|′ n (□|impl|□′ (n +1) (x , xs))) m m≤n ≡ □|impl|□′ n xs m m≤n
--   %lemma .0 x xs zero (zero , *) = *
--   %lemma .(m +1) x xs (m +1) (zero , *) = *
--   %lemma .((ℓ + 0) +1) x xs zero (ℓ +1 , *) = *
--   %lemma .((ℓ + (m +1)) +1) x xs (m +1) (ℓ +1 , *) = *



data Fork : Set where
  fork51 : Fork
  fork12 : Fork
  fork23 : Fork
  fork34 : Fork
  fork45 : Fork
  

data Philosopher : Set where
  phil1 phil2 phil3 phil4 phil5 : Philosopher


data Availability (frk : Fork) : Set ʷ where
  unAv : ∀ {t} → Availability frk t
  av : ∀ {t} → Availability frk t


data IsAv {frk : Fork} : [ Availability frk ⇒ ⟨ Set ⟩ ] where
  isAv : ∀{t aval} → aval ≡ av {frk} {t} → IsAv t aval


data IsUnAv {frk : Fork} : [ Availability frk ⇒ ⟨ Set ⟩ ] where
  isUnAv : ∀{t aval} → aval ≡ unAv {frk} {t} → IsUnAv t aval


data Hunger (phil : Philosopher) : Set ʷ where
  hungry : ∀{t} → Hunger phil t  
  notHungry : ∀{t} → Hunger phil t  

data IsHungry {phil : Philosopher} : [ Hunger phil ⇒ ⟨ Set ⟩ ] where
  isHungry : ∀{t hungr} → hungr ≡ hungry {phil} {t} → IsHungry t hungr


data IsNotHungry {phil : Philosopher} : [ Hunger phil ⇒ ⟨ Set ⟩ ] where
  isNotHungry : ∀{t hungr} → hungr ≡ notHungry {phil} {t} → IsNotHungry t hungr

data Action (phil : Philosopher) : Set ʷ where
  eating : ∀{t} → Action phil t
  thinking : ∀{t} → Action phil t

data IsEating {phil : Philosopher} : [ Action phil ⇒ ⟨ Set ⟩ ] where
  isEating : ∀{t act} → act ≡ eating {phil} {t} → IsEating t act

data IsThinking {phil : Philosopher} : [ Action phil ⇒ ⟨ Set ⟩ ] where
  isThinking : ∀{t act} → act ≡ thinking {phil} {t} → IsThinking t act



eatWhenYouCan : (frk1 : Fork) → (frk2 : Fork) → (phil : Philosopher) → Set ʷ 
eatWhenYouCan frk1 frk2 phil = {!Availability frk1 ⇒ᵈ lift (Availability frk2 ⇒ᵈ ?)!}

-- (((Availability frk1 ∧ Availability frk2) ∧ Hunger phil) ∧ᵈ {!(boths $ (IsAv · (fsts · fsts))) $ (IsAv · (snds · fsts))!})
-- {!boths $ (boths $ (IsAv · (fsts · fsts)) $ (IsAv · ?)) $ (IsHungry · ?)!}) -- λ n dv → ((IsAv $ {!fst dv!}) ∧ {!!}) {!!}) ⇒ {!!} -- (RIsAv frk1 ∧ RIsAv frk2 ∧ RIsHn phil) ▻ RIsUnAv frk1 ∧ RIsUnAv frk2 ∧ RIsEat phil


-- thinkWhenNotHungry : (phil : Philosopher) → RSet
-- thinkWhenNotHungry phil = RIsNtHn phil ▻ RIsTh phil


-- thinkingMakesYouHungry : (phil : Philosopher) → RSet
-- thinkingMakesYouHungry phil = RIsTh phil ▻ ◇ (RIsHn phil)


-- EatingSatisfiesHunger : (phil : Philosopher) → RSet
-- EatingSatisfiesHunger phil = RIsTh phil ▻ ◇ (RIsNtHn phil)




-- ↑ : ∀ {α β} {Aₛ : (Set α)ʷ} (Bₛ : (Set β)ʷ) → [ Aₛ ⇒ ⟨ Set β ⟩ ]
-- ↑ Bₛ n x = Bₛ n 


-- _⇒ʲ_ : ∀ {α β γ} {Cₛ : (Set γ)ʷ} → (Aₛ : [ Cₛ ⇒ ⟨ Set α ⟩ ]) → (Bₛ : [ Cₛ ⇒ ⟨ Set β ⟩ ]) → [ Cₛ ⇒ ⟨ Set (α ⊔ β) ⟩ ]
-- (Aₛ ⇒ʲ Bₛ) n c = Aₛ n c → Bₛ n c


-- _⇒ʲᵈʲ_ : ∀ {α β γ δ} {Cₛ : (Set γ)ʷ} → {Aₛ : [ Cₛ ⇒ ⟨ Set α ⟩ ]} → (Bₛ : [ Cₛ ⇒ᵈ (Aₛ  ⇒ʲ ↑ ⟨ Set β ⟩) ] ) → (Dₛ : [ Cₛ ⇒ᵈ (Aₛ  ⇒ʲ ↑ ⟨ Set δ ⟩) ] ) → [ Cₛ ⇒ᵈ (Aₛ  ⇒ʲ ↑ ⟨ Set (β ⊔ δ) ⟩) ] 
-- _⇒ʲᵈʲ_ Bₛ Dₛ n c a = Bₛ n c a → Dₛ n c a 


-- ↑ʲ : ∀ {α β γ} {Cₛ : (Set γ)ʷ} → {Aₛ : [ Cₛ ⇒ ⟨ Set α ⟩ ]} → (Bₛ : [ Cₛ ⇒ ⟨ Set β ⟩ ]) → [ Cₛ ⇒ᵈ (Aₛ ⇒ʲ ↑ ⟨ Set β ⟩) ]
-- ↑ʲ Bₛ n c a = Bₛ n c


-- _⇒ʲᵈ_ : ∀ {α β γ} {Cₛ : (Set γ)ʷ} → (Aₛ : [ Cₛ ⇒ ⟨ Set α ⟩ ]) → (Bₛ : [ Cₛ ⇒ᵈ (Aₛ  ⇒ʲ ↑ ⟨ Set β ⟩) ] ) → [ Cₛ ⇒ ⟨ Set (α ⊔ β) ⟩ ]
-- _⇒ʲᵈ_ {Cₛ = Cₛ} Aₛ Bₛ n c = (a : Aₛ n c) → Bₛ n c a 


-- qq : ∀ {α β γ δ} {Cₛ : (Set γ)ʷ} → (Aₛ : [ Cₛ ⇒ ⟨ Set α ⟩ ]) → (Bₛ : [ Cₛ ⇒ᵈ (Aₛ  ⇒ʲ ↑ ⟨ Set β ⟩) ] ) → (Dₛ : [ Cₛ ⇒ᵈ (Aₛ ⇒ʲᵈ (Bₛ ⇒ʲᵈʲ ↑ʲ (↑ ⟨ Set δ ⟩) ))  ])→ (Set {!!}) ʷ
-- qq {Cₛ = Cₛ} Aₛ Bₛ Dₛ n = {!!} -- (c : Cₛ n) → (a : Aₛ n c) → Bₛ n c a 

-- -- If we look at Bₛ , maybe we can introduce a trick that guarantees pointwise application of time.
-- aw : ∀ {α β γ} {Cₛ : (Set γ)ʷ} → {Aₛ : [ Cₛ ⇒ ⟨ Set α ⟩ ]} → (cₛ : [ Cₛ ] ) → (aₛ : [ Aₛ $ cₛ ]) → (Bₛ : (∀ n → (cₛ : [ Cₛ ]) → [ Aₛ $ cₛ ⇒ ⟨ Set β ⟩ ]) ) → {!!} -- [ Bₛ cₛ $ aₛ ]
-- aw = {!!}


-- g : ∀ {α β γ} (Cₛ : (Set γ)ʷ) → (Aₛ : [ Cₛ ⇒ ⟨ Set α ⟩ ]) → (Bₛ : ∀ n → (c : Cₛ n) → Aₛ n c → Set β ) → (Set (α ⊔ (β ⊔ γ))) ʷ
-- g Cₛ Aₛ Bₛ n = (c : Cₛ n) → (a : Aₛ n c) → Bₛ n c a 


-- go : ∀ {α β γ} (Cₛ : (Set γ)ʷ) → (Aₛ : [ Cₛ ⇒ ⟨ Set α ⟩ ]) → (Bₛ : [ Cₛ ⇒ ⟨ Set β ⟩ ]) → (Set (α ⊔ (β ⊔ γ))) ʷ
-- go Cₛ Aₛ Bₛ n = (c : Cₛ n) → Aₛ n c → Bₛ n c 






-- r : ∀ {α β γ} (Aₛ : (Set α)ʷ) → (Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ]) → (∀ n → (a : Aₛ n) → Bₛ n a → Set γ)
-- r = {!!}

-- w : ∀ {α β γ} {Aₛ : (Set α)ʷ} → (Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ]) → (aₛ : [ Aₛ ] ) → (fₛ : [ Aₛ ⇒ᵈ Bₛ ]) → [ (Bₛ $ aₛ) ⇒ ⟨ Set γ ⟩ ]
-- w Bₛ aₛ fₛ = {!!}

-- e : ∀ {α β} (Aₛ : (Set α)ʷ) → (Set (α ⊔ lsuc β)) ʷ
-- e {β = β} Aₛ = Aₛ ⇒ ⟨ Set β ⟩

-- e1 : ∀ {α β γ} (Aₛ : (Set α)ʷ) → (Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ]) → [ e {β = γ} Aₛ ]
-- e1 Aₛ Bₛ = {!!}

-- q : ∀ {α β} (Aₛ : (Set α)ʷ) → (Bₛ : [ Aₛ ⇒ ⟨ Set β ⟩ ]) → (Set (α ⊔ β)) ʷ
-- q Aₛ Bₛ = Aₛ ⇒ᵈ Bₛ

