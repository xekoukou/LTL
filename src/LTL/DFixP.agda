module LTL.DFixP where

open import LTL.Core public
open import LTL.Decoupled
open import LTL.Stateless
open import LTL.Product
open import LTL.Causal
open import Data.Product
open import LTL.Globally

-- -- Fixed points

-- -- The following type-checks, but fails to pass the termination
-- -- checker, as the well-ordering on time is not made explicit:
-- --
-- -- fix : ∀ {A} → ⟦ (A ▻ A) ⇒ □ A ⟧ 
-- -- fix {A} {s} f {u} s≤u = f s≤u (σ u) where
-- --
-- --   σ : (u : Time) → A [ s , u ⟩
-- --   σ u {t} s≤t t<u = f s≤t (σ t)
-- --
-- -- To get this to pass the termination checker, we have to
-- -- be explicit about the induction scheme, which is
-- -- over < being a well-ordering on an interval.


-- fix : ∀{α} → {A : (Set α) ʷ} → [ (A ▻ A) ⇒ □ᶠ A ]
-- fix {_} {A} s f u s≤u = f u s≤u (σ (<-wo s≤u)) where
--   σ : ∀ {u} → (∃ λ n → (s ≮[ n ] u)) → A [ s ,, u ⟩
--   σ (zero , ())
--   σ (suc x , y) _ s≤t t<u = f _ s≤t (σ (x , y s≤t t<u))


-- -- Indexed fixed points are derivable from fixed points

-- ifix : ∀{ℓ m} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} → [ ((A ∧ B) ▻ A) ⇒ (B ▻ A) ]
-- ifix {_} {_} {A} {B} s f v s≤v τ = fix _ g _ s≤v (diff! zero) where

--   A′ : (Set _) ʷ
--   A′ t = (t ≤ v) → A t

--   g : (A′ ▻ A′) s
--   g u s≤u σ u≤v = f _ s≤u ρ where
--     ρ : (A ∧ B) [ s ,, u ⟩
--     ρ t s≤t t<u = σ _ s≤t t<u (leq-trans {{OrdNatLaws}} (lt-to-leq {{OrdNat}} t<u) u≤v) , τ _ s≤t w where
--       w = inv-suc-monotone (leq-trans {{OrdNatLaws}} (suc-monotone t<u) u≤v)

-- -- -- Loops are derivable from indexed fixed points

-- loop : ∀{ℓ m n} {A : (Set ℓ) ʷ} {B : (Set m) ʷ} {C : (Set n) ʷ} → [ ((A ∧ B) ▻ (A ∧ C)) ⇒ (B ▻ C) ]
-- loop s f =  ((sndsᶜ _) ·ᵈˡ f) ·ᵈʳ e where 
--   w = couple _ (ifix _ (fstsᶜ _ ·ᵈˡ f))
--   e = bothsᶜ s w (identity _)
