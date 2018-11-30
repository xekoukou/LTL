module LTL.Theorems where

open import LTL.Core
open import LTL.Stateless
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


foo′ : ∀{α k m w} → {A : Set α} → ∀{a b} → (dec : (a b : A) → Dec (a ≡ b)) → (beh : A ʷ) → k < m → ¬ (a ≡ b) → beh k ≡ a → beh m ≡ b
       → m ∸ k ≡ w → ∃ λ h → (k ≤ h) × (h < m) × ( ⟨ a ≡_ ⟩ $ beh) [ k ,, h ] × ¬ (beh (suc h) ≡ a)
foo′ {w = zero} dec beh klm ¬eq lbnd rbnd negeq = ⊥-elim ((<⇒≱ klm) (m∸n≡0⇒m≤n negeq)) 
foo′ {k = k} {m} {suc zero} dec beh klm ¬eq lbnd rbnd negeq
  = k , (≤-refl , (klm , (λ m x y → subst (λ z → _ ≡ beh z) (≤-antisym x y) (sym lbnd)) , λ x → ¬eq (trans (sym x) q))) where
    q = subst (λ z → beh z ≡ _) (trans (sym (m∸n+n≡m (<⇒≤ klm))) (cong (_+ k) negeq)) rbnd
foo′ {k = k} {w = suc (suc w)} {a = a} dec beh klm ¬eq lbnd rbnd negeq with dec (beh (suc k)) a
foo′ {k = k} {_} {suc (suc w)} {a = a} dec beh klm ¬eq lbnd rbnd negeq | yes p
  = let (h , sk≤h , h<m , intv , noteq) = foo′ {w = suc w} dec beh {!!} ¬eq p rbnd {!!}
    in h , ((≤⇒pred≤ sk≤h) , (h<m , (λ {m x y → {!!}}) , {!!}))
foo′ {k = k} {_} {suc (suc w)} {a = a} dec beh klm ¬eq lbnd rbnd negeq | no ¬p
  = k , (≤-refl , klm , ((λ m x y → subst (λ z → _ ≡ beh z) (≤-antisym x y) (sym lbnd)) , ¬p))


foo : ∀{α k m} → {A : Set α} → ∀{a b} → (beh : A ʷ) → k < m → ¬ (a ≡ b) → beh k ≡ a → beh m ≡ b
      → ∃ λ h → (k ≤ h) × (h < m) × ( ⟨ a ≡_ ⟩ $ beh) [ k ,, h ] × ¬ (beh (suc h) ≡ a)
foo {k = k} {m} beh (s≤s klm) ¬eq lbnd rbnd with (m ∸ k)
foo {k = k} {.(suc _)} beh (s≤s klm) ¬eq lbnd rbnd | zero = {!!}
foo {k = k} {.(suc _)} beh (s≤s klm) ¬eq lbnd rbnd | suc r = {!!}



-- m∸n+n≡m : ∀ {m n} → n ≤ m → (m ∸ n) + n ≡ m
-- m∸n+n≡m {m} {n} n≤m = begin


-- m+n∸m≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
-- m+n∸m≡n {m} {n} m≤n = begin
