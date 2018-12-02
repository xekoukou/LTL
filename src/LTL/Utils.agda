module LTL.Utils where

open import LTL.Core
open import LTL.Stateless
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality



private
  jj : ∀ {g k l} → k ≤ g → g ∸ k ≡ suc l → suc k ≤ g
  jj {g} {k} lt eq with trans (cong (λ z → z + k) (sym eq)) (m∸n+n≡m lt)
  jj {.(suc (_ + k))} {k} lt eq | refl = s≤s (n≤m+n _ k)
  
  
  bb : ∀ {g l} → ∀ k → g ∸ k ≡ suc l → g ∸ (suc k) ≡ l
  bb {zero} zero ()
  bb {zero} (suc k) ()
  bb {suc g} (zero) refl = refl
  bb {suc g} (suc k) eq = bb {g = g} k eq
  
  
  bb2 : ∀ {g l} → ∀ k → g ∸ k ≡ suc l → (pred g) ∸ k ≡ l
  bb2 {zero} zero ()
  bb2 {zero} (suc k) ()
  bb2 {suc g} zero refl = refl
  bb2 {suc g} (suc k) eq = bb k eq
  
  
  dd : ∀{m k} → m ∸ k ≡ 1 → pred m ≡ k
  dd {zero} {zero} ()
  dd {zero} {suc k} ()
  dd {suc .0} {zero} refl = refl
  dd {suc zero} {suc zero} ()
  dd {suc zero} {suc (suc k)} ()
  dd {suc m@(suc _)} {suc k} x = cong suc (dd x)
  



{-# TERMINATING #-}
[a→b]⇒[a→a]′ : ∀{α k m w} → {A : Set α} → ∀{a b} → (dec : (a b : A) → Dec (a ≡ b)) → (beh : A ʷ)
       → k < m → ¬ (a ≡ b) → beh k ≡ a → beh m ≡ b
       → m ∸ k ≡ w → ∃ λ h → (k ≤ h) × (h < m) × ( ⟨ a ≡_ ⟩ $ beh) [ k ,, h ] × ¬ (beh (suc h) ≡ a)
[a→b]⇒[a→a]′ {w = zero} dec beh klm ¬eq lbnd rbnd negeq = ⊥-elim ((<⇒≱ klm) (m∸n≡0⇒m≤n negeq)) 
[a→b]⇒[a→a]′ {k = k} {m} {suc zero} dec beh klm ¬eq lbnd rbnd negeq
  = k , (≤-refl , (klm , (λ m x y → subst (λ z → _ ≡ beh z) (≤-antisym x y) (sym lbnd)) , λ x → ¬eq (trans (sym x) q))) where
    q = subst (λ z → beh z ≡ _) (trans (sym (m∸n+n≡m (<⇒≤ klm))) (cong (_+ k) negeq)) rbnd
[a→b]⇒[a→a]′ {k = k} {w = suc (suc w)} {a = a} dec beh klm ¬eq lbnd rbnd negeq with dec (beh (suc k)) a
[a→b]⇒[a→a]′ {k = k} {m} {suc (suc w)} {a = a} dec beh klm ¬eq lbnd rbnd negeq | yes p
  = h , ((≤⇒pred≤ sk≤h) , (h<m , (λ g → d g refl) , noteq)) where
      e = (bb k negeq)
      f : ∃ λ h → ((suc k) ≤ h) × (h < m) × ( ⟨ a ≡_ ⟩ $ beh) [ (suc k) ,, h ] × ¬ (beh (suc h) ≡ a)
      f = [a→b]⇒[a→a]′ {w = suc w} dec beh (jj klm e) ¬eq p rbnd e
      h = proj₁ f
      sk≤h = proj₁ (proj₂ f)
      h<m = proj₁ (proj₂ (proj₂ f))
      intv = proj₁ (proj₂ (proj₂ (proj₂ f)))
      noteq = proj₂ (proj₂ (proj₂ (proj₂ f)))
      d : ∀{l} → (g : ℕ) → g ∸ k ≡ l → k ≤ g → g ≤ h → a ≡ beh g
      d {zero} g eq kleg gleh = subst (λ z → a ≡ beh z) (≤-antisym kleg (m∸n≡0⇒m≤n eq)) (sym lbnd)
      d {suc l} g eq kleg gleh = intv g (jj kleg eq) gleh


[a→b]⇒[a→a]′ {k = k} {_} {suc (suc w)} {a = a} dec beh klm ¬eq lbnd rbnd negeq | no ¬p
  = k , (≤-refl , klm , ((λ m x y → subst (λ z → _ ≡ beh z) (≤-antisym x y) (sym lbnd)) , ¬p))


[a→b]⇒[a→a] : ∀{α k m} → {A : Set α} → ∀{a b} → (dec : (a b : A) → Dec (a ≡ b)) → (beh : A ʷ)
       → k < m → ¬ (a ≡ b) → beh k ≡ a → beh m ≡ b
       → ∃ λ h → (k ≤ h) × (h < m) × ( ⟨ a ≡_ ⟩ $ beh) [ k ,, h ] × ¬ (beh (suc h) ≡ a)
[a→b]⇒[a→a] dec beh klm ¬eq lbnd rbnd = [a→b]⇒[a→a]′ dec beh klm ¬eq lbnd rbnd refl



{-# TERMINATING #-}
[a→b]⇒[b←b]′ : ∀{α k m w} → {A : Set α} → ∀{a b} → (dec : (a b : A) → Dec (a ≡ b)) → (beh : A ʷ)
       → k < m → ¬ (a ≡ b) → beh k ≡ a → beh m ≡ b
       → m ∸ k ≡ w → ∃ λ h → (k < h) × (h ≤ m) × ( ⟨ b ≡_ ⟩ $ beh) [ h ,, m ] × ¬ (beh (pred h) ≡ b)
[a→b]⇒[b←b]′ {w = zero} dec beh klm ¬eq lbnd rbnd negeq = ⊥-elim ((<⇒≱ klm) (m∸n≡0⇒m≤n negeq))
[a→b]⇒[b←b]′ {k = k} {m} {suc zero} dec beh klm ¬eq lbnd rbnd negeq
  = (m , klm , (≤-refl , ((λ z x y → subst (λ z → _ ≡ beh z) (≤-antisym x y) (sym rbnd)) ,  λ x → ¬eq (trans (sym q) x)))) where
    q = subst ((λ z → beh z ≡ _)) (sym (dd negeq)) lbnd
[a→b]⇒[b←b]′ {k = k} {m} {suc (suc w)} {b = b} dec beh klm ¬eq lbnd rbnd negeq with dec (beh (pred m)) b
[a→b]⇒[b←b]′ {k = k} {m} {suc (suc w)} {b = b} dec beh klm ¬eq lbnd rbnd negeq | yes p
  = h , k<h , (≤pred⇒≤ h≤m , (λ z → d z refl) , noteq) where
    f = [a→b]⇒[b←b]′ {w = suc w} dec beh (<⇒≤pred (jj klm (bb k negeq))) ¬eq lbnd p (bb2 k negeq)
    h = proj₁ f
    k<h = proj₁ (proj₂ f)
    h≤m = proj₁ (proj₂ (proj₂ f))
    intv = proj₁ (proj₂ (proj₂ (proj₂ f)))
    noteq = proj₂ (proj₂ (proj₂ (proj₂ f)))
    d : ∀{l} → (z : ℕ) → m ∸ z ≡ l → h ≤ z → z ≤ m → b ≡ beh z
    d {zero} z eq x y =  subst (λ z → b ≡ beh z) (≤-antisym (m∸n≡0⇒m≤n eq) y) (sym rbnd)
    d {suc l} z eq x y = intv z x (<⇒≤pred (jj y eq))
[a→b]⇒[b←b]′ {k = k} {m} {suc (suc w)} {b = b} dec beh klm ¬eq lbnd rbnd negeq | no ¬p
  = m , klm , (≤-refl , (λ z x y → subst (λ z → _ ≡ beh z) (≤-antisym x y) (sym rbnd)) , ¬p)

[a→b]⇒[b←b] : ∀{α k m} → {A : Set α} → ∀{a b} → (dec : (a b : A) → Dec (a ≡ b)) → (beh : A ʷ)
       → k < m → ¬ (a ≡ b) → beh k ≡ a → beh m ≡ b
       → ∃ λ h → (k < h) × (h ≤ m) × ( ⟨ b ≡_ ⟩ $ beh) [ h ,, m ] × ¬ (beh (pred h) ≡ b)
[a→b]⇒[b←b] dec beh klm ¬eq lbnd rbnd = [a→b]⇒[b←b]′ dec beh klm ¬eq lbnd rbnd refl




[a→b]⇒x<y : ∀{α k m} → {A : Set α} → ∀{a b} → (dec : (a b : A) → Dec (a ≡ b)) → (beh : A ʷ)
  → (klm : k < m) → (¬eq : ¬ (a ≡ b)) → (lbnd : beh k ≡ a) → (rbnd : beh m ≡ b)
  → ¬ (proj₁ ([a→b]⇒[b←b] dec beh klm ¬eq lbnd rbnd) ≤ proj₁ ([a→b]⇒[a→a] dec beh klm ¬eq lbnd rbnd))
[a→b]⇒x<y dec beh klm ¬eq lbnd rbnd x with ([a→b]⇒[b←b] dec beh klm ¬eq lbnd rbnd) | ([a→b]⇒[a→a] dec beh klm ¬eq lbnd rbnd)
[a→b]⇒x<y dec beh klm ¬eq lbnd rbnd x | ha , _ , _ , ga , _ | hb , hblt2 , hblt , gb , _
  = ¬eq (trans gbr (sym gar)) where
    gar = ga hb x (≤⇒pred≤ hblt)
    gbr = gb hb hblt2 ≤-refl




{-# TERMINATING #-}
[a→b]⇒[Pa→Px]′ : ∀{α β k m w} → {A : Set α} → {P : A → Set β} → (dec : (x : A) → Dec (P x)) → (beh : A ʷ)
       → k < m → P (beh k) → ¬ P (beh m) → m ∸ k ≡ w
       → ∃ λ h → (k ≤ h) × (h < m) × ( ⟨ P ⟩ $ beh) [ k ,, h ] × ¬ (P (beh (suc h)))
[a→b]⇒[Pa→Px]′ {w = zero} dec beh klm lbnd rbnd negeq =  ⊥-elim ((<⇒≱ klm) (m∸n≡0⇒m≤n negeq))
[a→b]⇒[Pa→Px]′ {k = k} {m} {w = suc zero} {P = P} dec beh klm lbnd rbnd negeq
  = k , (≤-refl , (klm , (λ m x y → subst (λ z → P (beh z)) (≤-antisym x y) lbnd) , q)) where
    q = subst (λ z → ¬ P (beh z)) (trans (sym (m∸n+n≡m (<⇒≤ klm))) (cong (_+ k) negeq)) rbnd
[a→b]⇒[Pa→Px]′ {k = k} {m} {w = suc (suc w)} {P = P} dec beh klm lbnd rbnd negeq with dec (beh (suc k))
[a→b]⇒[Pa→Px]′ {k = k} {m} {suc (suc w)} {P = P} dec beh klm lbnd rbnd negeq | yes p
  =  h , ((≤⇒pred≤ sk≤h) , (h<m , (λ g → d g refl) , noteq)) where
      e = (bb k negeq)
      f : ∃ λ h → ((suc k) ≤ h) × (h < m) × ( ⟨ P ⟩ $ beh) [ (suc k) ,, h ] × ¬ P (beh (suc h))
      f = [a→b]⇒[Pa→Px]′ {w = suc w} dec beh (jj klm e) p rbnd e
      h = proj₁ f
      sk≤h = proj₁ (proj₂ f)
      h<m = proj₁ (proj₂ (proj₂ f))
      intv = proj₁ (proj₂ (proj₂ (proj₂ f)))
      noteq = proj₂ (proj₂ (proj₂ (proj₂ f)))
      d : ∀{l} → (g : ℕ) → g ∸ k ≡ l → k ≤ g → g ≤ h → P (beh g)
      d {zero} g eq kleg gleh = subst (λ z → P (beh z)) (≤-antisym kleg (m∸n≡0⇒m≤n eq)) lbnd
      d {suc l} g eq kleg gleh = intv g (jj kleg eq) gleh
[a→b]⇒[Pa→Px]′ {k = k} {m} {suc (suc w)} {P = P} dec beh klm lbnd rbnd negeq | no ¬p
  = k , (≤-refl , klm , ((λ m x y → subst (λ z → P (beh z)) (≤-antisym x y) lbnd) , ¬p))


[a→b]⇒[Pa→Px] : ∀{α β k m} → {A : Set α} → {P : A → Set β} → (dec : (x : A) → Dec (P x)) → (beh : A ʷ)
       → k < m → P (beh k) → ¬ P (beh m)
       → ∃ λ h → (k ≤ h) × (h < m) × ( ⟨ P ⟩ $ beh) [ k ,, h ] × ¬ (P (beh (suc h)))
[a→b]⇒[Pa→Px] dec beh klm lbnd rbnd = [a→b]⇒[Pa→Px]′ dec beh klm lbnd rbnd refl



{-# TERMINATING #-}
[a→b]⇒[¬Px←¬Pb]′ : ∀{α β k m w} → {A : Set α} → {P : A → Set β} → (dec : (x : A) → Dec (P x)) → (beh : A ʷ)
       → k < m → P (beh k) → ¬ P (beh m) → m ∸ k ≡ w
       → ∃ λ h → (k < h) × (h ≤ m) × ( ⟨ (λ z → ¬ P z) ⟩ $ beh) [ h ,, m ] × P (beh (pred h))
[a→b]⇒[¬Px←¬Pb]′ {w = zero} dec beh klm lbnd rbnd negeq =  ⊥-elim ((<⇒≱ klm) (m∸n≡0⇒m≤n negeq))
[a→b]⇒[¬Px←¬Pb]′ {k = k} {m} {suc zero} {P = P} dec beh klm lbnd rbnd negeq
  = (m , klm , (≤-refl , ((λ z x y → subst (λ z → ¬ P (beh z)) (≤-antisym x y) rbnd ) ,  q))) where 
    q = subst ((λ z → P (beh z))) (sym (dd negeq)) lbnd
[a→b]⇒[¬Px←¬Pb]′ {k = k} {m} {suc (suc w)} dec beh klm lbnd rbnd negeq with dec (beh (pred m))
[a→b]⇒[¬Px←¬Pb]′ {k = k} {m} {suc (suc w)} {P = P} dec beh klm lbnd rbnd negeq | no ¬p
  =  h , k<h , (≤pred⇒≤ h≤m , (λ z → d z refl) , noteq) where
     f = [a→b]⇒[¬Px←¬Pb]′ {w = suc w} dec beh (<⇒≤pred (jj klm (bb k negeq))) lbnd ¬p (bb2 k negeq)
     h = proj₁ f
     k<h = proj₁ (proj₂ f)
     h≤m = proj₁ (proj₂ (proj₂ f))
     intv = proj₁ (proj₂ (proj₂ (proj₂ f)))
     noteq = proj₂ (proj₂ (proj₂ (proj₂ f)))
     d : ∀{l} → (z : ℕ) → m ∸ z ≡ l → h ≤ z → z ≤ m → ¬ P (beh z)
     d {zero} z eq x y =  subst (λ z → ¬ P (beh z)) (≤-antisym (m∸n≡0⇒m≤n eq) y) rbnd
     d {suc l} z eq x y = intv z x (<⇒≤pred (jj y eq))
[a→b]⇒[¬Px←¬Pb]′ {k = k} {m} {suc (suc w)} {P = P} dec beh klm lbnd rbnd negeq | yes p
  = m , klm , (≤-refl , (λ z x y → subst (λ z → ¬ P (beh z)) (≤-antisym x y) rbnd) , p)

[a→b]⇒[¬Px←¬Pb] : ∀{α β k m} → {A : Set α} → {P : A → Set β} → (dec : (x : A) → Dec (P x)) → (beh : A ʷ)
       → k < m → P (beh k) → ¬ P (beh m)
       → ∃ λ h → (k < h) × (h ≤ m) × ( ⟨ (λ z → ¬ P z) ⟩ $ beh) [ h ,, m ] × P (beh (pred h))
[a→b]⇒[¬Px←¬Pb] dec beh klm lbnd rbnd = [a→b]⇒[¬Px←¬Pb]′ dec beh klm lbnd rbnd refl
