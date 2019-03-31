module LTL.CoreP where

open import LTL.Core

open import Data.Nat 
open import Data.Empty
open import Data.Nat.Properties
open import Data.Product
open import Relation.Nullary
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])


lemma1 : ∀{a} {A : Set a} → A ʷ ≡ [ ⟨ A ⟩ ]
lemma1 = refl

lemma2 : ∀ {α} → {Aₛ : (Set α) ʷ } → !ₛ Aₛ ≡ ! {Aₛ = ⟨ Set α ⟩ } Aₛ
lemma2 = refl

lemma3 : ∀ {α} {Aₛ : (Set α) ʷ} → ○ₛ Aₛ ≡ ○ Aₛ
lemma3 = refl

