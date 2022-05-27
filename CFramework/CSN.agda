import CFramework.CTerm as CTerm

open import Agda.Primitive
--open import Relation {lzero} using (Rel; dual)

module CFramework.CSN (C : Set) (_▹_ : CTerm.Rel C) where

open import Data.Product renaming (map to mapΣ)
open import Induction.WellFounded as WF

open CTerm C
open import CFramework.CSubstitution C renaming (Σ to Subst) hiding (_∘_; R)
open import CFramework.CAlpha C
open import CFramework.CReduction C _▹_ as Reduction
open import CFramework.CDefinitions C

sn : Λ → Set
sn = Acc (dual _⟿_)

inversionSnApp : ∀ {M N} → sn (M · N) → sn M × sn N
inversionSnApp {M} {N} (acc snMN) = acc (λ M′ M→M′ → proj₁ (inversionSnApp (snMN (M′ · N) (appL M→M′)))) , acc (λ N′ N→N′ → proj₂ (inversionSnApp (snMN (M · N′) (appR N→N′))))

{-closureSn∼α : Comm∼α _⟿_ → ∀ {M N} → sn M → M ∼α N → sn N
closureSn∼α h {M} {N} (acc snM) M∼N = acc aux
  where
    aux : ∀ P → N ⟿ P → sn P
    aux P N→P =
      let Q , M→Q , Q∼P = h M∼N N→P
      in closureSn∼α h (snM Q M→Q) Q∼P-}

closureSn∼α : Comm∼α _⟿_ → ∀ {M N} → sn M → M ∼α N → sn N
closureSn∼α h {M} {N} (acc snM) M∼N =
  acc λ P P←N → let Q , M→Q , Q∼P = h M∼N P←N
                in closureSn∼α h (snM Q M→Q) Q∼P
      

