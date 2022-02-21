module STLC where

open import Data.Nat as Nat hiding (_*_)
open import Data.Product renaming (map to mapΣ)
open import Induction.WellFounded as WF
open import Data.Empty
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Nullary

open import Chi hiding (+-comm)
open import CFramework.CTerm renaming (Λ to Term)
open import CFramework.CSubstitution renaming (Σ to Subst) hiding (_∘_)
open import CFramework.CSubstitutionLemmas 
open import ListProperties hiding (_-_)
open import CFramework.CAlpha
import Relation
open import CFramework.CType
open import Context Type _≟_
open import CFramework.CBetaContraction
open import CFramework.CReduction _▹β_ as Reduction renaming (_⟿_ to _→β_)

infix 3 _⊢_∶_
data _⊢_∶_ (Γ : Cxt) : Term → Type → Set where
  ⊢var : ∀ {x} → (k : x ∈ Γ) → Γ ⊢ v x ∶ Γ ⟨ k ⟩
  ⊢abs : ∀ {x M α β} → Γ ‚ x ∶ α ⊢ M ∶ β → Γ ⊢ ƛ x M ∶ α ⇒ β
  ⊢app : ∀ {M N α β} → Γ ⊢ M ∶ α ⇒ β → Γ ⊢ N ∶ α → Γ ⊢ M · N ∶ β

data Neβ : Term → Set where
  var : ∀ {x} → Neβ (v x)
  app : ∀ {M} → Neβ M → ∀ {N} → Neβ (M · N)
  beta : ∀ {x M N} → Neβ (ƛ x M · N)

open import CFramework.CReducibility _▹β_ Neβ as Reducibility

conditions▹β : Conditions▹
conditions▹β = record
  { cond1 = λ { {x} {M} () }
  }

conditionsNeβ : ConditionsNe
conditionsNeβ = record
  { cond1 = var
  ; cond2 = app
  ; cond3 = λ { {_} var {_} {_} () ; {_} (app _) {_} {_} () ; {_} beta {_} {_} () }
  }

open Reduction.CompatSubst lemma*◃β compat▹β∙
open Reducibility.Properties lemma*◃β compat▹β∙ commut∼α▹β conditionsNeβ conditions▹β

lemma-abs : ∀ {x M N α β} → sn M → sn N → Red α N → (∀ {P} → Red α P → Red β (M [ P / x ])) → Red β (ƛ x M · N)
lemma-abs snM snN RedN RedM[P/x] = CR3 beta (hyp-aux snM snN RedN RedM[P/x])
  where
    hyp-aux : ∀ {α β x M N P} → sn M → sn N → Red α N → (∀ {P} → Red α P → Red β (M [ P / x ])) → ƛ x M · N →β P → Red β P
    hyp-aux _ _ RedN RedM[P/x] (redex beta) = RedM[P/x] RedN 
    hyp-aux {α} {β} {P = ƛ x M′ · N} (acc snM) snN RedN RedM[P/x] (appL (abs M→M′)) =
      lemma-abs (snM M′ M→M′) snN RedN RedM′[P/x]
        where
          RedM′[P/x] : ∀ {P} → Red α P → Red β (M′ [ P / x ])
          RedM′[P/x] RedP =
            let _ , M[P/x]→Q , Q∼M′[P/x] = compat⟿∙ M→M′
            in closureRed∼α (CR2 (RedM[P/x] RedP) M[P/x]→Q) Q∼M′[P/x]
    hyp-aux {P = ƛ x M · N′} snM (acc snN) RedN RedM[P/x] (appR N→N′) = lemma-abs snM (snN N′ N→N′) (CR2 RedN N→N′) RedM[P/x]
    hyp-aux _ _ _ _ (appL (redex ()))

subst-lemma : ∀ {α M σ Γ} → Γ ⊢ M ∶ α → RedSubst σ Γ → Red α (M ∙ σ)
subst-lemma (⊢var {x} x∈Γ) Redσ = Redσ x x∈Γ
subst-lemma {α ⇒ β} {ƛ x M} {σ} (⊢abs M:β) Redσ {N} RedN = lemma-abs (CR1 RedMσ,y/x) (CR1 RedN) RedN RedMσ,y/x[P/y]
  where
    y : V
    y = χ (σ , ƛ x M)
    RedMσ,y/x : Red β (M ∙ σ ≺+ (x , v y))
    RedMσ,y/x = subst-lemma M:β (Red-upd Redσ x (CR4 var lemmaNfV))
    RedMσ,y/x[P/y] : ∀ {P} → Red α P → Red β ((M ∙ σ ≺+ (x , v y)) [ P / y ])
    RedMσ,y/x[P/y] RedP = closureRed∼α (subst-lemma M:β (Red-upd Redσ x RedP)) (∼σ (corollary1SubstLemma (χ-lemma2 σ (ƛ x M))))
subst-lemma (⊢app M:α→β N:α) Redσ = (subst-lemma M:α→β Redσ) (subst-lemma N:α Redσ)

strong-normalization : ∀ {Γ M α} → Γ ⊢ M ∶ α → sn M
strong-normalization M:α = closureSn∼α (CR1 (subst-lemma M:α Red-ι)) (∼σ lemma∙ι)
