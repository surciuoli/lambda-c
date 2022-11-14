module STLC where

open import Data.Nat as Nat hiding (_*_)
open import Data.Product renaming (map to mapΣ)
open import Induction.WellFounded as WF
open import Data.Empty
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Nullary

open import CFramework.CChi hiding (+-comm)
open import CFramework.CTerm ⊥ renaming (Λ to Term)
open import CFramework.CSubstitution ⊥ renaming (Σ to Subst) hiding (_∘_)
open import CFramework.CSubstitutionLemmas ⊥
open import CFramework.Misc.ListProperties hiding (_-_)
open import CFramework.CAlpha ⊥
open import CFramework.CType
open import CFramework.CContext Type _≟_
open import CFramework.CBetaContraction ⊥
open import CFramework.CReduction ⊥ _▹β_ as Reduction renaming (_⟿_ to _→β_)
open import CFramework.CSN ⊥ _▹β_
open import CFramework.CReducibility ⊥ _▹β_ as Reducibility

infix 3 _⊢_∶_
data _⊢_∶_ (Γ : Cxt) : Term → Type → Set where
  ⊢var : ∀ {x} → (k : x ∈ Γ) → Γ ⊢ v x ∶ Γ ⟨ k ⟩
  ⊢abs : ∀ {x M α β} → Γ ‚ x ∶ α ⊢ M ∶ β → Γ ⊢ ƛ x M ∶ α ⇒ β
  ⊢app : ∀ {M N α β} → Γ ⊢ M ∶ α ⇒ β → Γ ⊢ N ∶ α → Γ ⊢ M · N ∶ β

-- First step:

cond▹β : ∀ {x N} → Vec (v x) N → ∀ {Q} → ¬(N ▹β Q)
cond▹β nil ()
cond▹β (cons ()) beta

lemmaβNe : ∀ {x M N} → Ne ((ƛ x M) · N)
lemmaβNe nil ()
lemmaβNe (cons _) ()

open Reducibility.RedProperties cond▹β

-- Second step:

open Reduction.CompatSubst preser▹β# compat▹β∙ renaming (compat⟿∙ to compat→β∙)
open Reduction.CommutesAlpha preser▹β# compat▹β∙ commut▹βα renaming (commut⟿α to commut→βα)

lemmaAbs : ∀ {x M N α β} → sn M → sn N → Red α N → (∀ {P} → Red α P → Red β (M [ P / x ])) → Red β (ƛ x M · N)
lemmaAbs snM snN RedN RedM[P/x] = CR3 lemmaβNe (hyp-aux snM snN RedN RedM[P/x])
  where
    hyp-aux : ∀ {α β x M N P} → sn M → sn N → Red α N → (∀ {P} → Red α P → Red β (M [ P / x ])) → ƛ x M · N →β P → Red β P
    hyp-aux _ _ RedN RedM[P/x] (redex beta) = RedM[P/x] RedN 
    hyp-aux {α} {β} {P = ƛ x M′ · N} (acc snM) snN RedN RedM[P/x] (appL (abs M→M′)) =
      lemmaAbs (snM M′ M→M′) snN RedN RedM′[P/x]
        where
          RedM′[P/x] : ∀ {P} → Red α P → Red β (M′ [ P / x ])
          RedM′[P/x] RedP =
            let _ , M[P/x]→Q , Q∼M′[P/x] = compat→β∙ M→M′
            in closureRed∼α commut→βα (CR2 (RedM[P/x] RedP) M[P/x]→Q) Q∼M′[P/x]
    hyp-aux {P = ƛ x M · N′} snM (acc snN) RedN RedM[P/x] (appR N→N′) = lemmaAbs snM (snN N′ N→N′) (CR2 RedN N→N′) RedM[P/x]
    hyp-aux _ _ _ _ (appL (redex ()))

main : ∀ {α M σ Γ} → Γ ⊢ M ∶ α → RedSubst σ Γ → Red α (M ∙ σ)
main (⊢var {x} x∈Γ) Redσ = Redσ x x∈Γ
main {α ⇒ β} {ƛ x M} {σ} (⊢abs M:β) Redσ {N} RedN = lemmaAbs (CR1 RedMσ,y/x) (CR1 RedN) RedN RedMσ,y/x[P/y]
  where
    y : V
    y = χ (σ , ƛ x M)
    RedMσ,y/x : Red β (M ∙ σ ≺+ (x , v y))
    RedMσ,y/x = main M:β (Red-upd Redσ x (CR3 lemmaNeV (λ x⟿N → ⊥-elim (lemmaNfV x⟿N))))
    RedMσ,y/x[P/y] : ∀ {P} → Red α P → Red β ((M ∙ σ ≺+ (x , v y)) [ P / y ])
    RedMσ,y/x[P/y] RedP = closureRed∼α commut→βα (main M:β (Red-upd Redσ x RedP)) (∼σ (corollary1SubstLemma (χ-lemma2 σ (ƛ x M))))
main (⊢app M:α→β N:α) Redσ = (main M:α→β Redσ) (main N:α Redσ)

strongNormalization : ∀ {Γ M α} → Γ ⊢ M ∶ α → sn M
strongNormalization M:α = closureSn∼α commut→βα (CR1 (main M:α Red-ι)) (∼σ lemma∙ι)
