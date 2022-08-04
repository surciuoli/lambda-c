import CFramework.CTerm as CTerm

open import Agda.Primitive

module CFramework.CReducibility (C : Set) (_▹_ : CTerm.Rel C) where

open import Data.Nat as Nat hiding (_*_)
open import Data.Product renaming (map to mapΣ)
open import Induction.WellFounded as WF
open import Data.Empty
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Nullary

open CTerm C
open import CFramework.CChi hiding (+-comm)
open import CFramework.CSubstitution C renaming (Σ to Subst) hiding (_∘_; R)
open import CFramework.CSubstitutionLemmas C
open import CFramework.Misc.ListProperties hiding (_-_)
open import CFramework.CAlpha C
open import CFramework.CType
open import CFramework.CContext Type _≟_
open import CFramework.CReduction C _▹_ as Reduction
open import CFramework.CDefinitions C
open import CFramework.CSN C _▹_ as SN

--Nf : Λ → Set
--Nf M = ∀ {N} → ¬(M ⟿ N)

Red : Type → Λ → Set
Red τ M = sn M 
Red (α ⇒ β) M = ∀ {N} → Red α N → Red β (M · N)

RedSubst : Subst → Cxt → Set
RedSubst σ Γ  = ∀ x → (k : x ∈ Γ) → Red (Γ ⟨ k ⟩) (σ x)

Red-upd : ∀ {α Γ σ N} → RedSubst σ Γ → (x : V) → Red α N → RedSubst (σ ≺+ (x , N)) (Γ ‚ x ∶ α)
Red-upd Redσ x RedN y y∈Γ,x:α with x ≟ y
Red-upd Redσ x RedN y (there _ y∈Γ)  | no _ = Redσ y y∈Γ
Red-upd Redσ x RedN .x here          | no x≢y = ⊥-elim (x≢y refl)
Red-upd Redσ x RedN .x (there x≢y _) | yes refl = ⊥-elim (x≢y refl)
Red-upd Redσ x RedN .x here          | yes refl = RedN

closureRed∼α : Comm∼α _⟿_ → ∀ {α M N} → Red α M → M ∼α N → Red α N
closureRed∼α h {τ} = closureSn∼α h
closureRed∼α h {_ ⇒ _} RedM M∼N RedP = closureRed∼α h (RedM RedP) (∼· M∼N ∼ρ)

record ConditionsNe (Ne : Pred) : Set where
  field
    cond1 : ∀ {x} → Ne (v x)
    cond2 : ∀ {M} → Ne M → ∀ {N} → Ne (M · N)
    cond3 : ∀ {M} → Ne M → ∀ {N P} → ¬((M · N) ▹ P)

record Conditions▹ : Set where
  field
    cond1 : ∀ {x M} → ¬(v x ▹ M)

module RedProperties (Ne : Pred) (condNe : ConditionsNe Ne) (cond▹ : Conditions▹) where

  lemmaNfV :  ∀ {x N} → {A : Set lzero} → v x ⟿ N → A
  lemmaNfV (redex r) = ⊥-elim (Conditions▹.cond1 cond▹ r)

  mutual 
    CR1 : ∀ {α M} → Red α M → sn M
    CR1 {τ} snM = snM
    CR1 {α ⇒ β} Redα⇒β = proj₁ (inversionSnApp {N = v 0} (CR1 (Redα⇒β (CR3 (ConditionsNe.cond1 condNe) lemmaNfV))))

    CR2 : ∀ {α M N} → Red α M → M ⟿ N → Red α N
    CR2 {τ} {_} {N} (acc snM) (M→N) = snM N M→N
    CR2 {α ⇒ β} RedM M→N RedP = CR2 (RedM RedP) (appL M→N)
  
    CR3 : ∀ {α M} → Ne M → (∀ {N} → M ⟿ N → Red α N) → Red α M
    CR3 {τ} _ h = acc (λ _ M→N → h M→N)
    CR3 {α ⇒ β} neM h RedP = CR3-arrow neM h RedP (CR1 RedP)

    CR3-arrow : ∀ {α β M P} → Ne M → (∀ {N} → M ⟿ N → Red (α ⇒ β) N) → Red α P → sn P → Red β (M · P)
    CR3-arrow {α} {β} {M} neM h RedP snP = CR3 (ConditionsNe.cond2 condNe neM) (hyp-aux neM h RedP snP)
      where
        hyp-aux : ∀ {M P Q} → Ne M → (∀ {N} → M ⟿ N → Red (α ⇒ β) N) → Red α P → sn P → M · P ⟿ Q → Red β Q
        hyp-aux neM _ _ _ (redex redx) = ⊥-elim (ConditionsNe.cond3 condNe neM redx) 
        hyp-aux _ h RedP _ (appL M→M') = h M→M' RedP
        hyp-aux {M} {P} {.M · P'} neM h RedP (acc snP) (appR P→P') = CR3-arrow neM h (CR2 RedP P→P') (snP P' P→P')       

    --CR4 : ∀ {α M} → Ne M → Nf M → Red α M
    --CR4 neM nfM = CR3 neM (λ r → ⊥-elim (nfM r))

  Red-ι : ∀ {Γ} → RedSubst ι Γ
  Red-ι = λ _ _ → CR3 (ConditionsNe.cond1 condNe) lemmaNfV

