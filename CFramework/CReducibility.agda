open import CFramework.CTerm

open import Relation.Binary.Core hiding (_⇒_)
open import Relation.Unary using (Pred)

module CFramework.CReducibility {ℓ : _} (_▹_ : Rel Λ ℓ) (Ne : Pred Λ ℓ) where

open import Data.Nat as Nat hiding (_*_)
open import Data.Product renaming (map to mapΣ)
open import Induction.WellFounded as WF
open import Data.Empty
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Nullary
open import Agda.Primitive

open import Chi hiding (+-comm)
open import CFramework.CSubstitution renaming (Σ to Subst) hiding (_∘_; R)
open import CFramework.CSubstitutionLemmas 
open import ListProperties hiding (_-_)
open import CFramework.CAlpha
open import CFramework.CType
open import Context Type _≟_
open import CFramework.CReduction _▹_ as Reduction
open import CFramework.CDefinitions

dual→β : Λ → Λ → Set ℓ
dual→β = λ M N → N ⟿ M
  
sn : Λ → Set ℓ
sn M = Acc {lzero} {ℓ} {Λ} dual→β M

Nf : Λ → Set ℓ
Nf M = ∀ {N} → ¬(M ⟿ N)

Red : Type → Λ → Set ℓ
Red τ M = sn M 
Red (α ⇒ β) M = ∀ {N} → Red α N → Red β (M · N)

RedSubst : Subst → Cxt → Set ℓ
RedSubst σ Γ  = ∀ x → (k : x ∈ Γ) → Red (Γ ⟨ k ⟩) (σ x)

inversionSnApp : ∀ {M N} → sn (M · N) → sn M × sn N
inversionSnApp {M} {N} (acc snMN) = acc (λ M′ M→M′ → proj₁ (inversionSnApp (snMN (M′ · N) (appL M→M′)))) , acc (λ N′ N→N′ → proj₂ (inversionSnApp (snMN (M · N′) (appR N→N′))))

record ConditionsNe : Set ℓ where
  field
    cond1 : ∀ {x} → Ne (v x)
    cond2 : ∀ {M} → Ne M → ∀ {N} → Ne (M · N)
    cond3 : ∀ {M} → Ne M → ∀ {N P} → ¬((M · N) ▹ P)

record Conditions▹ : Set ℓ where
  field
    cond1 : ∀ {x M} → ¬(v x ▹ M)

module Properties (pres : Preserves* _▹_) (compat : Compat∙ _▹_) (comm : Comm∼α _▹_) (condNe : ConditionsNe) (cond▹ : Conditions▹) where
  open Reduction.CommutesAlpha pres compat comm

  closureSn∼α : ∀ {M N} → sn M → M ∼α N → sn N
  closureSn∼α {M} {N} (acc snM) M∼N = acc aux
    where
      aux : ∀ P → N ⟿ P → sn P
      aux P N→P =
        let Q , M→Q , Q∼P = commut∼α⟿ M∼N N→P
        in closureSn∼α (snM Q M→Q) Q∼P

  closureRed∼α : ∀ {α M N} → Red α M → M ∼α N → Red α N
  closureRed∼α {τ} = closureSn∼α
  closureRed∼α {_ ⇒ _} RedM M∼N RedP = closureRed∼α (RedM RedP) (∼· M∼N ∼ρ)

  lemmaNfV : ∀ {x} → Nf (v x)
  lemmaNfV (redex r) = Conditions▹.cond1 cond▹ r

  mutual 
    CR1 : ∀ {α M} → Red α M → sn M
    CR1 {τ} snM = snM
    CR1 {α ⇒ β} Redα⇒β = proj₁ (inversionSnApp {N = v 0} (CR1 (Redα⇒β (CR4 (ConditionsNe.cond1 condNe) lemmaNfV))))

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

    CR4 : ∀ {α M} → Ne M → Nf M → Red α M
    CR4 neM nfM = CR3 neM (λ r → ⊥-elim (nfM r))

  Red-ι : ∀ {Γ} → RedSubst ι Γ
  Red-ι = λ _ _ → CR4 (ConditionsNe.cond1 condNe) lemmaNfV

  Red-upd : ∀ {α Γ σ N} → RedSubst σ Γ → (x : V) → Red α N → RedSubst (σ ≺+ (x , N)) (Γ ‚ x ∶ α)
  Red-upd Redσ x RedN y y∈Γ,x:α with x ≟ y
  Red-upd Redσ x RedN y (there _ y∈Γ) | no _ = Redσ y y∈Γ
  Red-upd Redσ x RedN .x (here refl) | no x≢y = ⊥-elim (x≢y refl)
  Red-upd Redσ x RedN .x (there x≢y _) | yes refl = ⊥-elim (x≢y refl)
  Red-upd Redσ x RedN .x (here refl) | yes refl = RedN

