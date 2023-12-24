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
open import CFramework.CChi 
open import CFramework.CSubstitution C renaming (Σ to Subst) hiding (_∘_; R)
open import CFramework.CSubstitutionLemmas C
open import CFramework.Misc.ListProperties hiding (_-_)
open import CFramework.CAlpha C
open import CFramework.CType
open import CFramework.CContext Type _≟_
open import CFramework.CReduction C _▹_ as Reduction
open import CFramework.CDefinitions C
open import CFramework.CSN C _▹_ as SN

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

data Vec : Λ → Λ → Set where
  nil : ∀ {M} → Vec M M
  cons : ∀ {M N} → Vec M N → ∀ {P} → Vec M (N · P)

Ne : Λ → Set
Ne M = ∀ {N} → Vec M N → ∀ {P Q} → ¬ (N · P) ▹ Q

lemmaVec : ∀ {M N P} → Vec (M · N) P → Vec M P
lemmaVec nil = cons nil
lemmaVec (cons vec) = cons (lemmaVec vec)

lemmaNe : ∀ {M} → Ne M → ∀ {N} → Ne (M · N)
lemmaNe NeM vec = NeM (lemmaVec vec)

module RedProperties (cond▹ : ∀ {x N} → Vec (v x) N → ∀ {Q} → ¬ N ▹ Q) where

  lemmaNfV : ∀ {x N} → ¬(v x ⟿ N)
  lemmaNfV (redex r) = ⊥-elim (cond▹ nil r)

  lemmaNeV : ∀ {x} → Ne (v x)
  lemmaNeV vec = cond▹ (cons vec)

  mutual 
    CR1 : ∀ {α M} → Red α M → sn M
    CR2 : ∀ {α M N} → Red α M → M ⟿ N → Red α N
    CR3 : ∀ {α M} → Ne M → (∀ {N} → M ⟿ N → Red α N) → Red α M
    
    CR1 {τ} snM = snM
    CR1 {α ⇒ β} Redα⇒β = proj₁ (inversionSnApp {N = v 0} (CR1 (Redα⇒β (CR3 lemmaNeV (λ 0⟿N → ⊥-elim (lemmaNfV 0⟿N))))))

    CR2 {τ} {_} {N} (acc snM) (M→N) = snM N M→N
    CR2 {α ⇒ β} RedM M→N RedP = CR2 (RedM RedP) (appL M→N)
  
    CR3 {τ} _ h = acc (λ _ M→N → h M→N)
    CR3 {α ⇒ β} neM h RedP = CR3-arrow neM h RedP (CR1 RedP)
    
    CR3-arrow : ∀ {α β M P} → Ne M → (∀ {N} → M ⟿ N → Red (α ⇒ β) N) → Red α P → sn P → Red β (M · P)
    CR3-arrow {α} {β} {M} NeM h RedP snP = CR3 (lemmaNe NeM) (hyp-aux NeM h RedP snP)
      where
        hyp-aux : ∀ {M P Q} → Ne M → (∀ {N} → M ⟿ N → Red (α ⇒ β) N) → Red α P → sn P → M · P ⟿ Q → Red β Q
        hyp-aux {M} {P} NeM _ _ _ (redex redx) = ⊥-elim (NeM nil redx)
        hyp-aux _ h RedP _ (appL M→M') = h M→M' RedP
        hyp-aux {M} {P} {.M · P'} NeM h RedP (acc snP) (appR P→P') = CR3-arrow NeM h (CR2 RedP P→P') (snP P' P→P')       

  Red-ι : ∀ {Γ} → RedSubst ι Γ
  Red-ι = λ _ _ → CR3 lemmaNeV (λ x⟿N → ⊥-elim (lemmaNfV x⟿N))

