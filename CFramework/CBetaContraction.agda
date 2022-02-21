open import Level
open import Data.Product
open import Data.Nat hiding (_*_)
open import Relation.Nullary
open import Relation.Binary.Core
import Relation.Binary.PreorderReasoning as PreR
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty

open import Chi
open import CFramework.CTerm
open import CFramework.CSubstitution
open import CFramework.CSubstitutionLemmas
open import CFramework.CAlpha
open import CFramework.CDefinitions
import CFramework.CReducibility

module CFramework.CBetaContraction where

infix 3 _▹β_
data _▹β_ : Λ → Λ → Set where
  beta : ∀ {x M N} → ƛ x M · N ▹β M [ N / x ]

lemma*◃β : Preserves* _▹β_
lemma*◃β {x} {ƛ y M · N} x*M[y/N] beta with lemmafreeσ→ {x} {M} x*M[y/N]
...  | z , z*M , x*z[y/N] with y ≟ z
lemma*◃β {x} {ƛ y M · N} x*M[y/N] beta | .y , y*M , x*N | yes refl = *·r x*N
lemma*◃β {x} {ƛ y M · N} x*M[y/N] beta | .x , x*M , *v | no y≢z = *·l (*ƛ x*M y≢z)

compat▹β∙ : Compat∙ _▹β_ 
compat▹β∙ {ƛ x M · N} {_} {σ} beta = (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N ∙ σ) , beta , aux
  where
    open PreR ≈-preorder∼
    y : V
    y = χ (σ , ƛ x M)
    aux : (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N ∙ σ) ∼α (M ∙ ι ≺+ (x , N)) ∙ σ
    aux = begin
      (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N ∙ σ) ∼⟨ corollary1SubstLemma (χ-lemma2 σ (ƛ x M)) ⟩
      M ∙ σ ≺+ (x , N ∙ σ)                    ≈⟨ corollary1Prop7 {M} {N} {σ} {x} ⟩
      (M ∙ ι ≺+ (x , N)) ∙ σ                  ∎

commut∼α▹β : Comm∼α _▹β_
commut∼α▹β .{ƛ x M · N} .{ƛ x′ M′ · N′} (∼· {_} {_} {N} .{N′} (∼ƛ {M} .{M′} {x} .{x′} {y} y#ƛxM y#ƛx′M′ M[y/x]∼M′[y/x′]) N∼N′) (beta {x′} {M′} {N′}) =
  M ∙ ι ≺+ (x , N) , beta , aux
    where
      open PreR ≈-preorder∼
      aux : M ∙ ι ≺+ (x , N) ∼α M′ ∙ ι ≺+ (x′ , N′)
      aux = begin
        M ∙ ι ≺+ (x , N)                       ≈⟨ lemma≺+ y#ƛxM ⟩
        (M ∙ ι ≺+ (x , v y)) ∙ ι ≺+ (y , N)    ∼⟨ lemma-subst M[y/x]∼M′[y/x′] (lemma≺+∼α⇂ {y} lemmaι∼α⇂ N∼N′) ⟩
        (M′ ∙ ι ≺+ (x′ , v y)) ∙ ι ≺+ (y , N′) ≈⟨ sym (lemma≺+ y#ƛx′M′) ⟩
        M′ ∙ ι ≺+ (x′ , N′)                    ∎

