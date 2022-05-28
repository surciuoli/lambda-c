open import Level
open import Data.Product
open import Data.Nat hiding (_*_)
open import Relation.Nullary
open import Relation.Binary.Core
import Relation.Binary.PreorderReasoning as PreR
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty

module CFramework.CBetaContraction (C : Set) where

open import CFramework.CChi
open import CFramework.CTerm C
open import CFramework.CSubstitution C
open import CFramework.CSubstitutionLemmas C
open import CFramework.CAlpha C
open import CFramework.CDefinitions C

infix 3 _▹β_
data _▹β_ : Λ → Λ → Set where beta : ∀ {x M N} → ƛ x M · N ▹β M [ N / x ]

preser▹β* : AntiPreserves* _▹β_
preser▹β* {x} .{ƛ y M · N} x*M[y/N] (beta {y} {M} {N}) with lemmafreeσ→ {x} {M} x*M[y/N]
...  | z , z*M , x*z[y/N] with y ≟ z
preser▹β* {x} .{ƛ y M · N} x*M[y/N] (beta {y} {M} {N}) | .y , y*M , x*N | yes refl = *·r x*N
preser▹β* {x} .{ƛ y M · N} x*M[y/N] (beta {y} {M} {N}) | .x , x*M , *v | no y≢z = *·l (*ƛ x*M y≢z)

preser▹β# : Preserves# _▹β_
preser▹β# = dual-*-# preser▹β*

compat▹β∙ : Compat∙ _▹β_ 
compat▹β∙ .{ƛ x M · N} {_} {σ} (beta {x} {M} {N}) = (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N ∙ σ) , beta , aux
  where
    open PreR ≈-preorder∼
    y : V
    y = χ (σ , ƛ x M)
    aux : (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N ∙ σ) ∼α (M ∙ ι ≺+ (x , N)) ∙ σ
    aux = begin
      (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N ∙ σ) ∼⟨ corollary1SubstLemma (χ-lemma2 σ (ƛ x M)) ⟩
      M ∙ σ ≺+ (x , N ∙ σ)                    ≈⟨ corollary1Prop7 {M} {N} {σ} {x} ⟩
      (M ∙ ι ≺+ (x , N)) ∙ σ                  ∎

commut▹βα : Comm∼α _▹β_
commut▹βα .{ƛ x M · N} .{ƛ x′ M′ · N′} (∼· {_} {_} {N} .{N′} (∼ƛ {M} .{M′} {x} .{x′} {y} y#ƛxM y#ƛx′M′ M[y/x]∼M′[y/x′]) N∼N′) (beta {x′} {M′} {N′}) =
  M ∙ ι ≺+ (x , N) , beta , aux
    where
      open PreR ≈-preorder∼
      aux : M ∙ ι ≺+ (x , N) ∼α M′ ∙ ι ≺+ (x′ , N′)
      aux = begin
        M ∙ ι ≺+ (x , N)                       ≈⟨ lemma≺+ y#ƛxM ⟩
        (M ∙ ι ≺+ (x , v y)) ∙ ι ≺+ (y , N)    ∼⟨ lemma-subst M[y/x]∼M′[y/x′] (lemma≺+∼α⇂ {y} lemmaι∼α⇂ N∼N′) ⟩
        (M′ ∙ ι ≺+ (x′ , v y)) ∙ ι ≺+ (y , N′) ≈⟨ sym (lemma≺+ y#ƛx′M′) ⟩
        M′ ∙ ι ≺+ (x′ , N′)                    ∎

