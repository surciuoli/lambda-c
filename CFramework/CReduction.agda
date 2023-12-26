open import Level
open import Data.Product
open import Data.Nat hiding (_*_)
open import Relation.Nullary
--open import Relation.Binary.Core
import Relation.Binary.PreorderReasoning as PreR
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty

import CFramework.CTerm as CTerm

module CFramework.CReduction (C : Set) (_▹_ : CTerm.Rel C) where

  open CTerm C
  open import CFramework.CSubstitution C
  open import CFramework.CSubstitutionLemmas C
  open import CFramework.CAlpha C
  open import CFramework.CDefinitions C
  open import CFramework.CChi

  infix 3 _⟿_
  data _⟿_ : Rel where
    abs : ∀ {x M N} → M ⟿ N → ƛ x M ⟿ ƛ x N
    appL : ∀ {M N P} → M ⟿ N → M · P ⟿ N · P
    appR : ∀ {M N P} → M ⟿ N → P · M ⟿ P · N
    redex : ∀ {M N} → M ▹ N → M ⟿ N -- redex --> δ-redex (or delta)

  module PreservesFreshness (pres# : Preserves# _▹_) where

    pres* : AntiPreserves* _▹_
    pres* = dual-#-* pres#

    lemma*⟿⁻¹ : AntiPreserves* _⟿_
    lemma*⟿⁻¹ (*·l x*N) (appL M⟿N) = *·l (lemma*⟿⁻¹ x*N M⟿N)
    lemma*⟿⁻¹ (*·r x*N') (appL M⟿N) = *·r x*N'
    lemma*⟿⁻¹ (*·l x*N) (appR M⟿N) = *·l x*N
    lemma*⟿⁻¹ (*·r x*N') (appR M⟿N) = *·r (lemma*⟿⁻¹ x*N' M⟿N)
    lemma*⟿⁻¹ (*ƛ x*N y≢x) (abs M⟿N) = *ƛ (lemma*⟿⁻¹ x*N M⟿N) y≢x
    lemma*⟿⁻¹ x*N (redex rMN) = pres* x*N rMN

    lemma#⇂⟿ : ∀ {x M N σ} → x #⇂ (σ , M) → M ⟿ N → x #⇂ (σ , N)
    lemma#⇂⟿ {x} h M→N y y*N = h y (lemma*⟿⁻¹ y*N M→N)

  module CompatSubst (pres : Preserves# _▹_) (compat : Compat∙ _▹_) where
    open PreservesFreshness pres

    compat⟿∙ : Compat∙ _⟿_ 
    compat⟿∙ {ƛ x M} {ƛ .x N} {σ} (abs M→N) with compat⟿∙ M→N
    ... | P , M→P , P∼N = ƛ y P , abs M→P , ∼τ (lemma∼λ P∼N) aux
      where
        y : V
        y = χ (σ , ƛ x M)
        aux : ƛ y (N ∙ σ ≺+ (x , v y)) ∼α ƛ x N ∙ σ
        aux = ∼σ (corollary4-2 {x} {y} {N} (lemma#⇂⟿ (χ-lemma2 σ (ƛ x M)) (abs M→N)))
    compat⟿∙ {M · N} {_} {σ} (appL M→N) with compat⟿∙ M→N
    ... | P , M→P , P∼N = P · (N ∙ σ) , appL M→P , ∼· P∼N ∼ρ
    compat⟿∙ {M · N} {_} {σ} (appR M→N) with compat⟿∙ M→N
    ... | P , M→P , P∼N = (M ∙ σ) · P , appR M→P , ∼· ∼ρ P∼N 
    compat⟿∙ (redex rMN) = map (λ x → x) (map redex (λ x → x)) (compat rMN)

  module CommutesAlpha (pres : Preserves# _▹_) (compat : Compat∙ _▹_) (comm : Comm∼α _▹_) where
    open PreservesFreshness pres
    open CompatSubst pres compat

    lemma#⟿ : ∀ {x M N} → x # M → M ⟿ N → x # N
    lemma#⟿ {x} {M} {N} y#M M→N with x #? N
    ... | yes y#N = y#N
    ... | no ¬y#N = ⊥-elim (lemma-free→¬# (lemma*⟿⁻¹ (lemma¬#→free ¬y#N) M→N) y#M) 

    commut⟿α : Comm∼α _⟿_
    commut⟿α (∼· {M} {M′} {N} {N′} M~M′ N~N′) (appL M′→M″) with commut⟿α M~M′ M′→M″
    ... | P , M→P , P∼M″ = P · N , appL M→P , ∼· P∼M″ N~N′
    commut⟿α {M · N} {M′ · N′} {.M′ · N″} (∼· M~M′ N~N′) (appR N′→N″) with commut⟿α N~N′ N′→N″
    ... | P , N→P , P∼N″ = M · P , appR N→P , ∼· M~M′ P∼N″
    commut⟿α {ƛ x M} {ƛ y N} {ƛ .y P} (∼ƛ {y = z} z#ƛxM z#ƛyN M[z/x]~N[z/y]) (abs N→P) = ƛ x R′ , abs (proj₁ (proj₂ r)) , ∼τ ƛxR∼ƛyP[y/x] (∼σ (corollary4-2' x#ƛyP))
      where
        q : Σ[ Q ∈ Λ ](N [ v x / y ] ⟿ Q × Q ∼α P [ v x / y ])
        q = compat⟿∙ N→P
        Q : Λ
        Q = proj₁ q
        ƛxM∼ƛyN : ƛ x M ∼α ƛ y N
        ƛxM∼ƛyN = ∼ƛ z#ƛxM z#ƛyN M[z/x]~N[z/y]
        x#ƛyN : x # ƛ y N
        x#ƛyN = lemmaM∼N# ƛxM∼ƛyN x #ƛ≡
        open PreR ≈-preorder∼
        M∼N[x/y] : M ∼α N [ v x / y ]
        M∼N[x/y] = begin 
          M                         ∼⟨ lemma∙ι ⟩
          M ∙ ι                     ≈⟨ sym (lemma≺+ι z#ƛxM) ⟩ 
          M [ v z / x ] [ v x / z ] ≈⟨ lemmaM∼M'→Mσ≡M'σ M[z/x]~N[z/y] ⟩ 
          N [ v z / y ] [ v x / z ] ≈⟨ sym (lemma≺+ z#ƛyN) ⟩ 
          N [ v x / y ]             ∎
        r : Σ[ R ∈ Λ ](M ⟿ R × R ∼α Q)
        r = commut⟿α M∼N[x/y] (proj₁ (proj₂ q))
        R′ : Λ
        R′ = proj₁ r
        ƛxR∼ƛyP[y/x] : ƛ x R′ ∼α ƛ x (P [ v x / y ])
        ƛxR∼ƛyP[y/x] = lemma∼λ (∼τ (proj₂ (proj₂ r)) (proj₂ (proj₂ q)))
        x#ƛyP : x # ƛ y P
        x#ƛyP = lemma#⟿ x#ƛyN (abs N→P)
    commut⟿α M∼N (redex NRP) = map (λ x → x) (map redex (λ x → x)) (comm M∼N NRP)
