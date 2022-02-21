module CFramework.CDefinitions where

open import Relation.Binary.Core

open import CFramework.CTerm
open import CFramework.CSubstitution
open import CFramework.CSubstitutionLemmas
open import CFramework.CAlpha

Preserves* : ∀ {ℓ} → Rel Λ ℓ → Set ℓ
Preserves* r = ∀ {x M N} → x * N → r M N → x * M

Compat∙ : ∀ {ℓ} → Rel Λ ℓ → Set ℓ
Compat∙ r = ∀ {M N σ} → r M N → Σ[ P ∈ Λ ](r (M ∙ σ) P × P ∼α N ∙ σ)

Comm∼α : ∀ {ℓ} → Rel Λ ℓ → Set ℓ
Comm∼α R = ∀ {M N P} → M ∼α N → R N P → Σ[ Q ∈ Λ ](R M Q × Q ∼α P)
