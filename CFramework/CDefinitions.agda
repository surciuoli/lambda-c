module CFramework.CDefinitions (C : Set) where

  open import Data.Product
  open import Relation.Nullary

  open import CFramework.CTerm C
  open import CFramework.CSubstitution C
  open import CFramework.CSubstitutionLemmas C
  open import CFramework.CAlpha C

  AntiPreserves* : Rel → Set
  AntiPreserves* r = ∀ {x M N} → x * N → r M N → x * M

  Preserves# : Rel → Set
  Preserves# r = ∀ {x M N} → x # M → r M N → x # N

  antipres*⇒pres# : {_▹_ : Rel} → AntiPreserves* _▹_ → Preserves# _▹_
  antipres*⇒pres# antipres* = dual-*-# antipres*

  pres#⇒antipres* : {_▹_ : Rel} →  Preserves# _▹_ → AntiPreserves* _▹_
  pres#⇒antipres* pres# = dual-#-* pres#

  Compat∙ : Rel → Set
  Compat∙ r = ∀ {M N σ} → r M N → Σ[ P ∈ Λ ](r (M ∙ σ) P × P ∼α N ∙ σ)

  Comm∼α : Rel → Set
  Comm∼α R = ∀ {M N P} → M ∼α N → R N P → Σ[ Q ∈ Λ ](R M Q × Q ∼α P)
