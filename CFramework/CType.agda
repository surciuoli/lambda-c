module CFramework.CType where

infixr 4 _⇒_
data Type : Set where
  τ : Type
  _⇒_ : Type → Type → Type
