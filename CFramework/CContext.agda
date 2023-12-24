open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_ ; refl ; cong ; _≗_ ; sym ; trans ; inspect ;  setoid) renaming ([_] to [_]i)
open PropEq.≡-Reasoning

module CFramework.CContext {K : Set}(D : Set)(_≟_ : Decidable (_≡_ {A = K})) where

open import CFramework.Misc.ListProperties

open import Data.Empty
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.List hiding (any;all)
open import Function
open import Data.List.Any as Any hiding (map;tail)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈l_)
open import Data.List.Membership.Propositional.Properties 
open import Data.Product renaming (map to map×)
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Maybe hiding (map)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 

infixl 3 _‚_ 
infix 2 _⊆_
infix 2 _∈_

Cxt : Set
Cxt = List (K × D)

∅ : Cxt
∅ = []

dom : Cxt → List K
dom = map proj₁

_‚_ : Cxt → K × D → Cxt -- \glq
_‚_ = λ x y → y ∷ x

private 
  infixr 4 _∶_
  _∶_ : ∀ {a b} → {A : Set a} → {B : A → Set b} → (x : A) → (y : B x) → Σ[ x ∈ A ](B x)
  x ∶ y = x , y

data _∈_ : K → Cxt → Set where
  here  : ∀ {x α Γ} → x ∈ Γ ‚ x ∶ α
  there : ∀ {x y α Γ} → x ≢ y → x ∈ Γ → x ∈ Γ ‚ y ∶ α 

_⟨_⟩ : {k : K} → (Γ : Cxt) → k ∈ Γ → D
[]             ⟨ ()        ⟩ 
((k , d) ∷ xs) ⟨ here      ⟩ = d
((k , d) ∷ xs) ⟨ there _ p ⟩ = xs ⟨ p ⟩

lemma∈→∈[]  : {xs : Cxt}{x : K} → (p : x ∈ xs) → Σ D (λ d → ((x , d) ∈l xs) × (xs ⟨ p ⟩ ≡ d))
lemma∈→∈[] {(y , d) ∷ xs}  (here)  =  d   , here refl      , refl
lemma∈→∈[]                 (there x≢y x∈xs)  
  with lemma∈→∈[] x∈xs
... | d' , x,d'∈xs , xs⟨x∈xs⟩≡d         =  d'  , there x,d'∈xs  , xs⟨x∈xs⟩≡d

lemma∈[]→∈  : {xs : Cxt}{x : K}{d : D} → (p : (x , d) ∈l xs) → x ∈ xs
lemma∈[]→∈          (here refl)  =  here 
lemma∈[]→∈ {x = x}  (there {y , d} p∈xs) with x ≟ y
lemma∈[]→∈ {x = .y}  (there {y , d} p∈xs) | yes refl = here 
... | no   x≢y                   = there x≢y (lemma∈[]→∈ p∈xs)

lemma∈!⟨⟩ : {xs : Cxt}{x : K} → (p p' : x ∈ xs) → xs ⟨ p ⟩ ≡ xs ⟨ p' ⟩
lemma∈!⟨⟩ (here  )        (here)        = refl
lemma∈!⟨⟩ (here )        (there x≢y _)      = ⊥-elim (x≢y refl)
lemma∈!⟨⟩ (there x≢x x∈x∷xs)  (here )        = ⊥-elim (x≢x refl)
lemma∈!⟨⟩ (there x≢y x∈y∷xs)  (there _ x∈y∷xs')  = lemma∈!⟨⟩ x∈y∷xs x∈y∷xs'

_⊆_ : Cxt → Cxt → Set
Γ ⊆ Δ = {x : K}(x∈Γ : x ∈ Γ) → Σ (x ∈ Δ) (λ x∈Δ → Γ ⟨ x∈Γ ⟩ ≡ Δ ⟨ x∈Δ ⟩ )

ρ⊆ : Reflexive _⊆_
ρ⊆ x∈Γ = x∈Γ , refl

τ⊆ : Transitive _⊆_
τ⊆ Γ⊆Δ Δ⊆Ε x∈Γ with Γ⊆Δ x∈Γ
... | x∈Δ , Γ⟨x∈Γ⟩≡Δ⟨x∈Δ⟩ with Δ⊆Ε x∈Δ
... | x∈Ε , Δ⟨x∈Δ⟩≡Ε⟨x∈Ε⟩ = x∈Ε , trans Γ⟨x∈Γ⟩≡Δ⟨x∈Δ⟩ Δ⟨x∈Δ⟩≡Ε⟨x∈Ε⟩

≈-preorder : Preorder _ _ _
≈-preorder =  
    record { 
      Carrier = Cxt;
      _≈_ = _≡_;
      _∼_ = _⊆_;
      isPreorder =  record {
        isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid Cxt) ;
        reflexive = λ { {Γ} {.Γ} refl → ρ⊆};
        trans = τ⊆ } }

import Relation.Binary.PreorderReasoning as PreR
open PreR ≈-preorder

lemma⊆xy : {x y : K}{d e : D}{Γ : Cxt} → x ≢ y → Γ ‚ x , d ‚ y , e ⊆ Γ ‚ y , e ‚ x , d
lemma⊆xy x≢y (here) 
  = there (⊥-elim ∘ x≢y ∘ sym ∘ trans (sym refl)) (here) , refl
lemma⊆xy x≢y (there z≢y (here)) 
  = here , refl
lemma⊆xy x≢y (there z≢y (there z≢x z∈Γ)) 
  = there z≢x (there z≢y z∈Γ) , refl

lemma⊆xx : {x : K}{d e : D}{Γ : Cxt} → Γ ‚ x , d ‚ x , e ⊆ Γ ‚ x , e
lemma⊆xx (here) 
  = here , refl
lemma⊆xx (there z≢x (here)) 
  = ⊥-elim (z≢x refl)
lemma⊆xx (there z≢x (there _ z∈Γ)) 
  = there z≢x z∈Γ , refl

lemma⊆x : {x : K}{d e : D}{Γ : Cxt} → Γ ‚ x , e ⊆ Γ ‚ x , d ‚ x , e 
lemma⊆x (here)       = here , refl
lemma⊆x (there y≢x y∈Γ)  = there y≢x (there y≢x y∈Γ) , refl

lemma⊆∷ : {x : K}{d : D}{Γ Δ : Cxt} → Γ ⊆ Δ → Γ ‚ x , d ⊆ Δ ‚ x , d
lemma⊆∷ Γ⊆Δ (here)       = here , refl
lemma⊆∷ Γ⊆Δ (there z≢x z∈Γ)  = there z≢x (proj₁ (Γ⊆Δ z∈Γ)) , proj₂ (Γ⊆Δ z∈Γ)

