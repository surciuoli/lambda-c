module CFramework.CTerm (C : Set) where

open import CFramework.Misc.NaturalProp
open import CFramework.Misc.ListProperties
open import CFramework.CChi

open import Data.String using (String)
open import Data.Nat as Nat hiding (_*_; _⊔_)
open import Data.Nat.Properties
open import Data.Bool hiding (_≟_;_∨_)
open import Data.Empty
open import Function
open import Function.Inverse hiding (sym;_∘_;map;id)
open Inverse
import Function.Equality as FE
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Product renaming (Σ to Σₓ;map to mapₓ)
open import Relation.Nullary 
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary hiding (Rel)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 
open import Data.List hiding (any) renaming (length to length') 
open import Algebra.Structures
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)
open import Agda.Primitive
import Relation.Binary as RB
import Relation.Unary as RU
  
infixr 4 _∶_
_∶_ : ∀ {a b} → {A : Set a} → {B : A → Set b} → (x : A) → (y : B x) → Σ[ x ∈ A ](B x)
x ∶ y = x , y

infixl 6 _·_ 
infix 3 _#_ 
infix 1 _*_ 

data Λ : Set where
  k : C → Λ 
  v : V → Λ
  ƛ : V → Λ → Λ
  _·_ : Λ → Λ → Λ

length : Λ → ℕ
length (k _)   = 1
length (v _)   = 1
length (M · N) = length M + length N
length (ƛ x M) = suc (length M)

length>0 : {M : Λ} → length M > zero
length>0 {k x}   = start
                    suc zero
                    ≤⟨ ≤-refl ⟩
                    suc zero
                   ◽
length>0 {v x}   = start
                    suc zero
                    ≤⟨ ≤-refl ⟩
                    suc zero
                   ◽
length>0 {M · N} = start
                      suc zero
                      ≤⟨ length>0 {M} ⟩
                      length M
                      ≤⟨ m≤m+n (length M) (length N) ⟩
                      length M + length N
                      ≤⟨ ≤-refl ⟩
                      length (M · N)
                   ◽
length>0 {ƛ x M} = start
                      suc zero 
                      ≤⟨ s≤s z≤n ⟩
                      suc (suc zero)
                      ≤⟨ s≤s (length>0 {M}) ⟩
                      suc (length M)
                      ≤⟨ ≤-refl ⟩
                      length (ƛ x M)
                   ◽


data _#_ : V → Λ → Set where
  #k : ∀ {x c} → x # k c
  #v : ∀ {x y} → y ≢ x → x # v y
  #· : ∀ {x M N} → x # M → x # N → x # M · N
  #ƛ≡ : ∀ {x M} → x # ƛ x M
  #ƛ : ∀ {x y M} → x # M → x # ƛ y M
  
_∼#_ : (M M' : Λ) → Set
_∼#_ M M' = (∀ x → x # M → x # M') × (∀ x → x # M' → x # M)

data _*_ : V → Λ → Set where
  *v : ∀ {x} → x * v x
  *·l : ∀ {x M N} → x * M → x * M · N
  *·r : ∀ {x M N} → x * N → x * M · N
  *ƛ : ∀ {x y M} → x * M → y ≢ x → x * ƛ y M

_#?_ : Decidable _#_
x #? (k c) = yes #k
x #? (v y) with y ≟ x
... | yes y≡x = no (λ {(#v y≢x) → y≢x y≡x})
... | no  y≢x = yes (#v y≢x)
x #? (M · N) with x #? M | x #? N 
... | yes x#M | yes  x#N = yes (#· x#M x#N)
... | yes x#M | no  ¬x#N = no (λ {(#· _ x#N) → ¬x#N x#N})
... | no ¬x#M | yes  x#N = no (λ {(#· x#M _)   → ¬x#M x#M})
... | no ¬x#M | no  ¬x#N = no (λ {(#· x#M _)   → ¬x#M x#M})
x #? (ƛ y M) with y | x ≟ y 
... | .x | yes refl = yes #ƛ≡
... | _  | no  x≢y with x #? M
...                | yes  x#M = yes (#ƛ x#M) 
x #? (ƛ y M) | w  | no  x≢w | no  ¬x#M = no (aux x≢w ¬x#M)
  where aux : {x w : V} → x ≢ w → ¬ (x # M) →  x # ƛ w M → ⊥
        aux x≢w ¬x#ƛwM #ƛ≡         =  ⊥-elim (x≢w refl)
        aux x≢w ¬x#ƛwM (#ƛ x#ƛwM)  =  ⊥-elim (¬x#ƛwM x#ƛwM)

lemma¬#→free : {x : V}{M : Λ} → ¬ (x # M) → x * M
lemma¬#→free {_} {k _} ¬x#c = ⊥-elim (¬x#c #k)
lemma¬#→free {x} {v y} ¬x#M with y ≟ x
... | no  y≢x   = ⊥-elim (¬x#M (#v y≢x))
lemma¬#→free {x} {v .x} ¬x#M 
    | yes refl  = *v
lemma¬#→free {x} {M · N} ¬x#MN with x #? M | x #? N 
... | yes x#M | yes x#N = ⊥-elim (¬x#MN (#· x#M x#N))
... | yes x#M | no ¬x#N = *·r (lemma¬#→free ¬x#N)
... | no ¬x#M | yes x#N = *·l (lemma¬#→free ¬x#M)
... | no ¬x#M | no ¬x#N = *·r (lemma¬#→free ¬x#N)
lemma¬#→free {x} {ƛ y M} ¬x#λxM with y ≟ x
... | no  y≢x with x #? M
... | yes x#M = ⊥-elim (¬x#λxM (#ƛ x#M))
... | no ¬x#M = *ƛ (lemma¬#→free ¬x#M) y≢x
lemma¬#→free {x} {ƛ .x M} ¬x#λxM 
    | yes refl = ⊥-elim (¬x#λxM #ƛ≡)

lemma-free→¬# : {x : V}{M : Λ} → x * M →  ¬ (x # M)
lemma-free→¬# {x} {v .x} *v            (#v x≢x) = ⊥-elim (x≢x refl)
lemma-free→¬# {x} {M · N} (*·l xfreeM) (#· x#M x#N) = ⊥-elim ((lemma-free→¬# xfreeM) x#M)
lemma-free→¬# {x} {M · N} (*·r xfreeN) (#· x#M x#N) = ⊥-elim ((lemma-free→¬# xfreeN) x#N)
lemma-free→¬# {x} {ƛ .x M} (*ƛ xfreeM x≢x) #ƛ≡ = ⊥-elim (x≢x refl)
lemma-free→¬# {x} {ƛ y M} (*ƛ xfreeM y≢x) (#ƛ x#M) = ⊥-elim ((lemma-free→¬# xfreeM) x#M)

lemma#→¬free : {x : V}{M : Λ} → x # M → ¬ (x * M)
lemma#→¬free x#M x*M = ⊥-elim ((lemma-free→¬# x*M) x#M)

lemma¬free→# : {x : V}{M : Λ} → ¬(x * M) → x # M
lemma¬free→# {x} {M} ¬x*M with x #? M
... | yes x#M = x#M
... | no ¬x#M = ⊥-elim (¬x*M (lemma¬#→free ¬x#M))

_∼*_ : (M M' : Λ) → Set
M ∼* M' = (∀ x → x * M → x * M') × (∀ x → x * M' → x * M)

∼*ρ : Reflexive _∼*_
∼*ρ {M} = (λ _ → id) ∶ (λ _ → id) 

Rel : Set (lsuc lzero)
Rel = RB.Rel Λ lzero 

Pred : Set (lsuc lzero)
Pred = RU.Pred Λ lzero

infix 2 _preserved-by_
_preserved-by_ : Pred → Rel → Set 
P preserved-by R = ∀ {M N} → P M → R M N → P N

dual : ∀ {a} → {A : Set a} {ℓ : _} → RB.Rel A ℓ → RB.Rel A ℓ -- Rel → Rel
dual R m n = R n m

dual-#-* : {R : Rel}{y : V} → (_#_ y) preserved-by R → (_*_ y) preserved-by (dual R)
dual-#-* {R} {y} #-pres-R {m} {m'} y*m m'Rm with y #? m'
... | yes y#m' = ⊥-elim (lemma-free→¬# y*m (#-pres-R {m'} {m} y#m' m'Rm))
... | no ¬y#m' = lemma¬#→free ¬y#m'

dual-*-# : {R : Rel}{y : V} → (_*_ y) preserved-by (dual R) → (_#_ y) preserved-by R
dual-*-# {R} {y} *-pres-R {m} {m'} y#m m'Rm with y #? m'
... | yes y#m' = y#m'
... | no ¬y#m' = ⊥-elim (lemma-free→¬# (*-pres-R (lemma¬#→free ¬y#m') m'Rm) y#m) 
