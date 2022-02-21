open import Level hiding (zero)
module Relation {l : Level} (A : Set l) where  

  open import Relation.Nullary
  import Relation.Binary as RB
  import Relation.Unary as RU
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) hiding (trans)

  Rel : Set (suc l)
  Rel = RB.Rel A l 

  Pred : Set (suc l)
  Pred = RU.Pred A l

  infix 2 _preserved-by_
  _preserved-by_ : Pred → Rel → Set l
  P preserved-by R = ∀ {M N : A} → P M → R M N → P N

  dual : Rel → Rel
  dual R m n = R n m

  infix 5 _∪_   
  _∪_  : (R S : Rel) → Rel 
  _∪_ R S a b = R a b ⊎ S a b

  _⊆_ : Rel → Rel → Set l
  R ⊆ S = RB._⇒_ R S

  refl-⊆ : {R : Rel} → R ⊆ R
  refl-⊆ aRb = aRb

  trans-⊆ : {R S T : Rel} → R ⊆ S → S ⊆ T → R ⊆ T
  trans-⊆ R⊆S S⊆T aRb = S⊆T (R⊆S aRb)

  data star (⟿ : Rel) : Rel where
    refl : ∀ {a} → star ⟿ a a
    just : ∀ {a b} → ⟿ a b → star ⟿ a b
    trans : ∀ {a b c } → star ⟿ a b → star ⟿ b c → star ⟿ a c

  mon-star : {R S : Rel} → R ⊆ S → star R ⊆ star S
  mon-star R⊆S refl = refl
  mon-star R⊆S (just aRb) = just (R⊆S aRb)
  mon-star R⊆S (trans aR⋆b bR⋆c) 
    = trans (mon-star R⊆S aR⋆b) (mon-star R⊆S bR⋆c)
  
  idem-star : {R : Rel} → star (star R) ⊆ star R
  idem-star refl = refl
  idem-star (just aRb) = aRb
  idem-star (trans aR⋆b bR⋆c) = trans (idem-star aR⋆b) (idem-star bR⋆c)

  trans-⊆-star : {R S : Rel} → R ⊆ star S → star R ⊆ star S
  trans-⊆-star {R} {S} R⊆S⋆ 
    = trans-⊆  {star R} {star (star S)} {star S} 
               (mon-star R⊆S⋆) 
               idem-star

  data steps (⟿ : Rel) : Rel where
    zero  : ∀ {a}                               → steps ⟿ a a
    one   : ∀ {a b}    → ⟿ a b                 → steps ⟿ a b
    more  : ∀ {a b c}  → ⟿ a b → steps ⟿ b c  → steps ⟿ a c

  _++_ :  {⟿ : Rel} {a b c : A} 
          → steps ⟿ a b → steps ⟿ b c → steps ⟿ a c
  zero ++ s' = s'
  one a⟿b ++ b⟿*c = more a⟿b b⟿*c
  more a⟿b b⟿*c ++ c⟿*d = more a⟿b (b⟿*c ++ c⟿*d)
  
  ⋆-to-ω : ∀ {a b ⟿} → star ⟿ a b → steps ⟿ a b
  ⋆-to-ω refl = zero
  ⋆-to-ω (just a⟿b) = one a⟿b
  ⋆-to-ω (trans a⟿*b b⟿*c) = ⋆-to-ω a⟿*b ++ ⋆-to-ω b⟿*c

  ω-to-⋆ : ∀ {a b ⟿} → steps ⟿ a b → star ⟿ a b
  ω-to-⋆ zero = refl
  ω-to-⋆ (one a⟿b) = just a⟿b
  ω-to-⋆ (more a⟿b b⟿*c) = trans (just a⟿b) (ω-to-⋆ b⟿*c)
