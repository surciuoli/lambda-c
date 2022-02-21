module SystemT where

open import Data.Nat as Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Product renaming (map to mapΣ)
open import Induction.WellFounded as WF
open import Data.Empty
open import Data.List renaming (map to mapL)
open import Data.List.Any as Any
open Any.Membership-≡ renaming (_∈_ to _∈′_) hiding (_⊆_)
open import Function
open import Relation.Binary.Core hiding (_⇒_)
import Relation.Binary.PreorderReasoning as PreR
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Nullary
open import Induction.Nat hiding (Rec)
open import Data.Nat.Properties
open import Algebra.Structures
open import Data.List.Any.Properties
open import Data.Sum

open import Chi hiding (+-comm)
open import CFramework.CTerm renaming (Λ to Term)
open import CFramework.CSubstitution renaming (Σ to Subst) hiding (_∘_)
open import CFramework.CSubstitutionLemmas
import Context
open import ListProperties hiding (_-_)
open import CFramework.CAlpha
open import CFramework.CType
import Relation
open import CFramework.CBetaContraction
open import CFramework.CDefinitions

infix 3 _⊢_∶_

open Context Type _≟_

Rec : Term
Rec = k "Rec"

O : Term
O = k "O"

S : Term
S = k "S"

nat : Type
nat = τ

data _⊢_∶_ (Γ : Cxt) : Term → Type → Set where
  ⊢zro : Γ ⊢ O ∶ nat
  ⊢suc : Γ ⊢ S ∶ nat ⇒ nat
  ⊢rec : ∀ {α} → Γ ⊢ Rec ∶ α ⇒ (nat ⇒ α ⇒ α) ⇒ nat ⇒ α
  ⊢var : ∀ {x} → (k : x ∈ Γ) → Γ ⊢ v x ∶ Γ ⟨ k ⟩
  ⊢abs : ∀ {x M α β} → Γ ‚ x ∶ α ⊢ M ∶ β → Γ ⊢ ƛ x M ∶ α ⇒ β
  ⊢app : ∀ {M N α β} → Γ ⊢ M ∶ α ⇒ β → Γ ⊢ N ∶ α → Γ ⊢ M · N ∶ β

infix 3 _▹T_
data _▹T_ : Term → Term → Set where
  beta : ∀ {M N} → M ▹β N → M ▹T N
  recO : ∀ {G H} → Rec · G · H · O ▹T G
  recS : ∀ {G H N} → Rec · G · H · (S · N) ▹T H · (S · N) · (Rec · G · H · N)

data NeT : Term → Set where
  var : ∀ {x} → NeT (v x)
  zro : NeT O
  suc : NeT S
  app : ∀ {M} → NeT M → ∀ {N} → NeT (M · N)
  beta : ∀ {x M N} → NeT (ƛ x M · N)
  neRec : ∀ {G H N} → NeT (Rec · G · H · N)
  
open import CFramework.CReduction _▹T_ as Reduction renaming (_⟿_ to _→β_)
open import CFramework.CReducibility _▹T_ NeT as Reducibility

red-aux : (M : Term) → List (Σ[ N ∈ Term ](M →β N))
red-aux (ƛ x M · N) = [ (M [ N / x ] , redex (beta beta)) ]
red-aux (k "Rec" · G · H · k "O") = [ (G , redex recO) ]
red-aux (k "Rec" · G · H · (k "S" · N)) = [ (H · (k "S" · N) · (k "Rec" · G · H · N) , redex recS) ]
red-aux _ = []
      
reductio : (M : Term) → List (Σ[ N ∈ Term ](M →β N))
reductio (k _) = []
reductio (v _) = []
reductio (ƛ x M) = mapL (mapΣ (ƛ x) abs) (reductio M)
reductio (M · N) = red-aux (M · N) ++ (mapL (mapΣ (flip _·_ N) appL) (reductio M) ++ mapL (mapΣ (_·_ M) appR) (reductio N))

ℓ : Term → ℕ
ℓ (k "S") = 1
ℓ (k _) = 0
ℓ (v _) = 0
ℓ (ƛ x M) = ℓ M
ℓ (M · N) = ℓ M + ℓ N

max : List ℕ → ℕ 
max = foldr _⊔_ 0

ν : ∀ {M} → sn M → ℕ 
ν {M} (acc snM) = suc (max (mapL (λ{(N , M→N) → ν (snM N M→N)}) (reductio M)))
    
open WF.Lexicographic _<′_ (λ _ → _<′_) renaming (_<_ to _<-lex_; well-founded to well-founded-lex)

conditions▹T : Conditions▹
conditions▹T = record
  { cond1 = λ { {x} {M} (beta ()) }
  }

cond3 : ∀ {M} → NeT M → ∀ {N P} → ¬((M · N) ▹T P)
cond3 var (beta ())
cond3 zro (beta ())
cond3 suc (beta ())
cond3 (app _) (beta ())
cond3 (app (app ())) recO
cond3 (app (app ())) recS 
cond3 beta (beta ()) 
cond3 neRec (beta ())

conditionsNeβ : ConditionsNe
conditionsNeβ = record
  { cond1 = var
  ; cond2 = app
  ; cond3 = cond3
  }

lemma*◃T : Preserves* _▹T_
lemma*◃T x*M (beta M▹βN) = lemma*◃β x*M M▹βN
lemma*◃T x*N recO = *·l (*·l (*·r x*N))
lemma*◃T (*·l (*·l x*M)) recS = *·l (*·r x*M)
lemma*◃T (*·l (*·r x*SN)) recS = *·r x*SN
lemma*◃T (*·r (*·l x*RecGH)) recS = *·l x*RecGH
lemma*◃T (*·r (*·r x*N)) recS = *·r (*·r x*N)

compat▹T∙ : Compat∙ _▹T_ 
compat▹T∙ (beta M▹βN) = mapΣ id (mapΣ beta id) (compat▹β∙ M▹βN)
compat▹T∙ {_} {_} {σ} (recO {G}) = G ∙ σ , recO , ∼ρ
compat▹T∙ {_} {_} {σ} (recS {G} {H} {N}) = (H · (S · N) · (Rec · G · H · N)) ∙ σ , recS , ∼ρ

commut∼α▹T : Comm∼α _▹T_
commut∼α▹T c (beta M▹βN) = mapΣ id (mapΣ beta id) (commut∼α▹β c M▹βN)
commut∼α▹T (∼· (∼· (∼· {_} {_} {G} ∼k G∼G′) _) ∼k) recO = G , recO , G∼G′
commut∼α▹T (∼· (∼· {_} {_} {H} (∼· {_} {_} {G} ∼k G∼G′) H∼H′) (∼· {_} {_} {N} ∼k N∼N′)) recS =
  H · (S · N) · (Rec · G · H · N) , recS , ∼· (∼· H∼H′ (∼· ∼k N∼N′)) (∼· (∼· (∼· ∼k G∼G′) H∼H′) N∼N′)

open Reduction.CompatSubst lemma*◃T compat▹T∙
open Reducibility.Properties lemma*◃T compat▹T∙ commut∼α▹T conditionsNeβ conditions▹T

lemmaSν : ∀ {M} → (p : sn M) → (q : sn (S · M)) → ν p ≡ ν q
lemmaSν {M} (acc hp) (acc hq) = cong suc (cong max aux4)
  where
    aux0 : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {g : B → C} {f : A → B} {l : List A} → mapL g (mapL f l) ≡ mapL (g ∘ f) l
    aux0 {l = []} = refl
    aux0 {l = x ∷ xs} = cong₂ _∷_ refl (aux0 {l = xs})
    aux1 : ∀ {M} → reductio (S · M) ≡ mapL (mapΣ (_·_ S) appR) (reductio M)
    aux1 = refl
    aux2 : {A B : Set}{l : List A}{f g : A → B} → (∀ x → f x ≡ g x) → mapL f l ≡ mapL g l
    aux2 {l = []} _ = refl
    aux2 {l = x ∷ xs} h = cong₂ _∷_ (h x) (aux2 {l = xs} h)
    aux3 : ∀ {N} {M→N : M →β N} → ν (hp N M→N) ≡ ν (hq (S · N) (appR M→N))
    aux3 {N} {M→N} = lemmaSν (hp N M→N) (hq (S · N) (appR M→N))
    open P.≡-Reasoning
    aux4 : mapL (λ{(N , M→N) → ν (hp N M→N)}) (reductio M) ≡ mapL (λ{(N , M→N) → ν (hq N M→N)}) (reductio (S · M))
    aux4 = begin
      mapL (λ {(N , M→N) → ν (hp N M→N)}) (reductio M)                            ≡⟨ aux2 (λ {(N , M→N) → aux3}) ⟩ 
      mapL (λ {(N , M→N) → ν (hq (S · N) (appR M→N))}) (reductio M)               ≡⟨⟩ 
      mapL ((λ {(N , M→N) → ν (hq N M→N)}) ∘ mapΣ (_·_ S) appR) (reductio M)      ≡⟨ sym aux0 ⟩ 
      mapL (λ {(N , M→N) → ν (hq N M→N)}) (mapL (mapΣ (_·_ S) appR) (reductio M)) ≡⟨ cong₂ mapL refl (sym aux1) ⟩ 
      mapL (λ {(N , M→N) → ν (hq N M→N)}) (reductio (S · M))                      ∎

lemmaStepν : ∀ {M N ihM} → (snM : sn M) → snM ≡ acc ihM → (M→N : M →β N) → ν (ihM N M→N) <′ ν snM
lemmaStepν {M} {N} {snM} (acc .snM) refl M→N = s≤′s p
  where
    ⊔-comm = IsCommutativeMonoid.comm (IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid ⊔-⊓-0-isCommutativeSemiringWithoutOne)
    lemma⊔ : ∀ m n p → m ≤ n → m ≤ n ⊔ p
    lemma⊔ .0 n p z≤n = z≤n
    lemma⊔ ._ ._ 0 (s≤s r) = s≤s r
    lemma⊔ (suc m) (suc n) (suc p) (s≤s r) = s≤s (lemma⊔ m n p r)
    lemmaMax : {m n : ℕ}{l : List ℕ} → m ∈′ l → n ≤ m → n ≤ max l --> The second parameter is not needed.
    lemmaMax {m} {n} {.m ∷ xs} (here refl) n≤m = lemma⊔ n m (max xs) n≤m
    lemmaMax {m} {n} {x ∷ xs} (there m∈xs) n≤m rewrite ⊔-comm x (max xs) = lemma⊔ n (max xs) x (lemmaMax m∈xs n≤m)
    lemma∈Map : {a : _}{b : _}{A : Set a}{B : Set b}{x : A}{l : List A}{f : A → B} → x ∈′ l → f x ∈′ (mapL f l) 
    lemma∈Map (here refl) = here refl
    lemma∈Map (there x∈xs) = there (lemma∈Map x∈xs)
    lemmaReductio : ∀ {M N} → (M→N : M →β N) → (N , M→N) ∈′ (reductio M)
    lemmaReductio (redex (beta beta)) = here refl
    lemmaReductio (redex recO) = here refl
    lemmaReductio (redex recS) = here refl
    lemmaReductio (abs r) = lemma∈Map (lemmaReductio r)
    lemmaReductio {M · P} {N · .P} (appL r) = ++ʳ (red-aux (M · P)) (++ˡ (lemma∈Map (lemmaReductio r)))
    lemmaReductio {P · M} {.P · N} (appR r) = ++ʳ (red-aux (P · M)) (++ʳ (mapL (mapΣ (flip _·_ M) appL) (reductio P)) (lemma∈Map (lemmaReductio r)))
    p : ν (snM N M→N) ≤′ max (mapL (λ{(P , M→P) → ν (snM P M→P)}) (reductio M))
    p = ≤⇒≤′ (lemmaMax (lemma∈Map {l = reductio M} {f = λ{(P , M→P) → ν (snM P M→P)}} (lemmaReductio M→N)) (≤′⇒≤ ≤′-refl))  --> The last parameter...

lemmaNfS : Nf S
lemmaNfS (redex (beta ()))

lemmaNfO : Nf O
lemmaNfO (redex (beta ()))

lemmaNfVar : ∀ {y} → Nf (v y)
lemmaNfVar (redex (beta ()))

lemma-rec : ∀ {α G H N} → sn G → sn H → (snN : sn N) → Acc _<-lex_ (ν snN , ℓ N) → Red α G → Red (nat ⇒ α ⇒ α) H → Red α (Rec · G · H · N)
lemma-rec {α} {G} {H} {N} (acc snG) (acc snH) snN accLex RedG RedH = CR3 neRec (hyp-aux snN accLex)
  where
    hyp-aux : ∀ {N P} → (snN : sn N) → Acc _<-lex_ (ν snN , ℓ N) → Rec · G · H · N →β P → Red α P
    hyp-aux _ _ (redex (beta ()))
    hyp-aux _ _ (redex recO) = RedG
    hyp-aux .{k "S" · N′} snSN′(acc ih) (redex (recS {N = N′})) =
      RedH (CR4 {nat ⇒ nat} suc lemmaNfS snN′) (lemma-rec (acc snG) (acc snH) snN′ (ih (ν snN′ , ℓ N′) aux) RedG RedH)
        where
          snN′ : sn N′
          snN′ = proj₂ (inversionSnApp snSN′)
          ℓN′<ℓSN′ : ℓ N′  <′ ℓ (S · N′)
          ℓN′<ℓSN′ = ≤′-refl
          aux : (ν snN′ , ℓ N′) <-lex (ν snSN′ , ℓ (S · N′))
          aux rewrite lemmaSν snN′ snSN′ = right ℓN′<ℓSN′
    hyp-aux snN accLex (appL (appL (appR {_} {G′} G→G′))) = lemma-rec (snG G′ G→G′) (acc snH) snN accLex (CR2 RedG G→G′) RedH
    hyp-aux snN accLex (appL (appR {_} {H′} H→H′)) = lemma-rec (acc snG) (snH H′ H→H′) snN accLex RedG (CR2 {nat ⇒ α ⇒ α} RedH H→H′)
    hyp-aux _ _ (appL (appL (appL (redex (beta ()))))) 
    hyp-aux _ _ (appL (appL (redex (beta ()))))
    hyp-aux _ _ (appL (redex (beta ())))
    hyp-aux {N} (acc snN) (acc ih) (appR {N = N′} N→N′) = lemma-rec (acc snG) (acc snH) snN′ (ih (ν snN′ , ℓ N′) (left (lemmaStepν (acc snN) refl N→N′))) RedG RedH
      where snN′ : sn N′ 
            snN′ = snN N′ N→N′

lemma-abs : ∀ {x M N α β} → sn M → sn N → Red α N → (∀ {P} → Red α P → Red β (M [ P / x ])) → Red β (ƛ x M · N)
lemma-abs snM snN RedN RedM[P/x] = CR3 beta (hyp-aux snM snN RedN RedM[P/x])
  where
    hyp-aux : ∀ {α β x M N P} → sn M → sn N → Red α N → (∀ {P} → Red α P → Red β (M [ P / x ])) → ƛ x M · N →β P → Red β P
    hyp-aux _ _ RedN RedM[P/x] (redex (beta beta)) = RedM[P/x] RedN 
    hyp-aux {α} {β} {P = ƛ x M′ · N} (acc snM) snN RedN RedM[P/x] (appL (abs M→M′)) =
      lemma-abs (snM M′ M→M′) snN RedN RedM′[P/x]
        where
          RedM′[P/x] : ∀ {P} → Red α P → Red β (M′ [ P / x ])
          RedM′[P/x] RedP =
            let _ , M[P/x]→Q , Q∼M′[P/x] = compat⟿∙ M→M′
            in closureRed∼α (CR2 (RedM[P/x] RedP) M[P/x]→Q) Q∼M′[P/x]
    hyp-aux {P = ƛ x M · N′} snM (acc snN) RedN RedM[P/x] (appR N→N′) = lemma-abs snM (snN N′ N→N′) (CR2 RedN N→N′) RedM[P/x]
    hyp-aux _ _ _ _ (appL (redex (beta ()))) 
        
subst-lemma : ∀ {α M σ Γ} → Γ ⊢ M ∶ α → RedSubst σ Γ → Red α (M ∙ σ)
subst-lemma ⊢zro _ = CR4 zro lemmaNfO
subst-lemma ⊢suc _ = CR4 {nat ⇒ nat} suc lemmaNfS
subst-lemma (⊢rec {α}) _ RedG RedH {N} RedN =
  lemma-rec (CR1 RedG) (CR1 {nat ⇒ α ⇒ α} RedH) RedN (well-founded-lex <-well-founded <-well-founded (ν RedN , ℓ N)) RedG RedH
subst-lemma (⊢var {x} x∈Γ) Redσ = Redσ x x∈Γ
subst-lemma {α ⇒ β} {ƛ x M} {σ} (⊢abs M:β) Redσ {N} RedN = lemma-abs (CR1 RedMσ,y/x) (CR1 RedN) RedN RedMσ,y/x[P/y]
  where
    y : V
    y = χ (σ , ƛ x M)
    RedMσ,y/x : Red β (M ∙ σ ≺+ (x , v y))
    RedMσ,y/x = subst-lemma M:β (Red-upd Redσ x (CR4 var lemmaNfVar))
    RedMσ,y/x[P/y] : ∀ {P} → Red α P → Red β ((M ∙ σ ≺+ (x , v y)) [ P / y ])
    RedMσ,y/x[P/y] RedP = closureRed∼α (subst-lemma M:β (Red-upd Redσ x RedP)) (∼σ (corollary1SubstLemma (χ-lemma2 σ (ƛ x M))))
subst-lemma (⊢app M:α→β N:α) Redσ = (subst-lemma M:α→β Redσ) (subst-lemma N:α Redσ)

strong-normalization : ∀ {Γ M α} → Γ ⊢ M ∶ α → sn M
strong-normalization M:α = closureSn∼α (CR1 (subst-lemma M:α Red-ι)) (∼σ lemma∙ι)
