{-# OPTIONS --copatterns #-}
module Guarded where

postulate TODO : ∀ {l} → {A : Set l} → A

open import Level renaming (suc to lsuc; zero to lzero) public
open import Data.Nat using (ℕ; _<′_; _≤′_; ≤′-refl; ≤′-step; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ℕ_) public
open import Data.Nat.Properties public

pred≤ℕ : ∀{n m} → suc n ≤ℕ suc m → n ≤ℕ m
pred≤ℕ (s≤s p) = p

pred≤′ : ∀{n m} → suc n ≤′ suc m → n ≤′ m
pred≤′ p = ≤⇒≤′(pred≤ℕ (≤′⇒≤ p))

≤′-trans : ∀ {m n o} -> m ≤′ n → n ≤′ o -> m ≤′ o
≤′-trans m≤n ≤′-refl = m≤n
≤′-trans m≤n (≤′-step m≤′n) = ≤′-step (≤′-trans m≤n m≤′n)

n≤sn : ∀ {n} → n ≤′ suc n
n≤sn = ≤′-step ≤′-refl
open import Function public
open import Data.Fin hiding (_≤_; lift) public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
record [] {i : Level} : Set i where
  constructor tt
open import Data.Product public

-- i for Ix ix, e for environment, t for term/value

postulate
  _i≤_ : (i0 : ℕ) (i1 : ℕ) → Set
  all≤ : ∀ {i0 i1} → i0 i≤ i1

Vec : ℕ → Set
Vec zero = []
Vec (suc n) = Vec n × ℕ

_≤_ : ∀ {n} → Vec n → Vec n → Set
_≤_ {zero} _ _ = []
_≤_ {suc n} (v0 , n0) (v1 , n1) = v0 ≤ v1 × n0 i≤ n1

refl≤ : ∀ {n} {i : Vec n} → i ≤ i
refl≤ {zero}  = tt
refl≤ {suc n} = refl≤ {n} , all≤

_!_ : ∀ {n} → Vec n → Fin n → ℕ
v ! zero = proj₂ v
v ! suc n = proj₁ v ! n

_[!]_ : ∀ {n} {i0 i1 : Vec n} → ([i] : i0 ≤ i1) → (k : Fin n) → (i0 ! k) i≤ (i1 ! k)
[i] [!] zero = proj₂ [i]
[i] [!] suc k = proj₁ [i] [!] k

update : ∀ {n} → Vec n → Fin n → ℕ → Vec n
update v zero n₁ = proj₁ v , n₁
update v (suc i) n₁ = update (proj₁ v) i n₁ , proj₂ v

[update] : ∀ {n} {i0 i1 : Vec n} ([i] : i0 ≤ i1) k {n0 n1} ([n] : n0 i≤ n1) → update i0 k n0 ≤ update i1 k n1
[update] [i] zero [n] = (proj₁ [i]) , [n]
[update] [i] (suc k) [n] = [update] (proj₁ [i]) k [n] , proj₂ [i]


record Cxt l : Set (lsuc l) where
  constructor con
  field
    ix : ℕ
  Ix = Vec ix
  field
    cxt⟦_⟧ : (i : Ix) -> Set l
    cxt⟦_⟧R : {i0 i1 : Ix} → ([i] : i0 ≤ i1) → (e0 : cxt⟦_⟧ i0) → (e1 : cxt⟦_⟧ i1) → Set l
  -- cxt⟦ Γ ⟧R ≤′-refl is supposed to be equality for cxt⟦ Γ ⟧ i

  -- If we model using setoids It should be enough to require cxt⟦ Γ ⟧R ≤′-refl
  -- to be an equivalence relation, since it's already "respected" by everything?

open Cxt public

record Type {i} j (Γ : Cxt i) : Set (lsuc j ⊔ i) where
  constructor con
  field
    type⟦_⟧  : ∀ i → (e : cxt⟦ Γ ⟧ i) → Set j
    type⟦_⟧R : ∀ {i0 i1} ([i] : i0 ≤ i1) →
           {e0 : cxt⟦ Γ ⟧ i0} {e1 : cxt⟦ Γ ⟧ i1} → ([e] : cxt⟦ Γ ⟧R [i] e0 e1) →
           (t0 : type⟦_⟧ i0 e0) → (t0 : type⟦_⟧ i1 e1) → Set j

open Type public

record Term  {i j : Level} (Γ : Cxt i) (A : Type j Γ) : Set (j ⊔ i) where
  constructor con
  field
    term⟦_⟧  : ∀ i → (e : cxt⟦ Γ ⟧ i) → type⟦ A ⟧ i e
    term⟦_⟧R : ∀ {i0 i1} ([i] : i0 ≤ i1) →
                 {e0 : cxt⟦ Γ ⟧ i0}{e1 : cxt⟦ Γ ⟧ i1} ([e] : cxt⟦ Γ ⟧R [i] e0 e1) →
                 type⟦ A ⟧R [i] [e] (term⟦_⟧ i0 e0) (term⟦_⟧ i1 e1)

open Term public

CV : ∀ {i} → Cxt i → Set
CV Γ = Fin (ix Γ)

-- record Free (k : CV) {i : Level} (Γ : Cxt i) : Set i where
--   constructor con
--   field
--     free : ∀ {i n} → cxt⟦ Γ ⟧ i → cxt⟦ Γ ⟧ (update i k n)
--     [free] : ∀ {i0 i1} {[i] : i0 ≤ i1}{n0 n1}([n] : n0 ≤′ n1) →
--                {e0 : cxt⟦ Γ ⟧ i0}{e1 : cxt⟦ Γ ⟧ i1} ([e] : cxt⟦ Γ ⟧R [i] e0 e1)
--                → cxt⟦ Γ ⟧R ([update] [i] k [n]) (free e0) (free e1)
-- open Free {{...}}

record Anti {i : Level} (Γ : Cxt i) (k : CV Γ) : Set i where
  constructor con
  field -- TODO make it more functorial
    anti : ∀ {i n} → (n< : n <′ i ! k) → cxt⟦ Γ ⟧ i → cxt⟦ Γ ⟧ (update i k n)
    [anti] : ∀ {i0 i1} {[i] : i0 ≤ i1}{n0 n0< n1 n1<}([n] : n0 i≤ n1) →
               {e0 : cxt⟦ Γ ⟧ i0}{e1 : cxt⟦ Γ ⟧ i1} ([e] : cxt⟦ Γ ⟧R [i] e0 e1)
               → cxt⟦ Γ ⟧R ([update] [i] k [n]) (anti n0< e0) (anti n1< e1)
open Anti {{...}}

Eq : ∀ {i j} {Γ : Cxt i} → (A : Type j Γ) → Term Γ A → Term Γ A → Set (j ⊔ i)
Eq {Γ = Γ} A t0 t1 = ∀ i e → ([e] : cxt⟦ Γ ⟧R {i} {i} refl≤ e e) → type⟦ A ⟧R {i} refl≤ [e] (term⟦ t0 ⟧ i e) (term⟦ t1 ⟧ i e)

reflEq : ∀ {i j} {Γ : Cxt i} → (A : Type j Γ) → (t : Term Γ A) → Eq A t t
reflEq A t = λ i e [e] → term⟦ t ⟧R _ [e]

-- symEq : ∀ {i j} {Γ : Cxt i} → (A : Type j Γ) → (s t : Term Γ A) → Eq A s t → Eq A t s
-- symEq A t = λ t₁ x i e [e] → TODO -- needs to be added as an axiom

-- transEq : ∀ {i j} {Γ : Cxt i} → (A : Type j Γ) → (t0 t1 t2 : Term Γ A) → Eq A t0 t1 → Eq A t1 t2 → Eq A t0 t2
-- transEq A t0 t1 t2 0≡1 1≡2 = λ i e [e] → TODO -- needs to be added as an axiom


-- * Contexts

ε[_] : ∀ {i} → ℕ → Cxt i
ε[ n ] = con n (λ i → []) (λ 0≤1 G0 G1 → [])

ε   : {i : Level} → Cxt i
ε = con zero (λ i → []) (λ 0≤1 G0 G1 → [])

_·_ : {i j : Level} (Γ : Cxt i) → Type j Γ → Cxt(i ⊔ j)
Γ · A = con (ix Γ) (λ i → Σ (cxt⟦ Γ ⟧ i) (type⟦ A ⟧ i))
            (λ [i] e0 e1 → Σ (cxt⟦ Γ ⟧R [i] (proj₁ e0) (proj₁ e1)) (λ [e] → type⟦ A ⟧R [i] [e] (proj₂ e0) (proj₂ e1)))

_·k : {i : Level} (Γ : Cxt i) → Cxt i
Γ ·k = con (suc (ix Γ)) (cxt⟦ Γ ⟧ ∘ proj₁) (cxt⟦ Γ ⟧R ∘ proj₁)


-- * Abbreviations

_⌜_⌝ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} →
       Type k (Γ · A) → Term Γ A → Type k Γ
type⟦ B ⌜ u ⌝ ⟧ = λ i e → type⟦ B ⟧ i (e , (term⟦ u ⟧ i e))
type⟦ B ⌜ u ⌝ ⟧R = λ [i] [e] t0 t1 → type⟦ B ⟧R [i] ([e] , term⟦ u ⟧R [i] [e]) t0 t1


-- * Variables and weakenings.

wk : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} → Type k Γ → Type k (Γ · A)
type⟦ wk B ⟧ = λ i e → type⟦ B ⟧ i (proj₁ e)
type⟦ wk B ⟧R = λ [i] [e] → type⟦ B ⟧R [i] (proj₁ [e])

wkT : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k Γ} → Term Γ B → Term (Γ · A) (wk B)
term⟦ wkT T ⟧ = λ i e → term⟦ T ⟧ i (proj₁ e)
term⟦ wkT T ⟧R = λ [i] [e] → term⟦ T ⟧R [i] (proj₁ [e])

wkk : ∀ {i j}{Γ : Cxt i} → Type j Γ → Type j (Γ ·k)
type⟦ wkk A ⟧ = λ i e → type⟦ A ⟧ (proj₁ i) e
type⟦ wkk A ⟧R = λ [i] [e] t0 t1 → type⟦ A ⟧R (proj₁ [i]) [e] t0 t1

wkkT : ∀ {i j}{Γ : Cxt i} {A : Type j Γ} → Term Γ A → Term (Γ ·k) (wkk A)
term⟦ wkkT t ⟧ = λ i e → term⟦ t ⟧ (proj₁ i) e
term⟦ wkkT t ⟧R = λ [i] [e] → term⟦ t ⟧R (proj₁ [i]) [e]

v0 : {i j : Level} {Γ : Cxt i} {A : Type j Γ} → Term (Γ · A) (wk A)
term⟦ v0 ⟧ = λ i e → proj₂ e
term⟦ v0 ⟧R = λ [i] [e] → proj₂ [e]

wkε : {i j : Level}{Γ : Cxt i} → Type {lzero} j ε[ ix Γ ] → Type j Γ
type⟦ wkε x ⟧ = λ i e → type⟦ x ⟧ i _
type⟦ wkε x ⟧R = λ [i] [e] t0 t1 → type⟦ x ⟧R [i] _ t0 t1

wkεT : {i j : Level}{Γ : Cxt i} {A : Type j ε[ ix Γ ]} → Term ε[ ix Γ ] A → Term Γ (wkε A)
term⟦ wkεT x ⟧ = λ i e → term⟦ x ⟧ i _
term⟦ wkεT x ⟧R = λ [i] [e] → term⟦ x ⟧R [i] _

wkkε : ∀ {i k j} {Γ : Cxt i} → (A : Type j (ε {k})) → Type j Γ
type⟦ wkkε A ⟧ = λ i e → type⟦ A ⟧ _ _
type⟦ wkkε A ⟧R = λ [i] [e] → type⟦ A ⟧R _ _


-- * Pi

Pi : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) → (B : Type k (Γ · A)) → Type (j ⊔ k) Γ
type⟦ Pi A B ⟧ i e = (x : type⟦ A ⟧ i e) → type⟦ B ⟧ i (e , x)
type⟦ Pi A B ⟧R [i] [e] f0 f1 = ∀ {x0 x1} ([x] : type⟦ A ⟧R [i] [e] x0 x1) → type⟦ B ⟧R [i] ([e] , [x]) (f0 x0) (f1 x1)

Lam   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          Term (Γ · A) B → Term Γ (Pi A B)
term⟦ Lam b ⟧ = λ i e x → term⟦ b ⟧ i (e , x)
term⟦ Lam b ⟧R = λ [i] [e] [x] → term⟦ b ⟧R [i] ([e] , [x])

App   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          Term Γ (Pi A B) → (u : Term Γ A) → Term Γ (B ⌜ u ⌝)
term⟦ App f u ⟧ = λ i e → term⟦ f ⟧ i e (term⟦ u ⟧ i e)
term⟦ App f u ⟧R = λ [i] [e] → term⟦ f ⟧R [i] [e] (term⟦ u ⟧R [i] [e])

-- sometimes it's more convinient to just unpack the lambda.
Πe : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} → {B : Type k (Γ · A)} → Term Γ (Pi A B) → Term (Γ · A) B
term⟦ Πe x ⟧ = λ i e → term⟦ x ⟧ i (proj₁ e) (proj₂ e)
term⟦ Πe x ⟧R = λ [i] [e] → term⟦ x ⟧R [i] (proj₁ [e]) (proj₂ [e])

-- Non-dependent functions

infixr 5 _⇒_
_⇒_ : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) → (B : Type k Γ) → Type (j ⊔ k) Γ
A ⇒ B = Pi A (wk B)

app   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k Γ} →
          Term Γ (A ⇒ B) → (u : Term Γ A) → Term Γ B
app {B = B} = App {B = wk B}

`id : ∀ {i j}{Γ : Cxt i}{A : Type j Γ} → Term Γ (A ⇒ A)
term⟦ `id ⟧ = λ i e x → x
term⟦ `id ⟧R = λ [i] [e] [x] → [x]

_`∘_ : ∀ {a b c i} {Γ : Cxt i}{A : Type a Γ} {B : Type b Γ} {C : Type c Γ} → Term Γ (B ⇒ C) → Term Γ (A ⇒ B) → Term Γ (A ⇒ C)
_`∘_ {A = A} {B} {C} f g = Lam {B = wk C} (app (wkT f) (app (wkT g) v0))


-- * Sigma

Sigma : {i j k : Level} {Γ : Cxt i} (A : Type j Γ) → Type k (Γ · A) → Type (j ⊔ k) Γ
type⟦ Sigma A B ⟧  = λ i γ → Σ (type⟦ A ⟧ i γ) \ u → type⟦ B ⟧ i (γ , u)
type⟦ Sigma A B ⟧R [i] [e] T0 T1 = Σ (type⟦ A ⟧R [i] [e] (proj₁ T0) (proj₁ T1)) (λ [a] → type⟦ B ⟧R [i] ([e] , [a]) (proj₂ T0) (proj₂ T1))

pair   : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          (u : Term Γ A) → Term Γ (B ⌜ u ⌝) → Term Γ (Sigma A B)
term⟦ pair u x ⟧ = λ i e → term⟦ u ⟧ i e , term⟦ x ⟧ i e
term⟦ pair u x ⟧R = λ [i] [e] → term⟦ u ⟧R [i] [e] , term⟦ x ⟧R [i] [e]

Pr₁ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          Term Γ (Sigma A B) → Term Γ A
term⟦ Pr₁ p ⟧ = λ i e → proj₁ (term⟦ p ⟧ i e)
term⟦ Pr₁ p ⟧R = λ [i] [e] → proj₁ (term⟦ p ⟧R [i] [e])

Pr₂ : {i j k : Level} {Γ : Cxt i} {A : Type j Γ} {B : Type k (Γ · A)} →
          (p : Term Γ (Sigma A B)) → Term Γ (B ⌜ Pr₁ p ⌝)
term⟦ Pr₂ p ⟧ = λ i e → proj₂ (term⟦ p ⟧ i e)
term⟦ Pr₂ p ⟧R = λ [i] [e] → proj₂ (term⟦ p ⟧R [i] [e])


-- * Universe

U     : {i : Level} {Γ : Cxt i} (j : Level) → Type (lsuc j) Γ
type⟦ U i ⟧        = λ ix γ → Set i
type⟦_⟧R (U j) [i] [e] T0 T1 = T0 → T1 → Set j -- TODO supposed to be type equality when i0 ≡ i1

El    : {i j : Level} {Γ : Cxt i} → (T : Term Γ (U j)) → Type j Γ
type⟦ El T ⟧  = term⟦ T ⟧
type⟦ El T ⟧R = term⟦ T ⟧R

∣_∣  : {i j : Level} {Γ : Cxt i} → Type j Γ → Term Γ (U j)
term⟦ ∣ T ∣ ⟧  = type⟦ T ⟧
term⟦ ∣ T ∣ ⟧R = type⟦ T ⟧R


-- * Clock Quantifiers

-- ∀
`∀    : {i j : Level} {Γ : Cxt i} → (A : Type j (Γ ·k)) → Type j Γ
type⟦ `∀ A ⟧  = λ i γ → ∀ n → type⟦ A ⟧ (i , n) γ
type⟦_⟧R (`∀ A) [i] [e] a0 a1 = ∀ {n0 n1} ([n] : n0 i≤ n1) → type⟦ A ⟧R ([i] , [n]) [e] (a0 n0) (a1 n1)

∀i : {i j : Level} {Γ : Cxt i}{A : Type j (Γ ·k)} → Term (Γ ·k) A → Term Γ (`∀ A)
term⟦ ∀i t ⟧ = λ i e n → term⟦ t ⟧ (i , n) e
term⟦ ∀i t ⟧R = λ [i] [e] [n] → term⟦ t ⟧R ([i] , [n]) [e]

∀e : {i j : Level} {Γ : Cxt i}{A : Type j (Γ ·k)} → (t : Term Γ (`∀ A)) → Term (Γ ·k) A
term⟦ ∀e t ⟧ = λ i e → term⟦ t ⟧ (proj₁ i) e (proj₂ i)
term⟦ ∀e t ⟧R = λ [i] [e] → term⟦ t ⟧R (proj₁ [i]) [e] (proj₂ [i])

_⟨_⟩ : ∀ {i j}{Γ : Cxt i}(A : Type j (Γ ·k)) → CV Γ → Type j Γ
type⟦ _⟨_⟩ A k ⟧ = λ i e → type⟦ A ⟧ (i , i ! k) e
type⟦ _⟨_⟩ A k ⟧R = λ [i] [e] → type⟦ A ⟧R ([i] , [i] [!] k) [e]

_[_] : ∀ {i j}{Γ : Cxt i}{A : Type j (Γ ·k)} → Term Γ (`∀ A) → (k : CV Γ) → Term Γ (A ⟨ k ⟩)
term⟦ T [ k ] ⟧ = λ i e → term⟦ T ⟧ i e (i ! k)
term⟦ T [ k ] ⟧R = λ [i] [e] → term⟦ T ⟧R [i] [e] ([i] [!] k)

_`$_   : {i j k : Level} {Γ : Cxt i} {A : Type j (Γ ·k)} {B : Type k (Γ ·k)} →
          Term Γ (`∀ (A ⇒ B)) → (u : Term Γ (`∀ A)) → Term Γ (`∀ B)
_`$_ {A = A} {B} x u = ∀i (app {A = A} {B = B} (∀e x) (∀e u))

-- ∃
`∃    : {i j : Level} {Γ : Cxt i} → (A : Type j (Γ ·k)) → Type j Γ
type⟦ `∃ A ⟧  = λ i γ → ∃ \ n → type⟦ A ⟧ (i , n) γ
type⟦ `∃ A ⟧R [i] [e] T0 T1 = let (n0 , a0) = T0; (n1 , a1) = T1 in
         ∃ \ ([n] : n0 i≤ n1) → type⟦ A ⟧R ([i] , [n]) [e] a0 a1 -- TODO quotient

`uncurryk : ∀ {j k i} {Γ : Cxt i} {A : Type j (Γ ·k)}{R : Type k Γ} → Term Γ (`∀ (A ⇒ wkk R)) → Term Γ (`∃ A ⇒ R)
term⟦ `uncurryk x ⟧ = λ i e a → term⟦ x ⟧ i e (proj₁ a) (proj₂ a)
term⟦ `uncurryk x ⟧R = λ [i] [e] [a] → term⟦ x ⟧R [i] [e] (proj₁ [a]) (proj₂ [a])


-- * Guards

₀▸   : {i j : Level} {Γ : Cxt i} → (k : CV Γ) → {{a : Anti Γ k}} → (A : Type j Γ) → Type j Γ
type⟦ ₀▸ k A ⟧     = λ i γ → Σ _ \ m → Σ _ \ (m< : m <′ i ! k) → type⟦ A ⟧ (update i k m) (anti m< γ)
type⟦ (₀▸ k T) ⟧R  [i] [e] t0' t1' = let (n0 , (n0< , t0)) = t0'; (n1 , (n1< , t1)) = t1' in
      Σ (n0 i≤ n1) λ [n] → type⟦ T ⟧R ([update] [i] k [n]) ([anti] [n] [e]) t0 t1 -- TODO quotient!

₁▸   : {i j : Level} {Γ : Cxt i} → (k : CV Γ) → {{a : Anti Γ k}} → (A : Type j Γ) → Type j Γ
type⟦ ₁▸ k A ⟧     = λ i γ → ∀   m → ∀   (m< : m <′ i ! k) → type⟦ A ⟧ (update i k m) (anti m< γ)
type⟦ ₁▸ k T ⟧R [i] [e] T0 T1 = ∀ {n0 n1 n0< n1<} → ([n] : n0 i≤ n1) → type⟦ T ⟧R ([update] [i] k [n]) ([anti] [n] [e]) (T0 n0 n0<) (T1 n1 n1<)

instance
  azero : ∀ {i} {Γ : Cxt i} → Anti (Γ ·k) zero
  azero = con (λ n< x → x) (λ [n] [e] → [e])

force : {i j : Level} {Γ : Cxt i} {A : Type j (Γ ·k)} → (t : Term Γ (`∀ (₁▸ zero A))) → Term Γ (`∀ A)
term⟦ force t ⟧ = λ i e n → term⟦ t ⟧ i e (suc n) n ≤′-refl
term⟦ force t ⟧R = λ [i] [e] [n] → term⟦ t ⟧R [i] [e] all≤ [n]

unforce : ∀ {i j}{Γ : Cxt i} {A : Type j (Γ ·k)} → (t : Term Γ (`∀ A)) → Term Γ (`∀ (₁▸ zero A))
term⟦ unforce t ⟧ = λ i e n m m< → term⟦ t ⟧ i e m
term⟦ unforce t ⟧R = λ [i] [e] [n] [n]₁ → term⟦ t ⟧R [i] [e] [n]₁


ex·k : ∀ {j i} {Γ : Cxt i} {X : Type j Γ}
       → Term (Γ ·k) (₀▸ zero (wkk X) ⇒ wkk X)
term⟦ ex·k ⟧ = λ i e x → proj₂ (proj₂ x)
term⟦ ex·k ⟧R = λ [i] [e] [x] → proj₂ [x]

⋆ : ∀ {j k i} {Γ : Cxt i} {A : Type j (Γ ·k)}{B : Type k (Γ ·k)}
    → Term (Γ ·k) (₁▸ zero (A ⇒ B) ⇒ (₀▸ zero A) ⇒ (₀▸ zero B))
term⟦ ⋆ ⟧ = λ i e f x → let (m , m< , x') = x in m , m< , f m m< x'
term⟦ ⋆ ⟧R = λ [i] [e] [f] [x] → let ([m] , [x]') = [x] in [m] , [f] [m] [x]'


-- * Guards on the universe

instance
  aempty : ∀ {i n}{k : Fin n} → Anti {i} ε[ n ] k
  aempty = λ {i} {n} {k} →
               con (λ {i₁} {n₁} n< _ → tt)
               (λ {i0} {i1} {[i]} {n0} {n0<} {n1} {n1<} [n] {e0} {e1} [e] → tt)

₁▹ : {i j : Level} {Γ : Cxt i} → (k : CV Γ) → Term Γ (Pi (wkε (₁▸ k (U j))) (U j))
term⟦ ₁▹ k ⟧  = λ i γ A → ∀ m → ∀ (m< : m <′ i ! k) → A m m<
term⟦ ₁▹ k ⟧R [i] [e] [A] a0 a1 = ∀ {n0 n1 n0< n1<} →
                                   ([n] : n0 i≤ n1) → [A] [n] (a0 n0 n0<) (a1 n1 n1<)

₀▹ : {i j : Level} {Γ : Cxt i} → (k : CV Γ) → Term Γ (Pi (wkε (₁▸ k (U j))) (U j))
term⟦ ₀▹ k ⟧  = λ i γ A → ∃ \ m → ∃ \ (m< : m <′ i ! k) → A m m<
term⟦ ₀▹ k ⟧R [i] [e] [A] a0' a1' = let (n0 , n0< , a0) = a0'; (n1 , n1< , a1) = a1' in
                                   ∃ \ ([n] : n0 i≤ n1) → [A] [n] a0 a1

-- instance
--   a₁▸ : {i j : Level} {Γ : Cxt i}{A : Type j Γ}{k : CV Γ} {{a : Anti Γ k}} → Anti (Γ · (₁▸ k A)) k
--   Anti.anti a₁▸ = λ n< x → (anti n< (proj₁ x)) , (λ m m< → {!proj₂ x m !})
--   Anti.[anti] a₁▸ = {!!}



-- Attempt at internalizing the typing of well-founded recursion,
-- it made Agda too sluggish.
--
-- Size : ∀ {i}{Γ : Cxt i} → Type _ Γ
-- Size = con (λ i e → ℕ) (λ [i] [e] t0 t1 → t0 ≤′ t1)

-- Le : ∀ {i}{Γ : Cxt i} → Type _ ((Γ · Size) · Size)
-- Le = con (λ { i ((e , m) , n) → n <′ m }) (λ [i] [e] t0 t1 → [])

-- inj : ∀ {l l1} → Type l (ε {l1} · Size) → ∀ {l2 Γ} → Type {l2} l (Γ · Size)
-- type⟦ inj P ⟧ = λ i e → type⟦ P ⟧ tt (tt , (proj₂ e))
-- type⟦ inj P ⟧R = λ [i] [e] t0 t1 → type⟦ P ⟧R tt (tt , proj₂ [e]) t0 t1

-- {-# NO_TERMINATION_CHECK #-}
-- mutual
--   wf' : ∀ {l l1} {P' : Type {l1} l (ε · Size)} (let P = inj P') → Term {l1} ε (Pi (Pi Size ((Pi Size (Le ⇒ P)) ⇒ P)) (Pi Size P))
--   term⟦ wf' {l1 = l1} {P' = P'} ⟧ = λ i e f n → f n (term⟦ wf'< {l1 = l1} {P' = P'} ⟧ tt tt f n )
--   term⟦ wf' {l1 = l1} {P' = P'} ⟧R = λ [i] [e] [f] [n] → [f] [n] (term⟦ wf'< {l1 = l1} {P' = P'} ⟧R tt tt [f] [n])

--   wf'< : ∀ {l l1} {P' : Type {l1} l (ε · Size)} (let P = inj P') → Term {l1} ε (Pi (Pi Size ((Pi Size (Le ⇒ P)) ⇒ P)) (Pi Size (Pi Size (Le ⇒ P))))
--   term⟦ wf'< {P' = P'} ⟧ i e f ._ x ≤′-refl = term⟦ wf' {P' = P'} ⟧ tt tt f x
--   term⟦ wf'< {P' = P'} ⟧ i e f ._ x (≤′-step le) = term⟦ wf'< {P' = P'} ⟧ i e f _ x le
--   term⟦ wf'< ⟧R = TODO where postulate TODO : {!!}


-- * Well-founded recursion in Agda.

mutual
  wf : ∀ {l} {P : ℕ → Set l} → (∀ n → (∀ {m} → m <′ n → P m) → P n) → ∀ (n : ℕ) → P n
  wf f n = f n (wf< f)
  wf< : ∀ {l} {P : ℕ → Set l} → (∀ n → (∀ {m} → m <′ n → P m) → P n) → ∀ {n}{m} → m <′ n → P m
  wf< f {._} {m} ≤′-refl = wf f m
  wf< f (≤′-step m<) = wf< f m<

cast-wf< : ∀ {l} (let P = \ _ → Set l) → (f : ∀ n → (∀ {m} → m <′ n → P m) → P n) → ∀ {n}{m} → (m< : m <′ n) → f m (wf< f)  → wf< f m<
cast-wf< f ≤′-refl x = x
cast-wf< f (≤′-step m<) x = cast-wf< f m< x


-- * Internal fix-point combinator

fix< : {i j : Level} {Γ : Cxt i} {A : Type j (Γ ·k)} → Term Γ (`∀ (₁▸ zero A ⇒ A) ⇒ `∀ (₁▸ zero A))
term⟦ fix< ⟧ i e f n m = wf< (λ n rec → f n (λ m m< → rec {m} m<))
term⟦_⟧R (fix< {A = A}) [i] [e] [f] [n] {n0< = ≤′-refl} {≤′-refl} [n]'
         = [f] [n]' (λ {_} {_} {0<} {1<} → term⟦ fix< {A = A} ⟧R [i] [e] [f] [n]' {_} {_} {0<} {1<})
term⟦_⟧R (fix< {A = A}) [i] [e] [f] [n] {n0< = ≤′-step n0<} {≤′-refl} [n]'
         = term⟦ fix< {A = A} ⟧R [i] [e] [f] all≤ {n0< = n0<} {≤′-refl} [n]'
term⟦_⟧R (fix< {A = A}) [i] [e] [f] [n] {n0< = ≤′-step n0<} {≤′-step n1<} [n]'
         = term⟦ fix< {A = A} ⟧R [i] [e] [f] all≤ {n0< = n0<} {n1<} [n]'
term⟦_⟧R (fix< {A = A}) [i] [e] [f] [n] {n0< = ≤′-refl} {≤′-step n1<} [n]'
         = term⟦ fix< {A = A} ⟧R [i] [e] [f] all≤ {n0< = ≤′-refl} {n1<} [n]'

fix : {i j : Level} {Γ : Cxt i} {A : Type j (Γ ·k)} → Term Γ (`∀ (₁▸ zero A ⇒ A) ⇒ `∀ A)
fix {A = A} = Lam (force {A = wk A} ((Πe (fix< {A = A}))))

-- Abbreviations for the Universe case

Ufix< : {i j : Level} {Γ : Cxt i} → Term Γ (`∀ (₁▸ zero (U j) ⇒ (U j))) → Term Γ (`∀ (₁▸ zero (U j)))
Ufix< {j = j} f = app (fix< {A = U j}) f

Ufix : {i j : Level} {Γ : Cxt i} → Term Γ (`∀ (₁▸ zero (U j) ⇒ (U j))) → Term Γ (`∀ (U j))
Ufix {j = j} f = app (fix {A = U j}) f


fix-thm0 : {i j : Level} {Γ : Cxt i} {A : Type j (Γ ·k)} → (f : Term Γ (`∀ (₁▸ zero A ⇒ A))) →
          let q = unforce {A = A} (app {A = `∀ (₁▸ zero A ⇒ A)} {B = `∀ A} (fix {A = A}) f)
              r =         (app {A = `∀ (₁▸ zero A ⇒ A)} {B = `∀ (₁▸ zero A)} (fix< {A = A}) f)
          in Eq (`∀ (₁▸ zero A)) q r
fix-thm0 {A = A} f i e [e] [n]' {n0< = ≤′-refl} {≤′-refl} [m] = reflEq (`∀ A) ((app {A = `∀ (₁▸ zero A ⇒ A)} {B = `∀ A} (fix {A = A}) f)) i e [e] [m]
fix-thm0 {A = A} f i e [e] [n]' {n0< = ≤′-refl} {≤′-step n1<} [m] = fix-thm0 {A = A} f i e [e] all≤ {n0< = ≤′-refl} {n1<}     [m]
fix-thm0 {A = A} f i e [e] [n]' {n0< = ≤′-step n0<} {≤′-refl} [m] = fix-thm0 {A = A} f i e [e] all≤     {n0< = n0<}     {≤′-refl} [m]
fix-thm0 {A = A} f i e [e] [n]' {n0< = ≤′-step n0<} {≤′-step n1<} [m] = fix-thm0 {A = A} f i e [e] all≤ {n0< = n0<}     {n1<}     [m]

fix-thm : {i j : Level} {Γ : Cxt i} {A : Type j (Γ ·k)} → (f : Term Γ (`∀ (₁▸ zero A ⇒ A))) →
          let q = unforce {A = A} (app {A = `∀ (₁▸ zero A ⇒ A)} {B = `∀ A} (fix {A = A}) f)
              r =         (app {A = `∀ (₁▸ zero A ⇒ A)} {B = `∀ A} (fix  {A = A}) f)
          in Eq (`∀ A) (_`$_ {A = ₁▸ zero A} {B = A} f q) r
fix-thm {A = A} f = λ i e [e] [n] → term⟦ f ⟧R refl≤ [e] [n]
  (\ {_} {_} {n0<} {n1<} [n]' → (fix-thm0 {A = A} f i e [e] [n] {n0< = n0<} {n1< = n1<} [n]'))


fix-cast₁ : ∀ {i j : Level} {Γ : Cxt i} → (f : Term Γ (`∀ (₁▸ zero (U j) ⇒ (U j))))
            → Term (Γ ·k) (₁▸ zero (El (∀e (Ufix f))) ⇒ El (app (₁▹ zero) (∀e (Ufix< f))))
term⟦ fix-cast₁ f ⟧ i e x m m< = cast-wf< (λ n rec → term⟦ f ⟧ (proj₁ i) e n (λ m₁ → rec)) m< (x m m<)
term⟦ fix-cast₁ f ⟧R = λ [i] [e] [x] [n] → TODO

fix-cast₀ : ∀ {i j : Level} {Γ : Cxt i} → (f : Term Γ (`∀ (₁▸ zero (U j) ⇒ (U j))))
            → Term (Γ ·k) (El (app (₀▹ zero) (∀e (Ufix< f))) ⇒ (₀▸ zero (El (∀e (Ufix f)))))
term⟦ fix-cast₀ f ⟧ i e x' = let (m , m< , x) = x' in  m , m< , TODO -- {! cast-wf< (λ n rec → term⟦ f ⟧ (proj₁ i) e n (λ m₁ → rec)) m< x !}
term⟦ fix-cast₀ f ⟧R = λ [i] [e] [x] → TODO





-- test1 : ∀ {i j}{Γ : Cxt i}{A : Type j Γ} → Term Γ (`∀ (wkk A) ⇒ A)
-- term⟦ test1 ⟧ = λ i e x → x 0
-- term⟦ test1 ⟧R = λ [i] [e] [x] → [x] ≤′-refl

-- ex : {i j : Level} {Γ : Cxt i} → (k : CV Γ) → {{a : Anti Γ k}} → {A : Type j Γ} → Term Γ (₀▸ k A ⇒ A)
-- term⟦ ex k ⟧ i e (n , n< , t) = {!t!}
-- term⟦ ex k ⟧R = {!!}

-- ∙dep : ∀ {i j l}{Γ : Cxt i}{k : CV Γ}{{_ : Anti Γ k}}{A : Type j Γ}{B : Type l (Γ · A)}
--      → Term Γ (₁▸ k (Pi A B) ⇒ Pi (₀▸ k A) {! B (ex v0) !})
-- term⟦ ∙dep ⟧ = λ i e f a → let (m , m< , a') = a in {!f m m< a'!}
-- term⟦ ∙dep ⟧R = {!!}

-- -- next : {i j : Level} {Γ : Cxt i} → (k : CV) → {{a : Anti k Γ}} → {A : Type j Γ} → Term Γ (A ⇒ ₁▸ k A)
-- -- term⟦ next k ⟧ i e t n n< = {!t!}
-- -- term⟦ next k ⟧R = {!!}

