{-# OPTIONS --copatterns #-}
module Guarded.Mu where

open import Guarded

-- * Types used to define finitary containers.
Nat : Type lzero (ε {lzero})
Nat = con (λ i e → ℕ) (λ [i] [e] t0 t1 → t0 ≡ t1)

`Fin : ∀ {i} {Γ : Cxt i} → (n : Term Γ (wkkε Nat)) → Type lzero Γ
type⟦ `Fin n ⟧ = λ i e → Fin (term⟦ n ⟧ i e)
type⟦ `Fin n ⟧R = λ [i] [e] t0 t1 → TODO


-- * Finitary Containers and their Extension (Normal Functor, shapely types)

Container : ∀ i → Type {lzero} (lsuc i) ε
Container i = Sigma (U i) (El v0 ⇒ wk Nat)

Ext : ∀ {j} {i} {Γ : Cxt i} → Term Γ (wkkε (Container j)) → Term Γ (U j ⇒ U j)
Ext {j} C = (Lam {B = U j} ∣ Sigma (El (Pr₁ (wkT C))) (`Fin (app (Pr₂ (wkT (wkT C))) v0) ⇒ El (wkT v0)) ∣)

`Ext : ∀ {j} {i} {Γ : Cxt i} → Term Γ (wkkε (Container j)) → Type j Γ → Type j Γ
`Ext {j} C X = El (app (Ext C) ∣ X ∣)

mapC : ∀ {j} {i} {Γ : Cxt i}{A B : Type j Γ} → (C : Term Γ (wkkε (Container j))) →
         Term Γ (A ⇒ B) → Term Γ (El (app (Ext C) ∣ A ∣) ⇒ El (app (Ext C) ∣ B ∣))
-- mapC {A = A} {B = B} C f = Lam {B = wk (El (app (Ext C) ∣ B ∣))} (pair (Pr₁ v0) (Lam {B = wk (wk B)} (app (wkT (wkT f)) (app (Pr₂ (wkT v0)) v0))))
-- ^ takes too long to typecheck
term⟦ mapC C x ⟧ = λ i e p → let s , t = p in s , (λ f → term⟦ x ⟧ i e (t f))
term⟦ mapC C x ⟧R = λ [i] [e] [p] → let [s] , [t] = [p] in [s] , (λ [f] → term⟦ x ⟧R [i] [e] ([t] [f]))



-- * Least fixed point of containers

MuF : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) → Term Γ (`∀ (₁▸ zero (U j) ⇒ (U j)))
MuF {j} C = ∀i (_`∘_ {A = ₁▸ zero (U j)} {C = U j} (wkkT (Ext C)) (₀▹ zero))

-- -- for contrast
-- NuF : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) → Term Γ (`∀ (₁▸ zero (U j) ⇒ (U j)))
-- NuF {j} C = ∀i (_`∘_ {A = ₁▸ zero (U j)} {C = U j} (wkkT (Ext C)) (₁▹ zero))

preMu : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) → Type j (Γ ·k)
preMu {j} C = El (∀e (app (fix {A = U j}) (MuF C)))

-- ∃ k'. (fix (Λ k. ⟦ C ⟧ ∘ ₀▹ k))[ k' ]
Mu : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) → Type j Γ
Mu {j} C = `∃ (preMu C)


postulate
  lim : ∀ {n} → (Fin n → ℕ) → ℕ
--  lim f = ?
  lim-< : ∀ {n}{f : Fin n → ℕ} p → f p ≤′ lim {n} f

inn : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) → Term Γ (`Ext C (Mu C) ⇒ Mu C)
term⟦ inn C ⟧ = λ i e x → let (s , t) = x in
                  suc (lim (λ p → proj₁ (t p))) , (s , (λ p → proj₁ (t p) , (s≤′s (lim-< p) , cast-wf< _ (s≤′s (lim-< p)) (proj₂ (t p)))))
term⟦ inn C ⟧R = λ [i] [e] [x] → let [s] , [t] = [x] in all≤ , ([s] , (λ [p] → all≤ , TODO))

-- -- * Iteration



-- pre-iter : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) {X : Type j Γ} → (φ : Term Γ (`Ext C X ⇒ X)) → Term Γ (`∀ (preMu C ⇒ wkk X))
-- pre-iter C {X} φ = app (fix {A = preMu C ⇒ wkk X}) (∀i (Lam {B = wk (preMu C ⇒ wkk X)} (Lam {B = wk (wk (wkk X))}
--            (app (wkT (wkT (wkkT φ))) (app (mapC {B = wk (wk (wkk X))} (wkT (wkT (wkkT C))) (Lam {B = wk (wk (wk (wkk X)))}
--              (app (wkT (wkT (wkT (ex·k {X = X})))) (app (app (wkT (wkT (wkT (⋆ {A = preMu C} {B = wkk X})))) (wkT (wkT v0)))
--                (app (wkT (wkT (wkT (fix-cast₀ (MuF C))))) v0))))) v0)))))

-- iter : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) {X : Type j Γ} → (φ : Term Γ (`Ext C X ⇒ X)) → Term Γ (Mu C ⇒ X)
-- iter C {X} φ = `uncurryk {A = preMu C} {R = X} (pre-iter C {X} φ)

-- \ t -> ∀ p -> X (proj₂ t p)
All : ∀ {j} {i} {Γ : Cxt i} {A : Type j Γ} → (C : Term Γ (wkkε (Container j))) (X : Term Γ (A ⇒ U j)) → Type j (Γ · `Ext C A)
All C X = Pi (`Fin (app (Pr₂ (wkT C)) (Pr₁ v0))) (El (app (wkT (wkT X)) (app (Pr₂ (wkT v0)) v0)))


`Fiber : ∀ {j i k} {Γ : Cxt i} {A : Type j (Γ ·k)} → (P : Term Γ (`∃ A ⇒ U k)) → Term (Γ ·k) (A ⇒ U k)
`Fiber P = ∀e (`curryk {R = U _} P)

postulate
  substT : ∀ {k}{j} {i} {Γ : Cxt i} {A : Type k Γ} → {X : Term Γ (A ⇒ U j)} → ∀ {x y : Term Γ A} → Term Γ (El (app X x)) → Term Γ (El (app X y))
--substT = {!!}

Typeee : (i : Level) -> (j : Level) -> Set _
Typeee i j = {Γ : Cxt i} (C : Term Γ (wkkε (Container j))) {X : Term Γ (Mu C ⇒ U j)} →
        Term Γ ((Pi (`Ext C (Mu C)) (All C X ⇒ El (app (wkT X) (app (wkT (inn C)) v0))))) →
        (let A = Pi (preMu C) (El (app (wkT (`Fiber X)) v0))) → Term (((Γ ·k) · (₁▸ zero A)) · wk (preMu C)) (El (app (wkT (wkT (`Fiber X))) v0))

fixee : {i j : Level} → Typeee i j
term⟦ fixee {Γ = Γ} C {X} φ ⟧ = λ i e → let (γ , rec) , (s , t) = e; ι , k = i in
  (let r = term⟦ φ ⟧ ι γ (s , (λ x → let m , m< , a = term⟦ fix-cast₀ (MuF C) ⟧ (ι , k) γ (t x) in m , a))
         (λ x → let m , m< , a = term⟦ fix-cast₀ (MuF C) ⟧ (ι , k) γ (t x); in rec m m< a ) in {!r!})
term⟦ fixee {Γ = Γ} C {X} φ ⟧R = {!!}

-- preind : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) {X : Term Γ (Mu C ⇒ U j)} →
--       Term Γ ((Pi (`Ext C (Mu C)) (All C X ⇒ El (app (wkT X) (app (wkT (inn C)) v0))))) → Term Γ (`∀ (Pi (preMu C) (El (app (wkT (`Fiber X)) v0))))
-- preind C {X} φ = app (fix {A = Ty}) (∀i (Lam {B = wk Ty} (Lam {B = Ty1} (fixee C {X} φ))))
--        where Ty = Pi (preMu C) (El (app (wkT (`Fiber X)) v0))
--              Ty1 = (El (app (wkT (wkT (`Fiber X))) v0))
--(fixee C {X} φ) -- (con (λ i e n x x₁ → term⟦ fixee C {X} φ ⟧ (i , n) (e , x) x₁) {!!})
-- (∀i (Lam {B = wk Ty} ((fixee C φ))))

-- (app (App (wkT (wkT (wkkT φ))) ?) ?)

-- -- (φ : (t : ⟦ C ⟧ (Mu C)) -> All C X t -> X (inn C t)) -> (i : Mu C) -> X i
-- ind : ∀ {j} {i} {Γ : Cxt i} → (C : Term Γ (wkkε (Container j))) {X : Term Γ (Mu C ⇒ U j)} →
--       (φ : Term Γ (Pi (`Ext C (Mu C)) (All C X ⇒ El (app (wkT X) (app (wkT (inn C)) v0))))) → Term Γ (Pi (Mu C) (El (app (wkT X) v0)))
-- ind C {X} φ = `∃e {R = X} (Πe {B =  (El (app (wkT (`Fiber X)) v0)) } (∀e (preind C {X = X} φ)))



