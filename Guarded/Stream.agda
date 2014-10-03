module Guarded.Stream where
open import Guarded

Nat : Type lzero (ε {lzero})
Nat = con (λ i e → ℕ) (λ [i] [e] t0 t1 → t0 ≡ t1)

mutual
  StreamF : ∀ {i} → Term {i} {lsuc lzero} ε (`∀ (₁▸ zero {{azero}} (U lzero) ⇒ U lzero))
  StreamF = (∀i (Lam ∣ Sigma (wkkε Nat) (wk (El (App (wkT (₁▹ zero)) v0))) ∣))
  Stream : ∀ {i} → Term {i} {lsuc lzero} ε (`∀ (U lzero))
  Stream {i} = app {B = `∀ (U lzero)} (fix {A = (U lzero)}) StreamF
  ▸Stream : ∀ {i} → Term {i} {lsuc lzero} (ε ·k) (U lzero)
  ▸Stream = app (₁▹ zero)
              (∀e
               (app {B = `∀ (₁▸ zero {{azero}} (U lzero))} (fix< {A = U lzero}) StreamF))

Str : Type {lzero} lzero (ε ·k)
Str = El (wkkT Stream [ zero ])

#N_ : ∀ {i} {Γ : Cxt i} → ℕ → Term Γ (wkkε Nat)
#N_ n = con (\ _ _ → n) (\ _ _ → refl)

ones : Term ε (`∀ Str)
ones = App {B = wk (`∀ Str)} (fix {A = Str}) (∀i (Lam (pair {A = wkkε Nat} {B = wk (wk (El ▸Stream))} (#N 1) (Πe (fix-cast₁ StreamF)))))
