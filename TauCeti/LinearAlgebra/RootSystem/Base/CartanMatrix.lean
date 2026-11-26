/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Base.Basic

/-!
# Cartan-matrix invariance under base-preserving equivalences

A base-preserving equivalence of crystallographic root pairings preserves Cartan matrix entries
along `RootPairing.Equiv.supportEquiv` (`RootPairing.Equiv.cartanMatrix_supportEquiv`).
-/

public section

namespace RootPairing

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
  (e : P.Equiv Q) {b : P.Base} {b' : Q.Base}
  (hb : ∀ i, i ∈ b.support ↔ e.indexEquiv i ∈ b'.support)

/-- A base-preserving equivalence preserves Cartan matrix entries along `supportEquiv`. -/
@[simp] theorem Equiv.cartanMatrix_supportEquiv [CharZero R] [P.IsCrystallographic]
    [Q.IsCrystallographic] (i j : b.support) :
    b'.cartanMatrix (e.supportEquiv hb i) (e.supportEquiv hb j) = b.cartanMatrix i j := by
  refine FaithfulSMul.algebraMap_injective ℤ R ?_
  rw [b'.algebraMap_cartanMatrixIn_apply ℤ, b.algebraMap_cartanMatrixIn_apply ℤ,
    e.coe_supportEquiv_apply, e.coe_supportEquiv_apply]
  exact e.toHom.pairing

end RootPairing
