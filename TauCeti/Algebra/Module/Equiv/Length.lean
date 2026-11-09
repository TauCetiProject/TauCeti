/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length

/-!
# Length under semilinear equivalences

An equivalence of modules over isomorphic rings identifies their submodule lattices,
so preserves length. In particular the length of a ring as its own module is invariant
under ring isomorphism. This allows lengths computed in quotient presentations to be
transported to isomorphic algebras.
-/

public section

namespace LinearEquiv

/-- A semilinear equivalence over a ring isomorphism preserves module length. -/
theorem length_eq_of_semilinear {R S M N : Type*} [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] N) : Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso
      (Submodule.orderIsoMapComapOfBijective e.toLinearMap e.bijective)]

end LinearEquiv

/-- Isomorphic rings have the same length as regular modules. -/
theorem RingEquiv.length_self_eq {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  exact e.toSemilinearEquiv.length_eq_of_semilinear
