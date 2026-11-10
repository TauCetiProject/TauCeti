/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The dimension under a semilinear equivalence

A semilinear equivalence over a ring isomorphism preserves `finrank`
(`LinearEquiv.finrank_eq_of_semilinear`); for example, a conjugate-linear equivalence of complex
vector spaces preserves the complex dimension. Mathlib's `LinearEquiv.finrank_eq` is the linear
case.
-/

public section

namespace LinearEquiv

/-- A semilinear equivalence over a ring isomorphism preserves `finrank`, as a conjugate-linear
equivalence of complex vector spaces preserves the complex dimension. Mathlib's
`LinearEquiv.finrank_eq` is the linear case. -/
theorem finrank_eq_of_semilinear {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (f : M ≃ₛₗ[σ] N) : Module.finrank R M = Module.finrank S N := by
  unfold Module.finrank
  rw [← Cardinal.toNat_lift, lift_rank_eq_of_equiv_equiv σ f.toAddEquiv
    (RingEquiv.ofRingHom σ σ' RingHomInvPair.comp_eq RingHomInvPair.comp_eq).bijective
    f.map_smulₛₗ, Cardinal.toNat_lift]

end LinearEquiv
