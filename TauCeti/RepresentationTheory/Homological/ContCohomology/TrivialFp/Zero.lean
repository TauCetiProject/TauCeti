/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp

/-!
# Zeroth continuous cohomology with trivial `ZMod p` coefficients

The canonical identification `cohomFpZeroLinearEquiv` sends zeroth continuous cohomology to
the underlying coefficient value in `ZMod p`. In particular, the cohomology module is finite
over `ZMod p`; when `p` is prime, it is a finite-dimensional vector space over `𝔽_p`.

This identification specializes Mathlib's `ContinuousCohomology.zeroIso`, composed with
`LinearEquiv.ofTop` for the trivial action and `trivialFpEquiv` for the coefficient value.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Zeroth continuous cohomology with trivial coefficients is canonically `ZMod p`. -/
noncomputable def cohomFpZeroLinearEquiv : cohomFp p G 0 ≃ₗ[ZMod p] ZMod p :=
  (_root_.ContinuousCohomology.zeroIso (trivialFp p G)).toContinuousLinearEquiv.toLinearEquiv
    |>.trans ((LinearEquiv.ofTop (trivialFp p G).ρ.invariants (Submodule.eq_top_iff'.2 fun x g ↦
      trivialFp_ρ_apply_apply p G g x)).trans (trivialFpEquiv p G))

/-- The canonical identification reads the coefficient value of the invariant representing
the cohomology class. -/
@[simp]
theorem cohomFpZeroLinearEquiv_apply (x : cohomFp p G 0) :
    cohomFpZeroLinearEquiv p G x = trivialFpEquiv p G
      ((_root_.ContinuousCohomology.zeroIso (trivialFp p G)).hom x).1 :=
  (rfl)

/-- Zeroth continuous cohomology with trivial coefficients is finite as a `ZMod p`-module. -/
instance : Module.Finite (ZMod p) (cohomFp p G 0) :=
  Module.Finite.equiv (cohomFpZeroLinearEquiv p G).symm

end TauCeti
