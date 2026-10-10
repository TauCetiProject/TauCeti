/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Contraction with a symplectic form

On a finite-dimensional real normed space, contraction with a symplectic form is an
invertible continuous linear map to the continuous dual. This identifies covectors with
vectors and allows the contraction equation in Moser's deformation argument to be solved
using the continuous-linear-map inverse.

See McDuff--Salamon, *Introduction to Symplectic Topology*, Section 3.2.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Contraction with a finite-dimensional symplectic form is an isomorphism to the
continuous dual. -/
@[simp]
theorem isInvertible_toContinuousBilinearMap (ω : SymplecticForm V) :
    ω.toBilinForm.toContinuousBilinearMap.IsInvertible := by
  have hinj : Function.Injective ω.toBilinForm :=
    LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp ω.nondegenerate.1)
  let e := (ω.toBilinForm.linearEquivOfInjective hinj
    (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).trans
      (LinearMap.toContinuousLinearMap : Module.Dual ℝ V ≃ₗ[ℝ] (V →L[ℝ] ℝ))
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  ext v w
  simp [e, LinearMap.toContinuousBilinearMap_apply]

end TauCeti.SymplecticForm
