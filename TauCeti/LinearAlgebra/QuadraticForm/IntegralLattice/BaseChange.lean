/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.Submodule
public import TauCeti.LinearAlgebra.QuadraticForm.IntegralLattice.Basic
import TauCeti.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Scalar extension of integral quadratic lattices

`IntegralQuadraticLattice.eq_comp_isBaseChange_subtype_iff` characterizes the pullback of
the generic form to the scalar extension of the lattice carrier to the total ring of fractions.
-/

public section

open scoped nonZeroDivisors TensorProduct

namespace TauCeti.IntegralQuadraticLattice

variable {R K V : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] {Q : QuadraticForm K V}
  (L : IntegralQuadraticLattice R Q)

/-- The pullback of the generic form to the scalar extension is characterized by the values
of the integral form on pure tensors with first factor one. -/
theorem eq_comp_isBaseChange_subtype_iff (q : QuadraticForm K (K ⊗[R] L.carrier)) :
    q = Q.comp (L.carrier.isBaseChange_subtype_of_span_eq_top R⁰
        (Submodule.IsFullLattice.span_eq_top (A := K))).equiv.toLinearMap ↔
      ∀ x : L.carrier, q (1 ⊗ₜ[R] x) = algebraMap R K (L.integralForm x) := by
  simpa only [Submodule.subtype_apply, algebraMap_integralForm] using
    (L.carrier.isBaseChange_subtype_of_span_eq_top R⁰
      (Submodule.IsFullLattice.span_eq_top (A := K))).eq_comp_quadraticMap_iff Q q

end TauCeti.IntegralQuadraticLattice
