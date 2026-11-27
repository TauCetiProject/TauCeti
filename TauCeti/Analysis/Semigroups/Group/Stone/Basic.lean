/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Unitary
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# The bounded part of Stone's theorem

This file begins the converse direction of Stone's theorem.  A bounded self-adjoint operator
`A` on a complex Hilbert space gives the unitary group `exp (t i A)`; its real-linear generator is
the expected operator `i A`.  The general self-adjoint case is
`TauCeti.Analysis.Semigroups.Group.Stone.Unbounded`.
-/

public section

noncomputable section

open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups

namespace StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- The exponential group associated to a bounded operator. It is unitary when the operator is
self-adjoint. -/
def ofBoundedExp (A : H →L[ℂ] H) : StronglyContinuousGroup H :=
  ofBounded ((Complex.I • A).restrictScalars ℝ)

/-- At time `t`, the bounded Stone group is the complex exponential regarded as real-linear. -/
@[simp]
theorem ofBoundedExp_apply (A : H →L[ℂ] H) (t : ℝ) :
    ofBoundedExp A t =
      (NormedSpace.exp ((t : ℂ) • (Complex.I • A))).restrictScalars ℝ := by
  rw [ofBoundedExp, ofBounded_apply, ← ContinuousLinearMap.restrictScalars_smul,
    ← ContinuousLinearMap.restrictScalars_exp, Complex.coe_smul]

/-- The generator of the bounded exponential group is `i A`, regarded as a real partial linear
map. -/
@[simp]
theorem ofBoundedExp_generator (A : H →L[ℂ] H) :
    (ofBoundedExp A).generator =
      ((Complex.I • A).restrictScalars ℝ).toLinearMap.toPMap ⊤ := by
  exact ofBounded_generator _

end StronglyContinuousGroup

section

namespace StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded exponential group is unitary when its operator is self-adjoint. -/
theorem isUnitary_ofBoundedExp (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary (ofBoundedExp A) := by
  refine IsUnitary.intro fun t x y => ?_
  rw [ofBoundedExp_apply]
  let _i : Module ℚ H := Module.compHom H (algebraMap ℚ ℂ)
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  have hskew : Complex.I • A ∈ skewAdjoint (H →L[ℂ] H) := by
    rw [Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint]
    exact hA
  have hscaled : t • (Complex.I • A) ∈ skewAdjoint (H →L[ℂ] H) :=
    skewAdjoint.smul_mem t hskew
  have hu0 : NormedSpace.exp (t • (Complex.I • A)) ∈ unitary (H →L[ℂ] H) :=
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hscaled
  have hu : NormedSpace.exp ((t : ℂ) • (Complex.I • A)) ∈ unitary (H →L[ℂ] H) := by
    simpa only [Complex.coe_smul] using hu0
  exact (NormedSpace.exp ((t : ℂ) • (Complex.I • A))).inner_map_map_of_mem_unitary hu x y

end StronglyContinuousGroup

end

end TauCeti.Semigroups

end
