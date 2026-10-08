/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.InvariantSubmodule
public import TauCeti.Geometry.Lie.Adjoint.OperatorExponential

/-!
# Invariant submodules under exponential conjugation

In a real Banach algebra, a closed linear subspace is preserved by conjugation with every element
of the one-parameter family `exp (t x)` exactly when it is preserved by commutation with `x`.
This is the closed-subspace form of differentiating the conjugation action.

For a Clifford algebra, taking the subspace to be the range of the generating-vector inclusion
turns preservation of vectors by the exponential conjugation flow into the corresponding
infinitesimal commutator condition.

## Main results

* `TauCeti.Lie.forall_exp_smul_mul_mem_iff_forall_commutator_mem`: exponential conjugation
  preserves a closed submodule if and only if the commutator does.
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- A closed real submodule of a Banach algebra is preserved by conjugation with every
`exp (t x)` if and only if it is preserved by the commutator `y ↦ x * y - y * x`. -/
theorem forall_exp_smul_mul_mem_iff_forall_commutator_mem (x : R)
    {S : Submodule ℝ R} (hS : IsClosed (S : Set R)) :
    (∀ (t : ℝ) (y : R), y ∈ S → exp (t • x) * y * exp (-(t • x)) ∈ S) ↔
      ∀ y : R, y ∈ S → x * y - y * x ∈ S := by
  have hscaled (t : ℝ) :
      t • (continuousCommutator x) = continuousCommutator (t • x) :=
    (map_smul continuousCommutator t x).symm
  have hflow :
      (∀ t : ℝ, S ∈ Module.End.invtSubmodule
        (ContinuousLinearMap.mulLeftRight ℝ R (exp (t • x))
          (exp (-(t • x)))).toLinearMap) ↔
        S ∈ Module.End.invtSubmodule (continuousCommutator x).toLinearMap := by
    rw [← ContinuousLinearMap.forall_exp_smul_mem_invtSubmodule_iff
      (continuousCommutator x) hS]
    apply forall_congr'
    intro t
    rw [hscaled, exp_continuousCommutator]
  simpa only [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem,
    ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.mulLeftRight_apply, continuousCommutator_apply] using hflow

end TauCeti.Lie

end

end
