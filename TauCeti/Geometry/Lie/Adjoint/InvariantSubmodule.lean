/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.InvariantSubmodule
public import TauCeti.Geometry.Lie.Adjoint.OperatorExponential
public import TauCeti.Geometry.Lie.Exponential.Unitary

/-!
# Invariant submodules under exponential conjugation

In a real Banach algebra, a closed linear subspace is preserved by conjugation with every element
of the one-parameter family `exp (t x)` exactly when it is preserved by commutation with `x`.
This is the closed-subspace form of differentiating the conjugation action.

For a Clifford algebra, taking the subspace to be the range of the generating-vector inclusion
turns preservation of vectors by the exponential conjugation flow into the corresponding
infinitesimal commutator condition. Combined with the unitary and closed-subspace
characterizations of exponential lines, this describes the exponential lines of unitaries in a
closed subalgebra whose conjugation preserves a closed subspace, the shape of a Spin group.

## Main results

* `TauCeti.Lie.forall_exp_smul_mul_mem_iff_forall_commutator_mem`: exponential conjugation
  preserves a closed submodule if and only if the commutator does.
* `TauCeti.Lie.forall_exp_smul_mem_unitary_and_mem_and_conj_mem_iff`: an exponential line of
  unitaries lies in a closed subalgebra and its conjugation preserves a closed subspace exactly
  when its generator lies in the subalgebra, is skew-adjoint, and brackets the subspace into itself.
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
      t • (continuousCommutator ℝ x) = continuousCommutator ℝ (t • x) :=
    (map_smul (continuousCommutator ℝ) t x).symm
  have hflow :
      (∀ t : ℝ, S ∈ Module.End.invtSubmodule
        (ContinuousLinearMap.mulLeftRight ℝ R (exp (t • x))
          (exp (-(t • x)))).toLinearMap) ↔
        S ∈ Module.End.invtSubmodule (continuousCommutator ℝ x).toLinearMap := by
    rw [← ContinuousLinearMap.forall_exp_smul_mem_invtSubmodule_iff
      (continuousCommutator ℝ x) hS]
    apply forall_congr'
    intro t
    rw [hscaled, exp_continuousCommutator]
  simpa only [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem,
    ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.mulLeftRight_apply, continuousCommutator_apply] using hflow

attribute [local instance] TauCeti.normedAlgebraRatOfReal in
/-- An exponential line consists of unitaries lying in a closed subalgebra `E` whose conjugation
preserves a closed subspace `V` exactly when its generator lies in `E`, is skew-adjoint, and
brackets `V` into itself. -/
theorem forall_exp_smul_mem_unitary_and_mem_and_conj_mem_iff [StarRing R] [ContinuousStar R]
    [StarModule ℝ R] {E : Subalgebra ℝ R} (hE : IsClosed (E : Set R)) {V : Submodule ℝ R}
    (hV : IsClosed (V : Set R)) (x : R) :
    (∀ t : ℝ, exp (t • x) ∈ unitary R ∧ exp (t • x) ∈ E ∧
        ∀ y ∈ V, exp (t • x) * y * star (exp (t • x)) ∈ V) ↔
      x ∈ E ∧ star x = -x ∧ ∀ y ∈ V, x * y - y * x ∈ V := by
  constructor
  · intro h
    refine ⟨mem_of_forall_exp_smul_mem (S := Subalgebra.toSubmodule E) hE fun t ↦ (h t).2.1,
      skewAdjoint.mem_iff.mp <|
        (forall_exp_smul_mem_unitary_iff_mem_skewAdjoint x).mp fun t ↦ (h t).1,
      (forall_exp_smul_mul_mem_iff_forall_commutator_mem x hV).mp fun t y hy ↦ ?_⟩
    simpa only [star_exp_eq_exp_neg_of_exp_mem_unitary (h t).1] using (h t).2.2 y hy
  · rintro ⟨hxE, hstar, hcomm⟩ t
    have hunitary : exp (t • x) ∈ unitary R :=
      (forall_exp_smul_mem_unitary_iff_mem_skewAdjoint x).mpr (skewAdjoint.mem_iff.mpr hstar) t
    refine ⟨hunitary, exp_mem hE (E.smul_mem hxE t), fun y hy ↦ ?_⟩
    rw [star_exp_eq_exp_neg_of_exp_mem_unitary hunitary]
    exact (forall_exp_smul_mul_mem_iff_forall_commutator_mem x hV).mpr hcomm t y hy

end TauCeti.Lie

end

end
