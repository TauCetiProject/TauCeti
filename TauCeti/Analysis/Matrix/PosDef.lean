/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# The positive-definite cone in the space of all square matrices

Positivity of `x ⬝ᵥ M *ᵥ x` on nonzero vectors cuts out an open set of real square matrices,
symmetric or not.

The positive-definite cone itself is not open in the space of all square matrices — the
Hermitian condition cuts out a proper subspace once there are at least two rows — but on the
symmetric subspace, where the Hermitian condition holds identically, the cone is the preimage
of this open set and hence open; see `TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef`.
Ambiently the cone is still measurable, being the intersection of the closed Hermitian condition
with that open one.

## Main declarations

* `TauCeti.isOpen_setOfPred_dotProduct_mulVec_pos` — positivity of the quadratic form on nonzero
  vectors is an open condition on real square matrices;
* `TauCeti.posDef_fin_one_iff` — a real `1 × 1` matrix is positive definite exactly when its
  single entry is positive;
* `TauCeti.measurableSet_setOfPred_posDef` — the positive-definite matrices form a measurable
  set.
-/

public section

noncomputable section

open Topology

open scoped Matrix

namespace TauCeti

/-- A real `1 × 1` matrix is positive definite exactly when its single entry is positive. -/
theorem posDef_fin_one_iff (M : Matrix (Fin 1) (Fin 1) ℝ) :
    M.PosDef ↔ 0 < M 0 0 := by
  have hdiag : M = Matrix.diagonal ![M 0 0] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hdiag, Matrix.posDef_diagonal_iff]
  simp

section

variable {ι : Type*} [Fintype ι]

private theorem smul_dotProduct_mulVec_smul (M : Matrix ι ι ℝ) (c : ℝ)
    (x : ι → ℝ) : (c • x) ⬝ᵥ M *ᵥ (c • x) = c ^ 2 * (x ⬝ᵥ M *ᵥ x) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, sq]

/-- Positivity of the quadratic form on nonzero vectors is an open condition on square real
matrices, symmetric or not. -/
theorem isOpen_setOfPred_dotProduct_mulVec_pos :
    IsOpen {M : Matrix ι ι ℝ | ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x} := by
  rw [isOpen_iff_mem_nhds]
  intro M hM
  -- By compactness of the unit sphere, positivity on it is stable under small perturbations.
  have key : ∀ᶠ N in 𝓝 M, ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ N *ᵥ x := by
    refine (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
      fun y hy => ?_
    rw [mem_sphere_zero_iff_norm] at hy
    have hy0 : y ≠ 0 := norm_ne_zero_iff.1 (hy ▸ one_ne_zero)
    have hcont : Continuous fun z : Matrix ι ι ℝ × (ι → ℝ) =>
        z.2 ⬝ᵥ z.1 *ᵥ z.2 := by fun_prop
    exact (isOpen_lt continuous_const hcont).mem_nhds (hM y hy0)
  filter_upwards [key] with N hN x hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0]
  have hscale : x ⬝ᵥ N *ᵥ x = ‖x‖ ^ 2 * ((‖x‖⁻¹ • x) ⬝ᵥ N *ᵥ (‖x‖⁻¹ • x)) := by
    rw [smul_dotProduct_mulVec_smul]
    field_simp
  rw [hscale]
  exact mul_pos (pow_pos (norm_pos_iff.2 hx) 2) (hN _ hmem)

end

/-- The positive-definite real matrices form a measurable set. -/
theorem measurableSet_setOfPred_posDef {ι : Type*} [Finite ι] :
    MeasurableSet {A : Matrix ι ι ℝ | A.PosDef} := by
  have : Fintype ι := Fintype.ofFinite ι
  have hsplit : {A : Matrix ι ι ℝ | A.PosDef} =
      {A : Matrix ι ι ℝ | A.IsHermitian} ∩
        {M : Matrix ι ι ℝ | ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x} := by
    ext A
    exact Matrix.posDef_iff_dotProduct_mulVec
  rw [hsplit]
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet.inter
    isOpen_setOfPred_dotProduct_mulVec_pos.measurableSet

end TauCeti
