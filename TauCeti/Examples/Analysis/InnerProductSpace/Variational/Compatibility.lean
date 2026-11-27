/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Compatibility
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# A finite-dimensional witness for the compatibility condition

The compatibility condition for a Gårding form `B` on a Hilbert space `V`
(`IsCompactOperator.exists_forall_apply_eq_iff_of_garding`) says that `B(u, ·) = ℓ` is solvable
exactly when `ℓ` vanishes on the **adjoint kernel** `{w | ∀ v, B(v, w) = 0}`, not on the kernel
`{u | ∀ v, B(u, v) = 0}`. For a non-symmetric form the two differ. This file works out the
smallest example, on `V = H = ℝ²` with `J = id`, which is compact since `ℝ²` is finite
dimensional, and the form

`B(u, v) = ⟪L u, v⟫ = (u₀ + u₁) v₀`,  `L = [[1, 1], [0, 0]]`

(`witnessForm`). All declarations are in the namespace `TauCeti.CompatibilityExamples`.

* `B` satisfies Gårding's inequality `‖w‖² ≤ B(w, w) + 2 ‖w‖²` (`garding_witnessForm`) but is
  not coercive, since `B((-1, 1), (-1, 1)) = 0` (`not_isCoercive_witnessForm`). So the
  compatibility theorem applies and Lax–Milgram does not.
* The kernel is `ker L = span (-1, 1)` (`ker_witnessForm`) and the adjoint kernel is
  `ker Lᵀ = span (0, 1)` (`ker_flip_witnessForm`). They are different lines
  (`ker_flip_witnessForm_ne_ker`), of the same dimension `1`, as the index-zero statement
  `IsCompactOperator.finrank_ker_flip_eq_finrank_ker_of_garding` requires.
* By the compatibility theorem, `B(u, ·) = ⟪f, ·⟫` is solvable exactly when `f₁ = 0`
  (`exists_forall_witnessForm_eq_inner_iff`): the range of `L` is `(ker Lᵀ)ᗮ`, the vectors with
  `f₁ = 0` (`range_toEuclideanCLM_witnessMatrix`), and the solutions for `f = (f₀, 0)` are
  `f + ker L` (`forall_witnessForm_eq_inner_iff`).
* The condition against the kernel is neither sufficient nor necessary. `f = (1, 1)` is
  orthogonal to the kernel (`inner_one_one_eq_zero_of_mem_ker`) and gives no solution
  (`not_exists_forall_witnessForm_eq_inner_one_one`,
  `not_forall_exists_forall_witnessForm_eq_inner_iff_ker`), while `f = (1, 0)` gives a solvable
  problem although `⟪f, (-1, 1)⟫ = -1`
  (`exists_forall_witnessForm_eq_inner_one_zero_and_inner_ne_zero`). The problem with
  `f = (0, 1)`, which spans the adjoint kernel, has no solution
  (`not_exists_forall_witnessForm_eq_inner_zero_one`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.3, Theorem 4.
-/

public section

noncomputable section

open Module
open scoped RealInnerProductSpace

namespace TauCeti.CompatibilityExamples

/-- The matrix `L = [[1, 1], [0, 0]]`, whose kernel `span (-1, 1)` differs from the kernel
`span (0, 1)` of its transpose. -/
def witnessMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; 0, 0]

/-- The bilinear form `B(u, v) = ⟪L u, v⟫ = (u₀ + u₁) v₀` on `ℝ²` of the matrix
`L = [[1, 1], [0, 0]]`. -/
def witnessForm :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ((innerSL ℝ).comp (Matrix.toEuclideanCLM (𝕜 := ℝ) witnessMatrix) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

/-- The form is `⟪L u, v⟫`. -/
theorem witnessForm_apply_eq_inner (u v : EuclideanSpace ℝ (Fin 2)) :
    witnessForm u v = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) witnessMatrix u, v⟫ := by
  simp only [witnessForm, ContinuousLinearMap.comp_apply, innerSL_apply_apply]

/-- The values of the form: `B(u, v) = (u₀ + u₁) v₀`. -/
@[simp]
theorem witnessForm_apply (u v : EuclideanSpace ℝ (Fin 2)) :
    witnessForm u v = (u 0 + u 1) * v 0 := by
  simp [witnessForm_apply_eq_inner, witnessMatrix, PiLp.inner_apply, Fin.sum_univ_two,
    Matrix.mulVec, dotProduct, mul_comm]

/-- **Gårding's inequality** `‖w‖² ≤ B(w, w) + 2 ‖w‖²`, with `J = id`, in the form of the
hypothesis of `IsCompactOperator.exists_forall_apply_eq_iff_of_garding`. -/
theorem garding_witnessForm (w : EuclideanSpace ℝ (Fin 2)) :
    1 * ‖w‖ ^ 2 ≤ witnessForm w w + 2 * ‖ContinuousLinearMap.id ℝ _ w‖ ^ 2 := by
  simp only [ContinuousLinearMap.id_apply, witnessForm_apply, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_two]
  nlinarith [sq_nonneg (2 * w 0 + w 1 / 2), sq_nonneg (w 1)]

/-- The form is **not coercive**: it vanishes on `(-1, 1)`. -/
theorem not_isCoercive_witnessForm : ¬IsCoercive witnessForm := by
  rintro ⟨C, hC, h⟩
  have hx : (!₂[-1, 1] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := fun h₀ ↦ by
    simpa using congrArg (· 0) h₀
  have hpos := mul_pos (mul_pos hC (norm_pos_iff.2 hx)) (norm_pos_iff.2 hx)
  have h₁ := h !₂[-1, 1]
  norm_num at h₁
  linarith

/-! ### The kernel and the adjoint kernel -/

/-- `u` lies in the kernel `{u | ∀ v, B(u, v) = 0}` exactly when `u₀ + u₁ = 0`. -/
theorem mem_ker_witnessForm_iff {u : EuclideanSpace ℝ (Fin 2)} :
    u ∈ witnessForm.ker ↔ u 0 + u 1 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using DFunLike.congr_fun h (EuclideanSpace.single 0 1)
  · ext v
    simp [h]

/-- `w` lies in the adjoint kernel `{w | ∀ v, B(v, w) = 0}` exactly when `w₀ = 0`. -/
theorem mem_ker_flip_witnessForm_iff {w : EuclideanSpace ℝ (Fin 2)} :
    w ∈ witnessForm.flip.ker ↔ w 0 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using DFunLike.congr_fun h (EuclideanSpace.single 0 1)
  · ext v
    simp [h]

/-- **The kernel is `ker L = span (-1, 1)`.** -/
theorem ker_witnessForm : witnessForm.ker = ℝ ∙ !₂[-1, 1] := by
  ext u
  rw [mem_ker_witnessForm_iff, Submodule.mem_span_singleton]
  refine ⟨fun h ↦ ⟨u 1, ?_⟩, fun ⟨t, ht⟩ ↦ ?_⟩
  · ext i
    fin_cases i
    · simpa using (eq_neg_of_add_eq_zero_left h).symm
    · simp
  · subst ht
    simp

/-- **The adjoint kernel is `ker Lᵀ = span (0, 1)`.** -/
theorem ker_flip_witnessForm : witnessForm.flip.ker = ℝ ∙ !₂[0, 1] := by
  ext w
  rw [mem_ker_flip_witnessForm_iff, Submodule.mem_span_singleton]
  refine ⟨fun h ↦ ⟨w 1, ?_⟩, fun ⟨t, ht⟩ ↦ ?_⟩
  · ext i
    fin_cases i <;> simp [h]
  · subst ht
    simp

/-- The kernel and the adjoint kernel are different: `(-1, 1)` lies in the kernel and not in the
adjoint kernel. -/
theorem ker_flip_witnessForm_ne_ker : witnessForm.flip.ker ≠ witnessForm.ker := by
  intro h
  have h₁ : (!₂[-1, 1] : EuclideanSpace ℝ (Fin 2)) ∈ witnessForm.ker :=
    mem_ker_witnessForm_iff.2 (by simp)
  rw [← h, mem_ker_flip_witnessForm_iff] at h₁
  norm_num at h₁

/-- The kernel is a line. -/
theorem finrank_ker_witnessForm : finrank ℝ witnessForm.ker = 1 := by
  rw [ker_witnessForm, finrank_span_singleton]
  intro h
  simpa using congrArg (· 0) h

/-- The adjoint kernel is a line, of the same dimension as the kernel, as
`IsCompactOperator.finrank_ker_flip_eq_finrank_ker_of_garding` predicts. -/
theorem finrank_ker_flip_witnessForm : finrank ℝ witnessForm.flip.ker = 1 :=
  (IsCompactOperator.finrank_ker_flip_eq_finrank_ker_of_garding
    ((isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).2 inferInstance) one_pos
    garding_witnessForm).trans finrank_ker_witnessForm

/-! ### Solvability -/

/-- **The compatibility condition for `L = [[1, 1], [0, 0]]`.** The problem `B(u, ·) = ⟪f, ·⟫`
has a solution exactly when `f` is orthogonal to the adjoint kernel `span (0, 1)`, that is when
`f₁ = 0`. -/
theorem exists_forall_witnessForm_eq_inner_iff (f : EuclideanSpace ℝ (Fin 2)) :
    (∃ u, ∀ v, witnessForm u v = ⟪f, v⟫) ↔ f 1 = 0 := by
  have h := IsCompactOperator.exists_forall_apply_eq_iff_of_garding
    ((isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).2 inferInstance) one_pos
    garding_witnessForm (innerSL ℝ f)
  simp only [innerSL_apply_apply] at h
  rw [h]
  refine ⟨fun hf ↦ ?_, fun hf w hw ↦ ?_⟩
  · simpa [PiLp.inner_apply, Fin.sum_univ_two] using hf !₂[0, 1] fun v ↦ by simp
  · have hw₀ := mem_ker_flip_witnessForm_iff.1 (by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      exact ContinuousLinearMap.ext hw)
    simp [PiLp.inner_apply, Fin.sum_univ_two, hf, hw₀]

/-- **The solutions form a translate of the kernel.** `u` solves `B(u, ·) = ⟪f, ·⟫` exactly when
`f₁ = 0` and `u - f` lies in the kernel `span (-1, 1)`. -/
theorem forall_witnessForm_eq_inner_iff (u f : EuclideanSpace ℝ (Fin 2)) :
    (∀ v, witnessForm u v = ⟪f, v⟫) ↔ f 1 = 0 ∧ u - f ∈ witnessForm.ker := by
  rw [mem_ker_witnessForm_iff]
  simp only [witnessForm_apply, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    conj_trivial, PiLp.sub_apply]
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ v ↦ ?_⟩
  · have h₀ := h (EuclideanSpace.single 0 1)
    have h₁ := h (EuclideanSpace.single 1 1)
    simp at h₀ h₁
    exact ⟨h₁.symm, by linarith⟩
  · linear_combination v 0 * h₂ + (v 0 - v 1) * h₁

/-- **The range of `L` is `(ker Lᵀ)ᗮ`**, the vectors with `f₁ = 0`. -/
theorem range_toEuclideanCLM_witnessMatrix :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) witnessMatrix).range = witnessForm.flip.kerᗮ := by
  ext f
  rw [ker_flip_witnessForm, Submodule.mem_orthogonal_singleton_iff_inner_right,
    LinearMap.mem_range]
  simp only [ContinuousLinearMap.coe_coe]
  have hf : ⟪(!₂[0, 1] : EuclideanSpace ℝ (Fin 2)), f⟫ = f 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two]
  rw [hf, ← exists_forall_witnessForm_eq_inner_iff]
  refine exists_congr fun u ↦ ⟨fun h v ↦ ?_, fun h ↦ ext_inner_right ℝ h⟩
  rw [witnessForm_apply_eq_inner, h]

/-- `f = (1, 0)` is orthogonal to the adjoint kernel, and the problem `B(u, ·) = ⟪f, ·⟫` is
solvable, with solutions the `u` with `u₀ + u₁ = 1`. -/
theorem forall_witnessForm_eq_inner_one_zero_iff (u : EuclideanSpace ℝ (Fin 2)) :
    (∀ v, witnessForm u v = ⟪!₂[1, 0], v⟫) ↔ u 0 + u 1 = 1 := by
  rw [forall_witnessForm_eq_inner_iff, mem_ker_witnessForm_iff]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, true_and, PiLp.sub_apply]
  constructor <;> intro h <;> linarith

/-- The problem `B(u, ·) = ⟪(0, 1), ·⟫` has no solution: `(0, 1)` spans the adjoint kernel. -/
theorem not_exists_forall_witnessForm_eq_inner_zero_one :
    ¬∃ u, ∀ v, witnessForm u v = ⟪!₂[0, 1], v⟫ := by
  rw [exists_forall_witnessForm_eq_inner_iff]
  simp

/-- `(1, 1)` is orthogonal to the kernel `span (-1, 1)`. -/
theorem inner_one_one_eq_zero_of_mem_ker {w : EuclideanSpace ℝ (Fin 2)}
    (hw : w ∈ witnessForm.ker) : ⟪!₂[1, 1], w⟫ = 0 := by
  simpa [PiLp.inner_apply, Fin.sum_univ_two, add_comm] using mem_ker_witnessForm_iff.1 hw

/-- The problem `B(u, ·) = ⟪(1, 1), ·⟫` has no solution, although `(1, 1)` is orthogonal to the
kernel (`TauCeti.CompatibilityExamples.inner_one_one_eq_zero_of_mem_ker`). -/
theorem not_exists_forall_witnessForm_eq_inner_one_one :
    ¬∃ u, ∀ v, witnessForm u v = ⟪!₂[1, 1], v⟫ := by
  rw [exists_forall_witnessForm_eq_inner_iff]
  simp

/-- **The condition against the kernel is wrong.** It is not true that `B(u, ·) = ⟪f, ·⟫` is
solvable exactly when `f` is orthogonal to the kernel `{u | ∀ v, B(u, v) = 0}`: `f = (1, 1)` is
orthogonal to the kernel and gives no solution. The compatibility condition is against the adjoint
kernel. -/
theorem not_forall_exists_forall_witnessForm_eq_inner_iff_ker :
    ¬∀ f : EuclideanSpace ℝ (Fin 2),
      (∃ u, ∀ v, witnessForm u v = ⟪f, v⟫) ↔ ∀ w ∈ witnessForm.ker, ⟪f, w⟫ = 0 :=
  fun h ↦ not_exists_forall_witnessForm_eq_inner_one_one
    ((h _).2 fun _ ↦ inner_one_one_eq_zero_of_mem_ker)

/-- Nor is orthogonality to the kernel necessary: `f = (1, 0)` gives a solvable problem, with the
solution `(1, 0)`, but `⟪f, (-1, 1)⟫ = -1`. -/
theorem exists_forall_witnessForm_eq_inner_one_zero_and_inner_ne_zero :
    (∃ u, ∀ v, witnessForm u v = ⟪!₂[1, 0], v⟫) ∧
      ⟪(!₂[1, 0] : EuclideanSpace ℝ (Fin 2)), !₂[-1, 1]⟫ ≠ 0 := by
  refine ⟨⟨!₂[1, 0], (forall_witnessForm_eq_inner_one_zero_iff _).2 (by simp)⟩, ?_⟩
  simp [PiLp.inner_apply, Fin.sum_univ_two]

end TauCeti.CompatibilityExamples
