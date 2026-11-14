/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Data.Set.Card
import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# Moment functions on projective space

On the projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)` over `𝕜 = ℝ` or `ℂ`, with weights
`w : Fin (n + 1) → ℝ`, the **moment function** sends the line through `v` to the weighted average

`(∑ i, w i * ‖v i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2`.

Over `ℂ` with the weights `w i = i` it is the standard Morse function on `ℂℙⁿ`, a moment map of
the circle action `t • [z₀ : ⋯ : zₙ] = [z₀ : t z₁ : ⋯ : tⁿ zₙ]` up to an affine change of the
values. This file proves that for pairwise distinct weights it is a Morse function for the
underlying real smooth structure of projective space. Its critical points are the `n + 1`
coordinate points `[eₖ]`. The Morse index at `[eₖ]` is the real dimension of `𝕜` times the number
of weights below `w k`. On `ℂℙⁿ` with the standard weights, `[eₖ]` therefore has index `2 * k`,
so the critical points have the distinct even indices `0, 2, …, 2 * n`. On `ℝℙⁿ` there is one
critical point of each index `0, …, n`.

For arbitrary weights, the critical points are the lines spanned by eigenvectors of the diagonal
form with weights `w`, the point `[eₖ]` is nondegenerate exactly when the weight `w k` is simple,
and the moment function is Morse exactly when the weights are pairwise distinct.

The computation takes place in the standard affine chart at `k`, centred at `[eₖ]`. There the
moment function is the chart model `(w k + ∑ j, ν j * ‖z j‖ ^ 2) / (1 + ∑ j, ‖z j‖ ^ 2)` with
`ν = w ∘ k.succAbove` (`TauCeti.ProjectiveMomentChart.model`). Multiplying out the denominator
shows that its differential at `z` vanishes exactly when `(ν j - r) z j = 0` for every `j`, where
`r` is the value at `z`. This happens exactly when every nonzero `z j` has `ν j = w k`, which
forces `z = 0` when no `ν j` equals `w k`. The second derivative at the origin is
`2 ∑ j, (ν j - w k) ⟪v j, v' j⟫`. Each coordinate of `𝕜` contributes a `dim_ℝ 𝕜`-dimensional
block of the same sign to its inertia.

## Main declarations

* `TauCeti.projectiveMomentFunction`: the moment function with weights `w`.
* `TauCeti.contMDiff_projectiveMomentFunction`: it is smooth.
* `TauCeti.mk_mem_criticalPoints_projectiveMomentFunction_iff`: for arbitrary weights its critical
  points are the eigenlines of the diagonal form.
* `TauCeti.criticalPoints_projectiveMomentFunction`: for distinct weights its critical points are
  the coordinate points `[eₖ]`.
* `TauCeti.isMorse_projectiveMomentFunction`: for distinct weights it is a Morse function.
* `TauCeti.isManifoldNondegenerateCriticalPoint_projectiveMomentFunction_iff` and
  `TauCeti.isMorse_projectiveMomentFunction_iff`: `[eₖ]` is nondegenerate exactly when `w k` is a
  simple weight, and the function is Morse exactly when the weights are distinct.
* `TauCeti.manifoldMorseIndex_projectiveMomentFunction`: the Morse index at `[eₖ]` is
  `dim_ℝ 𝕜 * #{i | w i < w k}`.
* `TauCeti.totalCriticalCount_projectiveMomentFunction` and
  `TauCeti.criticalCount_projectiveMomentFunction`: the critical counts.
* `TauCeti.criticalCount_projectiveMomentFunction_mul` and
  `TauCeti.criticalCount_projectiveMomentFunction_eq_zero`: for distinct weights there is exactly
  one critical point of each index `dim_ℝ 𝕜 * j` with `j ≤ n`, and none of any other index.
* `TauCeti.criticalCount_projectiveMomentFunction_real`: on `ℝℙⁿ` with distinct weights there is
  one critical point of each index `j ≤ n`.
* `TauCeti.subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real`: in particular, no
  two of them have the same index.
* `TauCeti.le_projectiveMomentFunction` and `TauCeti.projectiveMomentFunction_le`: its values lie
  between the smallest and the largest weight.
* `TauCeti.le_projectiveMomentFunction_of_notMem_affineOpen` and
  `TauCeti.lt_projectiveMomentFunction_of_notMem_affineOpen`: outside the affine open `v k ≠ 0`,
  its values are bounded below by the other weights.
* `TauCeti.contractibleSpace_sublevel_projectiveMomentFunction`: if `w k ≤ c` and every other weight
  is greater than `c`, the sublevel `{f ≤ c}` is contractible.
* `TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast_complex` and
  `TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast_real`: with the standard weights,
  `[eₖ]` has index `2 * k` on `ℂℙⁿ` and `k` on `ℝℙⁿ`.
* `TauCeti.isCriticalBandCut_projectiveMomentFunction_natCast`: with the standard weights, the
  half-integers `q - 1/2` form a critical-band cut.
* `TauCeti.contractibleSpace_sublevel_projectiveMomentFunction_natCast`: with the standard weights,
  the sublevels `{f ≤ c}`, `0 ≤ c < 1`, are contractible.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §4 (the example of `ℂℙⁿ`).
* R. Bott, *Lectures on Morse theory, old and new*, Bull. Amer. Math. Soc. 7 (1982), §1.
-/

public section

open Function Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization RealInnerProductSpace

noncomputable section

namespace TauCeti

/-! ### The model in an affine chart -/

namespace ProjectiveMomentChart

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The weighted sum of squared norms `z ↦ ∑ j, c j * ‖z j‖ ^ 2`. -/
private def weightedNormSq (c : Fin n → ℝ) (z : Fin n → 𝕜) : ℝ :=
  ∑ j, c j * ‖z j‖ ^ 2

variable (𝕜) in
/-- The weighted real inner product `(z, w) ↦ ∑ j, c j * ⟪z j, w j⟫`. -/
private def weightedInner (c : Fin n → ℝ) : (Fin n → 𝕜) →L[ℝ] (Fin n → 𝕜) →L[ℝ] ℝ :=
  ∑ j, c j • (innerSL ℝ : 𝕜 →L[ℝ] 𝕜 →L[ℝ] ℝ).bilinearComp (ContinuousLinearMap.proj j)
    (ContinuousLinearMap.proj j)

private theorem weightedInner_apply (c : Fin n → ℝ) (z w : Fin n → 𝕜) :
    weightedInner 𝕜 c z w = ∑ j, c j * ⟪z j, w j⟫ := by
  simp [weightedInner]

private theorem hasFDerivAt_weightedNormSq (c : Fin n → ℝ) (z : Fin n → 𝕜) :
    HasFDerivAt (weightedNormSq c) (2 • weightedInner 𝕜 c z) z := by
  have h (j : Fin n) : HasFDerivAt (fun z : Fin n → 𝕜 ↦ c j * ‖z j‖ ^ 2)
      (c j • (2 • innerSL ℝ (z j)).comp (ContinuousLinearMap.proj j)) z := by
    have h1 : HasFDerivAt (fun w : 𝕜 ↦ ‖w‖ ^ 2) (2 • innerSL ℝ (z j)) (z j) :=
      (hasStrictFDerivAt_norm_sq (z j)).hasFDerivAt
    exact (h1.comp z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ 𝕜) j).hasFDerivAt
      ).const_mul (c j)
  convert HasFDerivAt.sum (u := Finset.univ) fun j _ ↦ h j using 1
  · ext z
    simp [weightedNormSq]
  · ext w
    simp [weightedInner_apply, Finset.mul_sum, mul_left_comm]

private theorem contDiff_weightedNormSq (c : Fin n → ℝ) {r : ℕ∞ω} :
    ContDiff ℝ r (weightedNormSq (𝕜 := 𝕜) c) :=
  ContDiff.sum fun j _ ↦ contDiff_const.mul ((contDiff_norm_sq ℝ).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ 𝕜) j).contDiff)

private theorem fderiv_weightedNormSq (c : Fin n → ℝ) :
    fderiv ℝ (weightedNormSq (𝕜 := 𝕜) c) = ⇑(2 • weightedInner 𝕜 c) := by
  ext z : 1
  exact (hasFDerivAt_weightedNormSq c z).fderiv

private theorem weightedNormSq_zero (c : Fin n → ℝ) : weightedNormSq c (0 : Fin n → 𝕜) = 0 := by
  simp [weightedNormSq]

private theorem weightedNormSq_nonneg {c : Fin n → ℝ} (hc : ∀ j, 0 ≤ c j) (z : Fin n → 𝕜) :
    0 ≤ weightedNormSq c z :=
  Finset.sum_nonneg fun j _ ↦ mul_nonneg (hc j) (sq_nonneg _)

private theorem weightedInner_self (c : Fin n → ℝ) (z : Fin n → 𝕜) :
    weightedInner 𝕜 c z z = weightedNormSq c z := by
  simp [weightedInner_apply, weightedNormSq]

private theorem weightedInner_single (c : Fin n → ℝ) (z : Fin n → 𝕜) (j : Fin n) (w : 𝕜) :
    weightedInner 𝕜 c z (Pi.single j w) = c j * ⟪z j, w⟫ := by
  rw [weightedInner_apply, Finset.sum_eq_single j (fun i _ hi ↦ by simp [hi]) (by simp)]
  simp

variable (𝕜) in
/-- The **chart model** of the moment function, `(a + ∑ j, ν j * ‖z j‖ ^ 2) / (1 + ∑ j, ‖z j‖ ^ 2)`.
In the affine chart at the coordinate `k`, the moment function with weights `w` is this model with
`a = w k` and `ν = w ∘ k.succAbove` (`TauCeti.projectiveMomentFunction_comp_affineChart_symm`). -/
def model (a : ℝ) (ν : Fin n → ℝ) (z : Fin n → 𝕜) : ℝ :=
  (a + weightedNormSq ν z) / (1 + weightedNormSq 1 z)

theorem model_apply (a : ℝ) (ν : Fin n → ℝ) (z : Fin n → 𝕜) :
    model 𝕜 a ν z = (a + ∑ j, ν j * ‖z j‖ ^ 2) / (1 + ∑ j, ‖z j‖ ^ 2) := by
  simp [model, weightedNormSq]

private theorem one_add_weightedNormSq_one_pos (z : Fin n → 𝕜) : 0 < 1 + weightedNormSq 1 z :=
  add_pos_of_pos_of_nonneg one_pos (weightedNormSq_nonneg (fun _ ↦ zero_le_one) z)

private theorem one_add_weightedNormSq_one_mul_model (a : ℝ) (ν : Fin n → ℝ) (z : Fin n → 𝕜) :
    (1 + weightedNormSq 1 z) * model 𝕜 a ν z = a + weightedNormSq ν z :=
  mul_div_cancel₀ _ (one_add_weightedNormSq_one_pos z).ne'

private theorem one_add_weightedNormSq_one_mul_model_eq (a : ℝ) (ν : Fin n → ℝ) :
    (fun z : Fin n → 𝕜 ↦ 1 + weightedNormSq 1 z) * model 𝕜 a ν = fun z ↦ a + weightedNormSq ν z :=
  funext (one_add_weightedNormSq_one_mul_model a ν)

@[simp]
theorem model_zero (a : ℝ) (ν : Fin n → ℝ) : model 𝕜 a ν 0 = a := by
  simp [model, weightedNormSq]

theorem contDiff_model (a : ℝ) (ν : Fin n → ℝ) {r : ℕ∞ω} : ContDiff ℝ r (model 𝕜 a ν) :=
  (contDiff_const.add (contDiff_weightedNormSq ν)).div
    (contDiff_const.add (contDiff_weightedNormSq 1)) fun z ↦ (one_add_weightedNormSq_one_pos z).ne'

/-- Clearing the denominator of the model: the derivative of `N = (1 + ∑ ‖z j‖ ^ 2) * model`. -/
private theorem two_smul_weightedInner_eq (a : ℝ) (ν : Fin n → ℝ) (z : Fin n → 𝕜) :
    2 • weightedInner 𝕜 ν z = (1 + weightedNormSq 1 z) • fderiv ℝ (model 𝕜 a ν) z +
      model 𝕜 a ν z • (2 • weightedInner 𝕜 1 z) := by
  have hD : HasFDerivAt (fun z : Fin n → 𝕜 ↦ 1 + weightedNormSq 1 z) (2 • weightedInner 𝕜 1 z) z :=
    (hasFDerivAt_weightedNormSq 1 z).const_add 1
  have hg := ((contDiff_model (𝕜 := 𝕜) a ν (r := 1)).differentiable one_ne_zero z).hasFDerivAt
  have hN := (hasFDerivAt_weightedNormSq ν z).const_add a
  have hmul := hD.mul hg
  rw [one_add_weightedNormSq_one_mul_model_eq] at hmul
  exact hN.unique hmul

@[simp]
theorem fderiv_model_zero (a : ℝ) (ν : Fin n → ℝ) : fderiv ℝ (model 𝕜 a ν) 0 = 0 := by
  have h := two_smul_weightedInner_eq (𝕜 := 𝕜) a ν 0
  simp only [map_zero, smul_zero, add_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (one_add_weightedNormSq_one_pos 0).ne'

/-- If every nonzero coordinate `z j` carries the weight `ν j = a`, then the weighted sum of
squares with weights `ν` is `a` times the plain sum of squares. -/
private theorem weightedInner_eq_smul_of_forall {a : ℝ} {ν : Fin n → ℝ} {z : Fin n → 𝕜}
    (hz : ∀ j, z j = 0 ∨ ν j = a) : weightedInner 𝕜 ν z = a • weightedInner 𝕜 1 z := by
  ext u
  simp only [weightedInner_apply, smul_apply, smul_eq_mul, Pi.one_apply, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases hz j with h0 | h0 <;> simp [h0]

/-- **The value of the chart model at an eigenvector.** If every nonzero coordinate `z j` carries
the weight `ν j = a`, the model takes the value `a` at `z`. -/
theorem model_eq_of_forall {a : ℝ} {ν : Fin n → ℝ} {z : Fin n → 𝕜}
    (hz : ∀ j, z j = 0 ∨ ν j = a) : model 𝕜 a ν z = a := by
  have hnorm : weightedNormSq ν z = a * weightedNormSq 1 z := by
    rw [← weightedInner_self, ← weightedInner_self, weightedInner_eq_smul_of_forall hz, smul_apply,
      smul_eq_mul]
  refine mul_left_cancel₀ (one_add_weightedNormSq_one_pos z).ne' ?_
  rw [one_add_weightedNormSq_one_mul_model, hnorm]
  ring

/-- **The critical points of the chart model.** The differential of the model vanishes at `z`
exactly when every nonzero coordinate `z j` carries the weight `ν j = a`. -/
theorem fderiv_model_eq_zero_iff_forall {a : ℝ} {ν : Fin n → ℝ} {z : Fin n → 𝕜} :
    fderiv ℝ (model 𝕜 a ν) z = 0 ↔ ∀ j, z j = 0 ∨ ν j = a := by
  have h := two_smul_weightedInner_eq (𝕜 := 𝕜) a ν z
  refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · set r := model 𝕜 a ν z with hr
    rw [hz, smul_zero, zero_add] at h
    -- Evaluating at `z` gives `∑ ν j ‖z j‖² = r ∑ ‖z j‖²`, which forces `r = a`.
    have hzz := congr($h z)
    simp only [smul_apply, weightedInner_self, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hzz
    have hra : r = a := by
      have := one_add_weightedNormSq_one_mul_model (𝕜 := 𝕜) a ν z
      rw [← hr] at this
      linarith
    -- Evaluating at `Pi.single j (z j)` gives `ν j ‖z j‖² = r ‖z j‖²`.
    intro j
    have hj := congr($h (Pi.single j (z j)))
    simp only [smul_apply, weightedInner_single, smul_eq_mul, Pi.one_apply,
      one_mul, real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat] at hj
    have hzero : (ν j - a) * ‖z j‖ ^ 2 = 0 := by rw [← hra]; linarith
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact Or.inr (sub_eq_zero.mp h0)
    · exact Or.inl (by simpa using h0)
  · rw [weightedInner_eq_smul_of_forall hz, model_eq_of_forall hz, smul_comm a (2 : ℕ)] at h
    exact (smul_eq_zero.mp (add_eq_right.mp h.symm)).resolve_left
      (one_add_weightedNormSq_one_pos z).ne'

/-- If no weight `ν j` equals `a`, the origin is the only critical point of the chart model. -/
theorem fderiv_model_eq_zero_iff {a : ℝ} {ν : Fin n → ℝ} (hν : ∀ j, ν j ≠ a) {z : Fin n → 𝕜} :
    fderiv ℝ (model 𝕜 a ν) z = 0 ↔ z = 0 := by
  rw [fderiv_model_eq_zero_iff_forall]
  exact ⟨fun h ↦ funext fun j ↦ (h j).resolve_right (hν j), by rintro rfl j; exact Or.inl rfl⟩

/-- The second derivative of the chart model at the origin is twice the weighted inner product with
the weights `ν j - a`. -/
private theorem fderiv_fderiv_model_zero (a : ℝ) (ν : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (model 𝕜 a ν)) 0 = 2 • weightedInner 𝕜 (fun j ↦ ν j - a) := by
  ext v w
  have hD : ContDiffAt ℝ 2 (fun z : Fin n → 𝕜 ↦ 1 + weightedNormSq 1 z) 0 :=
    (contDiff_const.add (contDiff_weightedNormSq 1)).contDiffAt
  have hmul := fderiv_fderiv_mul_apply hD (contDiff_model (𝕜 := 𝕜) a ν).contDiffAt v w
  rw [one_add_weightedNormSq_one_mul_model_eq] at hmul
  have hN : fderiv ℝ (fun z : Fin n → 𝕜 ↦ a + weightedNormSq ν z) = ⇑(2 • weightedInner 𝕜 ν) := by
    ext z : 1
    rw [fderiv_const_add, fderiv_weightedNormSq]
  have hD' : fderiv ℝ (fun z : Fin n → 𝕜 ↦ 1 + weightedNormSq 1 z) = ⇑(2 • weightedInner 𝕜 1) := by
    ext z : 1
    rw [fderiv_const_add, fderiv_weightedNormSq]
  rw [hN, hD', fderiv_model_zero] at hmul
  have hsum : ∑ j, (ν j - a) * ⟪v j, w j⟫ = ∑ j, ν j * ⟪v j, w j⟫ - a * ∑ j, ⟪v j, w j⟫ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp [sub_mul]
  simp only [smul_apply, nsmul_eq_mul, Nat.cast_ofNat, map_zero, zero_apply, model_zero,
    mul_zero, add_zero, weightedInner_apply, weightedNormSq_zero, ContinuousLinearMap.fderiv,
    Pi.one_apply, one_mul] at hmul ⊢
  rw [hsum]
  linarith
/-- The Hessian quadratic form of the chart model at the origin is
`v ↦ 2 * ∑ j, (ν j - a) * ‖v j‖ ^ 2`. -/
theorem hessianQuadraticForm_model_zero (a : ℝ) (ν : Fin n → ℝ) (v : Fin n → 𝕜) :
    hessianQuadraticForm (model 𝕜 a ν) 0 v = 2 * ∑ j, (ν j - a) * ‖v j‖ ^ 2 := by
  rw [hessianQuadraticForm_apply, fderiv_fderiv_model_zero, smul_apply, smul_apply,
    weightedInner_self, nsmul_eq_mul, Nat.cast_ofNat, weightedNormSq]

/-- If no weight `ν j` equals `a`, the origin is a nondegenerate critical point of the chart
model. -/
theorem isNondegenerateCriticalPoint_model_zero {a : ℝ} {ν : Fin n → ℝ} (hν : ∀ j, ν j ≠ a) :
    IsNondegenerateCriticalPoint (model 𝕜 a ν) 0 := by
  rw [isNondegenerateCriticalPoint_iff_separatingLeft]
  refine ⟨(contDiff_model a ν).contDiffAt, fderiv_model_zero a ν, fun v hv ↦ funext fun j ↦ ?_⟩
  have hj := hv (Pi.single j (v j))
  simp only [ContinuousLinearMap.toBilinForm_apply, fderiv_fderiv_model_zero, smul_apply,
    weightedInner_single, real_inner_self_eq_norm_sq, nsmul_eq_mul] at hj
  simpa [sub_ne_zero.mpr (hν j)] using hj

/-- The origin is a nondegenerate critical point of the chart model exactly when no weight `ν j`
equals `a`. -/
theorem isNondegenerateCriticalPoint_model_zero_iff {a : ℝ} {ν : Fin n → ℝ} :
    IsNondegenerateCriticalPoint (model 𝕜 a ν) 0 ↔ ∀ j, ν j ≠ a := by
  refine ⟨fun h j hj ↦ ?_, isNondegenerateCriticalPoint_model_zero⟩
  -- A coordinate of weight `a` spans a direction in the kernel of the Hessian.
  have hker := (isNondegenerateCriticalPoint_iff_separatingLeft.1 h).2.2
    (Pi.single j (1 : 𝕜)) fun u ↦ ?_
  · simpa using congrFun hker j
  rw [ContinuousLinearMap.toBilinForm_apply, fderiv_fderiv_model_zero, smul_apply, smul_apply,
    weightedInner_apply, Finset.sum_eq_single j (fun i _ hi ↦ by simp [hi]) (by simp)]
  simp [hj]

/-- The Morse index of the chart model at the origin is the real dimension of `𝕜` times the
number of weights `ν j` below `a`. -/
theorem morseIndex_model_zero (a : ℝ) (ν : Fin n → ℝ) :
    morseIndex (model 𝕜 a ν) 0 = Module.finrank ℝ 𝕜 * {j | ν j < a}.ncard := by
  set d := Module.finrank ℝ 𝕜
  let b := stdOrthonormalBasis ℝ 𝕜
  -- Real coordinates in an orthonormal basis of each factor `𝕜` diagonalize the Hessian.
  let e : (Fin n → 𝕜) ≃ₗ[ℝ] (Fin n × Fin d → ℝ) :=
    (LinearEquiv.piCongrRight fun _ ↦ b.toBasis.equivFun).trans
      (LinearEquiv.curry ℝ ℝ (Fin n) (Fin d)).symm
  have he (v : Fin n → 𝕜) (p : Fin n × Fin d) : e v p = b.repr (v p.1) p.2 := by
    obtain ⟨j, t⟩ := p
    simp [e, LinearEquiv.curry]
  have hequiv : (hessianQuadraticForm (model 𝕜 a ν) 0).Equivalent
      (QuadraticMap.weightedSumSquares ℝ fun p : Fin n × Fin d ↦ 2 * (ν p.1 - a)) := by
    refine ⟨{ e with map_app' := fun v ↦ ?_ }⟩
    rw [hessianQuadraticForm_model_zero, QuadraticMap.weightedSumSquares_apply,
      Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← b.repr.norm_map, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    simp only [LinearEquiv.toFun_eq_coe, he, smul_eq_mul]
    ring
  rw [morseIndex_def, QuadraticForm.sigNeg_of_equiv_weightedSumSquares hequiv]
  have hset : {p : Fin n × Fin d | 2 * (ν p.1 - a) < 0} = {j | ν j < a} ×ˢ univ := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true]
    constructor <;> intro h <;> linarith
  rw [hset, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, mul_comm]

end ProjectiveMomentChart

/-! ### The moment function on projective space -/

open Projectivization ProjectiveMomentChart

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The homogeneous expression of the moment function is invariant under nonzero scalars. -/
private theorem momentQuotient_smul (w : Fin (n + 1) → ℝ) {t : 𝕜} (ht : t ≠ 0)
    (v : Fin (n + 1) → 𝕜) :
    (∑ i, w i * ‖(t • v) i‖ ^ 2) / ∑ i, ‖(t • v) i‖ ^ 2 =
      (∑ i, w i * ‖v i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2 := by
  simp only [Pi.smul_apply, norm_smul, mul_pow]
  rw [← Finset.mul_sum, show ∑ i, w i * (‖t‖ ^ 2 * ‖v i‖ ^ 2) = ‖t‖ ^ 2 * ∑ i, w i * ‖v i‖ ^ 2 by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring]
  exact mul_div_mul_left _ _ (by positivity)

variable (𝕜) in
/-- The **moment function** with weights `w` on the projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`,
sending the line through `v` to `(∑ i, w i * ‖v i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2`. Over `ℂ` with integer
weights it is, up to an affine change of the values, the moment map of the circle acting on `ℂℙⁿ`
with these weights. -/
def projectiveMomentFunction (w : Fin (n + 1) → ℝ) : ℙ 𝕜 (Fin (n + 1) → 𝕜) → ℝ :=
  Projectivization.lift
    (fun v ↦ (∑ i, w i * ‖(v : Fin (n + 1) → 𝕜) i‖ ^ 2) / ∑ i, ‖(v : Fin (n + 1) → 𝕜) i‖ ^ 2)
    fun v v' t h ↦ by
      have ht : t ≠ 0 := by
        rintro rfl
        exact v.2 (by simpa using h)
      simp only [h, momentQuotient_smul w ht]

@[simp]
theorem projectiveMomentFunction_mk (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → 𝕜) (hv : v ≠ 0) :
    projectiveMomentFunction 𝕜 w (mk 𝕜 v hv) = (∑ i, w i * ‖v i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2 :=
  (rfl)

/-- The denominator `∑ i, ‖v i‖ ^ 2` of the moment function is positive at a nonzero vector. -/
private theorem sum_norm_sq_pos {v : Fin (n + 1) → 𝕜} (hv : v ≠ 0) : 0 < ∑ i, ‖v i‖ ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  exact Finset.sum_pos' (fun j _ ↦ by positivity)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩

/-- The moment function is at least any lower bound `c` of the weights. In particular it is
nonnegative when the weights are. -/
theorem le_projectiveMomentFunction {w : Fin (n + 1) → ℝ} {c : ℝ} (hw : ∀ i, c ≤ w i)
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) : c ≤ projectiveMomentFunction 𝕜 w x := by
  induction x using ind with | h v hv =>
  rw [projectiveMomentFunction_mk, le_div_iff₀ (sum_norm_sq_pos hv), Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hw i) (by positivity)

/-- The moment function is at most any upper bound `c` of the weights. -/
theorem projectiveMomentFunction_le {w : Fin (n + 1) → ℝ} {c : ℝ} (hw : ∀ i, w i ≤ c)
    (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) : projectiveMomentFunction 𝕜 w x ≤ c := by
  induction x using ind with | h v hv =>
  rw [projectiveMomentFunction_mk, div_le_iff₀ (sum_norm_sq_pos hv), Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hw i) (by positivity)

/-- Outside the affine open `v k ≠ 0`, the moment function is at least any lower bound `c` of the
weights other than `w k`. -/
theorem le_projectiveMomentFunction_of_notMem_affineOpen {w : Fin (n + 1) → ℝ} {k : Fin (n + 1)}
    {c : ℝ} (hw : ∀ i, i ≠ k → c ≤ w i) {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hx : x ∉ affineOpen k) :
    c ≤ projectiveMomentFunction 𝕜 w x := by
  induction x using ind with | h v hv =>
  rw [mk_mem_affineOpen_iff, not_not] at hx
  rw [projectiveMomentFunction_mk, le_div_iff₀ (sum_norm_sq_pos hv), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rcases eq_or_ne i k with rfl | hi
  · simp [hx]
  · exact mul_le_mul_of_nonneg_right (hw i hi) (by positivity)

/-- Outside the affine open `v k ≠ 0`, the moment function is greater than any strict lower bound
`c` of the weights other than `w k`. -/
theorem lt_projectiveMomentFunction_of_notMem_affineOpen {w : Fin (n + 1) → ℝ} {k : Fin (n + 1)}
    {c : ℝ} (hw : ∀ i, i ≠ k → c < w i) {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hx : x ∉ affineOpen k) :
    c < projectiveMomentFunction 𝕜 w x := by
  induction x using ind with | h v hv =>
  rw [mk_mem_affineOpen_iff, not_not] at hx
  rw [projectiveMomentFunction_mk, lt_div_iff₀ (sum_norm_sq_pos hv), Finset.mul_sum]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have hik : i ≠ k := by
    rintro rfl
    exact hi hx
  refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _,
    mul_lt_mul_of_pos_right (hw i hik) (pow_pos (norm_pos_iff.2 hi) 2)⟩
  rcases eq_or_ne j k with rfl | hj
  · simp [hx]
  · exact mul_le_mul_of_nonneg_right (hw j hj).le (by positivity)

/-- In the affine chart at the coordinate `k`, the moment function with weights `w` is the chart
model with `a = w k` and `ν = w ∘ k.succAbove`. -/
theorem projectiveMomentFunction_comp_affineChart_symm (w : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    projectiveMomentFunction 𝕜 w ∘ (affineChart k).symm = model 𝕜 (w k) (w ∘ k.succAbove) := by
  ext z
  simp [model_apply, Fin.sum_univ_succAbove _ k]

/-- The moment function takes the value `w k` at the coordinate point `[eₖ]`. -/
theorem projectiveMomentFunction_mk_single (w : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    projectiveMomentFunction 𝕜 w (mk 𝕜 (Pi.single k 1) (by simp)) = w k := by
  rw [← affineChart_symm_zero, ← comp_apply (f := projectiveMomentFunction 𝕜 w),
    projectiveMomentFunction_comp_affineChart_symm, model_zero]

/-- **Contractible sublevels.** If `w k ≤ c` and every other weight is greater than `c`, the
sublevel `{f ≤ c}` of the moment function with weights `w` is contractible. -/
theorem contractibleSpace_sublevel_projectiveMomentFunction {w : Fin (n + 1) → ℝ}
    {k : Fin (n + 1)} {c : ℝ} (hwk : w k ≤ c) (hw : ∀ i, i ≠ k → c < w i) :
    ContractibleSpace {x : ℙ 𝕜 (Fin (n + 1) → 𝕜) | projectiveMomentFunction 𝕜 w x ≤ c} := by
  -- The sublevel lies in the affine open `v k ≠ 0`, and in the chart at `k` it is star-convex
  -- about the origin, the coordinate point `[eₖ]`.
  set f := projectiveMomentFunction 𝕜 w
  set e := affineOpenPartialHomeomorph (K := 𝕜) (n := n) k
  have hsub : {x | f x ≤ c} ⊆ e.source := fun x hx ↦ by
    by_contra h
    exact absurd hx (not_le.2 (lt_projectiveMomentFunction_of_notMem_affineOpen hw
      (by simpa [e] using h)))
  have himage : e '' {x | f x ≤ c} = {z | f ((affineChart k).symm z) ≤ c} := by
    rw [e.image_eq_target_inter_inv_preimage hsub]
    simp [e]
  -- In the chart, `f z ≤ c` reads `∑ⱼ (νⱼ - c) ‖zⱼ‖² ≤ c - w k` with every `νⱼ - c > 0`, which is
  -- preserved by scaling `z` towards the origin.
  have hstar : StarConvex ℝ 0 {z | f ((affineChart k).symm z) ≤ c} := by
    intro z hz a b ha hb hab
    simp only [mem_ofPred_eq, smul_zero, zero_add] at hz ⊢
    rw [← Function.comp_apply (f := f), projectiveMomentFunction_comp_affineChart_symm,
      model_apply, div_le_iff₀ (by positivity)] at hz ⊢
    simp only [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Function.comp_apply]
    have hν : c * ∑ j, ‖z j‖ ^ 2 ≤ ∑ j, w (k.succAbove j) * ‖z j‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_right (hw _ (Fin.succAbove_ne k j)).le (by positivity)
    have hb1 : b ^ 2 ≤ 1 := by nlinarith
    rw [← Finset.mul_sum, show ∑ j, w (k.succAbove j) * (b ^ 2 * ‖z j‖ ^ 2) =
      b ^ 2 * ∑ j, w (k.succAbove j) * ‖z j‖ ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring]
    simp only [Function.comp_apply] at hz
    nlinarith [mul_le_mul_of_nonneg_right hb1 (sub_nonneg.2 hν)]
  have hne : {z | f ((affineChart (K := 𝕜) (n := n) k).symm z) ≤ c}.Nonempty :=
    ⟨0, by
      rw [mem_ofPred_eq, affineChart_symm_zero]
      exact (projectiveMomentFunction_mk_single w k).trans_le hwk⟩
  have := hstar.contractibleSpace hne
  exact (e.homeomorphOfImageSubsetSource hsub himage).contractibleSpace

private theorem projectiveMomentFunction_comp_extend_symm (w : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    projectiveMomentFunction 𝕜 w ∘ ((affineOpenPartialHomeomorph k).extend 𝓘(ℝ, Fin n → 𝕜)).symm =
      model 𝕜 (w k) (w ∘ k.succAbove) := by
  ext z
  simpa only [OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm, comp_apply,
    id_eq, coe_affineOpenPartialHomeomorph_symm] using
    congrFun (projectiveMomentFunction_comp_affineChart_symm w k) z

/-- The moment function is smooth for the underlying real manifold structure of projective
space. -/
theorem contMDiff_projectiveMomentFunction (w : Fin (n + 1) → ℝ) {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin n → 𝕜) 𝓘(ℝ) r (projectiveMomentFunction 𝕜 w) := by
  intro x
  obtain ⟨k, hk⟩ := exists_mem_affineOpen x
  rw [contMDiffAt_iff_contDiffAt_comp_extend_symm (affineOpenPartialHomeomorph_mem_maximalAtlas k)
    (by simpa using hk), projectiveMomentFunction_comp_extend_symm]
  exact (contDiff_model _ _).contDiffAt

private theorem mk_single_mem_source (k : Fin (n + 1)) :
    mk 𝕜 (Pi.single k 1) (by simp) ∈ (affineOpenPartialHomeomorph (K := 𝕜) k).source := by
  simp

/-- Every coordinate point `[eₖ]` is a critical point of the moment function. -/
theorem mk_single_mem_criticalPoints_projectiveMomentFunction (w : Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) :
    mk 𝕜 (Pi.single k 1) (by simp) ∈
      criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) := by
  rw [mem_criticalPoints, mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
    (affineOpenPartialHomeomorph_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → 𝕜)) k)
    (mk_single_mem_source k),
    projectiveMomentFunction_comp_extend_symm, affineOpenPartialHomeomorph_extend_mk_single]
  exact fderiv_model_zero _ _

/-- If the weight `w k` is simple, the only critical point of the moment function in the affine
open where the `k`-th coordinate is nonzero is the coordinate point `[eₖ]`. -/
theorem mem_criticalPoints_projectiveMomentFunction_iff {w : Fin (n + 1) → ℝ} {k : Fin (n + 1)}
    (hk : ∀ i, i ≠ k → w i ≠ w k) {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hx : x ∈ affineOpen k) :
    x ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ↔
      x = mk 𝕜 (Pi.single k 1) (by simp) := by
  have hs : x ∈ (affineOpenPartialHomeomorph (K := 𝕜) k).source := by simpa using hx
  rw [mem_criticalPoints, mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
    (affineOpenPartialHomeomorph_mem_maximalAtlas k) hs,
    projectiveMomentFunction_comp_extend_symm,
    fderiv_model_eq_zero_iff (ν := w ∘ k.succAbove) fun j ↦ hk _ (Fin.succAbove_ne k j),
    affineOpenPartialHomeomorph_extend_apply]
  constructor
  · intro h
    rw [← affineChart_symm_zero, ← h]
    exact ((affineChart k).left_inv (by simpa using hx)).symm
  · rintro rfl
    exact affineChart_mk_single k

/-- **The critical points of the moment function are its eigenlines.** For arbitrary weights, the
line through `v` is a critical point exactly when `v` is an eigenvector of the diagonal form with
weights `w`: every nonzero coordinate `v j` carries the weight `w j` equal to the value at `[v]`. -/
theorem mk_mem_criticalPoints_projectiveMomentFunction_iff {w : Fin (n + 1) → ℝ}
    {v : Fin (n + 1) → 𝕜} (hv : v ≠ 0) :
    mk 𝕜 v hv ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ↔
      ∀ j, v j = 0 ∨ w j = projectiveMomentFunction 𝕜 w (mk 𝕜 v hv) := by
  -- Work in the affine chart at a coordinate `k` where `v` is nonzero.
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
  rw [Pi.zero_apply] at hk
  have hx : mk 𝕜 v hv ∈ affineOpen k := (mk_mem_affineOpen_iff k v hv).2 hk
  have hs : mk 𝕜 v hv ∈ (affineOpenPartialHomeomorph (K := 𝕜) k).source := by simpa using hx
  have hval : projectiveMomentFunction 𝕜 w (mk 𝕜 v hv) =
      model 𝕜 (w k) (w ∘ k.succAbove) (affineChart k (mk 𝕜 v hv)) := by
    rw [← projectiveMomentFunction_comp_affineChart_symm, comp_apply,
      (affineChart k).left_inv (by simpa using hx)]
  have hz (j : Fin n) : affineChart k (mk 𝕜 v hv) j = 0 ↔ v (k.succAbove j) = 0 := by
    simp [affineChart_mk, hk]
  rw [mem_criticalPoints, mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
    (affineOpenPartialHomeomorph_mem_maximalAtlas k) hs,
    projectiveMomentFunction_comp_extend_symm, fderiv_model_eq_zero_iff_forall,
    affineOpenPartialHomeomorph_extend_apply, Fin.forall_iff_succAbove k]
  simp only [hk, false_or, comp_apply]
  constructor
  · intro h
    -- Every nonzero coordinate carries the weight `w k`, so the value at `[v]` is `w k`.
    have hm := model_eq_of_forall (𝕜 := 𝕜) (ν := w ∘ k.succAbove) h
    simp only [hval, hm, true_and]
    exact (fun j ↦ (h j).imp_left (hz j).1)
  · rintro ⟨hf, h⟩ j
    rw [← hf] at h
    exact (h j).imp_left (hz j).2

/-- **The critical points of the moment function.** For pairwise distinct weights, the critical
points of the moment function are exactly the `n + 1` coordinate points `[eₖ]`. -/
theorem criticalPoints_projectiveMomentFunction {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) =
      range fun k ↦ mk 𝕜 (Pi.single k 1 : Fin (n + 1) → 𝕜) (by simp) := by
  ext x
  obtain ⟨k, hk⟩ := exists_mem_affineOpen x
  rw [mem_criticalPoints_projectiveMomentFunction_iff (fun i hi ↦ hw.ne hi) hk]
  constructor
  · rintro rfl
    exact ⟨k, rfl⟩
  · rintro ⟨k', rfl⟩
    rw [(mk_single_mem_affineOpen_iff k' k).mp hk]

/-- At a coordinate point `[eₖ]` whose weight `w k` is simple, the moment function has a
nondegenerate critical point. -/
theorem isManifoldNondegenerateCriticalPoint_projectiveMomentFunction {w : Fin (n + 1) → ℝ}
    {k : Fin (n + 1)} (hk : ∀ i, i ≠ k → w i ≠ w k) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w)
      (mk 𝕜 (Pi.single k 1) (by simp)) := by
  rw [isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas
    (affineOpenPartialHomeomorph_mem_maximalAtlas k) (mk_single_mem_source k),
    projectiveMomentFunction_comp_extend_symm, affineOpenPartialHomeomorph_extend_mk_single]
  exact isNondegenerateCriticalPoint_model_zero fun j ↦ hk _ (Fin.succAbove_ne k j)

/-- The coordinate point `[eₖ]` is a nondegenerate critical point of the moment function exactly
when the weight `w k` is simple. -/
theorem isManifoldNondegenerateCriticalPoint_projectiveMomentFunction_iff {w : Fin (n + 1) → ℝ}
    {k : Fin (n + 1)} :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w)
        (mk 𝕜 (Pi.single k 1) (by simp)) ↔
      ∀ i, i ≠ k → w i ≠ w k := by
  rw [isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas
    (affineOpenPartialHomeomorph_mem_maximalAtlas k) (mk_single_mem_source k),
    projectiveMomentFunction_comp_extend_symm, affineOpenPartialHomeomorph_extend_mk_single,
    isNondegenerateCriticalPoint_model_zero_iff]
  simp [Fin.forall_iff_succAbove k, Fin.succAbove_ne]

/-- **The Morse index of the moment function.** At the coordinate point `[eₖ]` the Morse index of
the moment function is the real dimension of `𝕜` times the number of weights below `w k`. Over `ℂ`
this is twice that number. -/
theorem manifoldMorseIndex_projectiveMomentFunction (w : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w)
      (mk 𝕜 (Pi.single k 1) (by simp)) = Module.finrank ℝ 𝕜 * {i | w i < w k}.ncard := by
  rw [manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas
    (affineOpenPartialHomeomorph_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → 𝕜)) k)
    (mk_single_mem_source k) ((contMDiff_projectiveMomentFunction w) _)
    (mem_criticalPoints.mp (mk_single_mem_criticalPoints_projectiveMomentFunction (𝕜 := 𝕜) w k)),
    projectiveMomentFunction_comp_extend_symm, affineOpenPartialHomeomorph_extend_mk_single,
    morseIndex_model_zero]
  -- The weights below `w k` all sit at indices other than `k`.
  have himage : k.succAbove '' {j | (w ∘ k.succAbove) j < w k} = {i | w i < w k} := by
    ext i
    simp only [mem_image, mem_ofPred_eq, comp_apply]
    refine ⟨fun ⟨_, hj, hji⟩ ↦ hji ▸ hj, fun hi ↦ ?_⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (x := i) (y := k) fun h ↦ (h ▸ hi).false
    exact ⟨j, hi, rfl⟩
  rw [← himage, Fin.succAbove_right_injective.injOn.ncard_image]

/-- For pairwise distinct weights the moment function is a Morse function. -/
theorem isMorse_projectiveMomentFunction {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    IsMorse 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) := by
  rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints]
  refine ⟨(contMDiff_projectiveMomentFunction w).contMDiffOn, fun x _ hx ↦ ?_⟩
  rw [criticalPoints_projectiveMomentFunction hw] at hx
  obtain ⟨k, rfl⟩ := hx
  exact isManifoldNondegenerateCriticalPoint_projectiveMomentFunction fun i hi ↦ hw.ne hi

/-- **The moment function is Morse exactly when the weights are pairwise distinct.** -/
theorem isMorse_projectiveMomentFunction_iff {w : Fin (n + 1) → ℝ} :
    IsMorse 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ↔ Injective w := by
  refine ⟨fun h i k hik ↦ ?_, isMorse_projectiveMomentFunction⟩
  by_contra hne
  exact isManifoldNondegenerateCriticalPoint_projectiveMomentFunction_iff.1
    (h.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (mk_single_mem_criticalPoints_projectiveMomentFunction w k)) i hne hik

/-- For pairwise distinct weights the moment function has exactly `n + 1` critical points. -/
theorem totalCriticalCount_projectiveMomentFunction {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    totalCriticalCount 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) = n + 1 := by
  rw [totalCriticalCount_def, criticalPoints_projectiveMomentFunction hw,
    mk_single_injective.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  norm_cast

/-- For pairwise distinct weights, the number of critical points of index `j` of the moment
function is the number of coordinates `k` with `j` equal to the real dimension of `𝕜` times the
number of weights below `w k`. -/
theorem criticalCount_projectiveMomentFunction {w : Fin (n + 1) → ℝ} (hw : Injective w) (j : ℕ) :
    criticalCount 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) j =
      {k | Module.finrank ℝ 𝕜 * {i | w i < w k}.ncard = j}.encard := by
  rw [criticalCount_def, criticalPoints_projectiveMomentFunction hw,
    ← (mk_single_injective (K := 𝕜) (ι := Fin (n + 1))).encard_image]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_range, mem_image]
  constructor
  · rintro ⟨⟨k, rfl⟩, hx⟩
    exact ⟨k, by rwa [← manifoldMorseIndex_projectiveMomentFunction], rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, rfl⟩, by rwa [manifoldMorseIndex_projectiveMomentFunction]⟩

/-- **Critical counts by index.** For pairwise distinct weights the moment function has exactly
one critical point of index `dim_ℝ 𝕜 * j` for each `j ≤ n`, and none for larger `j`. -/
theorem criticalCount_projectiveMomentFunction_mul {w : Fin (n + 1) → ℝ} (hw : Injective w)
    (j : ℕ) :
    criticalCount 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) (Module.finrank ℝ 𝕜 * j) =
      if j ≤ n then 1 else 0 := by
  simp only [criticalCount_projectiveMomentFunction hw, mul_right_inj' Module.finrank_pos.ne',
    encard_setOf_ncard_setOf_lt_eq hw, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.lt_succ_iff]

/-- For pairwise distinct weights the moment function has no critical point whose index is not of
the form `dim_ℝ 𝕜 * j` with `j ≤ n`. -/
theorem criticalCount_projectiveMomentFunction_eq_zero {w : Fin (n + 1) → ℝ} (hw : Injective w)
    {m : ℕ} (hm : ∀ j ≤ n, Module.finrank ℝ 𝕜 * j ≠ m) :
    criticalCount 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) m = 0 := by
  rw [criticalCount_projectiveMomentFunction hw, encard_eq_zero, eq_empty_iff_forall_notMem]
  refine fun k hk ↦ hm _ (Nat.lt_succ_iff.1 ?_) hk
  simpa using ncard_lt_card (s := {i | w i < w k}) fun h ↦ lt_irrefl (w k) (h.symm ▸ mem_univ k :)

/-- **One critical point of each index on `ℝℙⁿ`.** For pairwise distinct weights the moment
function on real projective space has exactly one critical point of each index `j ≤ n`, and none
of larger index. -/
theorem criticalCount_projectiveMomentFunction_real {w : Fin (n + 1) → ℝ} (hw : Injective w)
    (j : ℕ) :
    criticalCount 𝓘(ℝ, Fin n → ℝ) (projectiveMomentFunction ℝ w) j = if j ≤ n then 1 else 0 := by
  simp only [criticalCount_projectiveMomentFunction hw, Module.finrank_self, one_mul,
    encard_setOf_ncard_setOf_lt_eq hw, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.lt_succ_iff]

/-- For pairwise distinct weights, at most one critical point of the moment function on `ℝℙⁿ` has
a given index. -/
theorem subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real
    {w : Fin (n + 1) → ℝ} (hw : Injective w) (j : ℕ) :
    {x | mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) (projectiveMomentFunction ℝ w) x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, Fin n → ℝ) (projectiveMomentFunction ℝ w) x = j}.Subsingleton := by
  rw [← encard_le_one_iff_subsingleton]
  have h := criticalCount_projectiveMomentFunction_real hw j
  rw [criticalCount_def] at h
  simp only [mem_criticalPoints_iff_mfderiv_eq_zero] at h
  rw [h]
  split_ifs <;> simp

/-! ### The standard weights -/

/-- With the standard weights `w i = i`, the coordinate point `[eₖ]` has Morse index the real
dimension of `𝕜` times `k`. -/
theorem manifoldMorseIndex_projectiveMomentFunction_natCast (k : Fin (n + 1)) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 fun i ↦ ((i : ℕ) : ℝ))
      (mk 𝕜 (Pi.single k 1) (by simp)) = Module.finrank ℝ 𝕜 * k := by
  rw [manifoldMorseIndex_projectiveMomentFunction]
  have hset : {i : Fin (n + 1) | ((i : ℕ) : ℝ) < (k : ℕ)} = ↑(Finset.Iio k) := by
    ext i
    simp only [mem_ofPred_eq, Nat.cast_lt, Finset.coe_Iio, mem_Iio, Fin.lt_def]
  rw [hset, ncard_coe_finset, Fin.card_Iio]

/-- **The Morse index on complex projective space.** For the moment function
`[z] ↦ (∑ j, j * ‖z j‖ ^ 2) / ∑ j, ‖z j‖ ^ 2` on `ℂℙⁿ`, the coordinate point `[eₖ]` has Morse
index `2 * k`. These points are all its critical points
(`TauCeti.criticalPoints_projectiveMomentFunction`), and they are nondegenerate. -/
theorem manifoldMorseIndex_projectiveMomentFunction_natCast_complex (k : Fin (n + 1)) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → ℂ) (projectiveMomentFunction ℂ fun i ↦ ((i : ℕ) : ℝ))
      (mk ℂ (Pi.single k 1) (by simp)) = 2 * k := by
  rw [manifoldMorseIndex_projectiveMomentFunction_natCast, Complex.finrank_real_complex]

/-- **The Morse index on real projective space.** For the moment function
`[v] ↦ (∑ j, j * v j ^ 2) / ∑ j, v j ^ 2` on `ℝℙⁿ`, the coordinate point `[eₖ]` has Morse index
`k`. These points are all its critical points
(`TauCeti.criticalPoints_projectiveMomentFunction`), and they are nondegenerate. -/
theorem manifoldMorseIndex_projectiveMomentFunction_natCast_real (k : Fin (n + 1)) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → ℝ) (projectiveMomentFunction ℝ fun i ↦ ((i : ℕ) : ℝ))
      (mk ℝ (Pi.single k 1) (by simp)) = k := by
  rw [manifoldMorseIndex_projectiveMomentFunction_natCast, Module.finrank_self, one_mul]

/-- A natural number in the band `[q - 1/2, q + 1/2]` is `q`. -/
private theorem natCast_eq_of_mem_Icc {k : ℕ} {q : ℤ}
    (h : (k : ℝ) ∈ Icc ((q : ℝ) - 1 / 2) (((q + 1 : ℤ) : ℝ) - 1 / 2)) : (k : ℤ) = q := by
  obtain ⟨h₁, h₂⟩ := h
  push_cast at h₂
  have h₁' : q - 1 < (k : ℤ) := by exact_mod_cast (show (q : ℝ) - 1 < k by linarith)
  have h₂' : (k : ℤ) < q + 1 := by exact_mod_cast (show (k : ℝ) < q + 1 by linarith)
  omega

/-- With the standard weights `w i = i`, a critical point of the moment function with value in
the band `[q - 1/2, q + 1/2]` is the coordinate point `[e_q]`. -/
theorem exists_eq_mk_single_of_mem_criticalPoints_projectiveMomentFunction_natCast
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} {q : ℤ}
    (hx : x ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 fun i ↦ ((i : ℕ) : ℝ)))
    (hfx : projectiveMomentFunction 𝕜 (fun i ↦ ((i : ℕ) : ℝ)) x ∈
      Icc ((q : ℝ) - 1 / 2) (((q + 1 : ℤ) : ℝ) - 1 / 2)) :
    ∃ k : Fin (n + 1), ((k : ℕ) : ℤ) = q ∧ x = mk 𝕜 (Pi.single k 1) (by simp) := by
  rw [criticalPoints_projectiveMomentFunction (w := fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ))
    (Nat.cast_injective.comp Fin.val_injective)] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [projectiveMomentFunction_mk_single] at hfx
  exact ⟨k, natCast_eq_of_mem_Icc hfx, rfl⟩

/-- **The half-integer cut.** For the moment function `[v] ↦ (∑ i, i * ‖v i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2`
on `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, whose critical points are the coordinate points `[eₖ]` with values
`k`, the half-integers `q - 1/2` form a critical-band cut: the band between `q - 1/2` and
`q + 1/2` is compact and its only possible critical value is `q`. -/
theorem isCriticalBandCut_projectiveMomentFunction_natCast :
    IsCriticalBandCut 𝓘(ℝ, Fin n → 𝕜)
      (projectiveMomentFunction 𝕜 fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ))
      fun q : ℤ ↦ (q : ℝ) - 1 / 2 := by
  refine ⟨fun q ↦ ⟨(isClosed_Icc.preimage
    (contMDiff_projectiveMomentFunction (r := 0) _).continuous).isCompact, q, ?_, ?_⟩⟩
  · push_cast
    constructor <;> linarith
  intro x hx hfx
  obtain ⟨k, hk, rfl⟩ :=
    exists_eq_mk_single_of_mem_criticalPoints_projectiveMomentFunction_natCast hx hfx
  rw [projectiveMomentFunction_mk_single]
  exact_mod_cast hk

/-- With the standard weights `w i = i`, a point outside the affine open `v₀ ≠ 0` has value at
least `1`. -/
theorem one_le_projectiveMomentFunction_natCast {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)}
    (hx : x ∉ affineOpen 0) :
    1 ≤ projectiveMomentFunction 𝕜 (fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ)) x :=
  le_projectiveMomentFunction_of_notMem_affineOpen
    (fun i hi ↦ by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.val_ne_zero_iff.2 hi)) hx

/-- **The sublevels below the second critical value are contractible.** With the standard weights
`w i = i`, for `0 ≤ c < 1` the sublevel `{f ≤ c}` of the moment function on
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` is contractible. -/
theorem contractibleSpace_sublevel_projectiveMomentFunction_natCast {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : c < 1) :
    ContractibleSpace
      {x : ℙ 𝕜 (Fin (n + 1) → 𝕜) |
        projectiveMomentFunction 𝕜 (fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ)) x ≤ c} :=
  contractibleSpace_sublevel_projectiveMomentFunction (k := 0) (by simpa using hc₀)
    fun i hi ↦ hc.trans_le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Fin.val_ne_zero_iff.2 hi))

end TauCeti
