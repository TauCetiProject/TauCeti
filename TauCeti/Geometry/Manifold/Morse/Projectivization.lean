/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.SecondDerivative
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
so the critical points have the distinct even indices `0, 2, …, 2 * n`.

The computation takes place in the standard affine chart at `k`, centred at `[eₖ]`. There the
moment function is the chart model `(w k + ∑ j, ν j * ‖z j‖ ^ 2) / (1 + ∑ j, ‖z j‖ ^ 2)` with
`ν = w ∘ k.succAbove` (`TauCeti.ProjectiveMomentChart.model`). Multiplying out the denominator
shows that its differential at `z` vanishes exactly when `(ν j - r) z j = 0` for every `j`, where
`r` is the value at `z`, and this forces `z = 0` when no `ν j` equals `w k`. The second derivative
at the origin is `2 ∑ j, (ν j - w k) ⟪v j, v' j⟫`. Each coordinate of `𝕜` contributes a
`dim_ℝ 𝕜`-dimensional block of the same sign to its inertia.

## Main declarations

* `TauCeti.projectiveMomentFunction`: the moment function with weights `w`.
* `TauCeti.contMDiff_projectiveMomentFunction`: it is smooth.
* `TauCeti.criticalPoints_projectiveMomentFunction`: for distinct weights its critical points are
  the coordinate points `[eₖ]`.
* `TauCeti.isMorse_projectiveMomentFunction`: for distinct weights it is a Morse function.
* `TauCeti.manifoldMorseIndex_projectiveMomentFunction`: the Morse index at `[eₖ]` is
  `dim_ℝ 𝕜 * #{i | w i < w k}`.
* `TauCeti.totalCriticalCount_projectiveMomentFunction` and
  `TauCeti.criticalCount_projectiveMomentFunction`: the critical counts.
* `TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast_complex`: on `ℂℙⁿ` with the
  standard weights, `[eₖ]` has index `2 * k`.

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

/-- If no weight `ν j` equals `a`, the origin is the only critical point of the chart model. -/
theorem fderiv_model_eq_zero_iff {a : ℝ} {ν : Fin n → ℝ} (hν : ∀ j, ν j ≠ a) {z : Fin n → 𝕜} :
    fderiv ℝ (model 𝕜 a ν) z = 0 ↔ z = 0 := by
  have h := two_smul_weightedInner_eq (𝕜 := 𝕜) a ν z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · set r := model 𝕜 a ν z with hr
    rw [hz, smul_zero, zero_add] at h
    -- Evaluating at `z` gives `∑ ν j ‖z j‖² = r ∑ ‖z j‖²`, which forces `r = a`.
    have hzz := congr($h z)
    simp only [smul_apply, weightedInner_self, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hzz
    have hra : r = a := by
      have := one_add_weightedNormSq_one_mul_model (𝕜 := 𝕜) a ν z
      rw [← hr] at this
      linarith
    -- Evaluating at `Pi.single j (z j)` gives `ν j ‖z j‖² = r ‖z j‖²`, so `z j = 0`.
    funext j
    have hj := congr($h (Pi.single j (z j)))
    simp only [smul_apply, weightedInner_single, smul_eq_mul, Pi.one_apply,
      one_mul, real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat] at hj
    have hzero : (ν j - a) * ‖z j‖ ^ 2 = 0 := by rw [← hra]; linarith
    simpa [sub_ne_zero.mpr (hν j)] using hzero
  · rintro rfl
    exact fderiv_model_zero a ν

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

/-- In the affine chart at the coordinate `k`, the moment function with weights `w` is the chart
model with `a = w k` and `ν = w ∘ k.succAbove`. -/
theorem projectiveMomentFunction_comp_affineChart_symm (w : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    projectiveMomentFunction 𝕜 w ∘ (affineChart k).symm = model 𝕜 (w k) (w ∘ k.succAbove) := by
  ext z
  simp [model_apply, Fin.sum_univ_succAbove _ k]

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
    (mk_single_mem_source k)
    ((contMDiff_projectiveMomentFunction w (r := 1)) _ |>.mdifferentiableAt one_ne_zero),
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
    (affineOpenPartialHomeomorph_mem_maximalAtlas k) hs
    ((contMDiff_projectiveMomentFunction w (r := 1)) x |>.mdifferentiableAt one_ne_zero),
    projectiveMomentFunction_comp_extend_symm,
    fderiv_model_eq_zero_iff (ν := w ∘ k.succAbove) fun j ↦ hk _ (Fin.succAbove_ne k j),
    affineOpenPartialHomeomorph_extend_apply]
  constructor
  · intro h
    rw [← affineChart_symm_zero, ← h]
    exact ((affineChart k).left_inv (by simpa using hx)).symm
  · rintro rfl
    exact affineChart_mk_single k

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
    refine ⟨fun ⟨j, hj, hji⟩ ↦ hji ▸ hj, fun hi ↦ ?_⟩
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

end TauCeti
