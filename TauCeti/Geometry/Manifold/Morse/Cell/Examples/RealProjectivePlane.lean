/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import TauCeti.Geometry.Manifold.Morse.Projectivization
import TauCeti.Geometry.Sphere.Circle

/-!
# Morse cells of the real projective plane

The function `f[x : y : z] = (y² + 2z²) / (x² + y² + z²)` on `ℝℙ² = ℙ ℝ (Fin 3 → ℝ)` is the
projective moment function `TauCeti.projectiveMomentFunction ℝ ![0, 1, 2]`. Its maximum is the
point `[0 : 0 : 1]`, at the level `2`, of index `2`. This file works out the top cell of `ℝℙ²`
attached there, for every width `0 < ε < 1`, in two normal-form charts, as a test of the attaching
maps `OpenPartialHomeomorph.morseAttachingMap` and the cell attachments
`TauCeti.morseCellAttachment` on a compact manifold whose lower sublevel is not simply connected.

The normalized chart `TauCeti.realProjPlaneTopChart` sends `[x : y : z]`, `z ≠ 0`, to

`w = (√2 x / z, y / z) / √(1 + (x / z)² + (y / z)²)`,

an open partial homeomorphism onto the ellipse `{w₀² / 2 + w₁² < 1}` in which `f = 2 - w₀² - w₁²`.
Its inverse is `w ↦ [w₀ / √2 : w₁ : √(1 - w₀² / 2 - w₁²)]`. For `ε < 1` the closed ball of radius
`√ε` fits in the chart, and `[0 : 0 : 1]` is the only critical point in the band
`f⁻¹[2 - ε, 2 + ε]`, which is compact since `ℝℙ²` is. The attaching map of this chart is

`α₊(s) = [√ε s₀ / √2 : √ε s₁ : √(1 - ε (s₀² / 2 + s₁²))]`,

a map of the circle `∂D²` into the lower sublevel `{f ≤ 2 - ε}`, a Möbius band around the
projective line `{z = 0}`. The opposite chart `TauCeti.realProjPlaneTopReflChart` reflects
the first coordinate, `r(w₀, w₁) = (-w₀, w₁)`. Its attaching and characteristic maps are strictly
`α₋ = α₊ ∘ r` and `χ₋ = χ₊ ∘ r`, so the identity of `{f ≤ 2 - ε}` together with `r` on the disc is a
homeomorphism between the two cell attachments relative to the lower sublevel, intertwining the
handle-to-cell comparisons into `{f ≤ 2 + ε}`.

The two attaching maps are nevertheless not homotopic. They are told apart by the **core angle**
`ρ[x : y : z] = (x + i y)² / (x² + y²)` on `ℝℙ² \ {[0 : 0 : 1]} = {f < 2}`
(`TauCeti.realProjPlaneCoreAngle`): the retraction onto the core `{z = 0} ≅ ℝℙ¹` followed by
`ℝℙ¹ ≅ S¹`. The **core degree** of a map `∂D² → {f < 2}` is the degree of its composite with `ρ`,
with `∂D²` run through counterclockwise in the normalized negative coordinates
(`TauCeti.realProjPlaneCoreDegree`); it is a homotopy invariant. The core circle
`θ ↦ [cos θ : sin θ : 0]`, `0 ≤ θ ≤ π`, has core degree `1`, while `α₊` has core degree `2` and
`α₋` has core degree `-2`: going once around `∂D²`, the boundary of the top cell runs twice
around the core of the Möbius band, in opposite directions for the two charts.

## Main results

* `TauCeti.realProjPlaneTopChart`, `TauCeti.realProjPlaneTopReflChart` and
  `TauCeti.projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart`: the two
  normalized charts at `[0 : 0 : 1]`, in which `f = 2 - w₀² - w₁²`.
* `TauCeti.criticalPoints_projectiveMomentFunction_inter_preimage_Icc`: every width `0 ≤ ε < 1` is
  admissible.
* `TauCeti.coe_morseAttachingMap_realProjPlaneTopChart_apply` and
  `TauCeti.realProjPlaneTopChart_symm_apply_of_lt`: the attaching map `α₊` explicitly.
* `TauCeti.morseAttachingMap_realProjPlaneTopReflChart`,
  `TauCeti.morseCharacteristicMap_realProjPlaneTopReflChart` and
  `TauCeti.exists_iso_morseCellAttachment_realProjPlaneTopReflChart_realProjPlaneTopChart`:
  `α₋ = α₊ ∘ r` and `χ₋ = χ₊ ∘ r` strictly, and the resulting homeomorphism of cell attachments
  relative to `{f ≤ 2 - ε}`.
* `TauCeti.realProjPlaneCoreDegree_eq_of_homotopic` and
  `TauCeti.realProjPlaneCoreDegree_realProjPlaneCoreMap`: the core degree is a homotopy
  invariant, and the core circle has core degree `1`.
* `TauCeti.realProjPlaneCoreDegree_morseAttachingMap_realProjPlaneTopChart` and
  `TauCeti.realProjPlaneCoreDegree_morseAttachingMap_realProjPlaneTopReflChart`: `α₊`
  and `α₋` have core degrees `2` and `-2`.
* `TauCeti.not_homotopic_morseAttachingMap_realProjPlaneTopChart_realProjPlaneTopReflChart`:
  `α₊` and `α₋` are not homotopic.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Lemma 3.6.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.42 (cellular
  homology of `ℝℙⁿ`: the attaching map of the top cell of `ℝℙ²` has degree `2` onto the core
  circle).
-/

public section

noncomputable section

open Set Metric Projectivization CategoryTheory Complex
open scoped LinearAlgebra.Projectivization Manifold ComplexConjugate

namespace TauCeti

/-! ### The normalized chart at the top point -/

private theorem ellipse_fwd (a b : ℝ) :
    ((√(1 + a ^ 2 + b ^ 2))⁻¹ * (√2 * a)) ^ 2 / 2 + ((√(1 + a ^ 2 + b ^ 2))⁻¹ * b) ^ 2 =
      1 - (1 + a ^ 2 + b ^ 2)⁻¹ := by
  have hs : 0 < 1 + a ^ 2 + b ^ 2 := by positivity
  rw [mul_pow, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hs.le, Real.sq_sqrt zero_le_two]
  field_simp
  ring

private theorem ellipse_bwd {a b : ℝ} (h : a ^ 2 / 2 + b ^ 2 < 1) :
    1 + ((√(1 - (a ^ 2 / 2 + b ^ 2)))⁻¹ * (a / √2)) ^ 2 +
      ((√(1 - (a ^ 2 / 2 + b ^ 2)))⁻¹ * b) ^ 2 = (1 - (a ^ 2 / 2 + b ^ 2))⁻¹ := by
  have hs : 0 < 1 - (a ^ 2 / 2 + b ^ 2) := by linarith
  rw [mul_pow, mul_pow, div_pow, inv_pow, Real.sq_sqrt hs.le, Real.sq_sqrt zero_le_two]
  linear_combination (-1 : ℝ) * inv_mul_cancel₀ hs.ne'

private theorem continuous_ellipseFun :
    Continuous fun z : Fin 2 → ℝ ↦
      (√(1 + z 0 ^ 2 + z 1 ^ 2))⁻¹ • (!₂[√2 * z 0, z 1] : EuclideanSpace ℝ (Fin 2)) := by
  have h (z : Fin 2 → ℝ) : √(1 + z 0 ^ 2 + z 1 ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hv : Continuous fun z : Fin 2 → ℝ ↦ (!₂[√2 * z 0, z 1] : EuclideanSpace ℝ (Fin 2)) :=
    (PiLp.continuous_toLp 2 _).comp (by fun_prop)
  have hs : Continuous fun z : Fin 2 → ℝ ↦ √(1 + z 0 ^ 2 + z 1 ^ 2) := by fun_prop
  exact (hs.inv₀ h).smul hv

private theorem continuousOn_ellipseInv :
    ContinuousOn (fun w : EuclideanSpace ℝ (Fin 2) ↦
      (√(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)))⁻¹ • (![w 0 / √2, w 1] : Fin 2 → ℝ))
      {w | w 0 ^ 2 / 2 + w 1 ^ 2 < 1} := by
  intro w hw
  have hw' : w 0 ^ 2 / 2 + w 1 ^ 2 < 1 := hw
  have h : √(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hw')).ne'
  have hv : Continuous fun w : EuclideanSpace ℝ (Fin 2) ↦ (![w 0 / √2, w 1] : Fin 2 → ℝ) :=
    by fun_prop
  have hs : Continuous fun w : EuclideanSpace ℝ (Fin 2) ↦ √(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)) := by
    fun_prop
  exact ((hs.continuousAt.inv₀ h).smul hv.continuousAt).continuousWithinAt

/-- The change of coordinates `z ↦ (√2 z₀, z₁) / √(1 + z₀² + z₁²)` from the affine plane onto the
open ellipse `{w | w₀² / 2 + w₁² < 1}` of `ℝ²`, with inverse
`w ↦ (w₀ / √2, w₁) / √(1 - w₀² / 2 - w₁²)`. Read in the affine chart `z = (x / z, y / z)` of
`ℝℙ²` at `[0 : 0 : 1]`, it gives the normalized coordinates in which
`(y² + 2z²) / (x² + y² + z²) = 2 - w₀² - w₁²`. -/
def realProjPlaneTopCoord : OpenPartialHomeomorph (Fin 2 → ℝ) (EuclideanSpace ℝ (Fin 2))
    where
  toFun z := (√(1 + z 0 ^ 2 + z 1 ^ 2))⁻¹ • !₂[√2 * z 0, z 1]
  invFun w := (√(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)))⁻¹ • ![w 0 / √2, w 1]
  source := univ
  target := {w | w 0 ^ 2 / 2 + w 1 ^ 2 < 1}
  map_source' z _ := by
    have : 0 < (1 + z 0 ^ 2 + z 1 ^ 2)⁻¹ := by positivity
    simp only [mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, ellipse_fwd]
    linarith
  map_target' _ _ := mem_univ _
  left_inv' z _ := by
    have hs : 0 < 1 + z 0 ^ 2 + z 1 ^ 2 := by positivity
    have hs' : √(1 + z 0 ^ 2 + z 1 ^ 2) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    have h2 : √2 ≠ 0 := by positivity
    simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      ellipse_fwd, sub_sub_cancel, Real.sqrt_inv, inv_inv]
    ext j
    fin_cases j <;> simp <;> field_simp
  right_inv' w hw := by
    have hw' : w 0 ^ 2 / 2 + w 1 ^ 2 < 1 := hw
    have hs : 0 < 1 - (w 0 ^ 2 / 2 + w 1 ^ 2) := sub_pos.2 hw'
    have hs' : √(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    have h2 : √2 ≠ 0 := by positivity
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, Pi.smul_apply,
      ellipse_bwd hw', Real.sqrt_inv, inv_inv]
    ext j
    fin_cases j <;> simp [h2, hs', mul_comm (√2), mul_assoc]
  open_source := isOpen_univ
  open_target := isOpen_lt (by fun_prop) continuous_const
  continuousOn_toFun := continuous_ellipseFun.continuousOn
  continuousOn_invFun := continuousOn_ellipseInv

@[simp]
theorem realProjPlaneTopCoord_apply (z : Fin 2 → ℝ) :
    realProjPlaneTopCoord z = (√(1 + z 0 ^ 2 + z 1 ^ 2))⁻¹ • !₂[√2 * z 0, z 1] :=
  (rfl)

@[simp]
theorem realProjPlaneTopCoord_symm_apply (w : EuclideanSpace ℝ (Fin 2)) :
    realProjPlaneTopCoord.symm w =
      (√(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)))⁻¹ • ![w 0 / √2, w 1] :=
  (rfl)

@[simp]
theorem realProjPlaneTopCoord_source : realProjPlaneTopCoord.source = univ :=
  (rfl)

@[simp]
theorem realProjPlaneTopCoord_target :
    realProjPlaneTopCoord.target = {w | w 0 ^ 2 / 2 + w 1 ^ 2 < 1} :=
  (rfl)

/-- The normalized Morse chart of `f[x : y : z] = (y² + 2z²) / (x² + y² + z²)` on `ℝℙ²` at its
maximum `[0 : 0 : 1]`: on the affine open `{z ≠ 0}` it is
`[x : y : z] ↦ (√2 x / z, y / z) / √(1 + (x / z)² + (y / z)²)`, with values in the open ellipse
`{w | w₀² / 2 + w₁² < 1}`. In it `f = 2 - w₀² - w₁²`
(`TauCeti.projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart`). -/
def realProjPlaneTopChart :
    OpenPartialHomeomorph (ℙ ℝ (Fin 3 → ℝ)) (EuclideanSpace ℝ (Fin 2)) :=
  (affineOpenPartialHomeomorph 2).trans realProjPlaneTopCoord

@[simp]
theorem realProjPlaneTopChart_source :
    realProjPlaneTopChart.source = affineOpen 2 := by
  simp [realProjPlaneTopChart]

@[simp]
theorem realProjPlaneTopChart_target :
    realProjPlaneTopChart.target = {w | w 0 ^ 2 / 2 + w 1 ^ 2 < 1} := by
  simp [realProjPlaneTopChart]

theorem realProjPlaneTopChart_apply (x : ℙ ℝ (Fin 3 → ℝ)) :
    realProjPlaneTopChart x = realProjPlaneTopCoord (affineChart 2 x) := by
  rw [realProjPlaneTopChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    coe_affineOpenPartialHomeomorph]

theorem realProjPlaneTopChart_symm_apply (w : EuclideanSpace ℝ (Fin 2)) :
    realProjPlaneTopChart.symm w =
      (affineChart 2).symm (realProjPlaneTopCoord.symm w) := by
  rw [realProjPlaneTopChart, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
    coe_affineOpenPartialHomeomorph_symm]

/-- The centre of the chart is the maximum `[0 : 0 : 1]`. -/
@[simp]
theorem realProjPlaneTopChart_symm_zero :
    realProjPlaneTopChart.symm 0 = mk ℝ (Pi.single 2 1) (by simp) := by
  rw [realProjPlaneTopChart_symm_apply, ← affineChart_symm_zero]
  congr 1
  ext j
  fin_cases j <;> simp

/-- In the affine chart at `[0 : 0 : 1]` the function is `(2 + z₁²) / (1 + z₀² + z₁²)`. -/
private theorem projectiveMomentFunction_affineChart_symm (z : Fin 2 → ℝ) :
    projectiveMomentFunction ℝ ![0, 1, 2] ((affineChart 2).symm z) =
      (2 + z 1 ^ 2) / (1 + z 0 ^ 2 + z 1 ^ 2) := by
  rw [← Function.comp_apply (f := projectiveMomentFunction ℝ ![0, 1, 2]),
    projectiveMomentFunction_comp_affineChart_symm, ProjectiveMomentChart.model_apply]
  simp [Fin.sum_univ_two, Fin.succAbove]
  ring

/-- **Normal form at the maximum.** In the chart `TauCeti.realProjPlaneTopChart`,
`f[x : y : z] = (y² + 2z²) / (x² + y² + z²)` is `2 - w₀² - w₁²`, so `[0 : 0 : 1]` is a critical
point of index `2` at the level `2`. -/
theorem projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart :
    ∀ y ∈ realProjPlaneTopChart.source, projectiveMomentFunction ℝ ![0, 1, 2] y =
      2 + ∑ j : Fin 2, (if j.val < 2 then -1 else 1) * realProjPlaneTopChart y j ^ 2 := by
  intro y hy
  obtain ⟨z, rfl⟩ : ∃ z, (affineChart 2).symm z = y :=
    ⟨affineChart 2 y, (affineChart 2).left_inv (by simpa using hy)⟩
  have hs : 0 < 1 + z 0 ^ 2 + z 1 ^ 2 := by positivity
  simp only [realProjPlaneTopChart_apply, projectiveMomentFunction_affineChart_symm,
    (affineChart 2).right_inv (by simp : z ∈ (affineChart 2).target), realProjPlaneTopCoord_apply,
    Fin.sum_univ_two]
  simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow,
    inv_pow, Real.sq_sqrt hs.le, Real.sq_sqrt zero_le_two]
  simp
  field_simp
  ring

/-- For `ε < 1` the closed ball of radius `√ε` lies in the target ellipse of the chart, so every
width `ε < 1` fits the chart. -/
theorem closedBall_subset_realProjPlaneTopChart_target {ε : ℝ} (hε : ε < 1) :
    closedBall 0 √ε ⊆ realProjPlaneTopChart.target := by
  intro w hw
  rw [mem_closedBall_zero_iff] at hw
  have hn : w 0 ^ 2 + w 1 ^ 2 < 1 := by
    have h := pow_le_pow_left₀ (norm_nonneg w) hw 2
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs] at h
    exact h.trans_lt (by rw [Real.sq_sqrt']; exact max_lt hε one_pos)
  rw [realProjPlaneTopChart_target, mem_ofPred_eq]
  nlinarith [sq_nonneg (w 0)]

/-- The reflection `(w₀, w₁) ↦ (-w₀, w₁)` of `ℝ²` in the axis spanned by `e₁`, applied to the first
coordinate. -/
@[simp]
private theorem reflection_single_one_apply_zero (w : EuclideanSpace ℝ (Fin 2)) :
    (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection w 0 = -w 0 := by
  rw [Submodule.reflection_singleton_apply]
  simp

@[simp]
private theorem reflection_single_one_apply_one (w : EuclideanSpace ℝ (Fin 2)) :
    (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection w 1 = w 1 := by
  rw [Submodule.reflection_singleton_apply]
  simp [EuclideanSpace.inner_single_left]
  ring

/-- The opposite normalized chart at `[0 : 0 : 1]`: `TauCeti.realProjPlaneTopChart` followed
by the reflection `(w₀, w₁) ↦ (-w₀, w₁)` of the first negative coordinate. -/
def realProjPlaneTopReflChart :
    OpenPartialHomeomorph (ℙ ℝ (Fin 3 → ℝ)) (EuclideanSpace ℝ (Fin 2)) :=
  realProjPlaneTopChart.transHomeomorph
    (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection.toHomeomorph

@[simp]
theorem realProjPlaneTopReflChart_source :
    realProjPlaneTopReflChart.source = affineOpen 2 := by
  simp [realProjPlaneTopReflChart]

theorem realProjPlaneTopReflChart_apply (x : ℙ ℝ (Fin 3 → ℝ)) :
    realProjPlaneTopReflChart x =
      (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection (realProjPlaneTopChart x) :=
  (rfl)

theorem realProjPlaneTopReflChart_symm_apply (w : EuclideanSpace ℝ (Fin 2)) :
    realProjPlaneTopReflChart.symm w =
      realProjPlaneTopChart.symm ((ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection w) := by
  simp [realProjPlaneTopReflChart, Submodule.reflection_symm]

/-- **Normal form at the maximum in the opposite chart.** -/
theorem projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart :
    ∀ y ∈ realProjPlaneTopReflChart.source, projectiveMomentFunction ℝ ![0, 1, 2] y =
      2 + ∑ j : Fin 2, (if j.val < 2 then -1 else 1) * realProjPlaneTopReflChart y j ^ 2 := by
  intro y hy
  rw [projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart y (by simpa using hy)]
  simp [realProjPlaneTopReflChart_apply, Fin.sum_univ_two]

/-- For `ε < 1` the closed ball of radius `√ε` lies in the target of the opposite chart. -/
theorem closedBall_subset_realProjPlaneTopReflChart_target {ε : ℝ} (hε : ε < 1) :
    closedBall 0 √ε ⊆ realProjPlaneTopReflChart.target := by
  intro w hw
  have h := closedBall_subset_realProjPlaneTopChart_target hε
    (by simpa using hw : (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection w ∈ closedBall 0 √ε)
  simpa [realProjPlaneTopReflChart, Submodule.reflection_symm] using h

/-- In homogeneous coordinates the inverse of the chart is
`w ↦ [w₀ / √2 : w₁ : √(1 - w₀² / 2 - w₁²)]` on its target ellipse. -/
theorem realProjPlaneTopChart_symm_apply_of_lt {w : EuclideanSpace ℝ (Fin 2)}
    (hw : w 0 ^ 2 / 2 + w 1 ^ 2 < 1) :
    realProjPlaneTopChart.symm w = mk ℝ ![w 0 / √2, w 1, √(1 - (w 0 ^ 2 / 2 + w 1 ^ 2))]
      (fun h ↦ (Real.sqrt_pos.2 (sub_pos.2 hw)).ne' (by simpa using congrFun h 2)) := by
  have hs : 0 < √(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)) := Real.sqrt_pos.2 (sub_pos.2 hw)
  rw [realProjPlaneTopChart_symm_apply, affineChart_symm_apply, mk_eq_mk_iff']
  refine ⟨(√(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)))⁻¹, ?_⟩
  ext j
  fin_cases j <;> simp [Fin.insertNth, Fin.succAboveCases, hs.ne', mul_comm]

/-! ### Admissibility of the widths `0 ≤ ε < 1` -/

private theorem injective_weights : Function.Injective (![0, 1, 2] : Fin 3 → ℝ) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num at h <;> rfl

/-- For `0 ≤ ε < 1` the only critical point of `f[x : y : z] = (y² + 2z²) / (x² + y² + z²)` in the
band `f⁻¹[2 - ε, 2 + ε]` is the maximum `[0 : 0 : 1]`. (The band is compact, as `ℝℙ²` is.) -/
theorem criticalPoints_projectiveMomentFunction_inter_preimage_Icc {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε₁ : ε < 1) :
    criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ ![0, 1, 2]) ∩
        projectiveMomentFunction ℝ ![0, 1, 2] ⁻¹' Icc (2 - ε) (2 + ε) =
      {mk ℝ (Pi.single 2 1) (by simp)} := by
  rw [criticalPoints_projectiveMomentFunction injective_weights]
  ext x
  simp only [mem_inter_iff, mem_range, mem_preimage, mem_Icc, mem_singleton_iff]
  constructor
  · rintro ⟨⟨k, rfl⟩, h₁, h₂⟩
    rw [projectiveMomentFunction_mk_single] at h₁ h₂
    fin_cases k
    · norm_num at h₁; linarith
    · norm_num at h₁; linarith
    · rfl
  · rintro rfl
    refine ⟨⟨2, rfl⟩, ?_⟩
    rw [projectiveMomentFunction_mk_single]
    constructor <;> simp <;> linarith

/-! ### The attaching maps of the top cell -/

section Attaching

variable {ε : ℝ}

/-- The cell parametrization of `TauCeti.realProjPlaneTopChart` is `w ↦ ψ⁻¹(√ε w)`. -/
theorem morseCellMap_realProjPlaneTopChart (w : EuclideanSpace ℝ (Fin 2)) :
    realProjPlaneTopChart.morseCellMap le_rfl ε w =
      realProjPlaneTopChart.symm (√ε • w) := by
  rw [OpenPartialHomeomorph.morseCellMap_def]
  congr 2
  ext j
  simp

/-- The cell parametrization of the opposite chart is that of `TauCeti.realProjPlaneTopChart`
precomposed with the reflection `(w₀, w₁) ↦ (-w₀, w₁)`. -/
theorem morseCellMap_realProjPlaneTopReflChart (w : EuclideanSpace ℝ (Fin 2)) :
    realProjPlaneTopReflChart.morseCellMap le_rfl ε w =
      realProjPlaneTopChart.morseCellMap le_rfl ε
        ((ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection w) := by
  rw [morseCellMap_realProjPlaneTopChart, OpenPartialHomeomorph.morseCellMap_def,
    realProjPlaneTopReflChart_symm_apply, map_smul]
  congr 3
  ext j
  simp

variable (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)

/-- The attaching map `α₊ : ∂D² → {f ≤ 2 - ε}` of the top cell of `ℝℙ²` in the chart
`ψ = TauCeti.realProjPlaneTopChart` is `s ↦ ψ⁻¹(√ε s)`; by
`TauCeti.realProjPlaneTopChart_symm_apply_of_lt` this is the point
`[√ε s₀ / √2 : √ε s₁ : √(1 - ε (s₀² / 2 + s₁²))]`. -/
theorem coe_morseAttachingMap_realProjPlaneTopChart_apply (s : TopCat.diskBoundary.{0} 2) :
    (realProjPlaneTopChart.morseAttachingMap le_rfl hε₀
        (closedBall_subset_realProjPlaneTopChart_target hε₁)
        projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart s :
          ℙ ℝ (Fin 3 → ℝ)) =
      realProjPlaneTopChart.symm (√ε • s.down) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply, morseCellMap_realProjPlaneTopChart]

/-- The attaching maps of the two charts differ strictly by the reflection
`r : (w₀, w₁) ↦ (-w₀, w₁)` of the disc: `α₋ = α₊ ∘ r` on `∂D²`. -/
theorem morseAttachingMap_realProjPlaneTopReflChart :
    realProjPlaneTopReflChart.morseAttachingMap le_rfl hε₀
        (closedBall_subset_realProjPlaneTopReflChart_target hε₁)
        projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart =
      (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection.diskBoundaryIso.hom ≫
        realProjPlaneTopChart.morseAttachingMap le_rfl hε₀
          (closedBall_subset_realProjPlaneTopChart_target hε₁)
          projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart := by
  ext s
  rw [ConcreteCategory.comp_apply, OpenPartialHomeomorph.coe_morseAttachingMap_apply,
    OpenPartialHomeomorph.coe_morseAttachingMap_apply, morseCellMap_realProjPlaneTopReflChart,
    LinearIsometryEquiv.coe_diskBoundaryIso_hom_apply_down]

/-- The characteristic maps of the two charts differ strictly by the same reflection:
`χ₋ = χ₊ ∘ r` on `D²`. -/
theorem morseCharacteristicMap_realProjPlaneTopReflChart :
    realProjPlaneTopReflChart.morseCharacteristicMap le_rfl hε₀
        (closedBall_subset_realProjPlaneTopReflChart_target hε₁)
        projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart =
      (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection.diskIso.hom ≫
        realProjPlaneTopChart.morseCharacteristicMap le_rfl hε₀
          (closedBall_subset_realProjPlaneTopChart_target hε₁)
          projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart := by
  ext w
  rw [ConcreteCategory.comp_apply, OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
    OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
    morseCellMap_realProjPlaneTopReflChart, LinearIsometryEquiv.coe_diskIso_hom_apply_down]

/-- Since `α₋ = α₊ ∘ r` strictly, the map which is the identity on the lower sublevel
`{f ≤ 2 - ε}` and the reflection `r` on the disc is a homeomorphism between the two cell
attachments `{f ≤ 2 - ε} ∪_{α₋} D² ≅ {f ≤ 2 - ε} ∪_{α₊} D²`, relative to the lower sublevel. Since
also `χ₋ = χ₊ ∘ r`, it intertwines the handle-to-cell comparisons into `{f ≤ 2 + ε}`. -/
theorem exists_iso_morseCellAttachment_realProjPlaneTopReflChart_realProjPlaneTopChart :
    ∃ Φ : morseCellAttachment (fun _ : Unit ↦ realProjPlaneTopReflChart) (fun _ ↦ 2)
        (fun _ ↦ le_rfl) hε₀ (fun _ ↦ closedBall_subset_realProjPlaneTopReflChart_target hε₁)
        (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart) ≅
      morseCellAttachment (fun _ : Unit ↦ realProjPlaneTopChart) (fun _ ↦ 2)
        (fun _ ↦ le_rfl) hε₀ (fun _ ↦ closedBall_subset_realProjPlaneTopChart_target hε₁)
        (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart),
      morseCellAttachmentIncl (fun _ : Unit ↦ realProjPlaneTopReflChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε₀
          (fun _ ↦ closedBall_subset_realProjPlaneTopReflChart_target hε₁)
          (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart) ≫
          Φ.hom =
        morseCellAttachmentIncl (fun _ : Unit ↦ realProjPlaneTopChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε₀ (fun _ ↦ closedBall_subset_realProjPlaneTopChart_target hε₁)
          (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart) ∧
      morseCellAttachmentCell (fun _ : Unit ↦ realProjPlaneTopReflChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε₀
          (fun _ ↦ closedBall_subset_realProjPlaneTopReflChart_target hε₁)
          (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart) () ≫
          Φ.hom =
        (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection.diskIso.hom ≫
          morseCellAttachmentCell (fun _ : Unit ↦ realProjPlaneTopChart) (fun _ ↦ 2)
            (fun _ ↦ le_rfl) hε₀ (fun _ ↦ closedBall_subset_realProjPlaneTopChart_target hε₁)
            (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart) () ∧
      Φ.hom ≫ morseCellComparison (fun _ : Unit ↦ realProjPlaneTopChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε₀ (fun _ ↦ closedBall_subset_realProjPlaneTopChart_target hε₁)
          (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart) =
        morseCellComparison (fun _ : Unit ↦ realProjPlaneTopReflChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε₀
          (fun _ ↦ closedBall_subset_realProjPlaneTopReflChart_target hε₁)
          (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart) := by
  set r : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ℝ ∙ EuclideanSpace.single 1 (1 : ℝ)).reflection
  have hα : ∀ _ : Unit, realProjPlaneTopReflChart.morseAttachingMap le_rfl hε₀
        (closedBall_subset_realProjPlaneTopReflChart_target hε₁)
        projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart =
      r.diskBoundaryIso.hom ≫ realProjPlaneTopChart.morseAttachingMap le_rfl hε₀
          (closedBall_subset_realProjPlaneTopChart_target hε₁)
          projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart :=
    fun _ ↦ morseAttachingMap_realProjPlaneTopReflChart hε₀ hε₁
  refine ⟨morseCellAttachmentIso (fun _ : Unit ↦ realProjPlaneTopChart)
    (fun _ : Unit ↦ realProjPlaneTopReflChart) (fun _ ↦ 2) (fun _ ↦ le_rfl) hε₀
    (fun _ ↦ closedBall_subset_realProjPlaneTopChart_target hε₁)
    (fun _ ↦ closedBall_subset_realProjPlaneTopReflChart_target hε₁)
    (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart)
    (fun _ ↦ projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart)
    (fun _ ↦ r.diskIso) (fun _ ↦ r.diskBoundaryIso)
    (fun _ ↦ LinearIsometryEquiv.diskBoundaryIso_hom_comp_diskBoundaryInclusion _) hα,
    by simp, by simp, ?_⟩
  exact morseCellAttachmentIso_hom_comp_morseCellComparison _ _ _ _ _ _ _ _ _ _ _ _ _
    fun _ ↦ morseCharacteristicMap_realProjPlaneTopReflChart hε₀ hε₁

end Attaching

/-! ### Squared directions in the plane -/

/-- The squared direction `(x + i y)² / (x² + y²)` of a nonzero vector `(x, y)` of the plane, a
point of the unit circle which does not change when `(x, y)` is rescaled by a nonzero real. -/
private def sqDir (x y : ℝ) : ℂ :=
  ((x : ℂ) + y * I) ^ 2 / ((x ^ 2 + y ^ 2 : ℝ) : ℂ)

private theorem norm_sqDir {x y : ℝ} (h : 0 < x ^ 2 + y ^ 2) : ‖sqDir x y‖ = 1 := by
  rw [sqDir, norm_div, norm_pow, Complex.sq_norm, normSq_add_mul_I, norm_real,
    Real.norm_of_nonneg h.le, div_self h.ne']

private theorem sqDir_mul {t : ℝ} (ht : t ≠ 0) (x y : ℝ) : sqDir (t * x) (t * y) = sqDir x y := by
  have ht' : ((t : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.2 ht)
  rw [sqDir, sqDir, ← mul_div_mul_left _ (((x ^ 2 + y ^ 2 : ℝ) : ℂ)) ht']
  push_cast
  ring_nf

private theorem sqDir_neg_left (x y : ℝ) : sqDir (-x) y = conj (sqDir x y) := by
  simp only [sqDir, map_div₀, map_pow, map_add, map_mul, conj_ofReal, conj_I]
  congr 1
  · push_cast; ring
  · push_cast; ring

private theorem continuousAt_sqDir {X : Type*} [TopologicalSpace X] {x y : X → ℝ} {p : X}
    (hx : Continuous x) (hy : Continuous y) (hp : 0 < x p ^ 2 + y p ^ 2) :
    ContinuousAt (fun q ↦ sqDir (x q) (y q)) p := by
  have hnum : Continuous fun q ↦ ((x q : ℂ) + y q * I) ^ 2 :=
    ((continuous_ofReal.comp hx).add ((continuous_ofReal.comp hy).mul continuous_const)).pow 2
  have hden : Continuous fun q ↦ ((x q ^ 2 + y q ^ 2 : ℝ) : ℂ) :=
    continuous_ofReal.comp ((hx.pow 2).add (hy.pow 2))
  exact hnum.continuousAt.div hden.continuousAt (ofReal_ne_zero.2 hp.ne')

/-- The squared direction of the point `(a cos θ, sin θ)` of an ellipse. -/
private def ellipseAngle (a θ : ℝ) : ℂ :=
  sqDir (a * Real.cos θ) (Real.sin θ)

private theorem sq_add_sq_pos {a : ℝ} (ha : a ≠ 0) (θ : ℝ) :
    0 < (a * Real.cos θ) ^ 2 + Real.sin θ ^ 2 := by
  rcases eq_or_ne (Real.sin θ) 0 with hs | hs
  · have hc : Real.cos θ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hs, mul_pow, hc]
    positivity
  · have := pow_pos (abs_pos.2 hs) 2
    rw [sq_abs] at this
    positivity

private theorem ellipseAngle_one (θ : ℝ) : ellipseAngle 1 θ = Circle.exp (2 * θ) := by
  rw [ellipseAngle, sqDir, Circle.coe_exp, one_mul, Real.cos_sq_add_sin_sq, ofReal_one, div_one,
    ofReal_cos, ofReal_sin, ← exp_mul_I, ← exp_nat_mul]
  push_cast
  ring_nf

/-- A loop in the circle which follows the squared direction of the ellipse
`θ ↦ (a cos θ, sin θ)`, `a > 0`, once around has degree `2`. -/
private theorem degree_eq_two_of_ellipseAngle {a : ℝ} (ha : 0 < a) {x : Circle} (γ : Path x x)
    (hγ : ∀ t : unitInterval, (γ t : ℂ) = ellipseAngle a (2 * Real.pi * t)) :
    Circle.degree γ = 2 := by
  -- Deform the ellipse to the unit circle through the ellipses with `b = (1 - s) a + s > 0`.
  have hb (s : unitInterval) : (1 - (s : ℝ)) * a + s ≠ 0 := by
    have h₀ : (0 : ℝ) ≤ s := s.2.1
    have h₁ : (s : ℝ) ≤ 1 := s.2.2
    rcases le_or_gt (s : ℝ) (1 / 2) with h | h <;> nlinarith
  let F : C(unitInterval × unitInterval, Circle) :=
    { toFun p := ⟨ellipseAngle ((1 - (p.1 : ℝ)) * a + p.1) (2 * Real.pi * p.2),
        mem_sphere_zero_iff_norm.2 (norm_sqDir (sq_add_sq_pos (hb p.1) _))⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun p ↦
          continuousAt_sqDir (x := fun p : unitInterval × unitInterval ↦
            ((1 - (p.1 : ℝ)) * a + p.1) * Real.cos (2 * Real.pi * p.2))
            (y := fun p : unitInterval × unitInterval ↦ Real.sin (2 * Real.pi * p.2))
            (by fun_prop) (by fun_prop) (sq_add_sq_pos (hb p.1) _)) _ }
  have hF (p : unitInterval × unitInterval) :
      (F p : ℂ) = ellipseAngle ((1 - (p.1 : ℝ)) * a + p.1) (2 * Real.pi * p.2) := (rfl)
  let γ₁ := Circle.expLoop.map (continuous_pow 2)
  have h₁ (t : unitInterval) : (γ₁ t : ℂ) = Circle.exp (4 * Real.pi * t) := by
    simp only [γ₁, Path.map_coe, Function.comp_apply, Circle.expLoop_apply]
    rw [← Circle.exp_nsmul]
    congr 2
    simp
    ring
  rw [Circle.degree_eq_of_homotopy γ γ₁ F (fun t ↦ Subtype.ext ?_) (fun t ↦ Subtype.ext ?_)
    (fun s ↦ Subtype.ext ?_)]
  · exact Circle.degree_eq_of_sub_eq γ₁ (θ := fun t ↦ 4 * Real.pi * t) (by fun_prop)
      (fun t ↦ Circle.coe_inj.1 (h₁ t).symm) (by push_cast; ring)
  · rw [hF, hγ]
    simp
  · rw [hF, h₁]
    simp only [Set.Icc.coe_one, sub_self, zero_mul, zero_add, ellipseAngle_one]
    congr 2
    ring
  · simp [hF, ellipseAngle]

/-! ### The core angle of `ℝℙ² \ {[0 : 0 : 1]}` -/

/-- A nonzero vector of `ℝ³` has positive squared length. -/
private theorem sum_sq_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  by_contra h
  refine hv (funext fun j ↦ ?_)
  fin_cases j <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

/-- `f[x : y : z] = (y² + 2z²) / (x² + y² + z²)` in homogeneous coordinates. -/
private theorem projectiveMomentFunction_mk_eq (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    projectiveMomentFunction ℝ ![0, 1, 2] (mk ℝ v hv) =
      (v 1 ^ 2 + 2 * v 2 ^ 2) / (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  rw [projectiveMomentFunction_mk]
  simp [Fin.sum_univ_three]

/-- The function `f[x : y : z] = (y² + 2z²) / (x² + y² + z²)` is below its maximum `2` exactly off
the point `[0 : 0 : 1]`, where `x² + y² > 0`. -/
theorem projectiveMomentFunction_mk_lt_two_iff (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    projectiveMomentFunction ℝ ![0, 1, 2] (mk ℝ v hv) < 2 ↔ 0 < v 0 ^ 2 + v 1 ^ 2 := by
  rw [projectiveMomentFunction_mk_eq, div_lt_iff₀ (sum_sq_pos hv)]
  constructor <;> intro h <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- The squared direction of the first two homogeneous coordinates, `[x : y : z] ↦ (x + i y)² /
(x² + y²)`, well defined on projective space (with value `0` at `[0 : 0 : 1]`). -/
private def coreAngleFun : ℙ ℝ (Fin 3 → ℝ) → ℂ :=
  Projectivization.lift (fun v ↦ sqDir (v.1 0) (v.1 1)) fun a b t h ↦ by
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by simpa using h)
    rw [h]
    exact sqDir_mul ht _ _

private theorem coreAngleFun_mk (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    coreAngleFun (mk ℝ v hv) = sqDir (v 0) (v 1) :=
  (rfl)

private theorem norm_coreAngleFun {x : ℙ ℝ (Fin 3 → ℝ)}
    (hx : projectiveMomentFunction ℝ ![0, 1, 2] x < 2) : ‖coreAngleFun x‖ = 1 := by
  induction x using Projectivization.ind with | h v hv =>
  rw [coreAngleFun_mk]
  exact norm_sqDir ((projectiveMomentFunction_mk_lt_two_iff v hv).1 hx)

private theorem continuousAt_coreAngleFun {x : ℙ ℝ (Fin 3 → ℝ)}
    (hx : projectiveMomentFunction ℝ ![0, 1, 2] x < 2) : ContinuousAt coreAngleFun x := by
  obtain ⟨v, rfl⟩ := isOpenQuotientMap_mk'.surjective x
  rw [mk'_eq_mk, projectiveMomentFunction_mk_lt_two_iff] at hx
  rw [← isOpenQuotientMap_mk'.continuousAt_comp_iff]
  exact continuousAt_sqDir (x := fun v : {v : Fin 3 → ℝ // v ≠ 0} ↦ v.1 0)
    (y := fun v : {v : Fin 3 → ℝ // v ≠ 0} ↦ v.1 1)
    ((continuous_apply 0).comp continuous_subtype_val)
    ((continuous_apply 1).comp continuous_subtype_val) hx

/-- The **core angle** `ρ[x : y : z] = (x + i y)² / (x² + y²)` of `ℝℙ²` minus the maximum
`[0 : 0 : 1]` of `f[x : y : z] = (y² + 2z²) / (x² + y² + z²)`, that is of the open set
`{f < 2}`. It is the retraction `[x : y : z] ↦ [x : y : 0]` onto the core circle
`{z = 0} ≅ ℝℙ¹` followed by the identification `ℝℙ¹ ≅ S¹`, `[x : y] ↦ (x + i y)² / (x² + y²)`.
It measures how often a loop winds around the core of the Möbius band `{f ≤ 2 - ε}`; see
`TauCeti.realProjPlaneCoreDegree`. -/
def realProjPlaneCoreAngle :
    C({x : ℙ ℝ (Fin 3 → ℝ) | projectiveMomentFunction ℝ ![0, 1, 2] x < 2}, Circle) where
  toFun x := ⟨coreAngleFun x, mem_sphere_zero_iff_norm.2 (norm_coreAngleFun x.2)⟩
  continuous_toFun := (continuousOn_of_forall_continuousAt (fun _ hx ↦ continuousAt_coreAngleFun hx)
    |>.comp_continuous continuous_subtype_val fun x ↦ x.2).subtype_mk _

@[simp]
theorem coe_realProjPlaneCoreAngle_mk (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (h : projectiveMomentFunction ℝ ![0, 1, 2] (mk ℝ v hv) < 2) :
    (realProjPlaneCoreAngle ⟨mk ℝ v hv, h⟩ : ℂ) =
      ((v 0 : ℂ) + v 1 * I) ^ 2 / ((v 0 ^ 2 + v 1 ^ 2 : ℝ) : ℂ) :=
  (rfl)

private theorem coe_realProjPlaneCoreAngle
    (x : {x : ℙ ℝ (Fin 3 → ℝ) | projectiveMomentFunction ℝ ![0, 1, 2] x < 2}) :
    (realProjPlaneCoreAngle x : ℂ) = coreAngleFun x :=
  (rfl)

/-- The counterclockwise parametrization `e^{iθ} ↦ (cos θ, sin θ)` of the boundary circle `∂D²`. -/
private def circleToDiskBoundary : C(Circle, TopCat.diskBoundary.{0} 2) where
  toFun z := ULift.up (EuclideanSpace.sphereHomeomorphCircle.symm z)
  continuous_toFun := continuous_uliftUp.comp EuclideanSpace.sphereHomeomorphCircle.symm.continuous

private theorem circleToDiskBoundary_apply_down (z : Circle) :
    (circleToDiskBoundary z).down = EuclideanSpace.sphereHomeomorphCircle.symm z :=
  (rfl)

private theorem coe_circleToDiskBoundary_exp (θ : ℝ) :
    ((circleToDiskBoundary (Circle.exp θ)).down : EuclideanSpace ℝ (Fin 2)) =
      !₂[Real.cos θ, Real.sin θ] := by
  rw [circleToDiskBoundary_apply_down, EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply]
  ext j
  fin_cases j <;> simp [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]

/-- The **core degree** of a map `g : ∂D² → ℝℙ² \ {[0 : 0 : 1]}`: the degree of the loop
`θ ↦ ρ (g (cos θ, sin θ))` in the circle, where `ρ` is the core angle
`TauCeti.realProjPlaneCoreAngle` and `∂D²` is run through once counterclockwise. It is
invariant under homotopy (`TauCeti.realProjPlaneCoreDegree_eq_of_homotopic`), and the core
circle `θ ↦ [cos θ : sin θ : 0]`, `0 ≤ θ ≤ π`, has core degree `1`
(`TauCeti.realProjPlaneCoreDegree_realProjPlaneCoreMap`). -/
def realProjPlaneCoreDegree
    (g : C(TopCat.diskBoundary.{0} 2,
      {x : ℙ ℝ (Fin 3 → ℝ) | projectiveMomentFunction ℝ ![0, 1, 2] x < 2})) : ℤ :=
  Circle.degree (Circle.expLoop.map
    (realProjPlaneCoreAngle.comp (g.comp circleToDiskBoundary)).continuous)

/-- The loop whose degree is the core degree, evaluated. -/
private theorem coreDegreeLoop_apply
    (g : C(TopCat.diskBoundary.{0} 2,
      {x : ℙ ℝ (Fin 3 → ℝ) | projectiveMomentFunction ℝ ![0, 1, 2] x < 2})) (t : unitInterval) :
    Circle.expLoop.map (realProjPlaneCoreAngle.comp (g.comp circleToDiskBoundary)).continuous t =
      realProjPlaneCoreAngle (g (circleToDiskBoundary (Circle.exp (2 * Real.pi * t)))) := by
  simp only [Path.map_coe, Function.comp_apply, Circle.expLoop_apply, ContinuousMap.comp_apply]

/-- **The core degree is a homotopy invariant.** -/
theorem realProjPlaneCoreDegree_eq_of_homotopic
    {g₀ g₁ : C(TopCat.diskBoundary.{0} 2,
      {x : ℙ ℝ (Fin 3 → ℝ) | projectiveMomentFunction ℝ ![0, 1, 2] x < 2})}
    (h : g₀.Homotopic g₁) :
    realProjPlaneCoreDegree g₀ = realProjPlaneCoreDegree g₁ := by
  obtain ⟨H⟩ := h
  exact Circle.degree_eq_of_homotopy _ _
    (realProjPlaneCoreAngle.comp (H.toContinuousMap.comp
      ((ContinuousMap.id _).prodMap (circleToDiskBoundary.comp Circle.expLoop.toContinuousMap))))
    (fun t ↦ by simp) (fun t ↦ by simp) (fun s ↦ by simp)

/-- The unit vector `(cos θ, sin θ, 0)` of `ℝ³` is nonzero. -/
theorem cos_sin_zero_ne_zero (θ : ℝ) : (![Real.cos θ, Real.sin θ, 0] : Fin 3 → ℝ) ≠ 0 :=
  fun h ↦ by
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h₀ h₁
    nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem projectiveMomentFunction_mk_cos_sin_zero_lt_two (θ : ℝ) :
    projectiveMomentFunction ℝ ![0, 1, 2] (mk ℝ _ (cos_sin_zero_ne_zero θ)) < 2 := by
  rw [projectiveMomentFunction_mk_lt_two_iff]
  simp [Real.cos_sq_add_sin_sq]

/-- The **core circle** of the Möbius band `{f ≤ 2 - ε}`, `t ↦ [cos πt : sin πt : 0]`, `0 ≤ t ≤ 1`:
the projective line `{z = 0}` run through once, as a loop in `{f < 2}` at `[1 : 0 : 0]`. -/
def realProjPlaneCoreLoop :
    Path (⟨mk ℝ ![1, 0, 0] (by simp),
        (projectiveMomentFunction_mk_lt_two_iff ![1, 0, 0] (by simp)).2 (by simp)⟩ :
        {x : ℙ ℝ (Fin 3 → ℝ) | projectiveMomentFunction ℝ ![0, 1, 2] x < 2})
      ⟨mk ℝ ![1, 0, 0] (by simp),
        (projectiveMomentFunction_mk_lt_two_iff ![1, 0, 0] (by simp)).2 (by simp)⟩ where
  toFun t := ⟨mk ℝ _ (cos_sin_zero_ne_zero (Real.pi * t)),
    projectiveMomentFunction_mk_cos_sin_zero_lt_two _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk
      (continuous_mk (K := ℝ) ?_ fun t : unitInterval ↦ cos_sin_zero_ne_zero (Real.pi * t)) _
    fun_prop
  source' := by simp
  target' := by
    refine Subtype.ext ?_
    simp only [Set.Icc.coe_one, mul_one, Real.cos_pi, Real.sin_pi]
    rw [mk_eq_mk_iff']
    exact ⟨-1, by ext j; fin_cases j <;> simp⟩

theorem coe_realProjPlaneCoreLoop_apply (t : unitInterval) :
    (realProjPlaneCoreLoop t : ℙ ℝ (Fin 3 → ℝ)) =
      mk ℝ _ (cos_sin_zero_ne_zero (Real.pi * t)) :=
  (rfl)

/-- The inverse `(cos θ, sin θ) ↦ e^{iθ}` of `TauCeti.circleToDiskBoundary`. -/
private def diskBoundaryToCircle : C(TopCat.diskBoundary.{0} 2, Circle) where
  toFun s := EuclideanSpace.sphereHomeomorphCircle s.down
  continuous_toFun := EuclideanSpace.sphereHomeomorphCircle.continuous.comp continuous_uliftDown

private theorem diskBoundaryToCircle_circleToDiskBoundary (z : Circle) :
    diskBoundaryToCircle (circleToDiskBoundary z) = z :=
  EuclideanSpace.sphereHomeomorphCircle.apply_symm_apply z

/-- The core circle as a map from `∂D²`: `(cos θ, sin θ) ↦ [cos (θ / 2) : sin (θ / 2) : 0]`. -/
def realProjPlaneCoreMap :
    C(TopCat.diskBoundary.{0} 2,
      {x : ℙ ℝ (Fin 3 → ℝ) | projectiveMomentFunction ℝ ![0, 1, 2] x < 2}) :=
  realProjPlaneCoreLoop.toCircle.comp diskBoundaryToCircle

/-- **The core circle has core degree `1`.** The core angle sends
`[cos θ : sin θ : 0]` to `e^{2iθ}`, which runs once around the circle for `0 ≤ θ ≤ π`. -/
theorem realProjPlaneCoreDegree_realProjPlaneCoreMap :
    realProjPlaneCoreDegree realProjPlaneCoreMap = 1 := by
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ 2 * Real.pi * t) (by fun_prop) (fun t ↦ ?_)
    (by push_cast; ring)
  rw [coreDegreeLoop_apply, realProjPlaneCoreMap, ContinuousMap.comp_apply,
    diskBoundaryToCircle_circleToDiskBoundary, Path.toCircle_exp]
  apply Circle.ext
  rw [coe_realProjPlaneCoreAngle, coe_realProjPlaneCoreLoop_apply, coreAngleFun_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← one_mul (Real.cos _), ← ellipseAngle, ellipseAngle_one]
  ring_nf

/-! ### The degrees of the attaching maps -/

section Degree

variable {ε : ℝ}

/-- The core angle of the point `ψ⁻¹(√ε w)` of the cell, for a unit vector `w`. -/
private theorem coreAngleFun_realProjPlaneTopChart_symm_smul (hε₀ : 0 < ε) (hε₁ : ε < 1)
    {w : EuclideanSpace ℝ (Fin 2)} (hw : w 0 ^ 2 + w 1 ^ 2 = 1) :
    coreAngleFun (realProjPlaneTopChart.symm (√ε • w)) = sqDir (w 0 / √2) (w 1) := by
  have hq : (√ε • w) 0 ^ 2 / 2 + (√ε • w) 1 ^ 2 < 1 := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt hε₀.le]
    nlinarith [sq_nonneg (w 0)]
  rw [realProjPlaneTopChart_symm_apply_of_lt hq, coreAngleFun_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.smul_apply, smul_eq_mul, mul_div_assoc]
  exact sqDir_mul (Real.sqrt_pos.2 hε₀).ne' _ _

private theorem cos_sq_add_sin_sq_circleToDiskBoundary (θ : ℝ) :
    ((circleToDiskBoundary (Circle.exp θ)).down : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 +
      ((circleToDiskBoundary (Circle.exp θ)).down : EuclideanSpace ℝ (Fin 2)) 1 ^ 2 = 1 := by
  simp [coe_circleToDiskBoundary_exp, Real.cos_sq_add_sin_sq]

/-- **The attaching map `α₊` has core degree `2`.** Going once counterclockwise around `∂D²` in the
normalized negative coordinates, the attaching map `α₊ : ∂D² → {f ≤ 2 - ε}` of the chart
`TauCeti.realProjPlaneTopChart` winds twice around the core of the Möbius band
`{f ≤ 2 - ε}`. -/
theorem realProjPlaneCoreDegree_morseAttachingMap_realProjPlaneTopChart
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    realProjPlaneCoreDegree ((ContinuousMap.inclusion
        (ofPred_subset_ofPred.2 fun _ hx ↦ hx.trans_lt (sub_lt_self 2 hε₀))).comp
      (realProjPlaneTopChart.morseAttachingMap le_rfl hε₀.le
        (closedBall_subset_realProjPlaneTopChart_target hε₁)
        projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart).hom) = 2 := by
  refine degree_eq_two_of_ellipseAngle (a := 1 / √2) (by positivity) _ fun t ↦ ?_
  rw [coreDegreeLoop_apply, coe_realProjPlaneCoreAngle]
  -- The attaching map is applied through its underlying continuous map `TopCat.Hom.hom`;
  -- unfolding it exposes the categorical application used by the evaluation lemma.
  rw [ContinuousMap.comp_apply, ContinuousMap.inclusion_apply_coe, TopCat.Hom.hom,
    coe_morseAttachingMap_realProjPlaneTopChart_apply hε₀.le hε₁]
  rw [coreAngleFun_realProjPlaneTopChart_symm_smul hε₀ hε₁
    (cos_sq_add_sin_sq_circleToDiskBoundary _), coe_circleToDiskBoundary_exp, ellipseAngle]
  simp [div_eq_inv_mul]

/-- **The attaching map `α₋` has core degree `-2`.** The attaching map
`α₋ = α₊ ∘ r : ∂D² → {f ≤ 2 - ε}` of the opposite chart `TauCeti.realProjPlaneTopReflChart`
winds twice around the core of the Möbius band `{f ≤ 2 - ε}`, in the opposite direction. -/
theorem realProjPlaneCoreDegree_morseAttachingMap_realProjPlaneTopReflChart
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    realProjPlaneCoreDegree ((ContinuousMap.inclusion
        (ofPred_subset_ofPred.2 fun _ hx ↦ hx.trans_lt (sub_lt_self 2 hε₀))).comp
      (realProjPlaneTopReflChart.morseAttachingMap le_rfl hε₀.le
        (closedBall_subset_realProjPlaneTopReflChart_target hε₁)
        projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart).hom) = -2 := by
  have hpos := realProjPlaneCoreDegree_morseAttachingMap_realProjPlaneTopChart hε₀ hε₁
  unfold realProjPlaneCoreDegree at hpos ⊢
  rw [Circle.degree_congr _ (Path.inv _) fun t ↦ Circle.ext ?_, Circle.degree_inv, hpos]
  rw [Path.inv_apply, Circle.coe_inv_eq_conj, coreDegreeLoop_apply, coreDegreeLoop_apply,
    coe_realProjPlaneCoreAngle, coe_realProjPlaneCoreAngle]
  -- As above, unfold `TopCat.Hom.hom` to reach the categorical application of the attaching maps.
  simp only [ContinuousMap.comp_apply, ContinuousMap.inclusion_apply_coe, TopCat.Hom.hom]
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply,
    OpenPartialHomeomorph.coe_morseAttachingMap_apply, morseCellMap_realProjPlaneTopReflChart,
    morseCellMap_realProjPlaneTopChart, morseCellMap_realProjPlaneTopChart,
    coreAngleFun_realProjPlaneTopChart_symm_smul hε₀ hε₁
      (cos_sq_add_sin_sq_circleToDiskBoundary _),
    coreAngleFun_realProjPlaneTopChart_symm_smul hε₀ hε₁ (by
      rw [reflection_single_one_apply_zero, reflection_single_one_apply_one, neg_sq]
      exact cos_sq_add_sin_sq_circleToDiskBoundary _),
    reflection_single_one_apply_zero, reflection_single_one_apply_one, neg_div, sqDir_neg_left]

/-- **The two attaching maps of the top cell of `ℝℙ²` are not homotopic.** For `0 < ε < 1` the
attaching maps `α₊, α₋ : ∂D² → {f ≤ 2 - ε}` of the two normalized charts
`TauCeti.realProjPlaneTopChart` and `TauCeti.realProjPlaneTopReflChart` at the maximum
`[0 : 0 : 1]` of `f[x : y : z] = (y² + 2z²) / (x² + y² + z²)` are not homotopic with their source
`∂D²` fixed, since their core degrees `2` and `-2` differ. They still give homeomorphic cell
attachments relative to `{f ≤ 2 - ε}`
(`TauCeti.exists_iso_morseCellAttachment_realProjPlaneTopReflChart_realProjPlaneTopChart`),
since `α₋ = α₊ ∘ r` for the reflection `r` of the disc. -/
theorem not_homotopic_morseAttachingMap_realProjPlaneTopChart_realProjPlaneTopReflChart
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ¬ (realProjPlaneTopChart.morseAttachingMap le_rfl hε₀.le
        (closedBall_subset_realProjPlaneTopChart_target hε₁)
        projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopChart).hom.Homotopic
      (realProjPlaneTopReflChart.morseAttachingMap le_rfl hε₀.le
        (closedBall_subset_realProjPlaneTopReflChart_target hε₁)
        projectiveMomentFunction_eq_two_add_sum_realProjPlaneTopReflChart).hom := fun h ↦ by
  have := realProjPlaneCoreDegree_eq_of_homotopic
    ((ContinuousMap.Homotopic.refl (ContinuousMap.inclusion
      (ofPred_subset_ofPred.2 fun _ hx ↦ hx.trans_lt (sub_lt_self 2 hε₀)))).comp h)
  rw [realProjPlaneCoreDegree_morseAttachingMap_realProjPlaneTopChart hε₀ hε₁,
    realProjPlaneCoreDegree_morseAttachingMap_realProjPlaneTopReflChart hε₀ hε₁] at this
  norm_num at this

end Degree

end TauCeti
