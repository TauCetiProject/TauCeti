/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Topology.Circle.Degree

/-!
# Morse cells of the projective plane

The moment function `f[x : y : z] = (y² + 2z²) / (x² + y² + z²)` on the real projective plane, the
moment function with the distinct weights `0, 1, 2` (`TauCeti.projectivePlaneMoment`), has its
maximum `2` at `[0 : 0 : 1]`, a nondegenerate critical point of index `2`. This file works out the
`2`-cell attached at that maximum, in two normal-form charts, as a concrete test of the attaching
maps `OpenPartialHomeomorph.morseAttachingMap` and the cell attachments
`TauCeti.morseCellAttachment` in a case where the attaching circle is not null-homotopic.

The chart `ψ₊ = TauCeti.projectivePlaneChart` sends `[x : y : z]` to the normalized negative
coordinates `(√2 x / z, y / z) / √(1 + (x / z)² + (y / z)²)`, in which `f = 2 - w₀² - w₁²`; the
chart `ψ₋ = TauCeti.projectivePlaneNegChart` reflects its first coordinate. For `0 < ε < 1` the
band `f⁻¹[2 - ε, 2 + ε]` is compact and contains no other critical point, and both chart targets
contain the closed ball of radius `√ε`. The attaching maps `α± : S¹ → {f ≤ 2 - ε}` then satisfy
`α₋ = α₊ ∘ r` strictly, for the reflection `r : (s₀, s₁) ↦ (-s₀, s₁)`.

To tell `α₊` and `α₋` apart, project to the line `{z = 0}`. Below the value `2` the first two
homogeneous coordinates do not both vanish, so the squared direction
`κ[x : y : z] = (x + iy)² / (x² + y²)` (`TauCeti.projectivePlaneCoreAngle`) is a continuous map
from the lower sublevel to the unit circle. On the line `{z = 0}` it is the homeomorphism
`[cos θ : sin θ : 0] ↦ e^{2iθ}`, so it carries the core loop `θ ↦ [cos θ : sin θ : 0]`,
`0 ≤ θ ≤ π`, to a loop of degree `1`. The degree of a map `α : S¹ → {f ≤ c}` is that of
`κ ∘ α` (`TauCeti.projectivePlaneSublevelDegree`); it is a homotopy invariant. Lowering the
coordinate `z` to `0` along a straight line of homogeneous coordinates stays in the lower sublevel
and deforms `α₊` into the double cover `s ↦ [s₀ : s₁ : 0]` of the core, of degree `2`. Hence `α₊`
has degree `2` and `α₋ = α₊ ∘ r` has degree `-2`, so the two attaching maps are not homotopic,
although the two charts present the same critical point. As `α₋ = α₊ ∘ r` strictly, the identity
of `{f ≤ 2 - ε}` together with `r` on the disc is nevertheless a homeomorphism of the two cell
attachments relative to the lower sublevel, compatible with the handle-to-cell comparisons.

## Main definitions

* `TauCeti.projectivePlaneMoment`: the moment function with weights `0, 1, 2`.
* `TauCeti.projectivePlaneChart`, `TauCeti.projectivePlaneNegChart`: the two normal-form charts at
  the maximum.
* `TauCeti.projectivePlaneCoreAngle`: the squared direction `(x + iy)² / (x² + y²)`.
* `TauCeti.projectivePlaneSublevelDegree`: the degree of a circle in a sublevel below `2`.
* `TauCeti.projectivePlaneCoreDoubleCover`, `TauCeti.projectivePlaneCoreLoop`: the double cover
  of the core by the circle, and the core loop.

## Main results

* `TauCeti.projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart`: the normal form
  `f = 2 - w₀² - w₁²` in the chart.
* `TauCeti.degree_map_projectivePlaneCoreLoop`: the core loop has degree `1`.
* `TauCeti.homotopic_morseAttachingMap_projectivePlaneChart_projectivePlaneCoreDoubleCover`:
  `α₊` is homotopic to the double cover of the core.
* `TauCeti.projectivePlaneSublevelDegree_morseAttachingMap_projectivePlaneChart`,
  `TauCeti.projectivePlaneSublevelDegree_morseAttachingMap_projectivePlaneNegChart`: `α₊` has
  degree `2` and `α₋` has degree `-2`.
* `TauCeti.not_homotopic_morseAttachingMap_projectivePlaneChart_projectivePlaneNegChart`: `α₊`
  and `α₋` are not homotopic.
* `TauCeti.morseAttachingMap_projectivePlaneNegChart`: `α₋ = α₊ ∘ r`.
* `TauCeti.exists_iso_morseCellAttachment_projectivePlaneNegChart_projectivePlaneChart`: the two
  cell attachments are homeomorphic relative to `{f ≤ 2 - ε}`.
* `TauCeti.isCompact_projectivePlaneMoment_preimage_Icc` and
  `TauCeti.criticalPoints_projectivePlaneMoment_inter_preimage_Icc`: the width `ε` is admissible.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Lemma 3.6.
-/

public section

noncomputable section

open Set Metric CategoryTheory Projectivization
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti

/-- The moment function `[x : y : z] ↦ (y² + 2z²) / (x² + y² + z²)` on the real projective
plane. -/
def projectivePlaneMoment : ℙ ℝ (Fin 3 → ℝ) → ℝ :=
  projectiveMomentFunction ℝ fun i ↦ ((i : ℕ) : ℝ)

/-- The moment function in homogeneous coordinates. -/
@[simp]
theorem projectivePlaneMoment_mk (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    projectivePlaneMoment (mk ℝ v hv) =
      (v 1 ^ 2 + 2 * v 2 ^ 2) / (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  simp [projectivePlaneMoment, Fin.sum_univ_three, sq_abs]

/-- The normalized coordinates `(u, v) ↦ (√2 u, v) / √(1 + u² + v²)` on the affine plane, a
homeomorphism onto the open ellipse `{w | w₀² / 2 + w₁² < 1}`. Read through the affine chart
`(u, v) = (x / z, y / z)`, they are the Morse coordinates of `TauCeti.projectivePlaneMoment` at its
maximum `[0 : 0 : 1]`. -/
def projectivePlaneMorseCoord : OpenPartialHomeomorph (Fin 2 → ℝ) (EuclideanSpace ℝ (Fin 2)) where
  toFun z := (√(1 + z 0 ^ 2 + z 1 ^ 2))⁻¹ • !₂[√2 * z 0, z 1]
  invFun w := (√(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)))⁻¹ • ![w 0 / √2, w 1]
  source := univ
  target := {w | w 0 ^ 2 / 2 + w 1 ^ 2 < 1}
  map_source' z _ := by
    have hs : 0 < 1 + z 0 ^ 2 + z 1 ^ 2 := by positivity
    have h2 : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    simp only [mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul, mul_pow, inv_pow,
      Real.sq_sqrt hs.le, Matrix.cons_val_zero, Matrix.cons_val_one, h2]
    rw [show ∀ a b : ℝ, (1 + a + b)⁻¹ * (2 * a) / 2 + (1 + a + b)⁻¹ * b = (a + b) / (1 + a + b) by
      intro a b; field_simp, div_lt_one hs]
    linarith
  map_target' := by simp
  left_inv' z _ := by
    have hs : 0 < 1 + z 0 ^ 2 + z 1 ^ 2 := by positivity
    have h2 : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    have h2' : 0 < √2 := by positivity
    have hS : 0 < √(1 + z 0 ^ 2 + z 1 ^ 2) := Real.sqrt_pos.2 hs
    simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow,
      inv_pow, Real.sq_sqrt hs.le, h2]
    have hQ : 1 - ((1 + z 0 ^ 2 + z 1 ^ 2)⁻¹ * (2 * z 0 ^ 2) / 2 +
        (1 + z 0 ^ 2 + z 1 ^ 2)⁻¹ * z 1 ^ 2) = (√(1 + z 0 ^ 2 + z 1 ^ 2))⁻¹ ^ 2 := by
      rw [inv_pow, Real.sq_sqrt hs.le]
      field_simp
      ring
    rw [hQ, Real.sqrt_sq (by positivity), inv_inv]
    ext i
    fin_cases i <;> simp <;> field_simp
  right_inv' w hw := by
    have hq : 0 < 1 - (w 0 ^ 2 / 2 + w 1 ^ 2) := sub_pos.2 hw
    have h2 : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    have h2' : 0 < √2 := by positivity
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow,
      inv_pow, div_pow, Real.sq_sqrt hq.le, h2]
    generalize hqd : 1 - (w 0 ^ 2 / 2 + w 1 ^ 2) = q at hq ⊢
    have hS : 1 + q⁻¹ * (w 0 ^ 2 / 2) + q⁻¹ * w 1 ^ 2 = (√q)⁻¹ ^ 2 := by
      rw [inv_pow, Real.sq_sqrt hq.le, add_assoc, ← mul_add,
        show w 0 ^ 2 / 2 + w 1 ^ 2 = 1 - q by linarith]
      field_simp
      ring
    rw [hS, Real.sqrt_sq (by positivity), inv_inv]
    have hQ : 0 < √q := Real.sqrt_pos.2 hq
    ext i
    fin_cases i <;> simp <;> field_simp
  open_source := isOpen_univ
  open_target := isOpen_lt (by fun_prop) continuous_const
  continuousOn_toFun := by
    refine Continuous.continuousOn ?_
    have h (z : Fin 2 → ℝ) : √(1 + z 0 ^ 2 + z 1 ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    fun_prop (disch := exact h _)
  continuousOn_invFun := by
    intro w hw
    have h : √(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hw)).ne'
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop (disch := exact h)

@[simp]
theorem projectivePlaneMorseCoord_apply (z : Fin 2 → ℝ) :
    projectivePlaneMorseCoord z = (√(1 + z 0 ^ 2 + z 1 ^ 2))⁻¹ • !₂[√2 * z 0, z 1] :=
  (rfl)

@[simp]
theorem projectivePlaneMorseCoord_symm_apply (w : EuclideanSpace ℝ (Fin 2)) :
    projectivePlaneMorseCoord.symm w = (√(1 - (w 0 ^ 2 / 2 + w 1 ^ 2)))⁻¹ • ![w 0 / √2, w 1] :=
  (rfl)

@[simp]
theorem projectivePlaneMorseCoord_source : projectivePlaneMorseCoord.source = univ :=
  (rfl)

@[simp]
theorem projectivePlaneMorseCoord_target :
    projectivePlaneMorseCoord.target = {w | w 0 ^ 2 / 2 + w 1 ^ 2 < 1} :=
  (rfl)

/-- The Morse chart of `TauCeti.projectivePlaneMoment` at its maximum `[0 : 0 : 1]`: the affine
chart `[x : y : z] ↦ (x / z, y / z)` followed by `TauCeti.projectivePlaneMorseCoord`, that is,
`[x : y : z] ↦ (√2 x / z, y / z) / √(1 + (x / z)² + (y / z)²)`. In it the moment function reads
`2 - w₀² - w₁²` (`TauCeti.projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart`), so the
maximum is a critical point of index `2`. -/
def projectivePlaneChart : OpenPartialHomeomorph (ℙ ℝ (Fin 3 → ℝ)) (EuclideanSpace ℝ (Fin 2)) :=
  (affineOpenPartialHomeomorph 2).trans projectivePlaneMorseCoord

@[simp]
theorem projectivePlaneChart_source : projectivePlaneChart.source = affineOpen 2 := by
  simp [projectivePlaneChart]

@[simp]
theorem projectivePlaneChart_target :
    projectivePlaneChart.target = {w | w 0 ^ 2 / 2 + w 1 ^ 2 < 1} := by
  simp [projectivePlaneChart]

theorem projectivePlaneChart_symm_apply (w : EuclideanSpace ℝ (Fin 2)) :
    projectivePlaneChart.symm w = (affineChart 2).symm (projectivePlaneMorseCoord.symm w) := by
  simp [projectivePlaneChart]

theorem projectivePlaneChart_apply (x : ℙ ℝ (Fin 3 → ℝ)) :
    projectivePlaneChart x = projectivePlaneMorseCoord (affineChart 2 x) := by
  simp [projectivePlaneChart]

/-- The moment function reads `2 - w₀² - w₁²` in the chart `TauCeti.projectivePlaneChart`. -/
theorem projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart :
    ∀ x ∈ projectivePlaneChart.source, projectivePlaneMoment x =
      2 + ∑ j : Fin 2, (if j.val < 2 then -1 else 1) * projectivePlaneChart x j ^ 2 := by
  intro x hx
  rw [projectivePlaneChart_source] at hx
  obtain ⟨z, rfl⟩ : ∃ z, (affineChart 2).symm z = x :=
    ⟨affineChart 2 x, (affineChart 2).left_inv (by simpa using hx)⟩
  have hz : affineChart 2 ((affineChart (K := ℝ) 2).symm z) = z :=
    (affineChart 2).right_inv (by simp)
  have hs : 0 < 1 + z 0 ^ 2 + z 1 ^ 2 := by positivity
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  rw [projectivePlaneChart_apply, hz, projectivePlaneMoment,
    ← Function.comp_apply (f := projectiveMomentFunction ℝ _),
    projectiveMomentFunction_comp_affineChart_symm, ProjectiveMomentChart.model_apply]
  have h21 : ((Fin.succAbove (2 : Fin 3) 1 : ℕ) : ℝ) = 1 := by simp [Fin.succAbove]
  simp only [Fin.sum_univ_two, projectivePlaneMorseCoord_apply, PiLp.smul_apply, smul_eq_mul,
    Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, Real.sq_sqrt hs.le]
  simp [h21]
  field_simp
  linear_combination (z 1 ^ 2 * z 0 ^ 2 + z 0 ^ 2 + z 0 ^ 4) * h2

/-- The target of `TauCeti.projectivePlaneChart` contains the closed ball of radius `√ε` for
`ε < 1`. -/
theorem closedBall_subset_projectivePlaneChart_target {ε : ℝ} (hε : ε < 1) :
    closedBall 0 √ε ⊆ projectivePlaneChart.target := by
  intro w hw
  have h1 : ‖w‖ < 1 :=
    (mem_closedBall_zero_iff.1 hw).trans_lt ((Real.sqrt_lt' one_pos).2 (by simpa))
  have h2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs] at h2
  rw [projectivePlaneChart_target, mem_ofPred_eq]
  nlinarith [sq_nonneg (w 0)]

/-- The reflection `(w₀, w₁) ↦ (-w₀, w₁)` of `ℝ²` in the line orthogonal to the first basis
vector. -/
def projectivePlaneReflection : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ℝ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℝ))ᗮ.reflection

@[simp]
theorem projectivePlaneReflection_apply_zero (w : EuclideanSpace ℝ (Fin 2)) :
    projectivePlaneReflection w 0 = -w 0 := by
  simp [projectivePlaneReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, EuclideanSpace.inner_single_left]
  ring

@[simp]
theorem projectivePlaneReflection_apply_one (w : EuclideanSpace ℝ (Fin 2)) :
    projectivePlaneReflection w 1 = w 1 := by
  simp [projectivePlaneReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, EuclideanSpace.inner_single_left]

@[simp]
theorem projectivePlaneReflection_symm :
    projectivePlaneReflection.symm = projectivePlaneReflection :=
  Submodule.reflection_symm

/-- The opposite Morse chart of `TauCeti.projectivePlaneMoment` at `[0 : 0 : 1]`: the chart
`TauCeti.projectivePlaneChart` followed by the reflection of its first negative coordinate. -/
def projectivePlaneNegChart :
    OpenPartialHomeomorph (ℙ ℝ (Fin 3 → ℝ)) (EuclideanSpace ℝ (Fin 2)) :=
  projectivePlaneChart.transHomeomorph projectivePlaneReflection.toHomeomorph

@[simp]
theorem projectivePlaneNegChart_source : projectivePlaneNegChart.source = affineOpen 2 := by
  simp [projectivePlaneNegChart]

theorem projectivePlaneNegChart_apply (x : ℙ ℝ (Fin 3 → ℝ)) :
    projectivePlaneNegChart x = projectivePlaneReflection (projectivePlaneChart x) :=
  (rfl)

theorem projectivePlaneNegChart_symm_apply (w : EuclideanSpace ℝ (Fin 2)) :
    projectivePlaneNegChart.symm w = projectivePlaneChart.symm (projectivePlaneReflection w) := by
  simp [projectivePlaneNegChart]

/-- The moment function reads `2 - w₀² - w₁²` in the chart `TauCeti.projectivePlaneNegChart`. -/
theorem projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart :
    ∀ x ∈ projectivePlaneNegChart.source, projectivePlaneMoment x =
      2 + ∑ j : Fin 2, (if j.val < 2 then -1 else 1) * projectivePlaneNegChart x j ^ 2 := by
  intro x hx
  rw [projectivePlaneNegChart_source, ← projectivePlaneChart_source] at hx
  rw [projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart x hx]
  simp [Fin.sum_univ_two, projectivePlaneNegChart_apply]

/-- The target of `TauCeti.projectivePlaneNegChart` contains the closed ball of radius `√ε` for
`ε < 1`. -/
theorem closedBall_subset_projectivePlaneNegChart_target {ε : ℝ} (hε : ε < 1) :
    closedBall 0 √ε ⊆ projectivePlaneNegChart.target := by
  intro w hw
  simp only [projectivePlaneNegChart, OpenPartialHomeomorph.transHomeomorph_target, mem_preimage]
  refine closedBall_subset_projectivePlaneChart_target hε ?_
  simpa using hw

/-! ### The attaching map -/

/-- The attaching map `α₊ : S¹ → {f ≤ 2 - ε}` of the chart `TauCeti.projectivePlaneChart` at the
level `2` with width `ε`: the point with affine coordinates
`(x / z, y / z) = √ε (s₀ / √2, s₁) / √(1 - ε (s₀² / 2 + s₁²))`. -/
theorem coe_morseAttachingMap_projectivePlaneChart_apply {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (s : TopCat.diskBoundary.{0} 2) :
    (projectivePlaneChart.morseAttachingMap le_rfl hε
      (closedBall_subset_projectivePlaneChart_target hε1)
      projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart s : ℙ ℝ (Fin 3 → ℝ)) =
      (affineChart 2).symm ((√(1 - ε * ((s.down : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 / 2 +
          (s.down : EuclideanSpace ℝ (Fin 2)) 1 ^ 2)))⁻¹ •
        ![√ε * (s.down : EuclideanSpace ℝ (Fin 2)) 0 / √2,
          √ε * (s.down : EuclideanSpace ℝ (Fin 2)) 1]) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply, OpenPartialHomeomorph.morseCellMap_def,
    projectivePlaneChart_symm_apply, projectivePlaneMorseCoord_symm_apply]
  simp [mul_pow, Real.sq_sqrt hε, mul_add, mul_div_assoc]

/-! ### The core of the lower sublevel and its angle -/

private theorem sum_sq_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  by_contra h
  refine hv (funext fun i ↦ ?_)
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  fin_cases i <;> simp [h0, h1, h2]

/-- Below the maximal value `2`, the first two homogeneous coordinates do not both vanish. -/
private theorem sq_add_sq_pos_of_projectivePlaneMoment_mk_lt_two {v : Fin 3 → ℝ} (hv : v ≠ 0)
    (h : projectivePlaneMoment (mk ℝ v hv) < 2) : 0 < v 0 ^ 2 + v 1 ^ 2 := by
  rw [projectivePlaneMoment_mk, div_lt_iff₀ (sum_sq_pos hv)] at h
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- The squared direction `[x : y : z] ↦ (x + i y)² / (x² + y²)` of the projection of a point of the
projective plane to its line `{z = 0}`. Away from `[0 : 0 : 1]` it is a point of the unit circle,
and on the line `{z = 0}` it is the homeomorphism `[cos θ : sin θ : 0] ↦ e^{2iθ}` onto the
circle. -/
def projectivePlaneCoreAngle : ℙ ℝ (Fin 3 → ℝ) → ℂ :=
  Projectivization.lift
    (fun v ↦ (((v : Fin 3 → ℝ) 0 : ℂ) + (v : Fin 3 → ℝ) 1 * Complex.I) ^ 2 /
      (((v : Fin 3 → ℝ) 0 ^ 2 + (v : Fin 3 → ℝ) 1 ^ 2 : ℝ) : ℂ))
    fun v v' t h ↦ by
      have ht : (t : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (by rintro rfl; exact v.2 (by simpa using h))
      simp only [h, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [show (t : ℂ) * ((v' : Fin 3 → ℝ) 0 : ℂ) + t * ((v' : Fin 3 → ℝ) 1 : ℂ) * Complex.I =
          t * (((v' : Fin 3 → ℝ) 0 : ℂ) + ((v' : Fin 3 → ℝ) 1 : ℂ) * Complex.I) by ring,
        show ((t : ℂ) * ((v' : Fin 3 → ℝ) 0 : ℂ)) ^ 2 + ((t : ℂ) * ((v' : Fin 3 → ℝ) 1 : ℂ)) ^ 2 =
          t ^ 2 * (((v' : Fin 3 → ℝ) 0 : ℂ) ^ 2 + ((v' : Fin 3 → ℝ) 1 : ℂ) ^ 2) by ring,
        mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 ht)]

@[simp]
theorem projectivePlaneCoreAngle_mk (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    projectivePlaneCoreAngle (mk ℝ v hv) =
      ((v 0 : ℂ) + v 1 * Complex.I) ^ 2 / ((v 0 ^ 2 + v 1 ^ 2 : ℝ) : ℂ) :=
  (rfl)

/-- Below the maximal value `2`, the squared direction lies on the unit circle. -/
theorem norm_projectivePlaneCoreAngle {x : ℙ ℝ (Fin 3 → ℝ)} (hx : projectivePlaneMoment x < 2) :
    ‖projectivePlaneCoreAngle x‖ = 1 := by
  induction x using Projectivization.ind with | h v hv => ?_
  have hpos := sq_add_sq_pos_of_projectivePlaneMoment_mk_lt_two hv hx
  rw [projectivePlaneCoreAngle_mk, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg
    hpos.le, Complex.sq_norm, Complex.normSq_add_mul_I, div_self hpos.ne']

/-- The moment function is continuous. -/
theorem continuous_projectivePlaneMoment : Continuous projectivePlaneMoment :=
  (contMDiff_projectiveMomentFunction (r := 0) _).continuous

/-- The squared direction is continuous away from `[0 : 0 : 1]`. -/
theorem continuousOn_projectivePlaneCoreAngle :
    ContinuousOn projectivePlaneCoreAngle {x | projectivePlaneMoment x < 2} := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨v, rfl⟩ := isOpenQuotientMap_mk'.surjective x
  rw [mk'_eq_mk] at hx
  have hpos := sq_add_sq_pos_of_projectivePlaneMoment_mk_lt_two v.2 hx
  rw [← isOpenQuotientMap_mk'.continuousAt_comp_iff]
  have hcomp : projectivePlaneCoreAngle ∘ mk' ℝ = fun v : {v : Fin 3 → ℝ // v ≠ 0} ↦
      (((v : Fin 3 → ℝ) 0 : ℂ) + (v : Fin 3 → ℝ) 1 * Complex.I) ^ 2 /
        (((v : Fin 3 → ℝ) 0 ^ 2 + (v : Fin 3 → ℝ) 1 ^ 2 : ℝ) : ℂ) :=
    funext fun v ↦ by rw [Function.comp_apply, mk'_eq_mk, projectivePlaneCoreAngle_mk]
  rw [hcomp]
  have hne : (((v : Fin 3 → ℝ) 0 ^ 2 + (v : Fin 3 → ℝ) 1 ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 hpos.ne'
  have h0 : Continuous fun v : {v : Fin 3 → ℝ // v ≠ 0} ↦ (v : Fin 3 → ℝ) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun v : {v : Fin 3 → ℝ // v ≠ 0} ↦ (v : Fin 3 → ℝ) 1 :=
    (continuous_apply 1).comp continuous_subtype_val
  exact ((((Complex.continuous_ofReal.comp h0).add ((Complex.continuous_ofReal.comp h1).mul
    continuous_const)).pow 2).continuousAt).div
      (Complex.continuous_ofReal.comp ((h0.pow 2).add (h1.pow 2))).continuousAt hne

/-- The squared direction of a sublevel `{f ≤ c}` with `c < 2`, as a map to the unit circle. It
detects the class of a loop in the sublevel: the core loop `θ ↦ [cos θ : sin θ : 0]`,
`0 ≤ θ ≤ π`, of the projective line `{z = 0}` is carried to a loop of degree `1`
(`TauCeti.degree_map_projectivePlaneCoreLoop`). -/
def projectivePlaneSublevelAngle {c : ℝ} (hc : c < 2) :
    C({x | projectivePlaneMoment x ≤ c}, Circle) where
  toFun x := ⟨projectivePlaneCoreAngle x,
    mem_sphere_zero_iff_norm.2 (norm_projectivePlaneCoreAngle (x.2.trans_lt hc))⟩
  continuous_toFun := (continuousOn_projectivePlaneCoreAngle.comp_continuous continuous_subtype_val
    fun x ↦ x.2.trans_lt hc).subtype_mk _

@[simp]
theorem coe_projectivePlaneSublevelAngle_apply {c : ℝ} (hc : c < 2)
    (x : {x | projectivePlaneMoment x ≤ c}) :
    (projectivePlaneSublevelAngle hc x : ℂ) = projectivePlaneCoreAngle x :=
  (rfl)

/-! ### The degree of a circle in the lower sublevel -/

/-- The point `(cos t, sin t)` of the circle `∂D²`. -/
private def circlePoint (t : ℝ) : TopCat.diskBoundary.{0} 2 :=
  ULift.up ⟨!₂[Real.cos t, Real.sin t], by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp⟩

private theorem continuous_circlePoint : Continuous circlePoint := by
  have h : Continuous fun t : ℝ ↦ (!₂[Real.cos t, Real.sin t] : EuclideanSpace ℝ (Fin 2)) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ by
      fin_cases i
      exacts [by simpa using Real.continuous_cos, by simpa using Real.continuous_sin])
  exact continuous_uliftUp.comp (h.subtype_mk _)

/-- The counterclockwise loop `t ↦ (cos 2πt, sin 2πt)` around the circle `∂D²`. -/
private def diskBoundaryLoop : Path (circlePoint 0) (circlePoint 0) where
  toFun t := circlePoint (2 * Real.pi * t)
  continuous_toFun := continuous_circlePoint.comp (by fun_prop)
  source' := by rw [Set.Icc.coe_zero, mul_zero]
  target' := by
    rw [Set.Icc.coe_one, mul_one, circlePoint, circlePoint]
    congr 2
    simp

/-- The **degree** of a map `α : S¹ → {f ≤ c}` into a sublevel below the maximal value `2`: the
degree of the loop of squared directions `t ↦ κ(α(cos 2πt, sin 2πt))` in the unit circle, where
`κ = TauCeti.projectivePlaneSublevelAngle`. It is invariant under homotopy
(`TauCeti.projectivePlaneSublevelDegree_eq_of_homotopic`), and normalized so that the core loop of
the projective line `{z = 0}` has degree `1` (`TauCeti.degree_map_projectivePlaneCoreLoop`). -/
def projectivePlaneSublevelDegree {c : ℝ} (hc : c < 2)
    (α : C(TopCat.diskBoundary.{0} 2, {x | projectivePlaneMoment x ≤ c})) : ℤ :=
  Circle.degree (diskBoundaryLoop.map ((projectivePlaneSublevelAngle hc).comp α).continuous)

private theorem coe_diskBoundaryLoop_map_projectivePlaneSublevelAngle_comp_apply {c : ℝ}
    (hc : c < 2) (α : C(TopCat.diskBoundary.{0} 2, {x | projectivePlaneMoment x ≤ c}))
    (t : unitInterval) :
    (diskBoundaryLoop.map ((projectivePlaneSublevelAngle hc).comp α).continuous t : ℂ) =
      projectivePlaneCoreAngle (α (circlePoint (2 * Real.pi * t))) :=
  (rfl)

/-- Homotopic maps of the circle into a sublevel below `2` have the same degree. -/
theorem projectivePlaneSublevelDegree_eq_of_homotopic {c : ℝ} (hc : c < 2)
    {α β : C(TopCat.diskBoundary.{0} 2, {x | projectivePlaneMoment x ≤ c})}
    (h : α.Homotopic β) :
    projectivePlaneSublevelDegree hc α = projectivePlaneSublevelDegree hc β := by
  obtain ⟨H⟩ := h
  refine Circle.degree_eq_of_homotopy _ _ (((projectivePlaneSublevelAngle hc).comp
    H.toContinuousMap).comp ⟨fun p ↦ (p.1, diskBoundaryLoop p.2), by fun_prop⟩)
      (fun t ↦ ?_) (fun t ↦ ?_) (fun t ↦ ?_)
  · simp
  · simp
  · simp

private theorem continuous_diskBoundary_apply (i : Fin 2) :
    Continuous fun s : TopCat.diskBoundary.{0} 2 ↦ (s.down : EuclideanSpace ℝ (Fin 2)) i :=
  (PiLp.continuous_apply 2 _ i).comp (continuous_subtype_val.comp continuous_uliftDown)

private theorem ne_zero_of_sq_add_sq_eq_one {a b c : ℝ} (h : a ^ 2 + b ^ 2 = 1) : ![a, b, c] ≠ 0 :=
  fun h0 ↦ by
    have ha : a = 0 := by simpa using congrFun h0 0
    have hb : b = 0 := by simpa using congrFun h0 1
    simp [ha, hb] at h

/-- On the projective line `{z = 0}` the moment function is `y² / (x² + y²) ≤ 1`. -/
private theorem projectivePlaneMoment_mk_le_one {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    projectivePlaneMoment (mk ℝ ![a, b, 0] (ne_zero_of_sq_add_sq_eq_one h)) ≤ 1 := by
  rw [projectivePlaneMoment_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [div_le_one (by nlinarith)]
  nlinarith [sq_nonneg a]

/-- The double cover `s ↦ [s₀ : s₁ : 0]` of the projective line `{z = 0}` by the circle `∂D²`, as
a map into a sublevel `{f ≤ c}` with `1 ≤ c`. -/
def projectivePlaneCoreDoubleCover {c : ℝ} (hc : 1 ≤ c) :
    TopCat.diskBoundary.{0} 2 ⟶ TopCat.of {x | projectivePlaneMoment x ≤ c} :=
  TopCat.ofHom
    { toFun s := ⟨mk ℝ ![(s.down : EuclideanSpace ℝ (Fin 2)) 0,
        (s.down : EuclideanSpace ℝ (Fin 2)) 1, 0]
          (ne_zero_of_sq_add_sq_eq_one (sq_add_sq_diskBoundary_two_eq_one s)),
        (projectivePlaneMoment_mk_le_one (sq_add_sq_diskBoundary_two_eq_one s)).trans hc⟩
      continuous_toFun := (continuous_mk (continuous_pi fun i ↦ by
          fin_cases i
          exacts [continuous_diskBoundary_apply 0, continuous_diskBoundary_apply 1,
            continuous_const]) _).subtype_mk _ }

@[simp]
theorem coe_projectivePlaneCoreDoubleCover_apply {c : ℝ} (hc : 1 ≤ c)
    (s : TopCat.diskBoundary.{0} 2) :
    ((projectivePlaneCoreDoubleCover hc).hom s : ℙ ℝ (Fin 3 → ℝ)) =
      mk ℝ ![(s.down : EuclideanSpace ℝ (Fin 2)) 0, (s.down : EuclideanSpace ℝ (Fin 2)) 1, 0]
        (fun h ↦ by simp at h; simpa [h.1, h.2] using sq_add_sq_diskBoundary_two_eq_one s) :=
  (rfl)

private theorem cos_add_sin_mul_I_sq (x : ℝ) :
    ((Real.cos x : ℂ) + Real.sin x * Complex.I) ^ 2 = Circle.exp (2 * x) := by
  rw [Circle.coe_exp, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I,
    ← Complex.exp_nat_mul]
  push_cast
  ring_nf

private theorem projectivePlaneCoreAngle_projectivePlaneCoreDoubleCover_circlePoint {c : ℝ}
    (hc : 1 ≤ c) (x : ℝ) :
    projectivePlaneCoreAngle ((projectivePlaneCoreDoubleCover hc).hom (circlePoint x)) =
      Circle.exp (2 * x) := by
  rw [coe_projectivePlaneCoreDoubleCover_apply, projectivePlaneCoreAngle_mk]
  simp only [circlePoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.cos_sq_add_sin_sq, Complex.ofReal_one, div_one]
  exact cos_add_sin_mul_I_sq x

private theorem diskBoundaryIso_projectivePlaneReflection_circlePoint (x : ℝ) :
    projectivePlaneReflection.diskBoundaryIso.hom (circlePoint x) = circlePoint (Real.pi - x) := by
  apply ULift.ext
  apply Subtype.ext
  rw [LinearIsometryEquiv.coe_diskBoundaryIso_hom_apply_down]
  ext i
  fin_cases i <;> simp [circlePoint, Real.cos_pi_sub, Real.sin_pi_sub]

/-- The double cover of the projective line by the circle has degree `2`. -/
theorem projectivePlaneSublevelDegree_projectivePlaneCoreDoubleCover {c : ℝ} (hc : 1 ≤ c)
    (hc2 : c < 2) :
    projectivePlaneSublevelDegree hc2 (projectivePlaneCoreDoubleCover hc).hom = 2 := by
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ 2 * (2 * Real.pi * t)) (by fun_prop)
    (fun t ↦ Circle.ext ?_) (by push_cast; ring)
  rw [coe_diskBoundaryLoop_map_projectivePlaneSublevelAngle_comp_apply,
    projectivePlaneCoreAngle_projectivePlaneCoreDoubleCover_circlePoint]

/-- Composed with the reflection `(s₀, s₁) ↦ (-s₀, s₁)` of the circle, the double cover of the
projective line has degree `-2`. -/
theorem projectivePlaneSublevelDegree_diskBoundaryIso_projectivePlaneCoreDoubleCover {c : ℝ}
    (hc : 1 ≤ c) (hc2 : c < 2) :
    projectivePlaneSublevelDegree hc2
      (projectivePlaneReflection.diskBoundaryIso.hom ≫ projectivePlaneCoreDoubleCover hc).hom =
        -2 := by
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ 2 * (Real.pi - 2 * Real.pi * t)) (by fun_prop)
    (fun t ↦ Circle.ext ?_) (by push_cast; ring)
  rw [coe_diskBoundaryLoop_map_projectivePlaneSublevelAngle_comp_apply, TopCat.hom_comp,
    ContinuousMap.comp_apply, diskBoundaryIso_projectivePlaneReflection_circlePoint,
    projectivePlaneCoreAngle_projectivePlaneCoreDoubleCover_circlePoint]

/-- The core loop `t ↦ [cos πt : sin πt : 0]` of the projective line `{z = 0}`, based at
`[1 : 0 : 0]`, in a sublevel `{f ≤ c}` with `1 ≤ c`. -/
def projectivePlaneCoreLoop {c : ℝ} (hc : 1 ≤ c) :
    Path (X := {x | projectivePlaneMoment x ≤ c})
      ⟨mk ℝ ![1, 0, 0] (by simp), by rw [mem_ofPred_eq, projectivePlaneMoment_mk]; simp; linarith⟩
      ⟨mk ℝ ![1, 0, 0] (by simp), by rw [mem_ofPred_eq, projectivePlaneMoment_mk]; simp; linarith⟩
    where
  toFun t := (projectivePlaneCoreDoubleCover hc).hom (circlePoint (Real.pi * t))
  continuous_toFun := (projectivePlaneCoreDoubleCover hc).hom.continuous.comp
    (continuous_circlePoint.comp (by fun_prop))
  source' := by
    apply Subtype.ext
    rw [coe_projectivePlaneCoreDoubleCover_apply]
    simp [circlePoint]
  target' := by
    apply Subtype.ext
    rw [coe_projectivePlaneCoreDoubleCover_apply, mk_eq_mk_iff']
    exact ⟨-1, by ext i; fin_cases i <;> simp [circlePoint]⟩

/-- The squared direction carries the core loop of the projective line `{z = 0}` to a loop of
degree `1` around the circle: the core loop represents the generator detected by
`TauCeti.projectivePlaneSublevelDegree`. -/
theorem degree_map_projectivePlaneCoreLoop {c : ℝ} (hc : 1 ≤ c) (hc2 : c < 2) :
    Circle.degree ((projectivePlaneCoreLoop hc).map (projectivePlaneSublevelAngle hc2).continuous) =
      1 := by
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ 2 * (Real.pi * t)) (by fun_prop)
    (fun t ↦ Circle.ext ?_) (by push_cast; ring)
  exact (projectivePlaneCoreAngle_projectivePlaneCoreDoubleCover_circlePoint hc _).symm

/-! ### The attaching maps wind twice around the core -/

private theorem one_sub_mul_pos {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (s : TopCat.diskBoundary.{0} 2) :
    0 < 1 - ε * ((s.down : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 / 2 +
      (s.down : EuclideanSpace ℝ (Fin 2)) 1 ^ 2) := by
  have h := sq_add_sq_diskBoundary_two_eq_one s
  nlinarith [sq_nonneg ((s.down : EuclideanSpace ℝ (Fin 2)) 0),
    sq_nonneg ((s.down : EuclideanSpace ℝ (Fin 2)) 1)]

private theorem insertNth_two_one (a b : ℝ) :
    Fin.insertNth (α := fun _ ↦ ℝ) 2 1 ![a, b] = ![a, b, 1] := by
  ext i
  fin_cases i <;> rfl

/-- The homogeneous coordinates of the straight-line homotopy from the attaching map to the double
cover of the core. -/
private def homotopyVec (ε τ a b : ℝ) : Fin 3 → ℝ :=
  ![√ε * a * ((1 - τ) / √2 + τ), √ε * b, (1 - τ) * √(1 - ε * (a ^ 2 / 2 + b ^ 2))]

private theorem homotopyVec_ne_zero {ε τ a b : ℝ} (hε : 0 < ε) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hab : a ^ 2 + b ^ 2 = 1) : homotopyVec ε τ a b ≠ 0 := fun h ↦ by
  have hk : 0 < (1 - τ) / √2 + τ := by
    rcases eq_or_lt_of_le hτ0 with rfl | hτ
    · simp
    · exact add_pos_of_nonneg_of_pos (div_nonneg (by linarith) (Real.sqrt_nonneg 2)) hτ
  have hs : 0 < √ε := Real.sqrt_pos.2 hε
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [homotopyVec, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
    mul_eq_zero, hs.ne', hk.ne', false_or, or_false] at h0 h1
  simp [h0, h1] at hab

private theorem projectivePlaneMoment_mk_homotopyVec_le {ε τ a b : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hab : a ^ 2 + b ^ 2 = 1) :
    projectivePlaneMoment (mk ℝ (homotopyVec ε τ a b) (homotopyVec_ne_zero hε hτ0 hτ1 hab)) ≤
      2 - ε := by
  rw [projectivePlaneMoment_mk, div_le_iff₀ (sum_sq_pos (homotopyVec_ne_zero hε hτ0 hτ1 hab))]
  simp only [homotopyVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have h2 : 1 ≤ √2 := Real.one_le_sqrt.2 one_le_two
  have hk : 1 / √2 ≤ (1 - τ) / √2 + τ := by
    rw [div_add' _ _ _ (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hk2 : 1 / 2 ≤ ((1 - τ) / √2 + τ) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hk 2
    rwa [div_pow, Real.sq_sqrt zero_le_two, one_pow] at this
  have hr : 0 ≤ 1 - ε * (a ^ 2 / 2 + b ^ 2) := by nlinarith [sq_nonneg a, sq_nonneg b]
  simp only [mul_pow, Real.sq_sqrt hε.le, Real.sq_sqrt hr]
  have hτ2 : (1 - τ) ^ 2 ≤ 1 := by nlinarith
  generalize ((1 - τ) / √2 + τ) ^ 2 = k at hk2 ⊢
  generalize (1 - τ) ^ 2 = u at hτ2 ⊢
  have hεab : ε * (a ^ 2 + b ^ 2) = ε := by rw [hab, mul_one]
  nlinarith [mul_nonneg (mul_nonneg hε.le hr) (sub_nonneg.2 hτ2),
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 (hε1.le.trans one_le_two)) hε.le)
      (sq_nonneg a)) (sub_nonneg.2 hk2)]

private theorem continuous_homotopyVec {ε : ℝ} :
    Continuous fun p : unitInterval × TopCat.diskBoundary.{0} 2 ↦ homotopyVec ε p.1
      ((p.2.down : EuclideanSpace ℝ (Fin 2)) 0) ((p.2.down : EuclideanSpace ℝ (Fin 2)) 1) := by
  have h0 := (continuous_diskBoundary_apply 0).comp (continuous_snd (X := unitInterval))
  have h1 := (continuous_diskBoundary_apply 1).comp (continuous_snd (X := unitInterval))
  have hτ : Continuous fun p : unitInterval × TopCat.diskBoundary.{0} 2 ↦ (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · exact (continuous_const.mul h0).mul (((continuous_const.sub hτ).div_const _).add hτ)
  · exact continuous_const.mul h1
  · exact (continuous_const.sub hτ).mul (((continuous_const.sub (continuous_const.mul
      (((h0.pow 2).div_const _).add (h1.pow 2)))).sqrt))

/-- **The attaching map of the maximum winds twice around the core.** The attaching map
`α₊ : S¹ → {f ≤ 2 - ε}` of `TauCeti.projectivePlaneChart` is homotopic to the double cover
`s ↦ [s₀ : s₁ : 0]` of the projective line `{z = 0}`, by the straight-line homotopy of
homogeneous coordinates which lowers the coordinate `z` to `0`. -/
theorem homotopic_morseAttachingMap_projectivePlaneChart_projectivePlaneCoreDoubleCover {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    (projectivePlaneChart.morseAttachingMap le_rfl hε.le
      (closedBall_subset_projectivePlaneChart_target hε1)
      projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart).hom.Homotopic
      (projectivePlaneCoreDoubleCover (c := 2 - ε) (by linarith)).hom := by
  refine ⟨{
    toFun p := ⟨mk ℝ (homotopyVec ε p.1 ((p.2.down : EuclideanSpace ℝ (Fin 2)) 0)
        ((p.2.down : EuclideanSpace ℝ (Fin 2)) 1))
        (homotopyVec_ne_zero hε p.1.2.1 p.1.2.2 (sq_add_sq_diskBoundary_two_eq_one p.2)),
      projectivePlaneMoment_mk_homotopyVec_le hε hε1 p.1.2.1 p.1.2.2
        (sq_add_sq_diskBoundary_two_eq_one p.2)⟩
    continuous_toFun := (continuous_mk continuous_homotopyVec _).subtype_mk _
    map_zero_left s := Subtype.ext ?_
    map_one_left s := Subtype.ext ?_ }⟩
  · have hq := one_sub_mul_pos hε.le hε1 s
    refine Eq.trans ?_ (coe_morseAttachingMap_projectivePlaneChart_apply hε.le hε1 s).symm
    rw [affineChart_symm_apply, mk_eq_mk_iff']
    refine ⟨√(1 - ε * ((s.down : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 / 2 +
      (s.down : EuclideanSpace ℝ (Fin 2)) 1 ^ 2)), ?_⟩
    have hs : √(1 - ε * ((s.down : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 * 2⁻¹ +
        (s.down : EuclideanSpace ℝ (Fin 2)) 1 ^ 2)) ≠ 0 := by
      simpa [div_eq_mul_inv] using (Real.sqrt_pos.2 hq).ne'
    ext i
    fin_cases i <;> simp [homotopyVec, insertNth_two_one, div_eq_mul_inv, mul_inv_cancel_left₀ hs]
  · refine Eq.trans ?_ (coe_projectivePlaneCoreDoubleCover_apply _ s).symm
    rw [mk_eq_mk_iff']
    refine ⟨√ε, ?_⟩
    ext i
    fin_cases i <;> simp [homotopyVec]

private theorem morseCellMap_projectivePlaneNegChart (ε : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    projectivePlaneNegChart.morseCellMap le_rfl ε w =
      projectivePlaneChart.morseCellMap le_rfl ε (projectivePlaneReflection w) := by
  rw [OpenPartialHomeomorph.morseCellMap_def, OpenPartialHomeomorph.morseCellMap_def,
    projectivePlaneNegChart_symm_apply]
  congr 1
  ext j
  fin_cases j <;> simp

/-- The attaching maps of the two charts differ strictly by the reflection
`r : (s₀, s₁) ↦ (-s₀, s₁)` of the circle: `α₋ = α₊ ∘ r`. -/
theorem morseAttachingMap_projectivePlaneNegChart {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    projectivePlaneNegChart.morseAttachingMap le_rfl hε
        (closedBall_subset_projectivePlaneNegChart_target hε1)
        projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart =
      projectivePlaneReflection.diskBoundaryIso.hom ≫ projectivePlaneChart.morseAttachingMap
        le_rfl hε (closedBall_subset_projectivePlaneChart_target hε1)
        projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart := by
  ext s
  rw [ConcreteCategory.comp_apply, OpenPartialHomeomorph.coe_morseAttachingMap_apply,
    OpenPartialHomeomorph.coe_morseAttachingMap_apply, morseCellMap_projectivePlaneNegChart,
    LinearIsometryEquiv.coe_diskBoundaryIso_hom_apply_down]

/-- The characteristic maps of the two charts differ strictly by the reflection
`r : (w₀, w₁) ↦ (-w₀, w₁)` of the disc: `χ₋ = χ₊ ∘ r`. -/
theorem morseCharacteristicMap_projectivePlaneNegChart {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    projectivePlaneNegChart.morseCharacteristicMap le_rfl hε
        (closedBall_subset_projectivePlaneNegChart_target hε1)
        projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart =
      projectivePlaneReflection.diskIso.hom ≫ projectivePlaneChart.morseCharacteristicMap
        le_rfl hε (closedBall_subset_projectivePlaneChart_target hε1)
        projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart := by
  ext w
  rw [ConcreteCategory.comp_apply, OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
    OpenPartialHomeomorph.coe_morseCharacteristicMap_apply, morseCellMap_projectivePlaneNegChart,
    LinearIsometryEquiv.coe_diskIso_hom_apply_down]

/-- The attaching map `α₊` of `TauCeti.projectivePlaneChart` has degree `2`: it winds twice around
the core of the lower sublevel. -/
theorem projectivePlaneSublevelDegree_morseAttachingMap_projectivePlaneChart {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    projectivePlaneSublevelDegree (c := 2 - ε) (by linarith)
      (projectivePlaneChart.morseAttachingMap le_rfl hε.le
        (closedBall_subset_projectivePlaneChart_target hε1)
        projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart).hom = 2 := by
  rw [projectivePlaneSublevelDegree_eq_of_homotopic _
      (homotopic_morseAttachingMap_projectivePlaneChart_projectivePlaneCoreDoubleCover hε hε1),
    projectivePlaneSublevelDegree_projectivePlaneCoreDoubleCover]

/-- The attaching map `α₋` of `TauCeti.projectivePlaneNegChart` has degree `-2`. -/
theorem projectivePlaneSublevelDegree_morseAttachingMap_projectivePlaneNegChart {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    projectivePlaneSublevelDegree (c := 2 - ε) (by linarith)
      (projectivePlaneNegChart.morseAttachingMap le_rfl hε.le
        (closedBall_subset_projectivePlaneNegChart_target hε1)
        projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart).hom = -2 := by
  rw [morseAttachingMap_projectivePlaneNegChart hε.le hε1, TopCat.hom_comp,
    projectivePlaneSublevelDegree_eq_of_homotopic _ (ContinuousMap.Homotopic.comp
      (homotopic_morseAttachingMap_projectivePlaneChart_projectivePlaneCoreDoubleCover hε hε1)
      (.refl _)),
    ← TopCat.hom_comp, projectivePlaneSublevelDegree_diskBoundaryIso_projectivePlaneCoreDoubleCover]

/-- The attaching maps `α₊` and `α₋` of the two charts are not homotopic as maps
`S¹ → {f ≤ 2 - ε}`, since their degrees `2` and `-2` differ. -/
theorem not_homotopic_morseAttachingMap_projectivePlaneChart_projectivePlaneNegChart {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ¬ (projectivePlaneChart.morseAttachingMap le_rfl hε.le
        (closedBall_subset_projectivePlaneChart_target hε1)
        projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart).hom.Homotopic
      (projectivePlaneNegChart.morseAttachingMap le_rfl hε.le
        (closedBall_subset_projectivePlaneNegChart_target hε1)
        projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart).hom := fun h ↦ by
  have := projectivePlaneSublevelDegree_eq_of_homotopic (by linarith) h
  rw [projectivePlaneSublevelDegree_morseAttachingMap_projectivePlaneChart hε hε1,
    projectivePlaneSublevelDegree_morseAttachingMap_projectivePlaneNegChart hε hε1] at this
  norm_num at this

/-- Since `α₋ = α₊ ∘ r` strictly, the map which is the identity on `{f ≤ 2 - ε}` and the reflection
`r : (w₀, w₁) ↦ (-w₀, w₁)` on the disc is a homeomorphism between the two cell attachments
`{f ≤ 2 - ε} ∪_{α₋} D² ≅ {f ≤ 2 - ε} ∪_{α₊} D²`, relative to the lower sublevel. Since also
`χ₋ = χ₊ ∘ r`, it intertwines the handle-to-cell comparisons into `{f ≤ 2 + ε}`. -/
theorem exists_iso_morseCellAttachment_projectivePlaneNegChart_projectivePlaneChart {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ Φ : morseCellAttachment (fun _ : Unit ↦ projectivePlaneNegChart) (fun _ ↦ 2)
        (fun _ ↦ le_rfl) hε (fun _ ↦ closedBall_subset_projectivePlaneNegChart_target hε1)
        (fun _ ↦ projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart) ≅
      morseCellAttachment (fun _ : Unit ↦ projectivePlaneChart) (fun _ ↦ 2) (fun _ ↦ le_rfl) hε
        (fun _ ↦ closedBall_subset_projectivePlaneChart_target hε1)
        (fun _ ↦ projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart),
      morseCellAttachmentIncl (fun _ : Unit ↦ projectivePlaneNegChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε (fun _ ↦ closedBall_subset_projectivePlaneNegChart_target hε1)
          (fun _ ↦ projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart) ≫ Φ.hom =
        morseCellAttachmentIncl (fun _ : Unit ↦ projectivePlaneChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε (fun _ ↦ closedBall_subset_projectivePlaneChart_target hε1)
          (fun _ ↦ projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart) ∧
      morseCellAttachmentCell (fun _ : Unit ↦ projectivePlaneNegChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε (fun _ ↦ closedBall_subset_projectivePlaneNegChart_target hε1)
          (fun _ ↦ projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart) () ≫ Φ.hom =
        projectivePlaneReflection.diskIso.hom ≫
          morseCellAttachmentCell (fun _ : Unit ↦ projectivePlaneChart) (fun _ ↦ 2)
            (fun _ ↦ le_rfl) hε (fun _ ↦ closedBall_subset_projectivePlaneChart_target hε1)
            (fun _ ↦ projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart) () ∧
      Φ.hom ≫ morseCellComparison (fun _ : Unit ↦ projectivePlaneChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε (fun _ ↦ closedBall_subset_projectivePlaneChart_target hε1)
          (fun _ ↦ projectivePlaneMoment_eq_two_add_sum_projectivePlaneChart) =
        morseCellComparison (fun _ : Unit ↦ projectivePlaneNegChart) (fun _ ↦ 2)
          (fun _ ↦ le_rfl) hε (fun _ ↦ closedBall_subset_projectivePlaneNegChart_target hε1)
          (fun _ ↦ projectivePlaneMoment_eq_two_add_sum_projectivePlaneNegChart) :=
  ⟨morseCellAttachmentIso _ _ _ _ _ _ _ _ _ (fun _ ↦ projectivePlaneReflection.diskIso)
    (fun _ ↦ projectivePlaneReflection.diskBoundaryIso)
    (fun _ ↦ LinearIsometryEquiv.diskBoundaryIso_hom_comp_diskBoundaryInclusion _)
    (fun _ ↦ morseAttachingMap_projectivePlaneNegChart hε hε1),
    by simp, by simp, morseCellAttachmentIso_hom_comp_morseCellComparison _ _ _ _ _ _ _ _ _ _ _ _ _
      fun _ ↦ morseCharacteristicMap_projectivePlaneNegChart hε hε1⟩

/-! ### Admissibility of the width -/

/-- Every band of the moment function is compact, since the projective plane is. -/
theorem isCompact_projectivePlaneMoment_preimage_Icc (a b : ℝ) :
    IsCompact (projectivePlaneMoment ⁻¹' Icc a b) :=
  (isClosed_Icc.preimage continuous_projectivePlaneMoment).isCompact

/-- For `0 < ε < 1` the only critical point of the moment function in the band
`f⁻¹[2 - ε, 2 + ε]` is its maximum `[0 : 0 : 1]`, the centre of `TauCeti.projectivePlaneChart`. -/
theorem criticalPoints_projectivePlaneMoment_inter_preimage_Icc {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    criticalPoints 𝓘(ℝ, Fin 2 → ℝ) projectivePlaneMoment ∩
        projectivePlaneMoment ⁻¹' Icc (2 - ε) (2 + ε) =
      {mk ℝ (Pi.single 2 1) (by simp)} := by
  have hw : Function.Injective fun i : Fin 3 ↦ ((i : ℕ) : ℝ) :=
    Nat.cast_injective.comp Fin.val_injective
  rw [projectivePlaneMoment, criticalPoints_projectiveMomentFunction hw]
  ext x
  simp only [mem_inter_iff, mem_range, mem_preimage, mem_Icc, mem_singleton_iff]
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    rw [projectiveMomentFunction_mk_single] at hk
    fin_cases k
    · norm_num at hk; linarith
    · norm_num at hk; linarith
    · rfl
  · rintro rfl
    refine ⟨⟨2, rfl⟩, ?_⟩
    rw [projectiveMomentFunction_mk_single]
    norm_num
    linarith

/-- The centre of `TauCeti.projectivePlaneChart` is the maximum `[0 : 0 : 1]`. -/
theorem projectivePlaneChart_symm_zero :
    projectivePlaneChart.symm 0 = mk ℝ (Pi.single 2 1) (by simp) := by
  rw [projectivePlaneChart_symm_apply, show projectivePlaneMorseCoord.symm 0 = 0 by
    ext i; fin_cases i <;> simp, affineChart_symm_zero]

end TauCeti
