/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.UnitFundamentalDomain

/-!
# Norm-one and radial coordinates for archimedean parameters

A positive archimedean parameter `y` decomposes uniquely as `x t^(1/n)`, where
`n = [K : ℚ]`, `archNorm x = 1` and `t = archNorm y > 0`. The exponent uses the
number-field degree, not the number of infinite places: complex places have multiplicity two.

`surfaceScale` and `surfacePart` give these coordinates on Mathlib's `realSpace K`.
`archParamHomeomorphSurfaceProd` identifies the positive orthant with the product of the
norm-one hypersurface and `(0, ∞)`. The coordinates commute with the unit action, which
acts only on the norm-one factor. This is the change of variables for integrating a theta
series over a unit fundamental domain and then taking its radial Mellin transform.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- Scale an archimedean parameter by `t^(1/[K : ℚ])`. On the norm-one surface its
norm is `t`, so this is the radial coordinate measured by the field norm. -/
noncomputable def surfaceScale (x : realSpace K) (t : ℝ) : realSpace K :=
  fun w ↦ x w * t ^ (1 / (Module.finrank ℚ K : ℝ))

@[simp]
theorem surfaceScale_apply (x : realSpace K) (t : ℝ) (w : InfinitePlace K) :
    surfaceScale x t w = x w * t ^ (1 / (Module.finrank ℚ K : ℝ)) := (rfl)

@[simp]
theorem surfaceScale_one (x : realSpace K) : surfaceScale x 1 = x := by
  ext w
  simp

/-- Successive nonnegative radial scalings multiply their norm coordinates. -/
theorem surfaceScale_surfaceScale (x : realSpace K) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    surfaceScale (surfaceScale x s) t = surfaceScale x (s * t) := by
  ext w
  simp [Real.mul_rpow hs ht, mul_assoc]

theorem surfaceScale_pos {x : realSpace K} (hx : ∀ w, 0 < x w) {t : ℝ} (ht : 0 < t)
    (w : InfinitePlace K) : 0 < surfaceScale x t w :=
  mul_pos (hx w) (Real.rpow_pos_of_pos ht _)

/-- Radial scaling multiplies the archimedean norm by exactly `t`. -/
theorem archNorm_surfaceScale (x : realSpace K) {t : ℝ} (ht : 0 ≤ t) :
    archNorm (surfaceScale x t) = archNorm x * t := by
  classical
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  simp only [archNorm_apply, surfaceScale_apply, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, sum_mult_eq]
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht, one_div_mul_cancel hn, Real.rpow_one]

/-- Remove the norm coordinate of a parameter. For positive `y`, this is
`y / archNorm(y)^(1/[K : ℚ])` and belongs to the norm-one hypersurface. -/
noncomputable def surfacePart (y : realSpace K) : realSpace K :=
  surfaceScale y (archNorm y)⁻¹

theorem surfacePart_def (y : realSpace K) :
    surfacePart y = surfaceScale y (archNorm y)⁻¹ := (rfl)

@[simp]
theorem surfacePart_apply (y : realSpace K) (hy : 0 ≤ archNorm y) (w : InfinitePlace K) :
    surfacePart y w = y w / (archNorm y) ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  simp [surfacePart_def, Real.inv_rpow hy, div_eq_mul_inv]

/-- The normalized parameter is positive and has norm one. -/
theorem surfacePart_mem_normOneSurface {y : realSpace K} (hy : ∀ w, 0 < y w) :
    surfacePart y ∈ normOneSurface K := by
  have hN := archNorm_pos hy
  apply mem_normOneSurface.mpr
  exact ⟨surfaceScale_pos hy (inv_pos.mpr hN), by
    rw [surfacePart_def, archNorm_surfaceScale _ (inv_nonneg.mpr hN.le), mul_inv_cancel₀ hN.ne']⟩

@[simp]
theorem surfacePart_of_mem_normOneSurface {x : realSpace K} (hx : x ∈ normOneSurface K) :
    surfacePart x = x := by
  simp [surfacePart_def, (mem_normOneSurface.mp hx).2]

/-- Recover a positive parameter from its surface part and its norm. -/
@[simp]
theorem surfaceScale_surfacePart {y : realSpace K} (hy : ∀ w, 0 < y w) :
    surfaceScale (surfacePart y) (archNorm y) = y := by
  have hN := archNorm_pos hy
  rw [surfacePart_def, surfaceScale_surfaceScale _ (inv_nonneg.mpr hN.le) hN.le,
    inv_mul_cancel₀ hN.ne', surfaceScale_one]

/-- A positive radial scaling does not change the surface coordinate. -/
@[simp]
theorem surfacePart_surfaceScale {x : realSpace K} (hx : x ∈ normOneSurface K)
    {t : ℝ} (ht : 0 < t) : surfacePart (surfaceScale x t) = x := by
  rw [surfacePart_def, archNorm_surfaceScale _ ht.le, (mem_normOneSurface.mp hx).2, one_mul,
    surfaceScale_surfaceScale _ ht.le (inv_nonneg.mpr ht.le), mul_inv_cancel₀ ht.ne',
    surfaceScale_one]

/-- The norm of a scaled surface point is its radial coordinate. -/
@[simp]
theorem archNorm_surfaceScale_of_mem_normOneSurface {x : realSpace K}
    (hx : x ∈ normOneSurface K) {t : ℝ} (ht : 0 ≤ t) :
    archNorm (surfaceScale x t) = t := by
  simp [archNorm_surfaceScale x ht, (mem_normOneSurface.mp hx).2]

/-- Uniqueness of the norm-one/radial decomposition, without choosing a surface representative. -/
theorem surfaceScale_eq_iff {x y : realSpace K} (hx : x ∈ normOneSurface K)
    (hy : ∀ w, 0 < y w) {t : ℝ} (ht : 0 < t) :
    surfaceScale x t = y ↔ surfacePart y = x ∧ archNorm y = t := by
  constructor
  · rintro rfl
    exact ⟨surfacePart_surfaceScale hx ht, archNorm_surfaceScale_of_mem_normOneSurface hx ht.le⟩
  · rintro ⟨hpart, hnorm⟩
    rw [← hpart, ← hnorm, surfaceScale_surfacePart hy]

/-- Joint continuity of radial scaling on all real radial coordinates. -/
theorem continuous_surfaceScale :
    Continuous (fun p : realSpace K × ℝ ↦ surfaceScale p.1 p.2) := by
  exact continuous_pi fun w ↦ ((continuous_apply w).comp continuous_fst).mul
    (continuous_snd.rpow_const fun _ ↦ Or.inr (by positivity))

/-- Continuity of normalization wherever the archimedean norm is nonzero. -/
theorem continuousOn_surfacePart :
    ContinuousOn (surfacePart : realSpace K → realSpace K) {y | archNorm y ≠ 0} := by
  apply continuousOn_pi.mpr
  intro w y hN
  simp only [surfacePart_def, surfaceScale_apply]
  exact ((continuous_apply w).continuousAt.mul
    ((continuous_archNorm.continuousAt.inv₀ hN).rpow_const
      (Or.inl (inv_ne_zero hN)))).continuousWithinAt

/-- Normalization is measurable on all of `realSpace K`, including where the norm vanishes. -/
theorem measurable_surfacePart : Measurable (surfacePart : realSpace K → realSpace K) :=
  Measurable.of_eval fun w ↦ (measurable_pi_apply w).mul
    ((continuous_archNorm.measurable.inv).pow_const _)

/-- Scaling a parameter of nonnegative norm by `c > 0` does not change its surface part. -/
theorem surfacePart_smul {c : ℝ} (hc : 0 < c) {y : realSpace K} (hy : 0 ≤ archNorm y) :
    surfacePart (c • y) = surfacePart y := by
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  have hcy : 0 ≤ archNorm (c • y) := by
    rw [archNorm_smul]
    positivity
  ext w
  rw [surfacePart_apply _ hcy, surfacePart_apply _ hy, archNorm_smul,
    Real.mul_rpow (by positivity) hy, ← Real.rpow_natCast, ← Real.rpow_mul hc.le,
    mul_one_div_cancel hn, Real.rpow_one, Pi.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hc.ne']

variable (K) in
/-- Positive archimedean parameters are the product of the norm-one hypersurface and the
positive radial coordinate, with inverse `(x,t) ↦ x t^(1/[K : ℚ])`. -/
noncomputable def archParamHomeomorphSurfaceProd :
    {y : realSpace K // ∀ w, 0 < y w} ≃ₜ normOneSurface K × Set.Ioi (0 : ℝ) where
  toFun y := (⟨surfacePart y.val, surfacePart_mem_normOneSurface y.property⟩,
    ⟨archNorm y.val, archNorm_pos y.property⟩)
  invFun p := ⟨surfaceScale p.1.val p.2.val,
    surfaceScale_pos (mem_normOneSurface.mp p.1.property).1 p.2.property⟩
  left_inv y := Subtype.ext (surfaceScale_surfacePart y.property)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (surfacePart_surfaceScale p.1.property p.2.property)
    · exact Subtype.ext (archNorm_surfaceScale_of_mem_normOneSurface p.1.property p.2.property.le)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuousOn_surfacePart.comp_continuous continuous_subtype_val
        (fun y ↦ (archNorm_pos y.property).ne')
    · exact (continuous_archNorm.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_surfaceScale.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))

@[simp]
theorem archParamHomeomorphSurfaceProd_apply_surface
    (y : {y : realSpace K // ∀ w, 0 < y w}) :
    ((archParamHomeomorphSurfaceProd K y).1 : realSpace K) = surfacePart y := (rfl)

@[simp]
theorem archParamHomeomorphSurfaceProd_apply_norm
    (y : {y : realSpace K // ∀ w, 0 < y w}) :
    ((archParamHomeomorphSurfaceProd K y).2 : ℝ) = archNorm y.val := (rfl)

@[simp]
theorem archParamHomeomorphSurfaceProd_symm_apply (x : normOneSurface K) (t : Set.Ioi (0 : ℝ)) :
    ((archParamHomeomorphSurfaceProd K).symm (x, t) : realSpace K) = surfaceScale x t := (rfl)

/-- Unit scaling acts only on the surface coordinate, not on the radial coordinate. -/
@[simp]
theorem surfaceScale_unitScale (u : (𝓞 K)ˣ) (x : realSpace K) (t : ℝ) :
    surfaceScale (unitScale u x) t = unitScale u (surfaceScale x t) := by
  ext w
  simp [mul_assoc]

@[simp]
theorem surfacePart_unitScale (u : (𝓞 K)ˣ) (y : realSpace K) :
    surfacePart (unitScale u y) = unitScale u (surfacePart y) := by
  simp [surfacePart_def]

end TauCeti.LFunctions
