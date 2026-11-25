/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Intrinsic conformality of Hersch transformations

On the unit sphere, a Hersch transformation agrees with a spherical inversion followed by a
translation. Its differential scales the round inner product by the square of the positive
factor `√(1 - ‖a‖²) / (1 + ⟪a, x⟫)`. This holds in any dimension.

## References

* J. Hersch, *Quatre propriétés isopérimétriques de membranes sphériques homogènes*,
  C. R. Acad. Sci. Paris Sér. A-B 270 (1970), A1645–A1648.
-/

public noncomputable section

open Bundle EuclideanGeometry Metric Module
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_inv_one_add_sqrt_smul_sq {a : E} (ha : ‖a‖ ≤ 1) :
    let s := √(1 - ‖a‖ ^ 2)
    ‖(1 + s)⁻¹ • a‖ ^ 2 = (1 - s) / (1 + s) := by
  dsimp only
  set s := √(1 - ‖a‖ ^ 2)
  have hs : s ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg a])
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hs₁ : 0 < 1 + s := by positivity
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs₁.le), mul_pow, inv_pow,
    show ‖a‖ ^ 2 = 1 - s ^ 2 by linarith]
  field_simp
  ring

private theorem herschInversion_scale {a x : E} (hx : ‖x‖ = 1) :
    let s := √(1 - ‖a‖ ^ 2)
    let b := (1 + s)⁻¹ • a
    (√(1 - ‖b‖ ^ 2) / dist x (-b)) ^ 2 = s / (1 + ⟪a, x⟫_ℝ) := by
  dsimp only
  by_cases ha : ‖a‖ < 1
  swap
  · have hs : √(1 - ‖a‖ ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith [le_of_not_gt ha])
    simp [hs]
  set s := √(1 - ‖a‖ ^ 2)
  set b := (1 + s)⁻¹ • a with hb
  have hs₀ : 0 < s := Real.sqrt_pos.2 (by nlinarith [norm_nonneg a])
  have hs₁ : 0 < 1 + s := by positivity
  have hd : 0 < 1 + ⟪a, x⟫_ℝ := one_add_inner_pos ha hx.le
  have hb₂ : ‖b‖ ^ 2 = (1 - s) / (1 + s) := norm_inv_one_add_sqrt_smul_sq ha.le
  have hr : 1 - ‖b‖ ^ 2 = 2 * s / (1 + s) := by
    rw [hb₂]
    field_simp [hs₁.ne']
    ring
  have hd₂ : ‖x + b‖ ^ 2 = 2 * (1 + ⟪a, x⟫_ℝ) / (1 + s) := by
    rw [norm_add_sq_real, hx, hb₂, hb, real_inner_smul_right, real_inner_comm x a]
    field_simp
    ring
  have hr₀ : 0 ≤ 1 - ‖b‖ ^ 2 := by rw [hr]; positivity
  rw [div_pow, Real.sq_sqrt hr₀, dist_eq_norm, sub_neg_eq_add, hr, hd₂]
  field_simp

/-- On the unit sphere, Hersch's map is a spherical inversion followed by a translation. -/
theorem herschMap_eq_add_inversion {a x : E} (ha : ‖a‖ < 1) (hx : ‖x‖ = 1) :
    let b := (1 + √(1 - ‖a‖ ^ 2))⁻¹ • a
    herschMap a x = 2 • b + inversion (-b) (√(1 - ‖b‖ ^ 2)) x := by
  dsimp only
  set s := √(1 - ‖a‖ ^ 2) with hs
  set b := (1 + s)⁻¹ • a with hb
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hd : 0 < 1 + ⟪a, x⟫_ℝ := one_add_inner_pos ha hx.le
  have hscale : (√(1 - ‖b‖ ^ 2) / dist x (-b)) ^ 2 = s / (1 + ⟪a, x⟫_ℝ) :=
    herschInversion_scale hx
  have hcoeff : (1 + ⟪a, x⟫_ℝ)⁻¹ * (⟪a, x⟫_ℝ / (1 + s) + 1) =
      (1 + s)⁻¹ + (s / (1 + ⟪a, x⟫_ℝ)) * (1 + s)⁻¹ := by
    field_simp
    ring
  simp only [inversion, vsub_eq_sub, vadd_eq_add, sub_neg_eq_add, herschMap_def, ← hs, two_nsmul]
  rw [hscale, hb, smul_add, smul_smul, smul_smul, hcoeff, div_eq_inv_mul s]
  module

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

private theorem mvfderiv_coe_herschHomeomorph {a : E} (ha : ‖a‖ < 1)
    (x : sphere (0 : E) 1) (u : TangentSpace (𝓡 n) x) :
    let b := (1 + √(1 - ‖a‖ ^ 2))⁻¹ • a
    let g : sphere (0 : E) 1 → sphere (0 : E) 1 := herschHomeomorph ha
    let j : sphere (0 : E) 1 → E := (↑)
    mvfderiv (𝓡 n) j (g x) (mfderiv (𝓡 n) (𝓡 n) g x u) =
      (√(1 - ‖a‖ ^ 2) / (1 + ⟪a, (x : E)⟫_ℝ)) •
        (ℝ ∙ ((x : E) + b))ᗮ.reflection (mvfderiv (𝓡 n) j x u) := by
  dsimp only
  set b := (1 + √(1 - ‖a‖ ^ 2))⁻¹ • a with hb_def
  let g : sphere (0 : E) 1 → sphere (0 : E) 1 := herschHomeomorph ha
  let j : sphere (0 : E) 1 → E := (↑)
  let G : E → E := fun y ↦ 2 • b + inversion (-b) (√(1 - ‖b‖ ^ 2)) y
  have hb : ‖b‖ < 1 := by
    have hs : 0 ≤ √(1 - ‖a‖ ^ 2) := Real.sqrt_nonneg _
    rw [hb_def, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div,
      div_lt_one (by positivity)]
    linarith
  have hne (y : sphere (0 : E) 1) : (y : E) ≠ -b := fun hy ↦
    hb.ne (by simpa only [hy, norm_neg] using mem_sphere_zero_iff_norm.mp y.property)
  have heq : j ∘ g = G ∘ j := funext fun y ↦
    (coe_herschHomeomorph ha y).trans (herschMap_eq_add_inversion ha
      (mem_sphere_zero_iff_norm.mp y.property))
  have hj : ContMDiff (𝓡 n) 𝓘(ℝ, E) 1 j := contMDiff_coe_sphere
  have hGj : ContMDiff (𝓡 n) 𝓘(ℝ, E) 1 (j ∘ g) := by
    rw [heq]
    intro y
    have hG : ContDiffAt ℝ 1 G (j y) :=
      contDiffAt_const.add (contDiffAt_const.inversion contDiffAt_const contDiffAt_id (hne y))
    exact hG.contMDiffAt.comp y (hj y)
  have hg : MDifferentiable (𝓡 n) (𝓡 n) g :=
    (hGj.codRestrict_sphere fun y ↦ (g y).property).mdifferentiable one_ne_zero
  have hG := (hasFDerivAt_inversion (R := √(1 - ‖b‖ ^ 2)) (hne x)).const_add (2 • b)
  rw [← mvfderiv_comp_apply x (hj.mdifferentiable (by simp) (g x)) (hg x), heq,
    mvfderiv_comp_apply_of_differentiableAt (φ := G) hG.differentiableAt
      (hj.mdifferentiable (by simp) x)]
  change fderiv ℝ (fun z ↦ 2 • b + inversion (-b) (√(1 - ‖b‖ ^ 2)) z)
    (x : E) (mvfderiv (𝓡 n) j x u) = _
  rw [hG.fderiv, sub_neg_eq_add, smul_apply,
    herschInversion_scale (mem_sphere_zero_iff_norm.mp x.property)]
  rfl

/-- The differential of a Hersch transformation is conformal for the intrinsic round metric,
with length factor `√(1 - ‖a‖²) / (1 + ⟪a, x⟫)`. -/
theorem inner_mfderiv_herschHomeomorph {a : E} (ha : ‖a‖ < 1)
    (x : sphere (0 : E) 1) (u v : TangentSpace (𝓡 n) x) :
    let g : sphere (0 : E) 1 → sphere (0 : E) 1 := herschHomeomorph ha
    ⟪mfderiv (𝓡 n) (𝓡 n) g x u, mfderiv (𝓡 n) (𝓡 n) g x v⟫_ℝ =
      (√(1 - ‖a‖ ^ 2) / (1 + ⟪a, (x : E)⟫_ℝ)) ^ 2 * ⟪u, v⟫_ℝ := by
  dsimp only
  rw [inner_tangentSpace_sphere, mvfderiv_coe_herschHomeomorph ha x u,
    mvfderiv_coe_herschHomeomorph ha x v, real_inner_smul_left, real_inner_smul_right,
    LinearIsometryEquiv.inner_map_map, ← inner_tangentSpace_sphere]
  ring

end TauCeti
