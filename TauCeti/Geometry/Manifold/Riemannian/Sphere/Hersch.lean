/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Inversion
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Geometry.Euclidean.Inversion
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Intrinsic conformality of Hersch transformations

For `‖a‖ < 1`, on the unit sphere a Hersch transformation agrees with a spherical inversion
followed by a translation. Its differential scales the round inner product by the square of
the positive factor `√(1 - ‖a‖²) / (1 + ⟪a, x⟫)`. This holds in any dimension and tracks
round metric distortion when using Hersch maps to balance sphere-valued test functions.

The proof uses `EuclideanGeometry.hasFDerivAt_inversion` for differentiability,
`EuclideanGeometry.inner_fderiv_inversion` for the ambient metric scaling, and
`TauCeti.inner_tangentSpace_sphere` to pass to the intrinsic round metric.

## References

* J. Hersch, *Quatre propriétés isopérimétriques de membranes sphériques homogènes*,
  C. R. Acad. Sci. Paris Sér. A-B 270 (1970), A1645–A1648.
-/

public noncomputable section

open Bundle EuclideanGeometry Metric Module
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

private theorem mvfderiv_coe_herschHomeomorph {a : E} (ha : ‖a‖ < 1)
    (x : sphere (0 : E) 1) (u : TangentSpace (𝓡 n) x) :
    let b := (1 + √(1 - ‖a‖ ^ 2))⁻¹ • a
    let g : sphere (0 : E) 1 → sphere (0 : E) 1 := herschHomeomorph ha
    let j : sphere (0 : E) 1 → E := (↑)
    mvfderiv (𝓡 n) j (g x) (mfderiv (𝓡 n) (𝓡 n) g x u) =
      fderiv ℝ (inversion (-b) (√(1 - ‖b‖ ^ 2))) (x : E)
        (mvfderiv (𝓡 n) j x u) := by
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
    (coe_herschHomeomorph ha y).trans (herschMap_eq_add_inversion (one_add_inner_pos ha
      (mem_sphere_zero_iff_norm.mp y.property).le).ne'
      (mem_sphere_zero_iff_norm.mp y.property))
  have hj : ContMDiff (𝓡 n) 𝓘(ℝ, E) 1 j := contMDiff_coe_sphere
  have hGj : ContMDiff (𝓡 n) 𝓘(ℝ, E) 1 (j ∘ g) := by
    intro y
    have hH := contDiffAt_herschMap (n := 1) ha
      (inner_ne_neg_one ha (mem_sphere_zero_iff_norm.mp y.property).le)
    simpa only [Function.comp_def, g, j, coe_herschHomeomorph] using
      hH.contMDiffAt.comp y (contMDiffAt_const.prodMk_space (hj y))
  have hg : MDifferentiable (𝓡 n) (𝓡 n) g :=
    (hGj.codRestrict_sphere fun y ↦ (g y).property).mdifferentiable one_ne_zero
  have hG : DifferentiableAt ℝ G (j x) :=
    ((hasFDerivAt_inversion (R := √(1 - ‖b‖ ^ 2)) (hne x)).const_add (2 • b)).differentiableAt
  rw [← mvfderiv_comp_apply x (hj.mdifferentiable (by simp) (g x)) (hg x), heq,
    mvfderiv_comp_apply_of_differentiableAt (φ := G) hG
      (hj.mdifferentiable (by simp) x)]
  exact congrArg (fun f : E →L[ℝ] E ↦ f (mvfderiv (𝓡 n) j x u))
    (fderiv_const_add (2 • b))

/-- The differential of a Hersch transformation is conformal for the intrinsic round metric,
with length factor `√(1 - ‖a‖²) / (1 + ⟪a, x⟫)`. -/
theorem inner_mfderiv_herschHomeomorph {a : E} (ha : ‖a‖ < 1)
    (x : sphere (0 : E) 1) (u v : TangentSpace (𝓡 n) x) :
    let g : sphere (0 : E) 1 → sphere (0 : E) 1 := herschHomeomorph ha
    ⟪mfderiv (𝓡 n) (𝓡 n) g x u, mfderiv (𝓡 n) (𝓡 n) g x v⟫_ℝ =
      (√(1 - ‖a‖ ^ 2) / (1 + ⟪a, (x : E)⟫_ℝ)) ^ 2 * ⟪u, v⟫_ℝ := by
  dsimp only
  rw [inner_tangentSpace_sphere, mvfderiv_coe_herschHomeomorph ha x u,
    mvfderiv_coe_herschHomeomorph ha x v, inner_fderiv_inversion,
    pow_mul _ 2 2, inversion_factor_eq_hersch_length_factor
      (mem_sphere_zero_iff_norm.mp x.property), ← inner_tangentSpace_sphere]

end TauCeti
