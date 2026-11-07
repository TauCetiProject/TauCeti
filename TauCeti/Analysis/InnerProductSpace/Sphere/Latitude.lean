/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Latitude coordinates on a unit sphere

Let `p` be a point of the unit sphere `S` of a real inner product space `E`, and let `S'` be the
unit sphere of the hyperplane `(ℝ ∙ p)ᗮ`, the equator of `S` relative to the poles `±p`. The
*latitude map*

`S' × [-1, 1] → S`, `(x, t) ↦ √(1 - t²) • x + t • p`

(`TauCeti.sphereLatitude`) is continuous. Its latitude `t` is the inner product of the image with
`p` (`TauCeti.inner_sphereLatitude_apply`). It sends the whole slice `t = 1` to `p` and the whole
slice `t = -1` to `-p`, and nothing else to these poles
(`TauCeti.sphereLatitude_apply_eq_iff_eq_one` and `TauCeti.sphereLatitude_apply_eq_neg_iff`). It
is injective on the open slab `-1 < t < 1` (`TauCeti.injOn_sphereLatitude`), and onto as soon as
the equator is nonempty (`TauCeti.sphereLatitude_surjective`). So `S` is the unreduced suspension
of its equator: the quotient of `S' × [-1, 1]` collapsing each end to a point.

This is the model map in Brown's proof of the generalized Schoenflies theorem: a bicollar
`S' × [-1, 1] → S` of an embedded codimension-one sphere is followed by the latitude map, and the
two outer regions of the complement are collapsed to the poles.

## Main definitions

* `TauCeti.sphereLatitude p`: the latitude map `S' × [-1, 1] → S`.

## Main results

* `TauCeti.sphereLatitude_apply_eq_iff_eq_one`, `TauCeti.sphereLatitude_apply_eq_neg_iff`: the
  preimages of the poles are the two end slices.
* `TauCeti.injOn_sphereLatitude`: injectivity away from the end slices.
* `TauCeti.sphereLatitude_surjective`: surjectivity.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
-/

public section

noncomputable section

open Metric Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- The latitude map lands on the unit sphere: `√(1 - t²) • x + t • p` has norm one for a unit
vector `x` orthogonal to `p` and `t ∈ [-1, 1]`. -/
private lemma norm_sqrt_smul_add_smul (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖√(1 - t ^ 2) • ((x : (ℝ ∙ (p : E))ᗮ) : E) + t • (p : E)‖ = 1 := by
  have hxp : ⟪((x : (ℝ ∙ (p : E))ᗮ) : E), (p : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (x : (ℝ ∙ (p : E))ᗮ).2
  have hx : ‖((x : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact norm_eq_of_mem_sphere x
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, norm_add_sq_real]
  simp [real_inner_smul_left, real_inner_smul_right, hxp, norm_smul,
    Real.sq_sqrt (show 0 ≤ 1 - t ^ 2 by linarith), hx]

/-- **The latitude map** of the unit sphere relative to the pole `p`: a point `x` of the unit
sphere of `(ℝ ∙ p)ᗮ` and a latitude `t ∈ [-1, 1]` give the point `√(1 - t²) • x + t • p` of the
unit sphere. -/
def sphereLatitude :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × Icc (-1 : ℝ) 1, sphere (0 : E) 1) where
  toFun z := ⟨√(1 - (z.2 : ℝ) ^ 2) • ((z.1 : (ℝ ∙ (p : E))ᗮ) : E) + (z.2 : ℝ) • (p : E),
    mem_sphere_zero_iff_norm.2 (norm_sqrt_smul_add_smul p z.1 z.2.2)⟩
  continuous_toFun := by fun_prop

/-- The coordinate formula for the latitude map. It is not a simp lemma, so that the simplifier
uses the characteristic lemmas `TauCeti.inner_sphereLatitude_apply`,
`TauCeti.sphereLatitude_apply_eq_iff_eq_one` and `TauCeti.sphereLatitude_apply_eq_neg_iff`
instead of expanding the formula. -/
theorem coe_sphereLatitude_apply (z : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × Icc (-1 : ℝ) 1) :
    (sphereLatitude p z : E) =
      √(1 - (z.2 : ℝ) ^ 2) • ((z.1 : (ℝ ∙ (p : E))ᗮ) : E) + (z.2 : ℝ) • (p : E) := (rfl)

/-- The latitude of `sphereLatitude p (x, t)` is `t`: its inner product with the pole `p`. -/
@[simp]
theorem inner_sphereLatitude_apply (z : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × Icc (-1 : ℝ) 1) :
    ⟪(sphereLatitude p z : E), (p : E)⟫ = z.2 := by
  have hxp : ⟪((z.1 : (ℝ ∙ (p : E))ᗮ) : E), (p : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (z.1 : (ℝ ∙ (p : E))ᗮ).2
  simp [coe_sphereLatitude_apply, inner_add_left, real_inner_smul_left, hxp]

/-- The latitude map sends a point to the pole `p` exactly on the slice `t = 1`. -/
@[simp]
theorem sphereLatitude_apply_eq_iff_eq_one
    {z : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × Icc (-1 : ℝ) 1} :
    sphereLatitude p z = p ↔ (z.2 : ℝ) = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subtype.ext ?_⟩
  · simpa [h] using (inner_sphereLatitude_apply p z).symm
  · simp [coe_sphereLatitude_apply, h]

/-- The latitude map sends a point to the pole `-p` exactly on the slice `t = -1`. -/
@[simp]
theorem sphereLatitude_apply_eq_neg_iff
    {z : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × Icc (-1 : ℝ) 1} :
    sphereLatitude p z = -p ↔ (z.2 : ℝ) = -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subtype.ext ?_⟩
  · simpa [h] using (inner_sphereLatitude_apply p z).symm
  · simp [coe_sphereLatitude_apply, h]

/-- The latitude map is injective away from the two end slices `t = ±1`. -/
theorem injOn_sphereLatitude :
    InjOn (sphereLatitude p) {z | (z.2 : ℝ) ∈ Ioo (-1 : ℝ) 1} := by
  intro z hz z' _ h
  -- The latitudes agree, since they are the inner products with `p`.
  have ht : (z.2 : ℝ) = z'.2 := by
    rw [← inner_sphereLatitude_apply p z, ← inner_sphereLatitude_apply p z', h]
  have hpos : √(1 - (z.2 : ℝ) ^ 2) ≠ 0 := by
    have : (z.2 : ℝ) ^ 2 < 1 := by nlinarith [hz.1, hz.2]
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  have hx := congrArg (fun q : sphere (0 : E) 1 ↦ (q : E) - (z.2 : ℝ) • (p : E)) h
  simp only [coe_sphereLatitude_apply, ← ht, add_sub_cancel_right] at hx
  exact Prod.ext (Subtype.ext (Subtype.ext (smul_right_injective E hpos hx))) (Subtype.ext ht)

/-- The latitude map is onto as soon as the equator is nonempty, that is, as soon as the
hyperplane `(ℝ ∙ p)ᗮ` is nontrivial. -/
theorem sphereLatitude_surjective [Nontrivial (ℝ ∙ (p : E))ᗮ] :
    Function.Surjective (sphereLatitude p) := by
  intro q
  set t := ⟪(q : E), (p : E)⟫ with ht
  have hq : ‖(q : E)‖ = 1 := norm_eq_of_mem_sphere q
  have hp : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  have htI : t ∈ Icc (-1 : ℝ) 1 := by
    have := abs_real_inner_le_norm (q : E) (p : E)
    rw [hq, hp, one_mul] at this
    exact abs_le.1 this
  -- The component `v` of `q` orthogonal to `p`, of norm `√(1 - t²)`.
  set v : E := (q : E) - t • (p : E) with hv
  have hvp : v ∈ (ℝ ∙ (p : E))ᗮ := by
    refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
    simp [hv, ht, inner_sub_right, real_inner_smul_right, hp, real_inner_comm]
  have hnorm : ‖v‖ = √(1 - t ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v), hv, norm_sub_sq_real]
    simp [real_inner_smul_right, ← ht, norm_smul, hq, hp]
    ring_nf
  -- A unit vector `x` of the equator with `‖v‖ • x = v`.
  obtain ⟨x, hx⟩ : ∃ x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1,
      ‖v‖ • ((x : (ℝ ∙ (p : E))ᗮ) : E) = v := by
    by_cases hv0 : v = 0
    · obtain ⟨x, hx⟩ :=
        (NormedSpace.sphere_nonempty (x := (0 : (ℝ ∙ (p : E))ᗮ)) (r := 1)).2 zero_le_one
      exact ⟨⟨x, hx⟩, by simp [hv0]⟩
    · refine ⟨⟨‖v‖⁻¹ • ⟨v, hvp⟩, ?_⟩, ?_⟩
      · simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
      · simp [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0)]
  refine ⟨(x, ⟨t, htI⟩), Subtype.ext ?_⟩
  rw [coe_sphereLatitude_apply, ← hnorm, hx, hv, sub_add_cancel]

end TauCeti
