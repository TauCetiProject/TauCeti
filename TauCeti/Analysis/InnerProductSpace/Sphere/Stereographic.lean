/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# The 2-sphere as the one-point compactification of the plane

For a unit vector `v` of a finite-dimensional real inner product space `E`, Mathlib's
`onePointHyperplaneHomeoUnitSphere` identifies the one-point compactification of the hyperplane
`vᗮ` with the unit sphere of `E` by inverse stereographic projection from `v`. It sends the point
at infinity to `v` (`TauCeti.coe_onePointHyperplaneHomeoUnitSphere_infty`) and a point `w` of the
hyperplane to `(‖w‖² + 4)⁻¹ • (4 • w + (‖w‖² - 4) • v)`
(`TauCeti.coe_onePointHyperplaneHomeoUnitSphere_coe`).

When `E` is three-dimensional the hyperplane `vᗮ` is a plane, which `ℂ` parametrizes isometrically
(`TauCeti.complexIsometryOrthogonalSpanSingleton`). The unit sphere is then the one-point
compactification of `ℂ`, with the point at infinity at `v` and the unit circle on the great circle
`⟪x, v⟫ = 0` (`TauCeti.exists_onePoint_homeomorph_sphere_preimage_inner_eq_zero`).

## Main definitions

* `TauCeti.complexIsometryOrthogonalSpanSingleton hv`: a linear isometry of `ℂ` onto the plane
  orthogonal to a nonzero vector of a three-dimensional real inner product space.

## Main results

* `TauCeti.coe_onePointHyperplaneHomeoUnitSphere_infty`,
  `TauCeti.coe_onePointHyperplaneHomeoUnitSphere_coe`: the values of the inverse stereographic
  projection from the one-point compactification of a hyperplane.
* `TauCeti.exists_onePoint_homeomorph_sphere_preimage_inner_eq_zero`: the 2-sphere is the one-point
  compactification of the plane, with the unit circle on a great circle.
-/

public section

noncomputable section

open scoped InnerProductSpace

open Metric Module OnePoint Set

namespace TauCeti

section Hyperplane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {v : E}

/-- Inverse stereographic projection from a unit vector `v` sends the point at infinity of the
one-point compactification of the hyperplane `vᗮ` to `v`. -/
@[simp]
theorem coe_onePointHyperplaneHomeoUnitSphere_infty (hv : ‖v‖ = 1) :
    (onePointHyperplaneHomeoUnitSphere hv ∞ : E) = v := by
  rw [onePointHyperplaneHomeoUnitSphere, equivOfIsEmbeddingOfRangeEq_apply_infty]

/-- Inverse stereographic projection from a unit vector `v` sends a point `w` of the hyperplane
`vᗮ` to `(‖w‖² + 4)⁻¹ • (4 • w + (‖w‖² - 4) • v)`. -/
theorem coe_onePointHyperplaneHomeoUnitSphere_coe (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    (onePointHyperplaneHomeoUnitSphere hv w : E) =
      (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • (w : E) + (‖w‖ ^ 2 - 4) • v) := by
  rw [onePointHyperplaneHomeoUnitSphere, equivOfIsEmbeddingOfRangeEq_apply_coe]
  exact stereoInvFun_apply hv w

end Hyperplane

section Three

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 3)]

/-- A linear isometry of `ℂ` onto the plane orthogonal to a nonzero vector `v` of a
three-dimensional real inner product space. -/
def complexIsometryOrthogonalSpanSingleton {v : E} (hv : v ≠ 0) : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ :=
  haveI : Fact (finrank ℝ E = 2 + 1) := ⟨Fact.out (p := finrank ℝ E = 3)⟩
  Complex.isometryOfOrthonormal (OrthonormalBasis.fromOrthogonalSpanSingleton 2 hv)

/-- **The 2-sphere is the one-point compactification of the plane**, with the point at infinity at
any given point `v` and the unit circle on the great circle `⟪x, v⟫ = 0`. -/
theorem exists_onePoint_homeomorph_sphere_preimage_inner_eq_zero (v : sphere (0 : E) 1) :
    ∃ K : OnePoint ℂ ≃ₜ sphere (0 : E) 1, K ∞ = v ∧
      K ⁻¹' {x | ⟪(x : E), (v : E)⟫_ℝ = 0} = (↑) '' sphere (0 : ℂ) 1 := by
  have hv1 : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  have : Fact (finrank ℝ E = 2 + 1) := ⟨Fact.out (p := finrank ℝ E = 3)⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 2
  /- `K` is inverse stereographic projection from `v`, read on the plane `vᗮ` through the isometry
  with `ℂ` after scaling by `2`: stereographic projection from `v` puts the great circle `vᗮ` on
  the circle of radius `2`. -/
  let D : ℂ ≃ₜ (ℝ ∙ (v : E))ᗮ := (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero).trans
    (complexIsometryOrthogonalSpanSingleton (ne_zero_of_mem_unit_sphere v)).toHomeomorph
  let K : OnePoint ℂ ≃ₜ sphere (0 : E) 1 :=
    D.onePointCongr.trans (onePointHyperplaneHomeoUnitSphere hv1)
  have hKinf : K ∞ = v := by
    ext
    simp [K]
  have hDz (z : ℂ) : ‖D z‖ = 2 * ‖z‖ := by
    simp [D]
  have hinner (z : ℂ) : ⟪(K z : E), (v : E)⟫_ℝ = (‖D z‖ ^ 2 - 4) / (‖D z‖ ^ 2 + 4) := by
    have hDv : ⟪(D z : E), (v : E)⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (D z).2
    simp only [K, Homeomorph.trans_apply, Homeomorph.onePointCongr_apply, map_some]
    rw [coe_onePointHyperplaneHomeoUnitSphere_coe]
    simp [inner_add_left, inner_smul_left, hDv, hv1]
    field_simp
  refine ⟨K, hKinf, ?_⟩
  ext q
  induction q using OnePoint.rec with
  | infty => simp [hKinf, hv1]
  | coe z =>
    rw [mem_preimage, mem_ofPred_eq, hinner, coe_injective.mem_set_image, hDz,
      mem_sphere_zero_iff_norm]
    have hpos : 0 < (2 * ‖z‖) ^ 2 + 4 := by positivity
    rw [div_eq_zero_iff, or_iff_left hpos.ne']
    constructor
    · intro h
      nlinarith [norm_nonneg z]
    · intro h
      rw [h]
      norm_num

end Three

end TauCeti
