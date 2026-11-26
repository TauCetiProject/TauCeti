/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Projection
public import Mathlib.Probability.CDF

/-!
# Orthogonal splitting of the standard Gaussian measure

For a subspace `F` of a finite-dimensional real inner product space `E`, the standard Gaussian
`stdGaussian E` is the image of the product `stdGaussian F ⊗ stdGaussian Fᗮ` under the addition
map `F × Fᗮ → E`, `(y, z) ↦ y + z`. Equivalently, the pair of orthogonal projections onto `F`
and `Fᗮ` has the product law. This is the form in which Fubini over `Fᗮ` is applied to `γ_E`.

In one dimension: the coordinate `⟪x, ν⟫` along a vector `ν` has law `gaussianReal 0 ‖ν‖²`
under `stdGaussian E`, so for a unit vector `ν` the half-space `{x | ⟪x, ν⟫ < s}` has measure
`Φ(s) = cdf (gaussianReal 0 1) s`.

## Main declarations

* `Submodule.map_orthogonalProjectionOnto_prod_stdGaussian`: the joint law of the projections
  onto `F` and `Fᗮ` is `stdGaussian F ⊗ stdGaussian Fᗮ`.
* `Submodule.map_add_prod_stdGaussian`: the addition map carries
  `stdGaussian F ⊗ stdGaussian Fᗮ` to `stdGaussian E`.
* `Submodule.stdGaussian_preimage_orthogonalProjectionOnto`: for any `U ⊆ F`, the cylinder
  `U ⊕ Fᗮ`, the preimage of `U` under the orthogonal projection onto `F` (see
  `Submodule.preimage_orthogonalProjectionOnto_eq`), has Gaussian measure `γ_F(U)`.
* `TauCeti.Probability.map_inner_stdGaussian`: the law of `⟪x, ν⟫` is `gaussianReal 0 ‖ν‖²`,
  and `gaussianReal 0 1` for a unit vector (`map_inner_stdGaussian_of_norm_eq_one`).
* `TauCeti.Probability.measureReal_stdGaussian_setOf_inner_lt`,
  `TauCeti.Probability.measureReal_stdGaussian_setOf_inner_le`: for a unit vector `ν`, the open
  and the closed half-spaces `{x | ⟪x, ν⟫ < s}` and `{x | ⟪x, ν⟫ ≤ s}` have measure `Φ(s)`.

## References

* E. Milman and J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*,
  Ann. of Math. 195 (2022), Section 2.
* M. Ledoux, *Isoperimetry and Gaussian analysis*, Lectures on probability theory and
  statistics (Saint-Flour, 1994), Lecture Notes in Math. 1648, Springer, 1996.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Submodule

/-- The orthogonal projections of a standard Gaussian onto a subspace `F` and onto its
orthogonal complement have the product law `stdGaussian F ⊗ stdGaussian Fᗮ`. -/
@[simp]
theorem map_orthogonalProjectionOnto_prod_stdGaussian (F : Submodule ℝ E) :
    (stdGaussian E).map (fun x ↦ (F.orthogonalProjectionOnto x, Fᗮ.orthogonalProjectionOnto x)) =
      (stdGaussian F).prod (stdGaussian Fᗮ) := by
  let K : Fin 2 → Submodule ℝ E := ![F, Fᗮ]
  have hK : Pairwise fun i j ↦ K i ⟂ K j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact F.isOrtho_orthogonal_right
    · exact F.isOrtho_orthogonal_left
    · exact absurd rfl hij
  have hind : IndepFun (fun x ↦ F.orthogonalProjectionOnto x)
      (fun x ↦ Fᗮ.orthogonalProjectionOnto x) (stdGaussian E) :=
    (TauCeti.Probability.iIndepFun_orthogonalProjectionOnto_stdGaussian K hK).indepFun
      (i := 0) (j := 1) (by decide)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1 hind,
    F.map_orthogonalProjectionOnto_stdGaussian, Fᗮ.map_orthogonalProjectionOnto_stdGaussian]

/-- **Orthogonal splitting of the standard Gaussian.** For a subspace `F`, the addition map
`F × Fᗮ → E`, `(y, z) ↦ y + z`, carries `stdGaussian F ⊗ stdGaussian Fᗮ` to `stdGaussian E`. -/
@[simp]
theorem map_add_prod_stdGaussian (F : Submodule ℝ E) :
    ((stdGaussian F).prod (stdGaussian Fᗮ)).map (fun p ↦ (p.1 : E) + p.2) = stdGaussian E := by
  rw [← F.map_orthogonalProjectionOnto_prod_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  convert Measure.map_id
  funext x
  exact F.starProjection_add_starProjection_orthogonal x

/-- **The Gaussian measure of a cylinder.** For any `U ⊆ F`, the cylinder `U ⊕ Fᗮ`, the
preimage of `U` under the orthogonal projection onto `F`, has standard Gaussian measure
`γ_E(U ⊕ Fᗮ) = γ_F(U)`. No measurability of `U` is needed, since the addition map
`F × Fᗮ → E` is a measurable embedding. -/
theorem stdGaussian_preimage_orthogonalProjectionOnto (F : Submodule ℝ E) (U : Set F) :
    stdGaussian E (F.orthogonalProjectionOnto ⁻¹' U) = stdGaussian F U := by
  have he : MeasurableEmbedding (fun p : F × Fᗮ ↦ (p.1 : E) + p.2) := by
    convert (F.prodEquivOfIsCompl Fᗮ F.isCompl_orthogonal).toContinuousLinearEquiv.toHomeomorph
      |>.measurableEmbedding using 1
    funext p
    simp [Submodule.coe_prodEquivOfIsCompl']
  have hpre : (fun p : F × Fᗮ ↦ (p.1 : E) + p.2) ⁻¹' (F.orthogonalProjectionOnto ⁻¹' U) =
      U ×ˢ univ := by
    ext ⟨y, z⟩
    simp [F.orthogonalProjectionOnto_eq_zero_iff.2 z.property]
  rw [← F.map_add_prod_stdGaussian, he.map_apply, hpre, Measure.prod_prod, measure_univ, mul_one]

end Submodule

namespace TauCeti.Probability

/-- Under the standard Gaussian, the coordinate `⟪x, ν⟫` along a vector `ν` has law
`gaussianReal 0 ‖ν‖²`. -/
@[simp]
theorem map_inner_stdGaussian (ν : E) :
    (stdGaussian E).map (fun x ↦ ⟪x, ν⟫) = gaussianReal 0 (‖ν‖₊ ^ 2) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ ν)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  have hfun : (fun x ↦ ⟪x, ν⟫) = innerSL ℝ ν := by
    funext x
    simp [real_inner_comm]
  rw [hfun, h]
  congr 1
  ext
  simp

/-- Under the standard Gaussian, the coordinate `⟪x, ν⟫` along a unit vector `ν` has the
standard normal law. -/
theorem map_inner_stdGaussian_of_norm_eq_one {ν : E} (hν : ‖ν‖ = 1) :
    (stdGaussian E).map (fun x ↦ ⟪x, ν⟫) = gaussianReal 0 1 := by
  have hν' : ‖ν‖₊ ^ 2 = 1 := by simp [← NNReal.coe_inj, hν]
  rw [map_inner_stdGaussian, hν']

/-- **Gaussian measure of a closed half-space.** For a unit vector `ν` and a real `s`, the
standard Gaussian measure of `{x | ⟪x, ν⟫ ≤ s}` is `Φ(s)`, the standard normal distribution
function at `s`. -/
theorem measureReal_stdGaussian_setOf_inner_le {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) :
    (stdGaussian E).real {x | ⟪x, ν⟫ ≤ s} = cdf (gaussianReal 0 1) s := by
  rw [← preimage_ofPred_eq (p := (· ≤ s)) (f := fun x ↦ ⟪x, ν⟫), Iic_def,
    ← map_measureReal_apply (by fun_prop) measurableSet_Iic,
    map_inner_stdGaussian_of_norm_eq_one hν, cdf_eq_real]

/-- **Gaussian measure of an open half-space.** For a unit vector `ν` and a real `s`, the
standard Gaussian measure of `{x | ⟪x, ν⟫ < s}` is `Φ(s)`. -/
theorem measureReal_stdGaussian_setOf_inner_lt {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) :
    (stdGaussian E).real {x | ⟪x, ν⟫ < s} = cdf (gaussianReal 0 1) s := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [← preimage_ofPred_eq (p := (· < s)) (f := fun x ↦ ⟪x, ν⟫), Iio_def,
    ← map_measureReal_apply (by fun_prop) measurableSet_Iio,
    map_inner_stdGaussian_of_norm_eq_one hν, cdf_eq_real]
  exact measureReal_congr Iio_ae_eq_Iic

end TauCeti.Probability
