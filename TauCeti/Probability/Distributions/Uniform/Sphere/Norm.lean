/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Probability.Distributions.Chi.Moments
import TauCeti.Probability.Distributions.Gaussian.Norm
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Mean norms and positively homogeneous integrals on the unit sphere

On a finite-dimensional real inner product space `E` of dimension `d`, polar factorization of the
standard Gaussian law (`TauCeti.Probability.stdGaussian_map_sphereDirection_prod_norm`) separates
any positively `1`-homogeneous observable `f : E → G` into a radial chi factor and a spherical
average:

`∫ x, f x ∂stdGaussian E = (∫ r, r ∂chiMeasure d 1) • ∫ u, f u ∂uniformSphereMeasure E`.

For `d ≥ 1` and a nonnegative positively `1`-homogeneous real function `f` (in particular any real
seminorm `p : Seminorm ℝ E`), the two-sided chi mean bounds `√(d / 2) ≤ 𝔼 ‖g‖ ≤ √d` from
`TauCeti.Probability.Distributions.Chi.Moments` yield the comparison

`(∫ x, p x ∂stdGaussian E) / √d ≤ ∫ u, p u ∂uniformSphereMeasure E` and
`∫ u, p u ∂uniformSphereMeasure E ≤ √(2 / d) * ∫ x, p x ∂stdGaussian E`.

Combining the lower bound with the Gaussian Rademacher-maximum estimate from
`TauCeti.Probability.Distributions.Gaussian.Norm` gives the mean-norm lower bound on the sphere:
if `b` is an orthonormal basis of `E` with `c ≤ p (b i)` for every `i` (where `0 ≤ c`), then

`c * √(log d / d) / 32 ≤ ∫ u : sphere (0 : E) 1, p u ∂uniformSphereMeasure E`

(in particular `(1 / 128) * √(log d / d)`, and hence `(1 / 400) * √(log d / d)`, when `c = 1 / 4`).
Specializing `p` to `(normSeminorm ℝ F).comp T` gives the corresponding lower bound for any real
linear map `T : E →ₗ[ℝ] F` into an arbitrary real seminormed space `F`, and evaluating on
`EuclideanSpace.basisFun` gives the coordinate form on `sphere (0 : EuclideanSpace ℝ ι) 1`.

## Main results

* `TauCeti.Probability.integral_stdGaussian_of_posHomog`: polar factorization of the standard
  Gaussian integral of a positively `1`-homogeneous vector-valued function.
* `TauCeti.Probability.div_sqrt_finrank_le_integral_seminorm_uniformSphereMeasure`,
  `TauCeti.Probability.integral_seminorm_uniformSphereMeasure_le_mul_sqrt_two_div_finrank`:
  two-sided comparison between Gaussian and spherical expectations of a seminorm.
* `TauCeti.Probability.mul_sqrt_log_finrank_div_le_integral_seminorm_uniformSphereMeasure`:
  logarithmic lower bound `c * √(log d / d) / 32` for the spherical mean of a seminorm.
* `TauCeti.Probability.mul_sqrt_log_finrank_div_le_integral_norm_comp_uniformSphereMeasure`,
  `TauCeti.Probability.mul_sqrt_log_card_div_le_integral_norm_sum_smul_uniformSphereMeasure`:
  norm forms for linear maps and Euclidean unit-sphere combinations.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 13.3.2 and Lemma 13.3.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real
open scoped BigOperators

namespace TauCeti.Probability

section PosHomog

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Polar factorization of Gaussian expectations.** For any positively `1`-homogeneous map
`f : E → G` into a real normed space whose restriction to the unit sphere is a.e. strongly
measurable, the standard Gaussian integral of `f` factors into the first moment of
`chiMeasure (finrank ℝ E) 1` times the uniform spherical integral of `f`. Neither completeness of
`G` nor nontriviality of `E` is required. -/
theorem integral_stdGaussian_of_posHomog [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G}
    (hf_meas : AEStronglyMeasurable (fun u : sphere (0 : E) 1 ↦ f u) (uniformSphereMeasure E))
    (hf_homog : ∀ {r : ℝ}, 0 < r → ∀ x : E, f (r • x) = r • f x) :
    ∫ x, f x ∂stdGaussian E =
      (∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1) •
        ∫ u : sphere (0 : E) 1, f u ∂uniformSphereMeasure E := by
  have hf0 : f 0 = 0 := by
    have h := hf_homog two_pos (0 : E)
    rw [smul_zero, two_smul] at h
    exact add_eq_left.1 h.symm
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hzero : ∀ x : E, f x = 0 := fun x ↦ Subsingleton.elim x 0 ▸ hf0
    have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun u ↦ (zero_ne_one' ℝ)
        (by simpa [Subsingleton.elim (u : E) 0] using norm_eq_of_mem_sphere u)⟩
    have hμ : uniformSphereMeasure E = 0 := Subsingleton.elim _ _
    simp [hzero, hμ]
  · have : IsProbabilityMeasure (chiMeasure (Module.finrank ℝ E) 1) :=
      isProbabilityMeasure_chiMeasure (Nat.cast_nonneg _) one_pos
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    let e : sphere (0 : E) 1 :=
      ⟨NormedSpace.normalize v, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hv)⟩
    have hdecomp (x : E) : f x = ‖x‖ • f (sphereDirection e x) := by
      rcases eq_or_ne x 0 with rfl | hx
      · simp [hf0]
      · conv_lhs => rw [← norm_smul_sphereDirection e x]
        exact hf_homog (norm_pos_iff.2 hx) _
    set Φ : E → sphere (0 : E) 1 × ℝ := fun x ↦ (sphereDirection e x, ‖x‖)
    have hΦ : Measurable Φ := (measurable_sphereDirection e).prodMk measurable_norm
    have hprod_meas : AEStronglyMeasurable (fun z : sphere (0 : E) 1 × ℝ ↦ z.2 • f z.1)
        ((uniformSphereMeasure E).prod (chiMeasure (Module.finrank ℝ E) 1)) :=
      measurable_snd.aestronglyMeasurable.smul hf_meas.comp_fst
    rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp)]
    have hmap : ∫ x, ‖x‖ • f (sphereDirection e x) ∂stdGaussian E =
        ∫ z, z.2 • f z.1 ∂(stdGaussian E).map Φ :=
      (integral_map hΦ.aemeasurable
        (by rw [stdGaussian_map_sphereDirection_prod_norm e]; exact hprod_meas)).symm
    rw [hmap, stdGaussian_map_sphereDirection_prod_norm e, ← integral_prod_swap]
    exact integral_prod_smul id (fun u : sphere (0 : E) 1 ↦ f u)

/-- In positive dimension, the uniform spherical integral of a positively `1`-homogeneous map is its
standard Gaussian integral divided by the chi radius mean. -/
theorem integral_uniformSphereMeasure_of_posHomog [Nontrivial E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G}
    (hf_meas : AEStronglyMeasurable (fun u : sphere (0 : E) 1 ↦ f u) (uniformSphereMeasure E))
    (hf_homog : ∀ {r : ℝ}, 0 < r → ∀ x : E, f (r • x) = r • f x) :
    ∫ u : sphere (0 : E) 1, f u ∂uniformSphereMeasure E =
      (∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1)⁻¹ • ∫ x, f x ∂stdGaussian E := by
  have hpos : 0 < ∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1 :=
    integral_id_chiMeasure_pos (Nat.cast_pos.2 Module.finrank_pos) one_pos
  rw [integral_stdGaussian_of_posHomog hf_meas hf_homog, inv_smul_smul₀ hpos.ne']

/-- For a nonnegative positively `1`-homogeneous real function on a nontrivial space `E`, dividing
its standard Gaussian expectation by `√(finrank ℝ E)` bounds its uniform spherical expectation from
below. -/
theorem div_sqrt_finrank_le_integral_uniformSphereMeasure_of_posHomog [Nontrivial E] {f : E → ℝ}
    (hf_meas : AEStronglyMeasurable (fun u : sphere (0 : E) 1 ↦ f u) (uniformSphereMeasure E))
    (hf_homog : ∀ {r : ℝ}, 0 < r → ∀ x : E, f (r • x) = r * f x)
    (hf_nonneg : ∀ u : sphere (0 : E) 1, 0 ≤ f u) :
    (∫ x, f x ∂stdGaussian E) / √(Module.finrank ℝ E) ≤
      ∫ u : sphere (0 : E) 1, f u ∂uniformSphereMeasure E := by
  have hd : 0 < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.2 Module.finrank_pos
  have hle : ∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1 ≤ √(Module.finrank ℝ E) := by
    simpa using integral_id_chiMeasure_le (k := Module.finrank ℝ E) zero_le_one
  have hsph0 : 0 ≤ ∫ u : sphere (0 : E) 1, f u ∂uniformSphereMeasure E :=
    integral_nonneg hf_nonneg
  rw [integral_stdGaussian_of_posHomog hf_meas hf_homog, smul_eq_mul,
    div_le_iff₀ (Real.sqrt_pos.2 hd), mul_comm]
  exact mul_le_mul_of_nonneg_left hle hsph0

/-- For a nonnegative positively `1`-homogeneous real function on a nontrivial space `E`, its
uniform spherical expectation is at most `√(2 / finrank ℝ E)` times its standard Gaussian
expectation. -/
theorem integral_uniformSphereMeasure_le_mul_sqrt_two_div_finrank_of_posHomog [Nontrivial E]
    {f : E → ℝ}
    (hf_meas : AEStronglyMeasurable (fun u : sphere (0 : E) 1 ↦ f u) (uniformSphereMeasure E))
    (hf_homog : ∀ {r : ℝ}, 0 < r → ∀ x : E, f (r • x) = r * f x)
    (hf_nonneg : ∀ u : sphere (0 : E) 1, 0 ≤ f u) :
    ∫ u : sphere (0 : E) 1, f u ∂uniformSphereMeasure E ≤
      √(2 / (Module.finrank ℝ E : ℝ)) * ∫ x, f x ∂stdGaussian E := by
  have hd : 0 < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.2 Module.finrank_pos
  have hd1 : (1 : ℝ) ≤ Module.finrank ℝ E := Nat.one_le_cast.2 Module.finrank_pos
  have hge : √((Module.finrank ℝ E : ℝ) / 2) ≤ ∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1 := by
    simpa using mul_sqrt_div_two_le_integral_id_chiMeasure hd1 zero_le_one
  have hsph0 : 0 ≤ ∫ u : sphere (0 : E) 1, f u ∂uniformSphereMeasure E :=
    integral_nonneg hf_nonneg
  have h1 : 1 ≤ √(2 / (Module.finrank ℝ E : ℝ)) * ∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1 := by
    calc (1 : ℝ) = √(2 / (Module.finrank ℝ E : ℝ)) * √((Module.finrank ℝ E : ℝ) / 2) := by
          rw [← Real.sqrt_mul (by positivity), div_mul_div_cancel₀ hd.ne',
            div_self two_ne_zero, Real.sqrt_one]
      _ ≤ √(2 / (Module.finrank ℝ E : ℝ)) * ∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1 :=
          mul_le_mul_of_nonneg_left hge (Real.sqrt_nonneg _)
  rw [integral_stdGaussian_of_posHomog hf_meas hf_homog, smul_eq_mul, ← mul_assoc]
  simpa using mul_le_mul_of_nonneg_right h1 hsph0

end PosHomog

section Seminorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every real seminorm on a finite-dimensional real inner product space is integrable on the unit
sphere under `uniformSphereMeasure E`. -/
theorem integrable_seminorm_uniformSphereMeasure (p : Seminorm ℝ E) :
    Integrable (fun u : sphere (0 : E) 1 ↦ p u) (uniformSphereMeasure E) := by
  obtain ⟨C, _, hC⟩ := p.bound_of_continuous_normedSpace p.continuous_of_finiteDimensional
  refine Integrable.of_bound
    (p.continuous_of_finiteDimensional.comp continuous_subtype_val).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg p (u : E))]
  simpa [norm_eq_of_mem_sphere u] using hC u

/-- The standard Gaussian expectation of a real seminorm equals the chi radius mean times its
uniform spherical expectation. -/
theorem integral_seminorm_stdGaussian (p : Seminorm ℝ E) :
    ∫ x, p x ∂stdGaussian E =
      (∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1) *
        ∫ u : sphere (0 : E) 1, p u ∂uniformSphereMeasure E :=
  integral_stdGaussian_of_posHomog
    (p.continuous_of_finiteDimensional.comp continuous_subtype_val).aestronglyMeasurable
    fun hr x ↦ by rw [map_smul_eq_mul, Real.norm_of_nonneg hr.le, smul_eq_mul]

/-- In positive dimension, the uniform spherical expectation of a real seminorm equals its standard
Gaussian expectation divided by the chi radius mean. -/
theorem integral_seminorm_uniformSphereMeasure [Nontrivial E] (p : Seminorm ℝ E) :
    ∫ u : sphere (0 : E) 1, p u ∂uniformSphereMeasure E =
      (∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1)⁻¹ * ∫ x, p x ∂stdGaussian E :=
  integral_uniformSphereMeasure_of_posHomog
    (p.continuous_of_finiteDimensional.comp continuous_subtype_val).aestronglyMeasurable
    fun hr x ↦ by rw [map_smul_eq_mul, Real.norm_of_nonneg hr.le, smul_eq_mul]

/-- Dividing the standard Gaussian expectation of a seminorm by `√(finrank ℝ E)` bounds its uniform
spherical expectation from below. -/
theorem div_sqrt_finrank_le_integral_seminorm_uniformSphereMeasure [Nontrivial E]
    (p : Seminorm ℝ E) :
    (∫ x, p x ∂stdGaussian E) / √(Module.finrank ℝ E) ≤
      ∫ u : sphere (0 : E) 1, p u ∂uniformSphereMeasure E :=
  div_sqrt_finrank_le_integral_uniformSphereMeasure_of_posHomog
    (p.continuous_of_finiteDimensional.comp continuous_subtype_val).aestronglyMeasurable
    (fun hr x ↦ by rw [map_smul_eq_mul, Real.norm_of_nonneg hr.le])
    fun u ↦ apply_nonneg p (u : E)

/-- The uniform spherical expectation of a seminorm is at most `√(2 / finrank ℝ E)` times its
standard Gaussian expectation. -/
theorem integral_seminorm_uniformSphereMeasure_le_mul_sqrt_two_div_finrank [Nontrivial E]
    (p : Seminorm ℝ E) :
    ∫ u : sphere (0 : E) 1, p u ∂uniformSphereMeasure E ≤
      √(2 / (Module.finrank ℝ E : ℝ)) * ∫ x, p x ∂stdGaussian E :=
  integral_uniformSphereMeasure_le_mul_sqrt_two_div_finrank_of_posHomog
    (p.continuous_of_finiteDimensional.comp continuous_subtype_val).aestronglyMeasurable
    (fun hr x ↦ by rw [map_smul_eq_mul, Real.norm_of_nonneg hr.le])
    fun u ↦ apply_nonneg p (u : E)

end Seminorm

section MeanNormLowerBound

variable {ι E F : Type*} [Fintype ι] [Nonempty ι]

/-- **Mean-seminorm lower bound on the unit sphere.** If `b` is an orthonormal basis of `E` and
`c ≤ p (b i)` for every `i` (with `0 ≤ c`), then the average of `p` over the unit sphere of `E` is
at least `c * √(log (finrank ℝ E) / finrank ℝ E) / 32`. -/
theorem mul_sqrt_log_finrank_div_le_integral_seminorm_uniformSphereMeasure
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (p : Seminorm ℝ E) (b : OrthonormalBasis ι ℝ E)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i, c ≤ p (b i)) :
    c * √(Real.log (Module.finrank ℝ E) / Module.finrank ℝ E) / 32 ≤
      ∫ u : sphere (0 : E) 1, p u ∂uniformSphereMeasure E := by
  let : Nontrivial E := ⟨⟨b (Classical.arbitrary ι), 0, b.orthonormal.ne_zero _⟩⟩
  have hd1 : (1 : ℝ) ≤ Module.finrank ℝ E := Nat.one_le_cast.2 Module.finrank_pos
  rw [Real.sqrt_div (Real.log_nonneg hd1)]
  calc c * (√(Real.log (Module.finrank ℝ E)) / √(Module.finrank ℝ E)) / 32
      = (c * √(Real.log (Module.finrank ℝ E)) / 32) / √(Module.finrank ℝ E) := by ring
    _ ≤ (∫ x, p x ∂stdGaussian E) / √(Module.finrank ℝ E) :=
        div_le_div_of_nonneg_right
          (mul_sqrt_log_finrank_div_le_integral_seminorm_stdGaussian p b hc hb)
          (Real.sqrt_nonneg _)
    _ ≤ ∫ u : sphere (0 : E) 1, p u ∂uniformSphereMeasure E :=
        div_sqrt_finrank_le_integral_seminorm_uniformSphereMeasure p

/-- **Mean-norm lower bound on the unit sphere for a linear map.** If `b` is an orthonormal basis
of `E` and `T : E →ₗ[ℝ] F` maps every basis vector to a vector of norm at least `c ≥ 0` in a real
seminormed space `F`, then `c * √(log (finrank ℝ E) / finrank ℝ E) / 32 ≤ ∫ u, ‖T u‖ dσ`. -/
theorem mul_sqrt_log_finrank_div_le_integral_norm_comp_uniformSphereMeasure
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ i, c ≤ ‖T (b i)‖) :
    c * √(Real.log (Module.finrank ℝ E) / Module.finrank ℝ E) / 32 ≤
      ∫ u : sphere (0 : E) 1, ‖T u‖ ∂uniformSphereMeasure E :=
  mul_sqrt_log_finrank_div_le_integral_seminorm_uniformSphereMeasure
    ((normSeminorm ℝ F).comp T) b hc hb

/-- **Mean-norm lower bound on the Euclidean unit sphere.** For `m = Fintype.card ι ≥ 1` vectors
`v : ι → F` in a real seminormed space satisfying `0 ≤ c ≤ ‖v i‖`, the spherical average of
`‖∑ i, uᵢ • v i‖` on `sphere (0 : EuclideanSpace ℝ ι) 1` is at least `c * √(log m / m) / 32`. -/
theorem mul_sqrt_log_card_div_le_integral_norm_sum_smul_uniformSphereMeasure
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] (v : ι → F) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ i, c ≤ ‖v i‖) :
    c * √(Real.log (Fintype.card ι) / Fintype.card ι) / 32 ≤
      ∫ u : sphere (0 : EuclideanSpace ℝ ι) 1, ‖∑ i, u.1 i • v i‖
        ∂uniformSphereMeasure (EuclideanSpace ℝ ι) := by
  classical
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] F :=
    ∑ i, (EuclideanSpace.proj i).toLinearMap.smulRight (v i)
  have hT_apply (x : EuclideanSpace ℝ ι) : T x = ∑ i, x i • v i := by
    simp [T, LinearMap.sum_apply]
  have hT_basis (i : ι) : c ≤ ‖T (EuclideanSpace.basisFun ι ℝ i)‖ := by
    rw [hT_apply, EuclideanSpace.basisFun_apply]
    simpa [Pi.single_apply] using hv i
  simpa only [finrank_euclideanSpace, hT_apply] using
    mul_sqrt_log_finrank_div_le_integral_norm_comp_uniformSphereMeasure T
      (EuclideanSpace.basisFun ι ℝ) hc hT_basis

end MeanNormLowerBound

end TauCeti.Probability
