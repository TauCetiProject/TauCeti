/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Normalizer
import TauCeti.Analysis.InnerProductSpace.NormPow
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# The mean of the von Mises–Fisher law

In dimension `d ≥ 2`, a von Mises–Fisher unit vector of positive concentration `κ` and
mean direction `m` has expectation `I_{d/2}(κ) / I_{d/2-1}(κ) • m`. At zero concentration
its expectation vanishes, as for the uniform sphere law. The natural-parameter formulation
uses `κ = ‖η‖` and direction `η / ‖η‖`.

The mean is a Bochner integral of the sphere embedding, whose finite moments and essential
boundedness are established by `memLp_coe_vonMisesFisherNaturalMeasure` in `Basic`. The scalar
mean formula also applies to any real linear observable, which allows using the mean without
first pushing the law into the ambient space.

The argument differentiates the normalizer ratio in
`mgf_inner_vonMisesFisherNaturalMeasure`, using the Bessel derivative identity and Mathlib's
`deriv_mgf_zero`. It does not require a choice of coordinates or rotational symmetry of the
tilted law.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real Set Filter
open scoped RealInnerProductSpace Topology

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- In dimension `d ≥ 2`, the mean of `⟪θ, x⟫` is the Bessel ratio
`I_{d/2}(‖η‖) / I_{d/2-1}(‖η‖)` times the projection `⟪θ, η⟫ / ‖η‖`
onto the direction of the nonzero natural parameter. -/
theorem integral_inner_vonMisesFisherNaturalMeasure (hd : 2 ≤ Module.finrank ℝ E)
    {η : E} (hη : η ≠ 0) (θ : E) :
    ∫ x : sphere (0 : E) 1, ⟪θ, (x : E)⟫ ∂vonMisesFisherNaturalMeasure η =
      besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
        besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ * (⟪θ, η⟫ / ‖η‖) := by
  set ν : ℝ := (Module.finrank ℝ E : ℝ) / 2 - 1
  have hκ : 0 < ‖η‖ := norm_pos_iff.2 hη
  have hdim : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have hΓ : Gamma ((Module.finrank ℝ E : ℝ) / 2) ≠ 0 :=
    (Gamma_pos_of_pos (by linarith)).ne'
  have hpow : (‖η‖ / 2) ^ (-ν) ≠ 0 := (rpow_pos_of_pos (by positivity) _).ne'
  have hI : besselI ν ‖η‖ ≠ 0 := (besselI_pos (by dsimp [ν]; linarith) hκ).ne'
  have hline : HasDerivAt (fun t : ℝ ↦ η + t • θ) θ 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (0 : ℝ)).smul_const θ).const_add η
  have hnorm : HasDerivAt (fun t : ℝ ↦ ‖η + t • θ‖) (⟪θ, η⟫ / ‖η‖) 0 := by
    simpa only [smul_apply, coe_innerSL_apply, smul_eq_mul, real_inner_comm η θ,
      inv_mul_eq_div, Function.comp_def] using
      (hasFDerivAt_norm_of_ne hη).comp_hasDerivAt_of_eq 0 hline (by simp)
  have hbessel := hasDerivAt_rpow_neg_mul_besselI ν hκ.ne'
  have hnum := (hbessel.comp_of_eq 0 hnorm (by simp)).const_mul
    (Gamma ((Module.finrank ℝ E : ℝ) / 2))
  -- Near zero the mgf is the ratio of normalized Bessel functions.
  have hmgf : mgf (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫)
      (vonMisesFisherNaturalMeasure η) =ᶠ[𝓝 0]
      fun t : ℝ ↦ Gamma ((Module.finrank ℝ E : ℝ) / 2) *
        ((‖η + t • θ‖ / 2) ^ (-ν) * besselI ν ‖η + t • θ‖) /
          (Gamma ((Module.finrank ℝ E : ℝ) / 2) *
            ((‖η‖ / 2) ^ (-ν) * besselI ν ‖η‖)) := by
    have hne : ∀ᶠ t : ℝ in 𝓝 0, η + t • θ ≠ 0 :=
      (isOpen_ne_fun (f := fun t : ℝ ↦ η + t • θ) (g := fun _ ↦ 0)
        (by fun_prop) continuous_const).eventually_mem (by simpa using hη)
    filter_upwards [hne] with t ht
    rw [mgf_inner_vonMisesFisherNaturalMeasure,
      integral_exp_inner_uniformSphereMeasure_eq_besselI hd ht,
      integral_exp_inner_uniformSphereMeasure_eq_besselI hd hη]
  have hderiv := (hnum.div_const (Gamma ((Module.finrank ℝ E : ℝ) / 2) *
    ((‖η‖ / 2) ^ (-ν) * besselI ν ‖η‖))).congr_of_eventuallyEq hmgf
  have hzero : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫) (vonMisesFisherNaturalMeasure η)) := by
    simp
  rw [← deriv_mgf_zero hzero, hderiv.deriv]
  have horder : ν + 1 = (Module.finrank ℝ E : ℝ) / 2 := by dsimp [ν]; ring
  simp only [horder]
  field_simp

/-- The embedded mean of a nonzero natural-parameter law is its unit natural direction
multiplied by the ratio of adjacent modified Bessel functions. -/
theorem integral_coe_vonMisesFisherNaturalMeasure (hd : 2 ≤ Module.finrank ℝ E)
    {η : E} (hη : η ≠ 0) :
    ∫ x : sphere (0 : E) 1, (x : E) ∂vonMisesFisherNaturalMeasure η =
      (besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
        besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ / ‖η‖) • η := by
  apply ext_inner_left ℝ
  intro θ
  rw [← integral_inner ((memLp_coe_vonMisesFisherNaturalMeasure η 1).integrable le_rfl),
    integral_inner_vonMisesFisherNaturalMeasure hd hη, real_inner_smul_right]
  ring

/-- At positive concentration, the mean is the specified unit direction times the
Bessel ratio `I_{d/2}(κ) / I_{d/2-1}(κ)`. -/
theorem integral_coe_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 < κ) :
    ∫ x : sphere (0 : E) 1, (x : E) ∂vonMisesFisherMeasure m κ =
      (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
        besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) • (m : E) := by
  rw [vonMisesFisherMeasure_of_nonneg m hκ.le,
    integral_coe_vonMisesFisherNaturalMeasure hd (smul_ne_zero hκ.ne'
      (ne_zero_of_mem_sphere one_ne_zero m))]
  simp only [norm_smul, norm_eq_abs, abs_of_pos hκ, mem_sphere_zero_iff_norm.mp m.property,
    mul_one, smul_smul]
  rw [div_mul_cancel₀ _ hκ.ne']

/-- At zero concentration the mean vanishes in every dimension. -/
theorem integral_coe_vonMisesFisherMeasure_zero (m : sphere (0 : E) 1) :
    ∫ x : sphere (0 : E) 1, (x : E) ∂vonMisesFisherMeasure m 0 = 0 := by
  simp [integral_coe_uniformSphereMeasure]

end TauCeti.Probability
