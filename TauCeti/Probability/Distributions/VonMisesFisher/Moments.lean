/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Normalizer
public import TauCeti.Probability.Distributions.Uniform.Sphere.Moments
import TauCeti.Analysis.InnerProductSpace.NormPow
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Mean and second moments of the von Mises–Fisher law

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

The mixed second moment of two linear observables splits into an isotropic term and a
rank-one term in the mean direction. Its coefficients are given by the ratio of adjacent
modified Bessel functions. At zero concentration the uniform-sphere formula applies. Products
of linear observables are integrable for every natural parameter and every concentration.

For second moments, the argument differentiates the directional mgf twice in the
regularized hypergeometric form of the normalizer, whose argument is the squared norm.
The Bessel recurrence then reduces the coefficients to a single adjacent-order ratio.

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

/-- Products of linear observables are integrable for every natural parameter by continuity
on the compact sphere. -/
theorem integrable_inner_mul_inner_vonMisesFisherNaturalMeasure (η u v : E) :
    Integrable (fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫)
      (vonMisesFisherNaturalMeasure η) := by
  have hc : Continuous (fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫) := by fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Products of linear observables are integrable at every concentration, including the
uniform law and the zero measure at negative concentration. -/
theorem integrable_inner_mul_inner_vonMisesFisherMeasure (m : sphere (0 : E) 1)
    (κ : ℝ) (u v : E) :
    Integrable (fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫)
      (vonMisesFisherMeasure m κ) := by
  by_cases hκ : 0 ≤ κ
  · rw [vonMisesFisherMeasure_of_nonneg m hκ]
    exact integrable_inner_mul_inner_vonMisesFisherNaturalMeasure _ u v
  · simp [vonMisesFisherMeasure_of_neg m (lt_of_not_ge hκ)]

private lemma integral_sq_inner_vmf_hypergeometric (hd : 2 ≤ Module.finrank ℝ E)
    (η θ : E) :
    let b := (Module.finrank ℝ E : ℝ) / 2
    let H := fun (a y : ℝ) ↦ (Complex.regularizedHGFun 0 {(a : ℂ)} y).re
    ∫ x : sphere (0 : E) 1, ⟪θ, (x : E)⟫ ^ 2 ∂vonMisesFisherNaturalMeasure η =
      (H (b + 2) (‖η‖ ^ 2 / 4) * (⟪η, θ⟫ / 2) ^ 2 +
        H (b + 1) (‖η‖ ^ 2 / 4) * (‖θ‖ ^ 2 / 2)) / H b (‖η‖ ^ 2 / 4) := by
  dsimp only
  let b := (Module.finrank ℝ E : ℝ) / 2
  let H := fun (a y : ℝ) ↦ (Complex.regularizedHGFun 0 {(a : ℂ)} y).re
  let q := fun t : ℝ ↦ ‖η + t • θ‖ ^ 2 / 4
  have hv (t : ℝ) : HasDerivAt (fun t : ℝ ↦ η + t • θ) θ t := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const θ).const_add η
  have hq (t : ℝ) : HasDerivAt q (⟪η + t • θ, θ⟫ / 2) t := by
    convert (hv t).norm_sq.div_const 4 using 1
    ring
  have hH (a t : ℝ) : HasDerivAt (fun t ↦ H a (q t))
      (H (a + 1) (q t) * (⟪η + t • θ, θ⟫ / 2)) t := by
    simpa only [H, Function.comp_def, Complex.ofReal_add, Complex.ofReal_one] using
      (Complex.hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re a (q t)).comp t (hq t)
  have hlin (t : ℝ) : HasDerivAt (fun t : ℝ ↦ ⟪η + t • θ, θ⟫ / 2)
      (‖θ‖ ^ 2 / 2) t := by
    simpa using ((hv t).inner ℝ (hasDerivAt_const t θ)).div_const 2
  -- The normalizer ratio is a smooth function of the quadratic polynomial `q`.
  have hmodel : mgf (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫)
      (vonMisesFisherNaturalMeasure η) = fun t ↦ H b (q t) / H b (q 0) := by
    funext t
    rw [mgf_inner_vonMisesFisherNaturalMeasure,
      integral_exp_inner_uniformSphereMeasure_eq_regularizedHGFun hd,
      integral_exp_inner_uniformSphereMeasure_eq_regularizedHGFun hd]
    have hb : 0 < b := div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_two hd)) two_pos
    have hcancel : Gamma b * H b (q t) / (Gamma b * H b (q 0)) =
        H b (q t) / H b (q 0) :=
      mul_div_mul_left _ _ (Gamma_pos_of_pos hb).ne'
    simpa only [H, b, q, zero_smul, add_zero] using hcancel
  have hdom : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫) (vonMisesFisherNaturalMeasure η)) := by simp
  have hm := iteratedDeriv_mgf_zero hdom 2
  simp only [Pi.pow_apply] at hm
  rw [← hm, hmodel]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hdiv : deriv (fun t ↦ H b (q t) / H b (q 0)) =
      fun t ↦ (H (b + 1) (q t) * (⟪η + t • θ, θ⟫ / 2)) / H b (q 0) :=
    funext fun t ↦ ((hH b t).div_const _).deriv
  rw [hdiv]
  have hs := (((hH (b + 1) 0).mul (hlin 0)).div_const (H b (q 0))).deriv
  have hstep : b + 1 + 1 = b + 2 := by ring
  simp only [Pi.mul_apply, zero_smul, add_zero, hstep] at hs
  convert hs using 1
  dsimp only [q, b, H]
  simp only [zero_smul, add_zero]
  ring

private lemma integral_sq_inner_vmf (hd : 2 ≤ Module.finrank ℝ E)
    {η : E} (hη : η ≠ 0) (θ : E) :
    let d := (Module.finrank ℝ E : ℝ)
    let A := besselI (d / 2) ‖η‖ / besselI (d / 2 - 1) ‖η‖
    ∫ x : sphere (0 : E) 1, ⟪θ, (x : E)⟫ ^ 2 ∂vonMisesFisherNaturalMeasure η =
      A / ‖η‖ * ‖θ‖ ^ 2 + (1 - d * A / ‖η‖) * (⟪η, θ⟫ / ‖η‖) ^ 2 := by
  let b := (Module.finrank ℝ E : ℝ) / 2
  let k := ‖η‖
  have hk : 0 < k := norm_pos_iff.mpr hη
  have hp : 0 < k / 2 := by positivity
  have hb : 0 < b := div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_two hd)) two_pos
  let H := fun (a : ℝ) ↦ (Complex.regularizedHGFun 0 {(a : ℂ)} (k ^ 2 / 4 : ℝ)).re
  have hH (a : ℝ) : H a = besselI (a - 1) k / (k / 2) ^ (a - 1) := by
    dsimp only [H]
    rw [regularizedHGFun_zero_singleton_ofReal_re_eq_rpow_mul_besselI a hk,
      ← neg_sub a 1, rpow_neg hp.le, ← div_eq_inv_mul]
  have hI : besselI (b - 1) k ≠ 0 := (besselI_pos (by linarith) hk).ne'
  have hrec := besselI_sub_besselI b hk.ne'
  have hpow : (k / 2) ^ b = (k / 2) ^ (b - 1) * (k / 2) := by
    simpa only [sub_add_cancel] using rpow_add_one hp.ne' (b - 1)
  have hpow' : (k / 2) ^ (b + 1) = (k / 2) ^ (b - 1) * (k / 2) ^ 2 := by
    rw [rpow_add_one hp.ne', hpow]
    ring
  have hm := integral_sq_inner_vmf_hypergeometric hd η θ
  dsimp only at hm ⊢
  rw [hm]
  suffices (H (b + 2) * (⟪η, θ⟫ / 2) ^ 2 + H (b + 1) * (‖θ‖ ^ 2 / 2)) / H b =
      besselI b k / besselI (b - 1) k / k * ‖θ‖ ^ 2 +
        (1 - 2 * b * (besselI b k / besselI (b - 1) k) / k) * (⟪η, θ⟫ / k) ^ 2 by
    have hd' : 2 * b = (Module.finrank ℝ E : ℝ) := by dsimp [b]; ring
    rw [hd'] at this
    exact this
  -- Express the two hypergeometric derivatives through adjacent Bessel orders.
  rw [hH (b + 2), hH (b + 1), hH b]
  have horder : b + 2 - 1 = b + 1 := by ring
  simp only [horder, add_sub_cancel_right]
  rw [hpow, hpow']
  have hp' : (k / 2) ^ (b - 1) ≠ 0 := (rpow_pos_of_pos hp _).ne'
  linear_combination (norm := (field_simp [hI, hk.ne', hp']; ring))
    -(⟪η, θ⟫ ^ 2 / (besselI (b - 1) k * k ^ 2)) * hrec

/-- The mixed second moment under a nonzero natural parameter. All products here are
integrable by continuity on the compact sphere. -/
theorem integral_inner_mul_inner_vonMisesFisherNaturalMeasure
    (hd : 2 ≤ Module.finrank ℝ E) {η : E} (hη : η ≠ 0) (u v : E) :
    ∫ x : sphere (0 : E) 1, ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫
        ∂vonMisesFisherNaturalMeasure η =
      besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ / ‖η‖ * ⟪u, v⟫ +
        (1 - (Module.finrank ℝ E : ℝ) *
          (besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖) / ‖η‖) *
          (⟪η, u⟫ / ‖η‖) * (⟪η, v⟫ / ‖η‖) := by
  have hint (w : E) := (memLp_inner_vonMisesFisherNaturalMeasure η w 2).integrable_sq
  have hproduct := integrable_inner_mul_inner_vonMisesFisherNaturalMeasure η u v
  have hsqadd : Integrable (fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ ^ 2 + ⟪v, (x : E)⟫ ^ 2)
      (vonMisesFisherNaturalMeasure η) := by
    refine ((hint u).add (hint v)).congr ?_
    filter_upwards with x
    exact Pi.add_apply _ _ x
  have hpoly : (fun x : sphere (0 : E) 1 ↦ ⟪u + v, (x : E)⟫ ^ 2) =
      (fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ ^ 2 + ⟪v, (x : E)⟫ ^ 2 +
        2 * (⟪u, (x : E)⟫ * ⟪v, (x : E)⟫)) := by
    funext x
    rw [inner_add_left]
    ring
  have hsum := integral_sq_inner_vmf hd hη (u + v)
  rw [hpoly, integral_add hsqadd (hproduct.const_mul 2),
    integral_add (hint u) (hint v), integral_const_mul,
    integral_sq_inner_vmf hd hη u, integral_sq_inner_vmf hd hη v] at hsum
  simp only [norm_add_sq_real, inner_add_right] at hsum
  linear_combination hsum / 2

/-- At positive concentration, the von Mises–Fisher second-moment tensor evaluated on any
two vectors is `(A/κ) I + (1-d A/κ) m mᵀ`, where `A = I_{d/2}(κ) / I_{d/2-1}(κ)`. -/
theorem integral_inner_mul_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 < κ) (u v : E) :
    ∫ x : sphere (0 : E) 1, ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫
        ∂vonMisesFisherMeasure m κ =
      besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ / κ * ⟪u, v⟫ +
        (1 - (Module.finrank ℝ E : ℝ) *
          (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) / κ) *
          ⟪(m : E), u⟫ * ⟪(m : E), v⟫ := by
  have hη : κ • (m : E) ≠ 0 := smul_ne_zero hκ.ne' (ne_zero_of_mem_sphere one_ne_zero m)
  have hnorm : ‖κ • (m : E)‖ = κ := by simp [norm_smul, abs_of_pos hκ]
  rw [vonMisesFisherMeasure_of_nonneg m hκ.le]
  simpa only [hnorm, real_inner_smul_left, mul_div_cancel_left₀ _ hκ.ne'] using
    integral_inner_mul_inner_vonMisesFisherNaturalMeasure hd hη u v

/-- At zero concentration, the second-moment tensor is the uniform tensor `I/d`. -/
theorem integral_inner_mul_inner_vonMisesFisherMeasure_zero
    (m : sphere (0 : E) 1) (u v : E) :
    ∫ x : sphere (0 : E) 1, ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫
        ∂vonMisesFisherMeasure m 0 = ⟪u, v⟫ / (Module.finrank ℝ E : ℝ) := by
  have : Nontrivial E := ⟨⟨m, 0, ne_zero_of_mem_sphere one_ne_zero m⟩⟩
  simp

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- At positive concentration, the second-moment tensor of a sphere-valued von Mises–Fisher
random variable, paired with arbitrary ambient vectors. The source measure needs no additional
normalization. -/
theorem integral_inner_mul_inner_vonMisesFisherMeasure
    {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → sphere (0 : E) 1} {m : sphere (0 : E) 1} {κ : ℝ}
    (hX : HasLaw X (vonMisesFisherMeasure m κ) P) (hd : 2 ≤ Module.finrank ℝ E)
    (hκ : 0 < κ) (u v : E) :
    ∫ ω, ⟪u, (X ω : E)⟫ * ⟪v, (X ω : E)⟫ ∂P =
      besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ / κ * ⟪u, v⟫ +
        (1 - (Module.finrank ℝ E : ℝ) *
          (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) / κ) *
          ⟪(m : E), u⟫ * ⟪(m : E), v⟫ := by
  rw [← TauCeti.Probability.integral_inner_mul_inner_vonMisesFisherMeasure hd m hκ u v]
  simpa only [Function.comp_def] using hX.integral_comp
    (f := fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫) (by fun_prop)

/-- At zero concentration, the second moment of a sphere-valued von Mises–Fisher random
variable is the uniform-sphere second moment. -/
theorem integral_inner_mul_inner_vonMisesFisherMeasure_zero
    {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → sphere (0 : E) 1} {m : sphere (0 : E) 1}
    (hX : HasLaw X (vonMisesFisherMeasure m 0) P) (u v : E) :
    ∫ ω, ⟪u, (X ω : E)⟫ * ⟪v, (X ω : E)⟫ ∂P =
      ⟪u, v⟫ / (Module.finrank ℝ E : ℝ) := by
  rw [← TauCeti.Probability.integral_inner_mul_inner_vonMisesFisherMeasure_zero m u v]
  simpa only [Function.comp_def] using hX.integral_comp
    (f := fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫) (by fun_prop)

end ProbabilityTheory.HasLaw
