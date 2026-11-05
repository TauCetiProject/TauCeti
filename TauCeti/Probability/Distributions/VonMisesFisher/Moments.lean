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
# First and second moments of the von Mises–Fisher law

In dimension `d ≥ 2`, a von Mises–Fisher unit vector `X` of positive concentration `κ` and
mean direction `m` has expectation `A • m`, where `A = I_{d/2}(κ) / I_{d/2-1}(κ)`. Its second
moments are `E[X Xᵀ] = A / κ • I + (1 - d A / κ) • m mᵀ`, so its covariance is
`A / κ • I + (1 - d A / κ - A ^ 2) • m mᵀ`. At zero concentration its expectation vanishes, as
for the uniform sphere law. The natural-parameter formulation uses `κ = ‖η‖` and direction
`η / ‖η‖`.

The mean is a Bochner integral of the sphere embedding, whose finite moments and essential
boundedness are established by `memLp_coe_vonMisesFisherNaturalMeasure` in `Basic`. The
second-moment matrix and the covariance are stated through the mixed moments
`E[⟪θ₁, X⟫ ⟪θ₂, X⟫]` and covariances of real linear observables, which determine them without
a choice of coordinates. The scalar formulas also allow using these moments without first
pushing the law into the ambient space.

The argument differentiates the normalizer ratio in
`mgf_inner_vonMisesFisherNaturalMeasure` once for the mean and twice for the second moments,
using the Bessel derivative identity and Mathlib's `deriv_mgf_zero` and
`iteratedDeriv_mgf_zero`. The second derivative produces `I_{d/2+1}(κ) / I_{d/2-1}(κ)` as the
coefficient of `m mᵀ`; the recurrence `I_{d/2-1} - I_{d/2+1} = (d / κ) I_{d/2}` rewrites it as
`1 - d A / κ`. Mixed moments follow from second moments of single observables by polarization.
The argument does not require a choice of coordinates or rotational symmetry of the tilted law.

## Main results

* `integral_coe_vonMisesFisherMeasure` — the mean `A • m`.
* `integral_inner_mul_inner_vonMisesFisherMeasure` — the second moments
  `E[⟪θ₁, X⟫ ⟪θ₂, X⟫] = A / κ ⟪θ₁, θ₂⟫ + (1 - d A / κ) ⟪θ₁, m⟫ ⟪θ₂, m⟫`.
* `covariance_inner_vonMisesFisherMeasure`, `variance_inner_vonMisesFisherMeasure` — the
  covariance and variance of linear observables.
* `integral_inner_mul_inner_vonMisesFisherNaturalMeasure`,
  `covariance_inner_vonMisesFisherNaturalMeasure` — the same formulas for a nonzero natural
  parameter.

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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Along a line avoiding the origin, the normalized Bessel function
`(x / 2) ^ (-ν) I_ν(x)` evaluated at the norm has derivative
`(x / 2) ^ (-ν - 1) I_{ν+1}(x) ⟪η + t • θ, θ⟫ / 2` with `x = ‖η + t • θ‖`. -/
private theorem hasDerivAt_rpow_neg_mul_besselI_norm (ν : ℝ) {η θ : E} {t : ℝ}
    (ht : η + t • θ ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ (‖η + t • θ‖ / 2) ^ (-ν) * besselI ν ‖η + t • θ‖)
      ((‖η + t • θ‖ / 2) ^ (-ν - 1) * besselI (ν + 1) ‖η + t • θ‖ *
        ⟪η + t • θ, θ⟫ / 2) t := by
  have hs : 0 < ‖η + t • θ‖ := norm_pos_iff.2 ht
  have hline : HasDerivAt (fun t : ℝ ↦ η + t • θ) θ t := by
    simpa only [one_smul] using ((hasDerivAt_id' t).smul_const θ).const_add η
  have hnorm : HasDerivAt (fun t : ℝ ↦ ‖η + t • θ‖)
      (⟪η + t • θ, θ⟫ / ‖η + t • θ‖) t := by
    simpa only [smul_apply, coe_innerSL_apply, smul_eq_mul,
      inv_mul_eq_div, Function.comp_def] using
      (hasFDerivAt_norm_of_ne ht).comp_hasDerivAt t hline
  convert (hasDerivAt_rpow_neg_mul_besselI ν hs.ne').comp t hnorm using 1
  · rfl
  · rw [rpow_sub_one (by positivity)]
    field_simp

/-- Near zero, the directional mgf under a nonzero natural parameter is the ratio of the
normalized Bessel functions `(x / 2) ^ (1 - d / 2) I_{d/2-1}(x)` at `x = ‖η + t • θ‖` and
`x = ‖η‖`. -/
private theorem mgf_inner_vonMisesFisherNaturalMeasure_eventuallyEq
    (hd : 2 ≤ Module.finrank ℝ E) {η : E} (hη : η ≠ 0) (θ : E) :
    mgf (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫) (vonMisesFisherNaturalMeasure η) =ᶠ[𝓝 0]
      fun t : ℝ ↦ (‖η + t • θ‖ / 2) ^ (-((Module.finrank ℝ E : ℝ) / 2 - 1)) *
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η + t • θ‖ /
        ((‖η‖ / 2) ^ (-((Module.finrank ℝ E : ℝ) / 2 - 1)) *
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖) := by
  have hdim : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have hΓ : Gamma ((Module.finrank ℝ E : ℝ) / 2) ≠ 0 :=
    (Gamma_pos_of_pos (by linarith)).ne'
  have hne : ∀ᶠ t : ℝ in 𝓝 0, η + t • θ ≠ 0 :=
    (isOpen_ne_fun (f := fun t : ℝ ↦ η + t • θ) (g := fun _ ↦ 0)
      (by fun_prop) continuous_const).eventually_mem (by simpa using hη)
  filter_upwards [hne] with t ht
  rw [mgf_inner_vonMisesFisherNaturalMeasure,
    integral_exp_inner_uniformSphereMeasure_eq_besselI hd ht,
    integral_exp_inner_uniformSphereMeasure_eq_besselI hd hη, mul_div_mul_left _ _ hΓ]

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
  have hpow : (‖η‖ / 2) ^ (-ν) ≠ 0 := (rpow_pos_of_pos (by positivity) _).ne'
  have hI : besselI ν ‖η‖ ≠ 0 := (besselI_pos (by dsimp [ν]; linarith) hκ).ne'
  have hderiv := (hasDerivAt_rpow_neg_mul_besselI_norm ν (η := η) (θ := θ) (t := 0)
    (by simpa using hη)).div_const ((‖η‖ / 2) ^ (-ν) * besselI ν ‖η‖)
  have hzero : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫) (vonMisesFisherNaturalMeasure η)) := by
    simp
  rw [← deriv_mgf_zero hzero,
    (mgf_inner_vonMisesFisherNaturalMeasure_eventuallyEq hd hη θ).deriv_eq, hderiv.deriv]
  have horder : ν + 1 = (Module.finrank ℝ E : ℝ) / 2 := by dsimp [ν]; ring
  simp only [zero_smul, add_zero, horder]
  rw [rpow_sub_one (by positivity), real_inner_comm]
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

/-! ### Second moments -/

/-- In dimension `d ≥ 2`, the second moment of `⟪θ, x⟫` under a nonzero natural parameter,
with the coefficient of the squared projection written as `I_{d/2+1}(κ) / I_{d/2-1}(κ)`. -/
private theorem integral_inner_sq_vonMisesFisherNaturalMeasure_besselI
    (hd : 2 ≤ Module.finrank ℝ E) {η : E} (hη : η ≠ 0) (θ : E) :
    ∫ x : sphere (0 : E) 1, ⟪θ, (x : E)⟫ ^ 2 ∂vonMisesFisherNaturalMeasure η =
      besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
          (‖η‖ * besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖) * ‖θ‖ ^ 2 +
        besselI ((Module.finrank ℝ E : ℝ) / 2 + 1) ‖η‖ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ * (⟪θ, η⟫ / ‖η‖) ^ 2 := by
  set ν : ℝ := (Module.finrank ℝ E : ℝ) / 2 - 1
  have hκ : 0 < ‖η‖ := norm_pos_iff.2 hη
  have hdim : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have hI : besselI ν ‖η‖ ≠ 0 := (besselI_pos (by dsimp [ν]; linarith) hκ).ne'
  set c := (‖η‖ / 2) ^ (-ν) * besselI ν ‖η‖
  have hc : c ≠ 0 := mul_ne_zero (rpow_pos_of_pos (by positivity) _).ne' hI
  have hne : ∀ᶠ t : ℝ in 𝓝 0, η + t • θ ≠ 0 :=
    (isOpen_ne_fun (f := fun t : ℝ ↦ η + t • θ) (g := fun _ ↦ 0)
      (by fun_prop) continuous_const).eventually_mem (by simpa using hη)
  -- Its derivative is again a normalized Bessel function, of order `ν + 1`.
  have hderiv : deriv (fun t : ℝ ↦ (‖η + t • θ‖ / 2) ^ (-ν) * besselI ν ‖η + t • θ‖ / c)
      =ᶠ[𝓝 0] fun t : ℝ ↦ (‖η + t • θ‖ / 2) ^ (-(ν + 1)) * besselI (ν + 1) ‖η + t • θ‖ *
        ⟪η + t • θ, θ⟫ / 2 / c := by
    filter_upwards [hne] with t ht
    rw [((hasDerivAt_rpow_neg_mul_besselI_norm ν ht).div_const c).deriv, neg_add']
  have hinner : HasDerivAt (fun t : ℝ ↦ ⟪η + t • θ, θ⟫) ⟪θ, θ⟫ 0 := by
    simpa only [inner_add_left, real_inner_smul_left, one_mul] using
      ((hasDerivAt_id' (0 : ℝ)).mul_const ⟪θ, θ⟫).const_add ⟪η, θ⟫
  have h2 := (((hasDerivAt_rpow_neg_mul_besselI_norm (ν + 1) (η := η) (θ := θ) (t := 0)
    (by simpa using hη)).fun_mul hinner).div_const 2).div_const c
  have hzero : (0 : ℝ) ∈ interior (integrableExpSet
      (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫) (vonMisesFisherNaturalMeasure η)) := by
    simp
  have hmom := iteratedDeriv_mgf_zero hzero 2
  simp only [Pi.pow_apply] at hmom
  rw [← hmom, (mgf_inner_vonMisesFisherNaturalMeasure_eventuallyEq hd hη θ).iteratedDeriv_eq 2,
    iteratedDeriv_succ, iteratedDeriv_one, hderiv.deriv_eq, h2.deriv]
  have horder : ν + 1 = (Module.finrank ℝ E : ℝ) / 2 := by dsimp [ν]; ring
  simp only [zero_smul, add_zero, ← horder, real_inner_self_eq_norm_sq, c, neg_add']
  rw [rpow_sub_one (by positivity), rpow_sub_one (by positivity), real_inner_comm]
  field_simp
  ring

/-- In dimension `d ≥ 2`, the mixed second moments of linear observables under a nonzero natural
parameter `η` are `E[⟪θ₁, X⟫ ⟪θ₂, X⟫] = A / κ ⟪θ₁, θ₂⟫ + (1 - d A / κ) ⟪θ₁, m⟫ ⟪θ₂, m⟫`,
where `κ = ‖η‖`, `m = η / κ` and `A = I_{d/2}(κ) / I_{d/2-1}(κ)`. Equivalently, the second
moment matrix of `X` is `A / κ • I + (1 - d A / κ) • m mᵀ`. -/
theorem integral_inner_mul_inner_vonMisesFisherNaturalMeasure (hd : 2 ≤ Module.finrank ℝ E)
    {η : E} (hη : η ≠ 0) (θ₁ θ₂ : E) :
    ∫ x : sphere (0 : E) 1, ⟪θ₁, (x : E)⟫ * ⟪θ₂, (x : E)⟫ ∂vonMisesFisherNaturalMeasure η =
      besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ / ‖η‖ * ⟪θ₁, θ₂⟫ +
        (1 - Module.finrank ℝ E * (besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖) / ‖η‖) *
          (⟪θ₁, η⟫ / ‖η‖) * (⟪θ₂, η⟫ / ‖η‖) := by
  have hκ : 0 < ‖η‖ := norm_pos_iff.2 hη
  have hdim : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have hI : besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ ≠ 0 :=
    (besselI_pos (by linarith) hκ).ne'
  -- The recurrence for `I_{d/2+1}` turns the coefficient of the squared projection into
  -- `1 - d A / κ`.
  have hrec : besselI ((Module.finrank ℝ E : ℝ) / 2 + 1) ‖η‖ =
      besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ -
        2 * ((Module.finrank ℝ E : ℝ) / 2) / ‖η‖ * besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ := by
    linarith [besselI_sub_besselI ((Module.finrank ℝ E : ℝ) / 2) hκ.ne']
  have hsq (θ : E) := (memLp_inner_vonMisesFisherNaturalMeasure η θ 2).integrable_sq
  -- Polarization reduces mixed moments to the second moments of single observables.
  have hpol : (fun x : sphere (0 : E) 1 ↦ ⟪θ₁, (x : E)⟫ * ⟪θ₂, (x : E)⟫) =
      fun x : sphere (0 : E) 1 ↦ (⟪θ₁ + θ₂, (x : E)⟫ ^ 2 - ⟪θ₁ - θ₂, (x : E)⟫ ^ 2) / 4 := by
    ext x
    rw [inner_add_left, inner_sub_left]
    ring
  rw [hpol, integral_div, integral_sub (hsq _) (hsq _),
    integral_inner_sq_vonMisesFisherNaturalMeasure_besselI hd hη,
    integral_inner_sq_vonMisesFisherNaturalMeasure_besselI hd hη, hrec,
    norm_add_sq_real, norm_sub_sq_real, inner_add_left, inner_sub_left]
  generalize besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ = I at hI ⊢
  field_simp
  ring

/-- In dimension `d ≥ 2`, linear observables under a nonzero natural parameter `η` have
covariance `A / κ ⟪θ₁, θ₂⟫ + (1 - d A / κ - A ^ 2) ⟪θ₁, m⟫ ⟪θ₂, m⟫`, where `κ = ‖η‖`,
`m = η / κ` and `A = I_{d/2}(κ) / I_{d/2-1}(κ)`. -/
theorem covariance_inner_vonMisesFisherNaturalMeasure (hd : 2 ≤ Module.finrank ℝ E)
    {η : E} (hη : η ≠ 0) (θ₁ θ₂ : E) :
    cov[fun x : sphere (0 : E) 1 ↦ ⟪θ₁, (x : E)⟫, fun x : sphere (0 : E) 1 ↦ ⟪θ₂, (x : E)⟫;
        vonMisesFisherNaturalMeasure η] =
      besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ / ‖η‖ * ⟪θ₁, θ₂⟫ +
        (1 - Module.finrank ℝ E * (besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖) / ‖η‖ -
          (besselI ((Module.finrank ℝ E : ℝ) / 2) ‖η‖ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖) ^ 2) *
          (⟪θ₁, η⟫ / ‖η‖) * (⟪θ₂, η⟫ / ‖η‖) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  rw [covariance_eq_sub (memLp_inner_vonMisesFisherNaturalMeasure η θ₁ 2)
    (memLp_inner_vonMisesFisherNaturalMeasure η θ₂ 2)]
  simp only [Pi.mul_apply]
  rw [integral_inner_mul_inner_vonMisesFisherNaturalMeasure hd hη,
    integral_inner_vonMisesFisherNaturalMeasure hd hη,
    integral_inner_vonMisesFisherNaturalMeasure hd hη]
  ring

/-- For a unit direction `m` and positive concentration `κ` in dimension `d ≥ 2`, the mixed
second moments of linear observables are
`E[⟪θ₁, X⟫ ⟪θ₂, X⟫] = A / κ ⟪θ₁, θ₂⟫ + (1 - d A / κ) ⟪θ₁, m⟫ ⟪θ₂, m⟫`, where
`A = I_{d/2}(κ) / I_{d/2-1}(κ)`. Equivalently, `E[X Xᵀ] = A / κ • I + (1 - d A / κ) • m mᵀ`. -/
theorem integral_inner_mul_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 < κ) (θ₁ θ₂ : E) :
    ∫ x : sphere (0 : E) 1, ⟪θ₁, (x : E)⟫ * ⟪θ₂, (x : E)⟫ ∂vonMisesFisherMeasure m κ =
      besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ / κ * ⟪θ₁, θ₂⟫ +
        (1 - Module.finrank ℝ E * (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) / κ) * ⟪θ₁, (m : E)⟫ * ⟪θ₂, (m : E)⟫ := by
  have hm : ‖(m : E)‖ = 1 := mem_sphere_zero_iff_norm.mp m.property
  rw [vonMisesFisherMeasure_of_nonneg m hκ.le,
    integral_inner_mul_inner_vonMisesFisherNaturalMeasure hd
      (smul_ne_zero hκ.ne' (ne_zero_of_mem_sphere one_ne_zero m))]
  simp only [norm_smul, norm_eq_abs, abs_of_pos hκ, hm, mul_one, real_inner_smul_right,
    mul_div_cancel_left₀ _ hκ.ne']

/-- For a unit direction `m` and positive concentration `κ` in dimension `d ≥ 2`, linear
observables have covariance `A / κ ⟪θ₁, θ₂⟫ + (1 - d A / κ - A ^ 2) ⟪θ₁, m⟫ ⟪θ₂, m⟫`, where
`A = I_{d/2}(κ) / I_{d/2-1}(κ)`. -/
theorem covariance_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 < κ) (θ₁ θ₂ : E) :
    cov[fun x : sphere (0 : E) 1 ↦ ⟪θ₁, (x : E)⟫, fun x : sphere (0 : E) 1 ↦ ⟪θ₂, (x : E)⟫;
        vonMisesFisherMeasure m κ] =
      besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ / κ * ⟪θ₁, θ₂⟫ +
        (1 - Module.finrank ℝ E * (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) / κ -
          (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) ^ 2) *
          ⟪θ₁, (m : E)⟫ * ⟪θ₂, (m : E)⟫ := by
  have hm : ‖(m : E)‖ = 1 := mem_sphere_zero_iff_norm.mp m.property
  rw [vonMisesFisherMeasure_of_nonneg m hκ.le,
    covariance_inner_vonMisesFisherNaturalMeasure hd
      (smul_ne_zero hκ.ne' (ne_zero_of_mem_sphere one_ne_zero m))]
  simp only [norm_smul, norm_eq_abs, abs_of_pos hκ, hm, mul_one, real_inner_smul_right,
    mul_div_cancel_left₀ _ hκ.ne']

/-- For a unit direction `m` and positive concentration `κ` in dimension `d ≥ 2`, the variance
of `⟪θ, X⟫` is `A / κ ‖θ‖ ^ 2 + (1 - d A / κ - A ^ 2) ⟪θ, m⟫ ^ 2`, where
`A = I_{d/2}(κ) / I_{d/2-1}(κ)`. -/
theorem variance_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 < κ) (θ : E) :
    Var[fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫; vonMisesFisherMeasure m κ] =
      besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ / κ * ‖θ‖ ^ 2 +
        (1 - Module.finrank ℝ E * (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) / κ -
          (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) ^ 2) * ⟪θ, (m : E)⟫ ^ 2 := by
  rw [← covariance_self (by fun_prop), covariance_inner_vonMisesFisherMeasure hd m hκ,
    real_inner_self_eq_norm_sq, mul_assoc, ← pow_two]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → sphere (0 : E) 1}

/-- Linear observables of a von Mises–Fisher random unit vector with positive concentration `κ`
and mean direction `m`, in dimension `d ≥ 2`, have covariance
`A / κ ⟪θ₁, θ₂⟫ + (1 - d A / κ - A ^ 2) ⟪θ₁, m⟫ ⟪θ₂, m⟫`, where
`A = I_{d/2}(κ) / I_{d/2-1}(κ)`. -/
theorem HasLaw.covariance_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    {m : sphere (0 : E) 1} {κ : ℝ} (hκ : 0 < κ) (hX : HasLaw X (vonMisesFisherMeasure m κ) P)
    (θ₁ θ₂ : E) :
    cov[fun ω ↦ ⟪θ₁, (X ω : E)⟫, fun ω ↦ ⟪θ₂, (X ω : E)⟫; P] =
      besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ / κ * ⟪θ₁, θ₂⟫ +
        (1 - Module.finrank ℝ E * (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) / κ -
          (besselI ((Module.finrank ℝ E : ℝ) / 2) κ /
            besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ) ^ 2) *
          ⟪θ₁, (m : E)⟫ * ⟪θ₂, (m : E)⟫ := by
  rw [hX.covariance_fun_comp (f := fun x : sphere (0 : E) 1 ↦ ⟪θ₁, (x : E)⟫)
    (g := fun x : sphere (0 : E) 1 ↦ ⟪θ₂, (x : E)⟫) (by fun_prop) (by fun_prop),
    TauCeti.Probability.covariance_inner_vonMisesFisherMeasure hd m hκ]

end ProbabilityTheory
