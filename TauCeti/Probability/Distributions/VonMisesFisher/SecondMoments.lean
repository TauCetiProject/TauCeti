/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Normalizer
public import TauCeti.Probability.Distributions.Uniform.Sphere.Moments
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Second moments of von Mises–Fisher laws

The mixed second moment of two linear observables splits into an isotropic term and a
rank-one term in the mean direction. Its coefficients are given by the ratio of adjacent
modified Bessel functions. At zero concentration the uniform-sphere formula applies. Products
of linear observables are integrable at every concentration by compactness of the sphere.

The calculation differentiates the directional moment-generating function twice. Writing the
normalizer in its regularized hypergeometric form makes its argument the squared norm, so
the differentiation does not require derivatives of the norm. The Bessel recurrence then
reduces the two coefficients to a single adjacent-order ratio.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Products of linear observables are integrable at every concentration, including the
uniform law and the zero measure at negative concentration. -/
theorem integrable_inner_mul_inner_vonMisesFisherMeasure (m : sphere (0 : E) 1)
    (κ : ℝ) (u v : E) :
    Integrable (fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫)
      (vonMisesFisherMeasure m κ) := by
  have hc : Continuous (fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫) := by fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

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
    have hb : 0 < b := by
      dsimp [b]
      exact div_pos (by exact_mod_cast (by omega : 0 < Module.finrank ℝ E)) two_pos
    simpa [H, b, q] using mul_div_mul_left (H b (q t)) (H b (q 0)) (Gamma_pos_of_pos hb).ne'
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
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (by exact_mod_cast (by omega : 0 < Module.finrank ℝ E)) two_pos
  let H := fun (a : ℝ) ↦ (Complex.regularizedHGFun 0 {(a : ℂ)} (k ^ 2 / 4 : ℝ)).re
  have hH (a : ℝ) : H a = besselI (a - 1) k / (k / 2) ^ (a - 1) := by
    rw [besselI_eq_rpow_mul]
    have harg : (k / 2) ^ 2 = k ^ 2 / 4 := by ring
    simp only [sub_add_cancel, harg]
    exact (mul_div_cancel_left₀ (H a) (rpow_pos_of_pos hp _).ne').symm
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
  field_simp [hI, hk.ne', hp']
  field_simp at hrec
  nlinarith [hrec]

/-- The mixed second moment under a nonzero natural parameter. All products here are
integrable by `memLp_inner_vonMisesFisherNaturalMeasure` and `MemLp.integrable_mul`. -/
theorem integral_inner_mul_inner_vonMisesFisherNaturalMeasure
    (hd : 2 ≤ Module.finrank ℝ E) {η : E} (hη : η ≠ 0) (u v : E) :
    let d := (Module.finrank ℝ E : ℝ)
    let A := besselI (d / 2) ‖η‖ / besselI (d / 2 - 1) ‖η‖
    ∫ x : sphere (0 : E) 1, ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫
        ∂vonMisesFisherNaturalMeasure η =
      A / ‖η‖ * ⟪u, v⟫ +
        (1 - d * A / ‖η‖) * (⟪η, u⟫ / ‖η‖) * (⟪η, v⟫ / ‖η‖) := by
  have hint (w : E) := (memLp_inner_vonMisesFisherNaturalMeasure η w 2).integrable_sq
  have hproduct : Integrable (fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫)
      (vonMisesFisherNaturalMeasure η) := by
    refine ((memLp_inner_vonMisesFisherNaturalMeasure η u 2).integrable_mul
      (memLp_inner_vonMisesFisherNaturalMeasure η v 2)).congr ?_
    filter_upwards with x
    exact Pi.mul_apply _ _ x
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
  dsimp only at hsum ⊢
  linear_combination hsum / 2

/-- The von Mises–Fisher second-moment tensor, evaluated on any two vectors. For positive
concentration it is `(A/κ) I + (1-d A/κ) m mᵀ`; at zero it is the uniform tensor `I/d`. -/
theorem integral_inner_mul_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) (u v : E) :
    let d := (Module.finrank ℝ E : ℝ)
    let A := besselI (d / 2) κ / besselI (d / 2 - 1) κ
    ∫ x : sphere (0 : E) 1, ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫
        ∂vonMisesFisherMeasure m κ =
      if κ = 0 then ⟪u, v⟫ / d else
        A / κ * ⟪u, v⟫ + (1 - d * A / κ) * ⟪(m : E), u⟫ * ⟪(m : E), v⟫ := by
  have : Nontrivial E := ⟨⟨m, 0, ne_zero_of_mem_sphere one_ne_zero m⟩⟩
  by_cases hzero : κ = 0
  · subst κ
    simp
  have hκ : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hzero)
  simp only [hzero, ↓reduceIte]
  have hη : κ • (m : E) ≠ 0 := smul_ne_zero hκ.ne' (ne_zero_of_mem_sphere one_ne_zero m)
  have hnorm : ‖κ • (m : E)‖ = κ := by simp [norm_smul, abs_of_pos hκ]
  rw [vonMisesFisherMeasure_of_nonneg m hκ.le]
  simpa only [hnorm, real_inner_smul_left, mul_div_cancel_left₀ _ hκ.ne'] using
    integral_inner_mul_inner_vonMisesFisherNaturalMeasure hd hη u v

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- The second-moment tensor of a sphere-valued von Mises–Fisher random variable, paired
with arbitrary ambient vectors. The source measure needs no additional normalization. -/
theorem integral_inner_mul_inner_vonMisesFisherMeasure
    {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → sphere (0 : E) 1} {m : sphere (0 : E) 1} {κ : ℝ}
    (hX : HasLaw X (vonMisesFisherMeasure m κ) P) (hd : 2 ≤ Module.finrank ℝ E)
    (hκ : 0 ≤ κ) (u v : E) :
    let d := (Module.finrank ℝ E : ℝ)
    let A := besselI (d / 2) κ / besselI (d / 2 - 1) κ
    ∫ ω, ⟪u, (X ω : E)⟫ * ⟪v, (X ω : E)⟫ ∂P =
      if κ = 0 then ⟪u, v⟫ / d else
        A / κ * ⟪u, v⟫ + (1 - d * A / κ) * ⟪(m : E), u⟫ * ⟪(m : E), v⟫ := by
  dsimp only
  rw [← TauCeti.Probability.integral_inner_mul_inner_vonMisesFisherMeasure hd m hκ u v]
  simpa only [Function.comp_def] using hX.integral_comp
    (f := fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫) (by fun_prop)

end ProbabilityTheory.HasLaw
