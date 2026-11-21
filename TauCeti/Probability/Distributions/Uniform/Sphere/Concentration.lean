/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Analysis.Normed.Module.Normalize.Measurable
import TauCeti.Probability.Concentration.SubgaussianTail
import TauCeti.Probability.Distributions.Chi.Moments
import TauCeti.Probability.Distributions.Gaussian.Concentration
import TauCeti.Probability.Distributions.Uniform.Sphere.Norm

/-!
# Concentration of Lipschitz functions on the sphere

Let `σ` be the uniform law on the unit sphere of a real inner product space `E` of dimension
`d ≥ 1`, and let `f` be an `L`-Lipschitz real function on the sphere. Then `f` concentrates
around its mean at scale `L / √d`: `f - 𝔼 f` is sub-Gaussian with variance proxy `8 π² L² / d`,
so that for `t ≥ 0`

`σ {u | t ≤ |f u - 𝔼 f|} ≤ 2 exp (-d t² / (16 π² L²))`.

This is the concentration of measure on the sphere behind Dvoretzky's theorem on almost Euclidean
sections of finite-dimensional normed spaces. In dimension zero the sphere is empty and both
statements hold trivially.

The proof transfers Gaussian concentration to the sphere. The centred function `g = f - 𝔼 f` has
`|g| ≤ 2L`, since the sphere has diameter `2`, so its positively homogeneous extension
`G x = ‖x‖ g (x / ‖x‖)` is `4L`-Lipschitz on `E` (`LipschitzWith.norm_mul_comp_sphereDirection`).
Gaussian concentration of Lipschitz functions
(`LipschitzWith.hasSubgaussianMGF_stdGaussian_sub_integral`) makes `G` sub-Gaussian with variance
proxy `4 π² L²` under the standard Gaussian law, and the polar factorization of that law makes
`G` have mean zero. Since the direction `x / ‖x‖` and the radius `‖x‖` of a standard Gaussian
vector are independent, uniform on the sphere and chi distributed, Jensen's inequality in the
radius gives `𝔼_σ exp (t m g) ≤ 𝔼 exp (t G)`, where `m ≥ √(d / 2)` is the mean of the chi law.
Rescaling `t` by `m` turns the variance proxy `4 π² L²` of `G` into `8 π² L² / d` for `g`.

## Main results

* `LipschitzWith.hasSubgaussianMGF_uniformSphereMeasure_sub_integral`: an `L`-Lipschitz function
  on the sphere is sub-Gaussian about its mean with variance proxy `8 π² L² / d`.
* `LipschitzWith.measureReal_uniformSphereMeasure_setOf_le_abs_sub_integral_le`: the tail bound
  `2 exp (-d t² / (16 π² L²))`.

## References

* G. Pisier, *Probabilistic methods in the geometry of Banach spaces*, in Probability and
  Analysis (Varenna, 1985), Lecture Notes in Math. **1206**, Springer, 1986, §2.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real TauCeti
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- An `L`-Lipschitz function on the unit sphere stays within `2L` of its uniform mean, since the
sphere has diameter at most `2`. -/
private lemma abs_sub_integral_uniformSphereMeasure_le {f : sphere (0 : E) 1 → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (u : sphere (0 : E) 1) :
    |f u - ∫ v, f v ∂uniformSphereMeasure E| ≤ 2 * L := by
  have : Nontrivial E := ⟨⟨u, 0, ne_zero_of_mem_sphere one_ne_zero u⟩⟩
  have hb (v : sphere (0 : E) 1) : |f u - f v| ≤ 2 * L := by
    have hdist : dist u v ≤ 2 := by
      rw [Subtype.dist_eq]
      calc dist (u : E) v ≤ dist (u : E) 0 + dist (0 : E) v := dist_triangle _ _ _
        _ = 2 := by
          rw [dist_comm (0 : E), mem_sphere.1 u.property, mem_sphere.1 v.property]; norm_num
    rw [← Real.dist_eq, mul_comm]
    exact (hf.dist_le_mul u v).trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
  have hfi : Integrable f (uniformSphereMeasure E) :=
    .of_bound hf.continuous.aestronglyMeasurable (|f u| + 2 * L) (.of_forall fun v ↦ by
      rw [Real.norm_eq_abs]
      linarith [abs_sub_abs_le_abs_sub (f v) (f u), abs_sub_comm (f u) (f v), hb v])
  have h := norm_integral_le_of_norm_le_const (μ := uniformSphereMeasure E)
    (f := fun v ↦ f u - f v) (C := 2 * L) (.of_forall fun v ↦ (Real.norm_eq_abs _).trans_le (hb v))
  rwa [probReal_univ, mul_one, integral_sub (integrable_const _) hfi, integral_const,
    probReal_univ, one_smul, Real.norm_eq_abs] at h

/-- **Jensen's inequality in the radius.** For the chi mean `m` of the radius of a standard
Gaussian vector, the exponential moment `𝔼_σ exp (t m g)` of a measurable function `g` on the
sphere is at most the Gaussian exponential moment of its homogeneous extension
`x ↦ ‖x‖ g (x / ‖x‖)`. -/
private lemma lintegral_exp_mul_integral_chiMeasure_le {g : sphere (0 : E) 1 → ℝ}
    (hg : Measurable g) (e : sphere (0 : E) 1) (t : ℝ) :
    ∫⁻ u, .ofReal (exp (t * (∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1) * g u))
        ∂uniformSphereMeasure E ≤
      ∫⁻ x, .ofReal (exp (t * (‖x‖ * g (sphereDirection e x)))) ∂stdGaussian E := by
  set d := Module.finrank ℝ E
  have : IsProbabilityMeasure (chiMeasure d 1) :=
    isProbabilityMeasure_chiMeasure (Nat.cast_nonneg _) one_pos
  set H : sphere (0 : E) 1 × ℝ → ℝ≥0∞ := fun z ↦ .ofReal (exp (t * (z.2 * g z.1)))
  have hH : Measurable H := by fun_prop
  have hΦ : Measurable fun x : E ↦ (sphereDirection e x, ‖x‖) :=
    (measurable_sphereDirection e).prodMk measurable_norm
  -- Polar coordinates turn the Gaussian integral into an iterated sphere-radius integral.
  -- The Gaussian integrand is `H` composed with `x ↦ (sphereDirection e x, ‖x‖)`.
  refine le_of_le_of_eq ?_ (lintegral_map (f := H) hH hΦ)
  rw [stdGaussian_map_sphereDirection_prod_norm e, lintegral_prod _ hH.aemeasurable]
  refine lintegral_mono fun u ↦ ?_
  have hint : Integrable (fun r ↦ exp (t * (r * g u))) (chiMeasure d 1) :=
    (integrable_exp_mul_id_chiMeasure d 1 (t * g u)).congr
      (.of_forall fun r ↦ congrArg exp (by ring))
  have hid : Integrable (fun r : ℝ ↦ t * (r * g u)) (chiMeasure d 1) := by
    have h1 : Integrable (fun r : ℝ ↦ r) (chiMeasure d 1) := by
      simpa using integrable_pow_chiMeasure d 1 1
    exact (h1.mul_const (g u)).const_mul t
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ (exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmean : ∫ r, t * (r * g u) ∂chiMeasure d 1 = t * (∫ r, r ∂chiMeasure d 1) * g u := by
    rw [integral_const_mul, integral_mul_const, mul_assoc]
  rw [← hmean]
  exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ (by simp) hid hint

/-- The standard Gaussian integral of the homogeneous extension `x ↦ ‖x‖ g (x / ‖x‖)` of a
measurable function `g` on the sphere is the chi mean times the uniform spherical integral
of `g`. -/
private lemma integral_stdGaussian_norm_mul_comp_sphereDirection {g : sphere (0 : E) 1 → ℝ}
    (hg : Measurable g) (e : sphere (0 : E) 1) :
    ∫ x, ‖x‖ * g (sphereDirection e x) ∂stdGaussian E =
      (∫ r, r ∂chiMeasure (Module.finrank ℝ E) 1) * ∫ u, g u ∂uniformSphereMeasure E := by
  have hhomog {r : ℝ} (hr : 0 < r) (x : E) :
      ‖r • x‖ * g (sphereDirection e (r • x)) = r • (‖x‖ * g (sphereDirection e x)) := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hpos : 0 < r * ‖x‖ := mul_pos hr (norm_pos_iff.2 hx)
    rw [show r • x = (r * ‖x‖) • (sphereDirection e x : E) by
        rw [mul_smul, norm_smul_sphereDirection],
      sphereDirection_smul_of_pos e hpos, norm_smul, Real.norm_of_nonneg hpos.le,
      norm_eq_of_mem_sphere, mul_one, smul_eq_mul, mul_assoc]
  have hmeas : Measurable fun u : sphere (0 : E) 1 ↦ ‖(u : E)‖ * g (sphereDirection e u) :=
    (measurable_norm.comp measurable_subtypeVal).mul
      (hg.comp ((measurable_sphereDirection e).comp measurable_subtypeVal))
  rw [integral_stdGaussian_of_posHomog hmeas.aestronglyMeasurable hhomog, smul_eq_mul]
  simp only [sphereDirection_coe, norm_eq_of_mem_sphere, one_mul]

/-- **Transfer of Gaussian concentration to the sphere.** If the homogeneous extension
`x ↦ ‖x‖ g (x / ‖x‖)` of a bounded measurable function `g` on the sphere is sub-Gaussian with
variance proxy `c` under the standard Gaussian law in dimension `d`, then `g` itself is
sub-Gaussian with variance proxy `2 c / d` under the uniform law on the sphere. -/
private lemma hasSubgaussianMGF_uniformSphereMeasure_of_stdGaussian {g : sphere (0 : E) 1 → ℝ}
    {M c : ℝ≥0} (hg : Measurable g) (hM : ∀ u, |g u| ≤ M) (e : sphere (0 : E) 1)
    (hG : HasSubgaussianMGF (fun x ↦ ‖x‖ * g (sphereDirection e x)) c (stdGaussian E)) :
    HasSubgaussianMGF g (2 * c / Module.finrank ℝ E) (uniformSphereMeasure E) := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  set d := Module.finrank ℝ E
  set m := ∫ r, r ∂chiMeasure d 1
  have hd : (0 : ℝ) < d := by exact_mod_cast Module.finrank_pos
  have hm : √((d : ℝ) / 2) ≤ m := by
    have h := mul_sqrt_div_two_le_integral_id_chiMeasure (k := (d : ℝ)) (s := 1)
      (by exact_mod_cast Module.finrank_pos) zero_le_one
    rwa [one_mul] at h
  have hm0 : 0 < m := lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) hm
  have hm2 : (d : ℝ) ≤ 2 * m ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hm 2
    rw [Real.sq_sqrt (by positivity)] at this
    linarith
  -- The function `g` is bounded, so all its exponential moments are finite.
  have hint (s : ℝ) : Integrable (fun u ↦ exp (s * g u)) (uniformSphereMeasure E) :=
    .of_bound (hg.const_mul s).exp.aestronglyMeasurable (exp (|s| * M)) (.of_forall fun u ↦ by
      rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_exp]
      calc s * g u ≤ |s| * |g u| := (le_abs_self _).trans (abs_mul _ _).le
        _ ≤ |s| * M := mul_le_mul_of_nonneg_left (hM u) (abs_nonneg _))
  refine ⟨hint, fun s ↦ ?_⟩
  -- Jensen's inequality in the radius at the rescaled parameter `s / m`.
  have hkey := lintegral_exp_mul_integral_chiMeasure_le hg e (s / m)
  rw [div_mul_cancel₀ s hm0.ne'] at hkey
  have h1 : ENNReal.ofReal (mgf g (uniformSphereMeasure E) s) ≤
      .ofReal (exp (c * (s / m) ^ 2 / 2)) :=
    calc ENNReal.ofReal (mgf g (uniformSphereMeasure E) s)
        = ∫⁻ u, .ofReal (exp (s * g u)) ∂uniformSphereMeasure E :=
          ofReal_integral_eq_lintegral_ofReal (hint s) (.of_forall fun _ ↦ (exp_pos _).le)
      _ ≤ ∫⁻ x, .ofReal (exp (s / m * (‖x‖ * g (sphereDirection e x)))) ∂stdGaussian E := hkey
      _ = .ofReal (mgf (fun x ↦ ‖x‖ * g (sphereDirection e x)) (stdGaussian E) (s / m)) :=
          (ofReal_integral_eq_lintegral_ofReal (hG.integrable_exp_mul _)
            (.of_forall fun _ ↦ (exp_pos _).le)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hG.mgf_le _)
  refine ((ENNReal.ofReal_le_ofReal_iff (exp_pos _).le).1 h1).trans (exp_le_exp.2 ?_)
  -- `c s² / (2 m²) ≤ c s² / d` since `d ≤ 2 m²`.
  push_cast
  rw [div_pow, show (c : ℝ) * (s ^ 2 / m ^ 2) / 2 = c * s ^ 2 / (2 * m ^ 2) by ring,
    show 2 * (c : ℝ) / d * s ^ 2 / 2 = c * s ^ 2 / d by field_simp]
  exact div_le_div_of_nonneg_left (by positivity) hd hm2

end TauCeti.Probability

namespace LipschitzWith

open TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {f : sphere (0 : E) 1 → ℝ} {L : ℝ≥0}

/-- **Concentration of measure on the sphere, exponential-moment form.** In dimension `d`, an
`L`-Lipschitz function `f` on the unit sphere is sub-Gaussian about its uniform mean with variance
proxy `8 π² L² / d`: `𝔼 exp (t (f - 𝔼 f)) ≤ exp (4 π² L² t² / d)`. -/
theorem hasSubgaussianMGF_uniformSphereMeasure_sub_integral (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun u ↦ f u - ∫ v, f v ∂uniformSphereMeasure E)
      (8 * NNReal.pi ^ 2 * L ^ 2 / Module.finrank ℝ E) (uniformSphereMeasure E) := by
  rcases isEmpty_or_nonempty (sphere (0 : E) 1) with hE | ⟨⟨e⟩⟩
  · -- In dimension zero the sphere is empty and its uniform law vanishes.
    rw [show uniformSphereMeasure E = 0 from Subsingleton.elim _ _]
    exact ⟨by simp, fun _ ↦ by simpa using (exp_pos _).le⟩
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  set g : sphere (0 : E) 1 → ℝ := fun u ↦ f u - ∫ v, f v ∂uniformSphereMeasure E
  have hgL : LipschitzWith L g :=
    .of_dist_le_mul fun u v ↦ by rw [dist_sub_right]; exact hf.dist_le_mul u v
  have hgM (u : sphere (0 : E) 1) : |g u| ≤ ((2 * L : ℝ≥0) : ℝ) := by
    push_cast
    exact abs_sub_integral_uniformSphereMeasure_le hf u
  -- `g` has mean zero, so its `4L`-Lipschitz homogeneous extension has Gaussian mean zero.
  have hgi : Integrable g (uniformSphereMeasure E) :=
    .of_bound hgL.continuous.aestronglyMeasurable (2 * L)
      (.of_forall fun u ↦ by simpa using hgM u)
  have hfi : Integrable f (uniformSphereMeasure E) :=
    (hgi.add (integrable_const (∫ v, f v ∂uniformSphereMeasure E))).congr
      (.of_forall fun u ↦ sub_add_cancel _ _)
  have hG0 : ∫ x, ‖x‖ * g (sphereDirection e x) ∂stdGaussian E = 0 := by
    rw [integral_stdGaussian_norm_mul_comp_sphereDirection hgL.continuous.measurable e,
      integral_sub hfi (integrable_const _), integral_const, probReal_univ, one_smul, sub_self,
      mul_zero]
  have hG := (hgL.norm_mul_comp_sphereDirection hgM e).hasSubgaussianMGF_stdGaussian_sub_integral
  simp only [hG0, sub_zero] at hG
  -- Gaussian concentration at proxy `π² (4L)² / 4` transfers to proxy `8 π² L² / d`.
  convert hasSubgaussianMGF_uniformSphereMeasure_of_stdGaussian hgL.continuous.measurable hgM e hG
    using 2
  ring

/-- **Concentration of measure on the sphere.** In dimension `d`, an `L`-Lipschitz function `f` on
the unit sphere satisfies `σ {u | t ≤ |f u - 𝔼 f|} ≤ 2 exp (-d t² / (16 π² L²))` for `t ≥ 0`, where
`σ` is the uniform law on the sphere. -/
theorem measureReal_uniformSphereMeasure_setOf_le_abs_sub_integral_le (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 ≤ t) :
    (uniformSphereMeasure E).real {u | t ≤ |f u - ∫ v, f v ∂uniformSphereMeasure E|} ≤
      2 * exp (-(Module.finrank ℝ E) * t ^ 2 / (16 * π ^ 2 * L ^ 2)) := by
  have hc : -t ^ 2 / (2 * ((8 * NNReal.pi ^ 2 * L ^ 2 / Module.finrank ℝ E : ℝ≥0) : ℝ)) =
      -(Module.finrank ℝ E) * t ^ 2 / (16 * π ^ 2 * L ^ 2) := by
    push_cast [NNReal.coe_real_pi]
    rw [mul_div_assoc', div_div_eq_mul_div]
    ring
  simpa only [hc] using
    hf.hasSubgaussianMGF_uniformSphereMeasure_sub_integral.measureReal_abs_ge_le ht

end LipschitzWith
