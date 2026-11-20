/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
public import TauCeti.Basic.Real.Sign
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Function.Sign

/-!
# Uniform attainment of the initial datum by the heat flow: examples

On a finite-dimensional real inner product space `E`, the heat flow `S(t) g = K_t ⋆ g` attains a
bounded uniformly continuous initial datum `g` uniformly, `‖S(t) g - g‖_∞ → 0` as `t → 0⁺`
(`TauCeti.tendstoUniformly_heatKernel_convolution`), and the rate is governed by a modulus of
continuity of `g`. This file records three examples showing what this does and does not cover.

* **A Lipschitz datum.** For `g(x) = min ‖x‖ 1`, which is `1`-Lipschitz, the rate is `√t`:
  `|S(t) g (x) - g(x)| ≤ M₁ √t` with `M₁ = ∫ ‖y‖ K_1(y) dy`
  (`TauCeti.abs_heatCauchyPotential_min_norm_one_sub_le`). Here `S(t) g` is the Cauchy potential
  `TauCeti.heatCauchyPotential g t`, which is `K_t ⋆ g` for `t > 0` and `g` for `t = 0`.
* **A bounded datum that is not uniformly continuous.** For `e ≠ 0` and the sign
  `f(x) = sign ⟪e, x⟫` of a linear form, `‖S(t) f - f‖_∞ = 1` for every `t > 0`
  (`TauCeti.eLpNorm_heatKernel_convolution_sign_inner_sub`). So the heat flow is not strongly
  continuous on `L^∞` (`TauCeti.not_tendsto_eLpNorm_heatKernel_convolution_sign_inner_sub`): the
  uniform attainment fails for this bounded datum, which is not uniformly continuous.
* **A bounded family that is not uniformly equicontinuous.** The plane waves are eigenfunctions
  of the heat flow, `S(t) sin ⟪ξ, ·⟫ = exp (-t ‖ξ‖²) sin ⟪ξ, ·⟫`
  (`TauCeti.heatKernel_convolution_sin_inner`). The family `sin ⟪ξ, ·⟫`, `ξ ∈ E`, is bounded by
  `1`, but for every `t > 0` it moves by exactly
  `‖S(t) sin ⟪ξ, ·⟫ - sin ⟪ξ, ·⟫‖_∞ = 1 - exp (-t ‖ξ‖²)`
  (`TauCeti.eLpNorm_heatKernel_convolution_sin_inner_sub`), which tends to `1` along
  `ξ = k • e`, `k → ∞`, for any `e ≠ 0`
  (`TauCeti.tendsto_eLpNorm_heatKernel_convolution_sin_inner_smul_sub`). So a common modulus of
  continuity cannot be dropped from a uniform rate of attainment for a family of data.

## The argument for the sign

Let `R` be the reflection in the hyperplane `⟪e, ·⟫ = 0`, an isometry, so measure preserving,
with `⟪e, R z⟫ = -⟪e, z⟫`. If `⟪e, x⟫ ≥ 0` and `⟪e, z⟫ ≥ 0`, then `‖x - z‖ ≤ ‖x - R z‖`, since
`‖x - R z‖² - ‖x - z‖² = 4 ⟪e, x⟫ ⟪e, z⟫ / ‖e‖²`. Averaging
`S(t) f (x) = ∫ K_t(x - z) sign ⟪e, z⟫ dz` with its image under `z ↦ R z` writes it as half the
integral of `(K_t(x - z) - K_t(x - R z)) sign ⟪e, z⟫`, which is nonnegative because `K_t` is
radially nonincreasing. Hence `S(t) f ≥ 0` where `⟪e, x⟫ ≥ 0`; being odd, `S(t) f ≤ 0` where
`⟪e, x⟫ ≤ 0`, so it vanishes on the hyperplane. With `|S(t) f| ≤ 1` this gives `|S(t) f - f| ≤ 1`.
Being continuous, `S(t) f` is small near the origin, while `f = 1` on the open half-space
`⟪e, ·⟫ > 0`. So `|S(t) f - f|` is close to `1` on a nonempty open set, which has positive
measure.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (diffusion on bounded uniformly continuous functions).
* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Chapter 3.
-/

public section

open MeasureTheory Filter Topology Set Real
open scoped RealInnerProductSpace Convolution ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### A Lipschitz datum -/

/-- **The heat flow attains the datum `min ‖x‖ 1` at the rate `√t`.** For `t ≥ 0`,
`|S(t) g (x) - g(x)| ≤ M₁ √t`, where `g(x) = min ‖x‖ 1` and `M₁ = ∫ ‖y‖ K_1(y) dy` is
`TauCeti.heatKernelMoment E 1`. This is the rate given by the modulus of continuity `r ↦ r` of the
`1`-Lipschitz datum. -/
theorem abs_heatCauchyPotential_min_norm_one_sub_le {t : ℝ} (ht : 0 ≤ t) (x : E) :
    |heatCauchyPotential (fun y : E ↦ min ‖y‖ 1) t x - min ‖x‖ 1| ≤ heatKernelMoment E 1 * √t := by
  have hlip : LipschitzWith 1 fun y : E ↦ min ‖y‖ 1 := lipschitzWith_one_norm.min_const 1
  have h := norm_heatCauchyPotential_sub_le hlip.holderWith hlip.continuous ht x
  rw [Real.sqrt_eq_rpow]
  simpa using h

/-! ### The sign of a linear form -/

section Sign

variable {e : E} {t : ℝ}

/-- The heat flow of `sign ⟪e, ·⟫` is odd. -/
theorem heatKernel_convolution_sign_inner_neg (e : E) (t : ℝ) (x : E) :
    (heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) (-x) =
      -(heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x := by
  rw [convolution_lsmul, convolution_lsmul, ← integral_neg, ← integral_neg_eq_self]
  congr 1
  ext y
  rw [show -x - -y = -(x - y) by abel]
  simp only [heatKernel_neg, inner_neg_right, Real.sign_neg, smul_neg]

omit [FiniteDimensional ℝ E] in
/-- `sign ⟪e, ·⟫` is measurable. -/
private theorem measurable_sign_inner (e : E) : Measurable fun y : E ↦ Real.sign ⟪e, y⟫ :=
  measurable_real_sign.comp (by fun_prop)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `sign ⟪e, ·⟫` is bounded by one. -/
private theorem norm_sign_inner_le_one (e y : E) : ‖Real.sign ⟪e, y⟫‖ ≤ 1 :=
  (Real.norm_eq_abs _).trans_le (Real.abs_sign_le_one _)

/-- **The heat flow of `sign ⟪e, ·⟫` is nonnegative on the half-space `⟪e, ·⟫ ≥ 0`.** -/
theorem heatKernel_convolution_sign_inner_nonneg (ht : 0 < t) {x : E} (hx : 0 ≤ ⟪e, x⟫) :
    0 ≤ (heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x := by
  let R := (ℝ ∙ e)ᗮ.reflection
  have hRe (z : E) : ⟪e, R z⟫ = -⟪e, z⟫ := inner_reflection_orthogonal_singleton z
  have hRR (z : E) : R (R z) = z := Submodule.reflection_reflection _ z
  let g : E → ℝ := fun z ↦ heatKernel t (x - z) * Real.sign ⟪e, z⟫
  have hconv : (heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x = ∫ z, g z := by
    simp only [convolution_lsmul_swap, smul_eq_mul, g]
  have hg : Integrable g := ((integrable_heatKernel ht).comp_sub_left x).mul_bdd
    (measurable_sign_inner e).aestronglyMeasurable (ae_of_all _ (norm_sign_inner_le_one e))
  have hR := R.measurePreserving
  have hgR : Integrable fun z ↦ g (R z) :=
    (hR.integrable_comp_emb R.toHomeomorph.measurableEmbedding).2 hg
  -- The integrand averaged with its reflection is pointwise nonnegative.
  have hpt (z : E) : 0 ≤ g z + g (R z) := by
    simp only [g, hRe, Real.sign_neg]
    rcases lt_trichotomy 0 ⟪e, z⟫ with hz | hz | hz
    · rw [Real.sign_of_pos hz]
      linarith [heatKernel_le_heatKernel_of_norm_le ht
        (norm_sub_le_norm_sub_reflection_orthogonal_singleton hz.le hx)]
    · simp [← hz]
    · rw [Real.sign_of_neg hz]
      have h := norm_sub_le_norm_sub_reflection_orthogonal_singleton
        (x := R z) (by rw [hRe]; linarith) hx
      rw [hRR] at h
      linarith [heatKernel_le_heatKernel_of_norm_le ht h]
  have hsum := integral_nonneg (μ := volume) (f := fun z ↦ g z + g (R z)) hpt
  rw [integral_add hg hgR, hR.integral_comp R.toHomeomorph.measurableEmbedding g] at hsum
  rw [hconv]
  linarith

/-- The heat flow of `sign ⟪e, ·⟫` is nonpositive on the half-space `⟪e, ·⟫ ≤ 0`. -/
theorem heatKernel_convolution_sign_inner_nonpos (ht : 0 < t) {x : E} (hx : ⟪e, x⟫ ≤ 0) :
    (heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x ≤ 0 := by
  have h := heatKernel_convolution_sign_inner_nonneg ht (x := -x)
    (by rw [inner_neg_right]; linarith)
  rw [heatKernel_convolution_sign_inner_neg] at h
  linarith

/-- The heat flow of `sign ⟪e, ·⟫` vanishes on the hyperplane `⟪e, ·⟫ = 0`. -/
theorem heatKernel_convolution_sign_inner_eq_zero (ht : 0 < t) {x : E} (hx : ⟪e, x⟫ = 0) :
    (heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x = 0 :=
  le_antisymm (heatKernel_convolution_sign_inner_nonpos ht hx.le)
    (heatKernel_convolution_sign_inner_nonneg ht hx.ge)

/-- At every point, the heat flow of `sign ⟪e, ·⟫` differs from `sign ⟪e, ·⟫` by at most `1`. -/
theorem abs_heatKernel_convolution_sign_inner_sub_le (ht : 0 < t) (x : E) :
    |(heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x - Real.sign ⟪e, x⟫| ≤ 1 := by
  have hle := norm_heatKernel_convolution_le ht (ae_of_all _ (norm_sign_inner_le_one e)) x
  rw [Real.norm_eq_abs, abs_le] at hle
  rw [abs_le]
  rcases lt_trichotomy 0 ⟪e, x⟫ with hx | hx | hx
  · rw [Real.sign_of_pos hx]
    have := heatKernel_convolution_sign_inner_nonneg ht hx.le
    constructor <;> linarith
  · rw [← hx, Real.sign_zero, heatKernel_convolution_sign_inner_eq_zero ht hx.symm]
    norm_num
  · rw [Real.sign_of_neg hx]
    have := heatKernel_convolution_sign_inner_nonpos ht hx.le
    constructor <;> linarith

/-- **The heat flow does not attain `sign ⟪e, ·⟫` uniformly.** For `e ≠ 0` and every `t > 0`,
`‖S(t) f - f‖_∞ = 1` for `f = sign ⟪e, ·⟫`, a bounded function that is not uniformly
continuous. -/
theorem eLpNorm_heatKernel_convolution_sign_inner_sub (he : e ≠ 0) (ht : 0 < t) :
    eLpNorm (fun x ↦ (heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x - Real.sign ⟪e, x⟫) ∞
      volume = 1 := by
  set u := heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫
  have hu : Continuous u :=
    (contDiff_heatKernel_convolution ht (ae_of_all _ (norm_sign_inner_le_one e))).continuous
  refine le_antisymm ?_ ?_
  · have hm : AEStronglyMeasurable (fun x ↦ u x - Real.sign ⟪e, x⟫) volume :=
      (hu.measurable.sub (measurable_sign_inner e)).aestronglyMeasurable
    rw [eLpNorm_exponent_top hm, ← ENNReal.ofReal_one]
    exact eLpNormEssSup_le_of_ae_bound
      (ae_of_all _ fun x ↦ abs_heatKernel_convolution_sign_inner_sub_le ht x)
  -- On the open half-space `⟪e, ·⟫ > 0` the difference is the continuous `u - 1`, whose values
  -- along `s • e` tend to `u 0 - 1 = -1` as `s → 0⁺`.
  have hU : IsOpen {x : E | 0 < ⟪e, x⟫} := isOpen_lt continuous_const (by fun_prop)
  have hcont : ContinuousOn (fun x ↦ u x - Real.sign ⟪e, x⟫) {x : E | 0 < ⟪e, x⟫} :=
    (by fun_prop : Continuous fun x ↦ u x - 1).continuousOn.congr fun x (hx : 0 < ⟪e, x⟫) ↦ by
      rw [Real.sign_of_pos hx]
  have hpos (s : ℝ) (hs : 0 < s) : 0 < ⟪e, s • e⟫ := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_pos hs (pow_pos (norm_pos_iff.2 he) 2)
  have hlim : Tendsto (fun s : ℝ ↦ ‖u (s • e) - 1‖ₑ) (𝓝[>] 0) (𝓝 1) := by
    have h0 : ‖u ((0 : ℝ) • e) - 1‖ₑ = 1 := by
      rw [zero_smul, show u 0 = 0 from
        heatKernel_convolution_sign_inner_eq_zero ht (inner_zero_right e)]
      simp
    rw [← h0]
    exact (((hu.comp (continuous_id.smul continuous_const)).sub continuous_const).eNorm.tendsto
      0).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun (s : ℝ) (hs : s ∈ Ioi 0) ↦ ?_)
  have h := (hcont.continuousAt (hU.mem_nhds (hpos s hs))).eNorm_le_eLpNorm_top (μ := volume)
  rwa [Real.sign_of_pos (hpos s hs)] at h

/-- **The heat flow is not strongly continuous on `L^∞`.** For `e ≠ 0`,
`‖S(t) f - f‖_∞` does not tend to `0` as `t → 0⁺` for `f = sign ⟪e, ·⟫`. -/
theorem not_tendsto_eLpNorm_heatKernel_convolution_sign_inner_sub (he : e ≠ 0) :
    ¬Tendsto (fun t ↦ eLpNorm (fun x ↦ (heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x -
      Real.sign ⟪e, x⟫) ∞ volume) (𝓝[>] 0) (𝓝 0) := by
  intro h
  have h1 : Tendsto (fun t ↦ eLpNorm (fun x ↦ (heatKernel t ⋆ fun y ↦ Real.sign ⟪e, y⟫) x -
      Real.sign ⟪e, x⟫) ∞ volume) (𝓝[>] 0) (𝓝 1) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun (t : ℝ) (ht : t ∈ Ioi 0) ↦
      (eLpNorm_heatKernel_convolution_sign_inner_sub he ht).symm)
  exact one_ne_zero (tendsto_nhds_unique h1 h)

end Sign

/-! ### Plane waves -/

section PlaneWave

variable {t : ℝ}

/-- For `t > 0`, the heat flow moves the sine wave `sin ⟪ξ, ·⟫` by exactly
`‖S(t) sin ⟪ξ, ·⟫ - sin ⟪ξ, ·⟫‖_∞ = 1 - exp (-t ‖ξ‖²)`. -/
theorem eLpNorm_heatKernel_convolution_sin_inner_sub (ht : 0 < t) (ξ : E) :
    eLpNorm (fun x ↦ (heatKernel t ⋆ fun y ↦ Real.sin ⟪ξ, y⟫) x - Real.sin ⟪ξ, x⟫) ∞ volume =
      ENNReal.ofReal (1 - Real.exp (-(t * ‖ξ‖ ^ 2))) := by
  set c := 1 - Real.exp (-(t * ‖ξ‖ ^ 2))
  have hc : 0 ≤ c := sub_nonneg.2 (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖ξ‖]))
  have heq (x : E) : (heatKernel t ⋆ fun y ↦ Real.sin ⟪ξ, y⟫) x - Real.sin ⟪ξ, x⟫ =
      -(c * Real.sin ⟪ξ, x⟫) := by
    rw [heatKernel_convolution_sin_inner ht]
    ring
  simp_rw [heq]
  refine le_antisymm ?_ ?_
  · rw [eLpNorm_exponent_top
      (by fun_prop : Continuous fun x : E ↦ -(c * Real.sin ⟪ξ, x⟫)).aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_bound (ae_of_all _ fun x ↦ ?_)
    rw [norm_neg, norm_mul, Real.norm_of_nonneg hc]
    exact mul_le_of_le_one_right hc (Real.abs_sin_le_one _)
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [c]
  -- At the point `x₀ = (π / 2 / ‖ξ‖²) • ξ` the sine equals `1`.
  set x₀ : E := (π / 2 / ‖ξ‖ ^ 2) • ξ
  have hx₀ : Real.sin ⟪ξ, x₀⟫ = 1 := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hξ)), Real.sin_pi_div_two]
  have h := (by fun_prop : Continuous fun x : E ↦ -(c * Real.sin ⟪ξ, x⟫)).continuousAt
    |>.eNorm_le_eLpNorm_top (μ := volume) (x := x₀)
  rwa [hx₀, mul_one, eNorm_neg, Real.eNorm_of_nonneg hc] at h

/-- **The heat flow does not attain a bounded family uniformly without a common modulus of
continuity.** For `e ≠ 0` and `t > 0`, the sine waves `sin ⟪k • e, ·⟫`, all bounded by `1`,
satisfy `‖S(t) sin ⟪k • e, ·⟫ - sin ⟪k • e, ·⟫‖_∞ → 1` as `k → ∞`. -/
theorem tendsto_eLpNorm_heatKernel_convolution_sin_inner_smul_sub {e : E} (he : e ≠ 0)
    (ht : 0 < t) :
    Tendsto (fun k : ℝ ↦ eLpNorm (fun x ↦ (heatKernel t ⋆ fun y ↦ Real.sin ⟪k • e, y⟫) x -
      Real.sin ⟪k • e, x⟫) ∞ volume) atTop (𝓝 1) := by
  have hpos : 0 < t * ‖e‖ ^ 2 := mul_pos ht (pow_pos (norm_pos_iff.2 he) 2)
  have hexp : Tendsto (fun k : ℝ ↦ Real.exp (-(t * ‖k • e‖ ^ 2))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
    have hk : (fun k : ℝ ↦ t * ‖k • e‖ ^ 2) = fun k ↦ k ^ 2 * (t * ‖e‖ ^ 2) := by
      funext k
      simp [norm_smul, mul_pow]
      ring
    rw [hk]
    exact (tendsto_pow_atTop two_ne_zero).atTop_mul_const hpos
  have h1 : Tendsto (fun k : ℝ ↦ ENNReal.ofReal (1 - Real.exp (-(t * ‖k • e‖ ^ 2)))) atTop
      (𝓝 1) := by
    have h := (ENNReal.continuous_ofReal.tendsto (1 - 0)).comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hexp)
    rwa [sub_zero, ENNReal.ofReal_one] at h
  exact h1.congr fun k ↦ (eLpNorm_heatKernel_convolution_sin_inner_sub ht (k • e)).symm

end PlaneWave

end TauCeti
