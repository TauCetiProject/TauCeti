/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Analysis.PDE.HeatKernel.Basic

/-!
# The heat kernel is an approximate identity

For a bounded measurable function `g` on a finite-dimensional real inner product space `E`, the
function `u(t, x) = (K_t ⋆ g)(x)`, where `K_t` is the heat kernel, is the candidate solution of the
Cauchy problem `∂ₜu = Δu`, `u(0, ·) = g`. This file proves that `u` attains its initial datum:

* the convolution is bounded by the same constant as `g` (`K_t ⋆ ·` is an `L^∞` contraction);
* if `g` is continuous at `x₀`, then `u(t, x) → g(x₀)` as `(t, x) → (0⁺, x₀)`;
* if `g` is bounded and uniformly continuous, then `K_t ⋆ g → g` uniformly as `t → 0⁺`.

The heat kernel is the dilation `K_t(x) = c ^ n K_1(c • x)` with `c = 1 / √t`
(`TauCeti.heatKernel_eq_mul_heatKernel_one_smul`), so as `t → 0⁺`
its mass concentrates at the origin (`TauCeti.tendsto_setIntegral_compl_ball_heatKernel`). This
follows from Mathlib's peak-function theorem
`MeasureTheory.tendsto_integral_comp_smul_smul_of_integrable`. The three statements above then come
from a single estimate, `TauCeti.norm_heatKernel_convolution_sub_le`, which splits the convolution
integral into the parts near and far from the origin.

Mathlib's `Real.tendsto_integral_gaussian_smul'` is the pointwise limit at a fixed point for an
*integrable* datum, which it needs for Fourier inversion. The Cauchy problem instead takes bounded
data, which need not be integrable, and needs the joint limit in `(t, x)`.

## Main declarations

* `TauCeti.tendsto_setIntegral_compl_ball_heatKernel`: the mass of `K_t` outside any ball about
  the origin tends to zero as `t → 0⁺`.
* `TauCeti.norm_heatKernel_convolution_le`: `‖(K_t ⋆ g)(x)‖ ≤ M` when `‖g‖ ≤ M` a.e.
* `TauCeti.norm_heatKernel_convolution_sub_le`: the approximate-identity estimate.
* `TauCeti.tendsto_heatKernel_convolution`: `(K_t ⋆ g)(x) → g(x₀)` as `(t, x) → (0⁺, x₀)` at a
  point of continuity of `g`.
* `TauCeti.tendstoUniformly_heatKernel_convolution`: `K_t ⋆ g → g` uniformly for bounded
  uniformly continuous `g`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.3.1, Theorem 1.
* E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter I,
  Section 1 (approximate identities).
-/

public section

noncomputable section

namespace TauCeti

open Filter Metric MeasureTheory Module Real Set Topology
open scoped BoundedContinuousFunction Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- At unit time the heat kernel decays faster than any power: `‖x‖ ^ k K_1(x) → 0` as
`‖x‖ → ∞` for every `k`. For `k = dim E` this is the decay hypothesis of Mathlib's peak-function
theorem. -/
theorem tendsto_norm_pow_mul_heatKernel_one (k : ℕ) :
    Tendsto (fun x : E => ‖x‖ ^ k * heatKernel 1 x) (Bornology.cobounded E) (𝓝 0) := by
  have hnorm := (tendsto_norm_cobounded_atTop (E := E)).mono_right atTop_le_cocompact
  have h := ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 4⁻¹) (by norm_num)
    k).comp hnorm).const_mul ((4 * π) ^ (-(finrank ℝ E : ℝ) / 2))
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, abs_norm, rpow_natCast, heatKernel_apply]
  ring_nf

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Concentration of the heat kernel.** As `t → 0⁺`, the mass of `K_t` outside any ball about
the origin tends to zero. -/
theorem tendsto_setIntegral_compl_ball_heatKernel {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t => ∫ z in (ball (0 : E) r)ᶜ, heatKernel t z) (𝓝[>] 0) (𝓝 0) := by
  -- The mass inside the ball tends to one: apply the peak-function theorem to the indicator of
  -- the ball, which is integrable and continuous at the origin.
  have hind : Integrable ((ball (0 : E) r).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  have hcont : ContinuousAt ((ball (0 : E) r).indicator fun _ => (1 : ℝ)) 0 :=
    (continuousAt_const (y := (1 : ℝ))).congr <| eventually_of_mem (ball_mem_nhds 0 hr) fun z hz =>
      by simp [hz]
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable (fun x => (heatKernel_pos one_pos
    x).le) (integral_heatKernel one_pos) (tendsto_norm_pow_mul_heatKernel_one _) hind hcont
  rw [indicator_of_mem (mem_ball_self hr)] at hpeak
  have hsqrt : Tendsto (fun t : ℝ => (√t)⁻¹) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    have := (continuous_sqrt.continuousWithinAt (x := 0)).tendsto_nhdsWithin
      (s := Ioi (0 : ℝ)) (t := Ioi 0) fun t ht => sqrt_pos.2 ht
    rwa [sqrt_zero] at this
  have hin : Tendsto (fun t => ∫ z in ball (0 : E) r, heatKernel t z) (𝓝[>] 0) (𝓝 1) :=
    (hpeak.comp hsqrt).congr' <| eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) => by
      simp only [Function.comp_apply]
      rw [← integral_indicator measurableSet_ball]
      congr 1 with z
      by_cases hz : z ∈ ball (0 : E) r <;>
        simp [hz, heatKernel_eq_mul_heatKernel_one_smul ht z]
  have hout := (tendsto_const_nhds (x := (1 : ℝ))).sub hin
  rw [sub_self] at hout
  refine hout.congr' <| eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) => ?_
  dsimp only
  rw [setIntegral_compl measurableSet_ball (integrable_heatKernel ht), integral_heatKernel ht]

/-- **The heat semigroup is an `L^∞` contraction.** If `‖g‖ ≤ M` almost everywhere, then
`‖(K_t ⋆ g)(x)‖ ≤ M` for every `t > 0` and every `x`. -/
theorem norm_heatKernel_convolution_le {t : ℝ} (ht : 0 < t) {g : E → F} {M : ℝ}
    (hM : ∀ᵐ y, ‖g y‖ ≤ M) (x : E) : ‖(heatKernel t ⋆ g) x‖ ≤ M := by
  have hg : ∀ᵐ z, ‖g (x - z)‖ ≤ M :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae hM
  calc ‖(heatKernel t ⋆ g) x‖ ≤ ∫ z, heatKernel t z * M := by
        rw [convolution_def]
        refine norm_integral_le_of_norm_le ((integrable_heatKernel ht).mul_const M) ?_
        filter_upwards [hg] with z hz
        rw [ContinuousLinearMap.lsmul_apply, norm_smul, norm_of_nonneg (heatKernel_pos ht z).le]
        exact mul_le_mul_of_nonneg_left hz (heatKernel_pos ht z).le
    _ = M := by rw [integral_mul_const, integral_heatKernel ht, one_mul]

/-- **The approximate-identity estimate for the heat kernel.** Let `‖g‖ ≤ M` almost everywhere,
and suppose `‖g(x - z) - a‖ ≤ ε` for all `z` in the ball of radius `r` about the origin. Then
`‖(K_t ⋆ g)(x) - a‖ ≤ ε + (M + ‖a‖) ∫_{‖z‖ ≥ r} K_t(z) dz`. -/
theorem norm_heatKernel_convolution_sub_le [CompleteSpace F] {t : ℝ} (ht : 0 < t) {g : E → F}
    (hg : AEStronglyMeasurable g) {M : ℝ} (hM : ∀ᵐ y, ‖g y‖ ≤ M) (x : E) (a : F) {r ε : ℝ}
    (hε₀ : 0 ≤ ε) (hε : ∀ z ∈ ball (0 : E) r, ‖g (x - z) - a‖ ≤ ε) :
    ‖(heatKernel t ⋆ g) x - a‖ ≤ ε + (M + ‖a‖) * ∫ z in (ball (0 : E) r)ᶜ, heatKernel t z := by
  have hK := integrable_heatKernel (E := E) ht
  have hK₀ : ∀ z : E, 0 ≤ heatKernel t z := fun z => (heatKernel_pos ht z).le
  have hqmp := quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure E) x
  have hg' : ∀ᵐ z, ‖g (x - z)‖ ≤ M := hqmp.ae hM
  have hint : Integrable fun z => heatKernel t z • g (x - z) :=
    hK.smul_of_top_left (memLp_top_of_bound (hg.comp_quasiMeasurePreserving hqmp) M hg')
  have hKr : Integrable ((ball (0 : E) r)ᶜ.indicator (heatKernel t)) :=
    hK.indicator measurableSet_ball.compl
  -- Since `K_t` has mass one, `(K_t ⋆ g)(x) - a` is the integral of `K_t(z) • (g(x - z) - a)`.
  have hdiff : (heatKernel t ⋆ g) x - a = ∫ z, heatKernel t z • (g (x - z) - a) := by
    simp_rw [smul_sub]
    rw [integral_sub hint (hK.smul_const a), integral_smul_const, integral_heatKernel ht, one_smul,
      convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
  rw [hdiff]
  -- Bound the integrand by `ε K_t` near the origin and by `(M + ‖a‖) K_t` away from it.
  refine (norm_integral_le_of_norm_le ((hK.const_mul ε).add (hKr.const_mul (M + ‖a‖))) ?_).trans_eq
    ?_
  · filter_upwards [hg'] with z hz
    rw [norm_smul, norm_of_nonneg (hK₀ z), Pi.add_apply]
    by_cases hzr : z ∈ ball (0 : E) r
    · rw [indicator_of_notMem (notMem_compl_iff.2 hzr), mul_zero, add_zero, mul_comm]
      exact mul_le_mul_of_nonneg_right (hε z hzr) (hK₀ z)
    · rw [indicator_of_mem (mem_compl hzr)]
      calc heatKernel t z * ‖g (x - z) - a‖ ≤ heatKernel t z * (M + ‖a‖) :=
            mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) (hK₀ z)
        _ ≤ ε * heatKernel t z + (M + ‖a‖) * heatKernel t z := by
            nlinarith [mul_nonneg hε₀ (hK₀ z)]
  · rw [Pi.add_def, integral_add (hK.const_mul ε) (hKr.const_mul (M + ‖a‖)), integral_const_mul,
      integral_const_mul, integral_heatKernel ht, mul_one,
      integral_indicator measurableSet_ball.compl]

/-- **The initial condition of the heat equation.** Let `g` be measurable and essentially bounded,
and continuous at `x₀`. Then `(K_t ⋆ g)(x) → g(x₀)` as `(t, x) → (0⁺, x₀)`: the function
`u(t, x) = (K_t ⋆ g)(x)` attains the initial datum `g` at `x₀`. -/
theorem tendsto_heatKernel_convolution [CompleteSpace F] {g : E → F}
    (hg : AEStronglyMeasurable g) {M : ℝ} (hM : ∀ᵐ y, ‖g y‖ ≤ M) {x₀ : E}
    (hx₀ : ContinuousAt g x₀) :
    Tendsto (fun p : ℝ × E => (heatKernel p.1 ⋆ g) p.2) (𝓝[>] 0 ×ˢ 𝓝 x₀) (𝓝 (g x₀)) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousAt_iff.1 hx₀ (ε / 2) (half_pos hε)
  have htail := (tendsto_setIntegral_compl_ball_heatKernel (E := E) (half_pos hδ)).const_mul
    (M + ‖g x₀‖)
  rw [mul_zero] at htail
  filter_upwards [((htail.eventually (gt_mem_nhds (half_pos hε))).and
    self_mem_nhdsWithin).prod_mk (ball_mem_nhds x₀ (half_pos hδ))] with ⟨t, x⟩ ⟨⟨htx, ht⟩, hx⟩
  rw [dist_eq_norm]
  refine (norm_heatKernel_convolution_sub_le (r := δ / 2) ht hg hM x (g x₀) (half_pos hε).le
    fun z hz => ?_).trans_lt (by linarith)
  -- `x - z` is within `δ / 2 + δ / 2` of `x₀`.
  rw [mem_ball_zero_iff] at hz
  rw [← dist_eq_norm]
  refine (hgδ ?_).le
  calc dist (x - z) x₀ ≤ dist x x₀ + ‖z‖ := by
        rw [dist_eq_norm, dist_eq_norm, sub_right_comm]
        exact norm_sub_le _ _
    _ < δ := by linarith

/-- **Uniform convergence to the initial datum.** For a bounded uniformly continuous `g`,
`K_t ⋆ g → g` uniformly on `E` as `t → 0⁺`. -/
theorem tendstoUniformly_heatKernel_convolution [CompleteSpace F] (g : E →ᵇ F)
    (hg : UniformContinuous g) :
    TendstoUniformly (fun t => heatKernel t ⋆ ⇑g) g (𝓝[>] 0) := by
  refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.1 hg (ε / 2) (half_pos hε)
  have htail := (tendsto_setIntegral_compl_ball_heatKernel (E := E) hδ).const_mul (2 * ‖g‖)
  rw [mul_zero] at htail
  filter_upwards [htail.eventually (gt_mem_nhds (half_pos hε)), self_mem_nhdsWithin]
    with t htx (ht : 0 < t) x
  have htail₀ : 0 ≤ ∫ z in (ball (0 : E) δ)ᶜ, heatKernel t z :=
    setIntegral_nonneg measurableSet_ball.compl fun z _ => (heatKernel_pos ht z).le
  rw [dist_comm, dist_eq_norm]
  refine (norm_heatKernel_convolution_sub_le (r := δ) ht g.continuous.aestronglyMeasurable
    (ae_of_all _ g.norm_coe_le_norm) x (g x) (half_pos hε).le fun z hz => ?_).trans_lt ?_
  · rw [← dist_eq_norm]
    refine (hgδ ?_).le
    rwa [dist_eq_norm, sub_sub_cancel_left, norm_neg, ← mem_ball_zero_iff]
  · nlinarith [g.norm_coe_le_norm x]

end TauCeti
