/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The perimeter of a ball

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E` of
dimension `n`, and write `ω = μ (ball 0 1)`. A ball of radius `r > 0` has perimeter

`P(ball c r) = n ω r^(n-1) = (n / r) μ (ball c r)`

in the whole space (`TauCeti.perimeter_ball`, `TauCeti.perimeter_ball_eq_ofReal_div_mul`). For
`μ` the volume of `EuclideanSpace ℝ (Fin n)` this is the classical surface area `n ω_n r^(n-1)`
of the sphere of radius `r`, where `ω_n` is the volume of the unit ball. The perimeter only sees a
set up to null sets, so the closed ball has the same perimeter (`TauCeti.perimeter_closedBall`).
In dimension `n ≥ 1` balls satisfy `P(ball c r)^n = n^n ω μ (ball c r)^(n-1)`
(`TauCeti.perimeter_ball_pow`): they attain equality in the isoperimetric inequality
`P(E)^n ≥ n^n ω μ E^(n-1)`, whose constant is fixed by this identity.

The perimeter is computed from its definition by duality. The test vector field
`x ↦ θ x • (x - c) / (r + δ)`, for a smooth bump `θ` equal to one on the ball and supported in
the ball of radius `r + δ`, has norm at most one and constant divergence `n / (r + δ)` on the
ball, which gives the lower bound as `δ → 0`. For the upper bound, the Lipschitz radial cutoffs
equal to one on the ball, vanishing outside the ball of radius `r + ε` and of slope `ε⁻¹` in
between converge to the indicator of the ball in `L¹`. Their total variation is at most
`ε⁻¹ ((r + ε)^n - r^n) ω`, the slope times the measure of the shell on which they are not
locally constant, so lower semicontinuity of the total variation bounds the perimeter by the
derivative `n r^(n-1) ω` of `r ↦ r^n ω`.

## Main results

* `TauCeti.perimeter_ball`: `P(ball c r) = n r^(n-1) μ (ball 0 1)` for `r > 0`.
* `TauCeti.perimeter_ball_eq_ofReal_div_mul`: `P(ball c r) = (n / r) μ (ball c r)`.
* `TauCeti.perimeter_closedBall`: the same formula for closed balls.
* `TauCeti.perimeter_ball_pow`: `P(ball c r)^n = n^n μ (ball 0 1) μ (ball c r)^(n-1)`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 12.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set Filter TopologicalSpace TestFunction
open scoped ENNReal NNReal Distributions Topology

variable {E : Type*} [NormedAddCommGroup E] {c : E} {r : ℝ}

/-- The Lipschitz radial cutoff equal to one on the ball of radius `r`, vanishing outside the ball
of radius `r + ε`, and affine in the distance to the centre in between. -/
private def radialCutoff (c : E) (r ε : ℝ) (x : E) : ℝ :=
  max 0 (min ((r + ε - dist x c) / ε) 1)

private theorem lipschitzWith_radialCutoff {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal ε⁻¹) (radialCutoff c r ε) := by
  refine ((LipschitzWith.of_dist_le_mul fun x y => ?_).min_const 1).const_max 0
  rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hε.le), ← sub_div,
    sub_sub_sub_cancel_left, abs_div, abs_of_pos hε, div_eq_inv_mul]
  gcongr
  rw [abs_sub_comm]
  exact abs_dist_sub_le x y c

private theorem radialCutoff_of_mem_ball {ε : ℝ} (hε : 0 < ε) {x : E} (hx : x ∈ ball c r) :
    radialCutoff c r ε x = 1 := by
  have : 1 ≤ (r + ε - dist x c) / ε := by
    rw [le_div_iff₀ hε]
    linarith [mem_ball.1 hx]
  simp [radialCutoff, min_eq_right this]

private theorem radialCutoff_of_notMem_closedBall {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∉ closedBall c (r + ε)) : radialCutoff c r ε x = 0 := by
  have : (r + ε - dist x c) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.1 (mt mem_closedBall.2 hx)]) hε.le
  simp [radialCutoff, min_le_of_left_le this]

/-- The radial cutoff differs from the indicator of the ball only on the annulus it ramps across,
and by at most one there. -/
private theorem enorm_radialCutoff_sub_indicator_le {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖radialCutoff c r ε x - (ball c r).indicator 1 x‖ₑ ≤
      (closedBall c (r + ε) \ ball c r).indicator 1 x := by
  by_cases hx : x ∈ ball c r
  · simp [radialCutoff_of_mem_ball hε hx, hx]
  by_cases hx' : x ∈ closedBall c (r + ε)
  · rw [indicator_of_mem (mem_sdiff_of_mem hx' hx), indicator_of_notMem hx, sub_zero,
      Pi.one_apply, ← ofReal_norm, radialCutoff, Real.norm_of_nonneg (le_max_left _ _)]
    exact ENNReal.ofReal_le_one.2 (max_le zero_le_one (min_le_right _ _))
  · simp [radialCutoff_of_notMem_closedBall hε hx', hx]

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

/-- **Lower bound for the perimeter of a ball.** The test vector field
`x ↦ θ x • (x - c) / (r + δ)`, where the bump `θ` is one on the ball of radius `r` and supported
in the ball of radius `r + δ`, is admissible and has divergence `n / (r + δ)` on the ball. -/
private theorem ofReal_le_perimeter_ball (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r)) ≤ perimeter μ ⊤ (ball c r) := by
  let θ : ContDiffBump c := ⟨r, r + δ, hr, by linarith⟩
  have hrδ : 0 < r + δ := by linarith
  let φ : 𝓓(⊤, E) :=
    ⟨fun x => ((r + δ)⁻¹ * θ x) • (x - c),
      (contDiff_const.mul θ.contDiff).smul (contDiff_id.sub contDiff_const),
      θ.hasCompactSupport.mul_left.smul_right, by simp⟩
  have hφ (x : E) : ‖φ x‖ ≤ 1 := by
    simp only [φ, coe_mk]
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hrδ.le) θ.nonneg)]
    by_cases hx : θ x = 0
    · simp [hx]
    have hxc : ‖x - c‖ < r + δ := by
      rw [← dist_eq_norm, ← mem_ball]
      exact θ.support_eq ▸ hx
    calc (r + δ)⁻¹ * θ x * ‖x - c‖ ≤ (r + δ)⁻¹ * 1 * (r + δ) := by
          gcongr
          · exact θ.le_one
    _ = 1 := by field_simp
  -- On the ball the bump is locally one, so the field is locally `x ↦ (x - c) / (r + δ)`.
  have hdiv : ∀ x ∈ ball c r, divergenceCLM φ x = finrank ℝ E / (r + δ) := by
    intro x hx
    have hloc : (φ : E → E) =ᶠ[𝓝 x] fun y => (r + δ)⁻¹ • (y - c) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp only [φ, coe_mk]
      rw [θ.one_of_mem_closedBall (ball_subset_closedBall hy), mul_one]
    have hd : HasFDerivAt (fun y => (r + δ)⁻¹ • (y - c))
        ((r + δ)⁻¹ • ContinuousLinearMap.id ℝ E) x :=
      ((hasFDerivAt_id x).sub_const c).const_smul _
    rw [divergenceCLM_apply, hloc.fderiv_eq, hd.fderiv]
    simp [div_eq_inv_mul]
  calc ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r))
      = ENNReal.ofReal (∫ x in ball c r, divergenceCLM φ x ∂μ) := by
        rw [setIntegral_congr_fun measurableSet_ball hdiv, setIntegral_const, smul_eq_mul,
          mul_comm]
    _ ≤ perimeter μ ⊤ (ball c r) := by
        rw [perimeter_eq_iSup measurableSet_ball.nullMeasurableSet]
        exact le_iSup₂_of_le (f := fun (φ : 𝓓(⊤, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
          ENNReal.ofReal (∫ x in ball c r, divergenceCLM φ x ∂μ)) φ hφ le_rfl

variable [μ.IsAddHaarMeasure]

/-- The total variation of the radial cutoff is at most its slope `ε⁻¹` times the volume of the
annulus it ramps across: its derivative vanishes off that annulus. -/
private theorem totalVariationOn_radialCutoff_le {ε : ℝ} (hε : 0 < ε) :
    totalVariationOn μ ⊤ (radialCutoff c r ε) ≤
      ENNReal.ofReal ε⁻¹ * μ (closedBall c (r + ε) \ ball c r) := by
  have hlip := lipschitzWith_radialCutoff (c := c) (r := r) hε
  rw [hlip.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
    Opens.coe_top, Measure.restrict_univ,
    ← lintegral_indicator_const (measurableSet_closedBall.diff measurableSet_ball)]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ closedBall c (r + ε) \ ball c r
  · rw [indicator_of_mem hx, ← ofReal_norm, ← Real.coe_toNNReal _ (inv_nonneg.2 hε.le)]
    exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ hlip)
  -- Off the annulus the cutoff is locally constant.
  have hloc : radialCutoff c r ε =ᶠ[𝓝 x] fun _ => radialCutoff c r ε x := by
    by_cases hb : x ∈ ball c r
    · filter_upwards [isOpen_ball.mem_nhds hb] with y hy
      rw [radialCutoff_of_mem_ball hε hy, radialCutoff_of_mem_ball hε hb]
    · have hc : x ∈ (closedBall c (r + ε))ᶜ := fun h => hx ⟨h, hb⟩
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hc] with y hy
      rw [radialCutoff_of_notMem_closedBall hε hy, radialCutoff_of_notMem_closedBall hε hc]
  rw [hloc.fderiv_eq, fderiv_const_apply, indicator_of_notMem hx]
  simp [enorm_eq_nnnorm]

/-- **Upper bound for the perimeter of a ball**, by lower semicontinuity of the total variation
along the radial cutoffs as `ε → 0`. -/
private theorem perimeter_ball_le (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) ≤ ENNReal.ofReal
      (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hann : ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ (closedBall c (r + ε) \ ball c r) =
      ENNReal.ofReal (((r + ε) ^ n - r ^ n) * ω) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← ofReal_measureReal (measure_ne_top_of_subset sdiff_subset measure_closedBall_lt_top.ne),
      μ.addHaar_real_closedBall_sdiff_ball c hr (by linarith [mem_Ioi.1 hε])]
  -- The annuli shrink to a null set.
  have hann0 : Tendsto (fun ε => μ (closedBall c (r + ε) \ ball c r)) (𝓝[>] 0) (𝓝 0) := by
    refine (tendsto_congr' hann).2 ?_
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    simpa using (by fun_prop : Continuous fun ε : ℝ => ((r + ε) ^ n - r ^ n) * ω).tendsto 0
  -- The total variations are bounded by difference quotients of `ε ↦ (r + ε)^n ω`.
  have hslope : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε⁻¹ * (((r + ε) ^ n - r ^ n) * ω)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (n * r ^ (n - 1) * ω))) := by
    refine ENNReal.tendsto_ofReal ?_
    simp_rw [← mul_assoc]
    exact ((hasDerivAt_pow n r).tendsto_slope_zero_right.mul_const ω).congr fun ε => by
      rw [smul_eq_mul]
  have hu : ∀ᶠ ε in 𝓝[>] (0 : ℝ), LocallyIntegrableOn (radialCutoff c r ε) (⊤ : Opens E) μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (lipschitzWith_radialCutoff hε).continuous.locallyIntegrable.locallyIntegrableOn _
  have hu₀ : LocallyIntegrableOn ((ball c r).indicator (1 : E → ℝ)) (⊤ : Opens E) μ :=
    ((locallyIntegrable_const 1).indicator measurableSet_ball).locallyIntegrableOn _
  -- The cutoffs converge to the indicator of the ball in `L¹`.
  have hL1 (K : Set E) (_ : IsCompact K) (_ : K ⊆ (⊤ : Opens E)) : Tendsto
      (fun ε => ∫⁻ x in K, ‖radialCutoff c r ε x - (ball c r).indicator 1 x‖ₑ ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hann0
      (.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    calc ∫⁻ x in K, ‖radialCutoff c r ε x - (ball c r).indicator 1 x‖ₑ ∂μ
        ≤ ∫⁻ x, ‖radialCutoff c r ε x - (ball c r).indicator 1 x‖ₑ ∂μ :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ x, (closedBall c (r + ε) \ ball c r).indicator 1 x ∂μ :=
          lintegral_mono (enorm_radialCutoff_sub_indicator_le hε)
      _ = μ (closedBall c (r + ε) \ ball c r) :=
          lintegral_indicator_one (measurableSet_closedBall.diff measurableSet_ball)
  calc perimeter μ ⊤ (ball c r)
      ≤ liminf (fun ε => totalVariationOn μ ⊤ (radialCutoff c r ε)) (𝓝[>] 0) := by
        rw [perimeter_def]
        exact totalVariationOn_le_liminf hu hu₀ hL1
    _ ≤ liminf (fun ε : ℝ => ENNReal.ofReal (ε⁻¹ * (((r + ε) ^ n - r ^ n) * ω))) (𝓝[>] 0) := by
        refine liminf_le_liminf ?_
        filter_upwards [self_mem_nhdsWithin, hann] with ε hε hεa
        rw [ENNReal.ofReal_mul (inv_nonneg.2 (le_of_lt hε)), ← hεa]
        exact totalVariationOn_radialCutoff_le hε
    _ = ENNReal.ofReal (n * r ^ (n - 1) * ω) := hslope.liminf_eq

/-- The two normal forms of the perimeter of a ball agree: `n r^(n-1) ω = (n / r) μ (ball c r)`. -/
private theorem finrank_mul_pow_mul_eq (hr : 0 < r) :
    finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1) =
      finrank ℝ E / r * μ.real (ball c r) := by
  rw [μ.addHaar_real_ball_of_pos c hr]
  cases finrank ℝ E with
  | zero => simp
  | succ k =>
    simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    field_simp
    ring

private theorem perimeter_ball_eq_ofReal (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) =
      ENNReal.ofReal (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  refine le_antisymm (perimeter_ball_le hr) (le_of_tendsto (x := 𝓝[>] (0 : ℝ))
    (f := fun δ => ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r))) ?_ ?_)
  · rw [finrank_mul_pow_mul_eq (c := c) hr]
    refine ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have : ContinuousAt (fun δ : ℝ => (finrank ℝ E : ℝ) / (r + δ) * μ.real (ball c r)) 0 := by
      fun_prop (disch := simpa using hr.ne')
    simpa using this.tendsto
  · filter_upwards [self_mem_nhdsWithin] with δ hδ using ofReal_le_perimeter_ball hr hδ

/-- **The perimeter of a ball.** Against an additive Haar measure `μ` on a space of dimension `n`,
a ball of radius `r > 0` has perimeter `n r^(n-1) μ (ball 0 1)` in the whole space. For the volume
of `EuclideanSpace ℝ (Fin n)` this is the surface area `n ω_n r^(n-1)` of the sphere of
radius `r`. -/
theorem perimeter_ball (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) =
      finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_ball_eq_ofReal hr, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ofReal_measureReal measure_ball_lt_top.ne]

/-- **The perimeter of a ball, normalized by its volume.** A ball of radius `r > 0` has perimeter
`(n / r) μ (ball c r)`, where `n` is the dimension. -/
theorem perimeter_ball_eq_ofReal_div_mul (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) = ENNReal.ofReal (finrank ℝ E / r) * μ (ball c r) := by
  rw [perimeter_ball_eq_ofReal hr, finrank_mul_pow_mul_eq hr, ENNReal.ofReal_mul (by positivity),
    ofReal_measureReal measure_ball_lt_top.ne]

/-- **The perimeter of a closed ball.** A closed ball of radius `r > 0` has the same perimeter
`n r^(n-1) μ (ball 0 1)` as the open ball, since they differ by a null set. -/
theorem perimeter_closedBall (hr : 0 < r) :
    perimeter μ ⊤ (closedBall c r) =
      finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_congr_ae (ae_restrict_of_ae (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero c r
    hr.ne')), perimeter_ball hr]

/-- **Balls are isoperimetric equality cases.** In dimension `n ≥ 1`, a ball of radius `r > 0`
satisfies `P(ball c r)^n = n^n μ (ball 0 1) μ (ball c r)^(n-1)`, equality in the isoperimetric
inequality `P(E)^n ≥ n^n μ (ball 0 1) μ E^(n-1)`. -/
theorem perimeter_ball_pow (hn : finrank ℝ E ≠ 0) (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) ^ finrank ℝ E =
      finrank ℝ E ^ finrank ℝ E * μ (ball 0 1) * μ (ball c r) ^ (finrank ℝ E - 1) := by
  rw [perimeter_ball hr, μ.addHaar_ball_of_pos c hr]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h : ENNReal.ofReal (r ^ k) ^ (k + 1) = ENNReal.ofReal (r ^ (k + 1)) ^ k := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity), ← pow_mul,
      ← pow_mul, mul_comm]
  rw [hk, Nat.succ_sub_one, Nat.succ_eq_add_one, mul_pow, mul_pow, h]
  ring

end TauCeti
