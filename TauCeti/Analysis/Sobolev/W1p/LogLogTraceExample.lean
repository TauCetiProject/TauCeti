/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A `W^{1,2}` function on the disc with no continuous boundary value

On the unit disc `D ⊆ ℂ` let

`f(z) = log log (4 / ‖1 - z‖)`

(`TauCeti.logLogTraceExample`). On `D` the distance `r = ‖1 - z‖` lies in `(0, 2)`, so
`log (4 / r) > log 2 > 0` and `f` is smooth on `D` (`TauCeti.contDiffOn_logLogTraceExample`).
Its gradient has size at most `1 / (r log (4 / r))`, and in polar coordinates about `1`

`∫₀² r · (r log (4 / r))⁻² dr = ∫₀² dr / (r log² (4 / r)) = 1 / log 2 < ∞`,

since `1 / log (4 / r)` is an antiderivative vanishing at `r = 0`. The function itself grows only
like `log log (1 / r)`. Hence `f` and `∇f` lie in `L²(D)`
(`TauCeti.memLp_logLogTraceExample`, `TauCeti.memLp_gradient_logLogTraceExample`) and `f`
defines an element of `W^{1,2}(D)`. On the other hand `f(z) → ∞` as `z → 1` inside `D`
(`TauCeti.tendsto_logLogTraceExample`), so no function equal to `f` almost everywhere on `D` is
continuous at `1` relative to the closed disc
(`TauCeti.not_continuousWithinAt_of_ae_eq_logLogTraceExample`).

`TauCeti.W1p.exists_logLogTraceExample` packages the two halves: there is an element of
`W^{1,2}(D)` with value `f` and weak gradient `∇f`, none of whose representatives is continuous
at the boundary point `1`. So for `k = 1`, `p = 2` (where `kp ≤ 2`) a boundary condition on
`W^{1,2}(D)` cannot be imposed pointwise and has to be read through a trace.

## Implementation notes

The constant `4` matters. With `log log (2 / ‖1 - z‖)` the inner logarithm vanishes at the
boundary point `z = -1`, where `‖1 - z‖ = 2`; near `-1` the gradient is comparable to the inverse
of the distance to the tangent line of the circle, which is not square integrable over the disc.
Any constant larger than `2` keeps `log (C / ‖1 - z‖)` bounded below on `D`, and `4` is the
simplest choice.

All integrability statements are reduced to one-variable integrals by Mathlib's polar formula
`integrableOn_fun_norm_addHaar` after translating the singularity to the origin.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B
  (Sobolev spaces, the borderline case `kp = n` of the Sobolev embedding).
* L. C. Evans, *Partial Differential Equations*, §5.6.3 (the example `log log (1 / |x|)` of an
  unbounded `W^{1,n}` function).
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Gradient Topology

/-- The function `f(z) = log log (4 / ‖1 - z‖)`. On the unit disc it is smooth and lies in
`W^{1,2}`, but it tends to `∞` at the boundary point `1`. -/
@[expose] def logLogTraceExample (z : ℂ) : ℝ :=
  Real.log (Real.log (4 / ‖1 - z‖))

/-- The radial profile `r ↦ log log (4 / r)` of `TauCeti.logLogTraceExample` about `1`. -/
private def profile (r : ℝ) : ℝ :=
  Real.log (Real.log (4 / r))

private theorem logLogTraceExample_eq (z : ℂ) : logLogTraceExample z = profile ‖z - 1‖ := by
  rw [logLogTraceExample, norm_sub_rev]
  rfl

/-- On the unit disc the distance to `1` lies in `(0, 2)`. -/
private theorem norm_sub_one_mem {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 < ‖z - 1‖ ∧ ‖z - 1‖ < 2 := by
  rw [mem_ball_zero_iff] at hz
  refine ⟨norm_pos_iff.2 (sub_ne_zero.2 ?_), ?_⟩
  · rintro rfl
    simp at hz
  · calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ < 2 := by rw [norm_one]; linarith

/-- For `0 < r < 2` the inner logarithm exceeds `log 2`. -/
private theorem log_two_lt_log_four_div {r : ℝ} (h0 : 0 < r) (h2 : r < 2) :
    Real.log 2 < Real.log (4 / r) :=
  Real.log_lt_log two_pos (by rw [lt_div_iff₀ h0]; linarith)

/-- `r ↦ 4 / r` has derivative `-(4 / r²)` at `r ≠ 0`. -/
private theorem hasDerivAt_four_div {r : ℝ} (h0 : r ≠ 0) :
    HasDerivAt (fun y : ℝ => 4 / y) (-(4 / r ^ 2)) r := by
  have h := (hasDerivAt_inv h0).const_mul (4 : ℝ)
  simp only [div_eq_mul_inv]
  convert h using 1
  ring

private theorem log_four_div_pos {r : ℝ} (h0 : 0 < r) (h2 : r < 2) : 0 < Real.log (4 / r) :=
  (Real.log_pos one_lt_two).trans (log_two_lt_log_four_div h0 h2)

/-- The function `f(z) = log log (4 / ‖1 - z‖)` is smooth on the unit disc. -/
theorem contDiffOn_logLogTraceExample : ContDiffOn ℝ ∞ logLogTraceExample (ball 0 1) := by
  intro z hz
  obtain ⟨h0, h2⟩ := norm_sub_one_mem hz
  have hr : ‖1 - z‖ = ‖z - 1‖ := norm_sub_rev _ _
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖1 - w‖) z :=
    (contDiffAt_const.sub contDiffAt_id).norm ℝ
      (by rw [← norm_pos_iff]; exact hr ▸ h0)
  have hd : ContDiffAt ℝ ∞ (fun w : ℂ => 4 / ‖1 - w‖) z :=
    contDiffAt_const.div hn (by rw [hr]; exact h0.ne')
  have hl : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log (4 / ‖1 - w‖)) z :=
    hd.log (by rw [hr]; positivity)
  exact (hl.log (by rw [hr]; exact (log_four_div_pos h0 h2).ne')).contDiffWithinAt

/-- The derivative of the radial profile: `d/dr log log (4 / r) = -(r log (4 / r))⁻¹`. -/
private theorem hasDerivAt_profile {r : ℝ} (h0 : 0 < r) (h2 : r < 2) :
    HasDerivAt profile (-(r * Real.log (4 / r))⁻¹) r := by
  have hL := log_four_div_pos h0 h2
  have h := ((hasDerivAt_four_div h0.ne').log (by positivity)).log hL.ne'
  refine h.congr_deriv ?_
  field_simp

/-- The classical gradient of `f` has size at most `(r log (4 / r))⁻¹`, `r = ‖z - 1‖`. -/
private theorem norm_gradient_logLogTraceExample_le {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖∇ logLogTraceExample z‖ ≤ (‖z - 1‖ * Real.log (4 / ‖z - 1‖))⁻¹ := by
  obtain ⟨h0, h2⟩ := norm_sub_one_mem hz
  have hg : HasFDerivAt (fun w : ℂ => ‖w - 1‖) (fderiv ℝ (fun w : ℂ => ‖w - 1‖) z) z :=
    ((differentiableAt_id.sub_const 1).norm ℝ (norm_pos_iff.1 h0)).hasFDerivAt
  have hcomp := (hasDerivAt_profile h0 h2).comp_hasFDerivAt z hg
  have hf : logLogTraceExample = profile ∘ fun w : ℂ => ‖w - 1‖ :=
    funext logLogTraceExample_eq
  have hlip : LipschitzWith 1 (fun w : ℂ => ‖w - 1‖) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa [Real.dist_eq, dist_eq_norm] using abs_norm_sub_norm_le (x - 1) (y - 1)
  have hD : ‖fderiv ℝ (fun w : ℂ => ‖w - 1‖) z‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ hlip
  have hpos : 0 < ‖z - 1‖ * Real.log (4 / ‖z - 1‖) := mul_pos h0 (log_four_div_pos h0 h2)
  rw [norm_gradient_eq_norm_fderiv, hf, hcomp.fderiv, norm_smul, norm_neg,
    Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
  calc (‖z - 1‖ * Real.log (4 / ‖z - 1‖))⁻¹ * ‖fderiv ℝ (fun w : ℂ => ‖w - 1‖) z‖
      ≤ (‖z - 1‖ * Real.log (4 / ‖z - 1‖))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

/-- The radial integrand of `f²` is bounded on `(0, 2)`: `r (log log (4 / r))² ≤ 36`. -/
private theorem integrableOn_mul_profile_sq :
    IntegrableOn (fun r : ℝ => r * profile r ^ 2) (Ioo 0 2) := by
  refine Measure.integrableOn_of_bounded (M := 36) (by simp) ?_ ?_
  · exact Measurable.aestronglyMeasurable (by unfold profile; fun_prop)
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun r ⟨h0, h2⟩ => ?_
    set L := Real.log (4 / r) with hLdef
    have hL : Real.log 2 < L := log_two_lt_log_four_div h0 h2
    have hL2 : 1 / 2 < L := by
      have := Real.one_sub_inv_le_log_of_pos (two_pos : (0 : ℝ) < 2)
      norm_num at this
      linarith
    have hLpos : 0 < L := by linarith
    -- `|log L| ≤ L + 1` because `L > 1 / 2`.
    have hup : Real.log L ≤ L + 1 := by linarith [Real.log_le_sub_one_of_pos hLpos]
    have hlow : -(L + 1) ≤ Real.log L := by
      have := Real.one_sub_inv_le_log_of_pos hLpos
      have : L⁻¹ < 2 := by
        rw [inv_lt_comm₀ hLpos two_pos]
        linarith
      linarith
    -- `L < 2 √(4 / r)`, so `r L² < 16`.
    have hsq : L < 2 * √(4 / r) := by
      have h4r : 0 ≤ 4 / r := by positivity
      have hs : 0 < √(4 / r) := Real.sqrt_pos.2 (by positivity)
      have : Real.log √(4 / r) < √(4 / r) := by
        linarith [Real.log_le_sub_one_of_pos hs]
      rw [Real.log_sqrt h4r] at this
      linarith
    have hrL : r * L ^ 2 ≤ 16 := by
      have h1 : L ^ 2 ≤ (2 * √(4 / r)) ^ 2 := pow_le_pow_left₀ hLpos.le hsq.le 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at h1
      calc r * L ^ 2 ≤ r * (2 ^ 2 * (4 / r)) := by gcongr
        _ = 16 := by field_simp; norm_num
    have hprof : profile r ^ 2 ≤ (L + 1) ^ 2 := by
      rw [profile, ← hLdef]
      exact sq_le_sq' hlow hup
    rw [Real.norm_of_nonneg (by positivity)]
    calc r * profile r ^ 2 ≤ r * (L + 1) ^ 2 := by gcongr
      _ ≤ 2 * (r * L ^ 2) + 2 * r := by nlinarith [sq_nonneg (L - 1)]
      _ ≤ 36 := by linarith

/-- The radial integrand of `‖∇f‖²` is integrable on `(0, 2)`: it is the derivative of
`r ↦ (log (4 / r))⁻¹`, which is continuous on `[0, 2]` and vanishes at `0`. -/
private theorem integrableOn_mul_inv_mul_log_sq :
    IntegrableOn (fun r : ℝ => r * ((r * Real.log (4 / r))⁻¹) ^ 2) (Ioo 0 2) := by
  set G : ℝ → ℝ := fun r => (Real.log (4 / r))⁻¹
  have hcont : ContinuousOn G (Icc 0 2) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | h0
    · refine (continuousWithinAt_Ioi_iff_Ici.1 ?_).mono Icc_subset_Ici_self
      have h4 : Tendsto (fun y : ℝ => 4 / y) (𝓝[>] 0) atTop := by
        simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop four_pos
      have hG0 : G 0 = 0 := by simp [G]
      rw [ContinuousWithinAt, hG0]
      exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp h4)
    · have hL : 0 < Real.log (4 / r) := Real.log_pos (by rw [lt_div_iff₀ h0]; linarith [hr.2])
      exact (((continuousAt_const (y := (4 : ℝ))).div continuousAt_id h0.ne').log
        (by change (4 : ℝ) / r ≠ 0; positivity)).inv₀ hL.ne' |>.continuousWithinAt
  have hderiv : ∀ r ∈ Ioo (0 : ℝ) 2,
      HasDerivAt G (r * ((r * Real.log (4 / r))⁻¹) ^ 2) r := by
    rintro r ⟨h0, h2⟩
    have hL := log_four_div_pos h0 h2
    have h := ((hasDerivAt_four_div h0.ne').log (by positivity)).inv hL.ne'
    convert h using 1
    field_simp
  have hnonneg : ∀ r ∈ Ioo (0 : ℝ) 2, 0 ≤ r * ((r * Real.log (4 / r))⁻¹) ^ 2 :=
    fun r hr => mul_nonneg hr.1.le (sq_nonneg _)
  exact (intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hnonneg).mono_set
    Ioo_subset_Ioc_self

/-- A radial function about `1` is integrable on the unit disc as soon as its one-variable polar
integrand is integrable on `(0, 2)`. -/
private theorem integrableOn_ball_of_integrableOn_mul {h : ℝ → ℝ}
    (hh : IntegrableOn (fun r : ℝ => r * h r) (Ioo 0 2)) :
    IntegrableOn (fun z : ℂ => h ‖z - 1‖) (ball 0 1) := by
  have h1 : IntegrableOn (fun w : ℂ => h ‖w‖) (ball 0 2) :=
    (integrableOn_fun_norm_addHaar volume).2 (by simpa [Complex.finrank_real_complex] using hh)
  have h2 : IntegrableOn (fun z : ℂ => h ‖z - 1‖) (ball 1 2) := by
    rw [← integrable_indicator_iff measurableSet_ball] at h1 ⊢
    refine (h1.comp_sub_right 1).congr (ae_of_all _ fun z => ?_)
    simp only [indicator, mem_ball, dist_eq_norm, sub_zero]
  exact h2.mono_set (ball_subset_ball' (by norm_num))

/-- The function `f(z) = log log (4 / ‖1 - z‖)` is square integrable on the unit disc. -/
theorem memLp_logLogTraceExample :
    MemLp logLogTraceExample 2 (volume.restrict (ball (0 : ℂ) 1)) := by
  refine (memLp_two_iff_integrable_sq
    (contDiffOn_logLogTraceExample.continuousOn.aestronglyMeasurable measurableSet_ball)).2 ?_
  have e : (fun z => logLogTraceExample z ^ 2) = fun z => profile ‖z - 1‖ ^ 2 :=
    funext fun z => by rw [logLogTraceExample_eq]
  rw [e]
  exact integrableOn_ball_of_integrableOn_mul (h := fun r => profile r ^ 2)
    integrableOn_mul_profile_sq

/-- The classical gradient of `f(z) = log log (4 / ‖1 - z‖)` is square integrable on the unit
disc. -/
theorem memLp_gradient_logLogTraceExample :
    MemLp (∇ logLogTraceExample) 2 (volume.restrict (ball (0 : ℂ) 1)) := by
  have hc : ContinuousOn (∇ logLogTraceExample) (ball 0 1) :=
    (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp_continuousOn
      (contDiffOn_logLogTraceExample.continuousOn_fderiv_of_isOpen isOpen_ball (by simp))
  have hm := hc.aestronglyMeasurable (μ := volume) measurableSet_ball
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine Integrable.mono' (integrableOn_ball_of_integrableOn_mul
    (h := fun r => ((r * Real.log (4 / r))⁻¹) ^ 2) integrableOn_mul_inv_mul_log_sq)
    (hm.norm.pow 2) (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_logLogTraceExample_le hz) 2

/-- The function `f(z) = log log (4 / ‖1 - z‖)` tends to `∞` at the boundary point `1` of the
unit disc. -/
theorem tendsto_logLogTraceExample :
    Tendsto logLogTraceExample (𝓝[ball 0 1] 1) atTop := by
  have hr : Tendsto (fun z : ℂ => ‖z - 1‖) (𝓝[ball 0 1] 1) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_id.sub continuous_const).norm.tendsto' 1 0
      (by simp)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz => (norm_sub_one_mem hz).1⟩
  have h4 : Tendsto (fun y : ℝ => 4 / y) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop four_pos
  refine (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (h4.comp hr))).congr
    fun z => ?_
  rw [logLogTraceExample_eq]
  rfl

/-- No function equal almost everywhere on the unit disc to `f(z) = log log (4 / ‖1 - z‖)` is
continuous at `1` relative to the closed disc. -/
theorem not_continuousWithinAt_of_ae_eq_logLogTraceExample {g : ℂ → ℝ}
    (hg : g =ᵐ[volume.restrict (ball (0 : ℂ) 1)] logLogTraceExample) :
    ¬ ContinuousWithinAt g (closedBall 0 1) 1 := by
  intro hc
  have hb : ∀ᶠ z in 𝓝[ball 0 1] 1, g z < g 1 + 1 :=
    nhdsWithin_mono _ ball_subset_closedBall (hc.eventually (gt_mem_nhds (lt_add_one _)))
  have hf : ∀ᶠ z in 𝓝[ball 0 1] 1, g 1 + 1 < logLogTraceExample z :=
    tendsto_logLogTraceExample.eventually_gt_atTop _
  obtain ⟨u, huo, hu1, hus⟩ := mem_nhdsWithin.1 (hb.and hf)
  have hS : (u ∩ ball 0 1).Nonempty := by
    have : (𝓝[ball (0 : ℂ) 1] 1).NeBot := mem_closure_iff_nhdsWithin_neBot.1
      (by rw [closure_ball (0 : ℂ) one_ne_zero]; simp)
    exact Filter.nonempty_of_mem (mem_nhdsWithin.2 ⟨u, huo, hu1, subset_rfl⟩)
  have hpos : 0 < volume (u ∩ ball (0 : ℂ) 1) := (huo.inter isOpen_ball).measure_pos _ hS
  have hfalse : ∀ᵐ z ∂volume.restrict (u ∩ ball (0 : ℂ) 1), False := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right hg,
      ae_restrict_mem (huo.inter isOpen_ball).measurableSet] with z hz hzS
    have := hus hzS
    exact absurd (this.1.trans this.2) (by rw [hz]; exact lt_irrefl _)
  have h0 : volume.restrict (u ∩ ball (0 : ℂ) 1) = 0 :=
    ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse)
  exact hpos.ne' (Measure.restrict_eq_zero.1 h0)

/-- **`W^{1,2}` functions on the disc need not have continuous boundary values.** The function
`f(z) = log log (4 / ‖1 - z‖)` defines an element of `W^{1,2}` of the unit disc, with weak
gradient its classical gradient, and no representative of it is continuous at the boundary
point `1` relative to the closed disc. -/
theorem W1p.exists_logLogTraceExample :
    ∃ U : W1p volume ⟨ball (0 : ℂ) 1, isOpen_ball⟩ 2,
      W1p.value U =ᵐ[volume.restrict (ball (0 : ℂ) 1)] logLogTraceExample ∧
      W1p.gradient U =ᵐ[volume.restrict (ball (0 : ℂ) 1)] ∇ logLogTraceExample ∧
      ∀ g : ℂ → ℝ, g =ᵐ[volume.restrict (ball (0 : ℂ) 1)] W1p.value U →
        ¬ ContinuousWithinAt g (closedBall 0 1) 1 := by
  obtain ⟨U, hv, hg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn
    (mu := volume) (Omega := ⟨ball (0 : ℂ) 1, isOpen_ball⟩) (p := 2)
    (contDiffOn_logLogTraceExample.of_le (by simp)) memLp_logLogTraceExample
    memLp_gradient_logLogTraceExample
  exact ⟨U, hv, hg, fun g hgU => not_continuousWithinAt_of_ae_eq_logLogTraceExample
    (hgU.trans hv)⟩

end TauCeti
