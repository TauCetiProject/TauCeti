/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Integrability.Log.LogLog
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable

/-!
# An unbounded function in the local class `W^{1,2}` of the plane

On the disc `D = ball 0 (1 / 2) ⊆ ℂ` let

`u(z) = log log (4 / ‖z‖)`

(`TauCeti.logLogInterior`). With `r = ‖z‖ ∈ (0, 1 / 2)` the inner logarithm exceeds `log 8 > 1`, so
`u` is smooth and positive on the punctured disc. On the larger punctured disc `ball 0 2` its
gradient has size at most `1 / (r log (4 / r))`, and in polar coordinates both `u²` and `‖∇u‖²`
have integrable radial profiles, so `u` and its classical derivative are square integrable on
`ball 0 2` (`TauCeti.memLp_logLogInterior`, `TauCeti.memLp_fderiv_logLogInterior`).

The classical derivative is also the weak derivative across the singularity at the origin
(`TauCeti.hasWeakFDerivOn_logLogInterior`). The proof regularises `u` to
`u_ε(z) = log log (4 / (‖z‖ + ε))`, which is continuous on `D` and smooth off the origin, so
`TauCeti.hasWeakFDerivOn_of_hasFDerivAt_off_countable` gives its weak derivative. As `ε → 0⁺`,
`0 < u_ε ≤ u` and `‖∇u_ε‖ ≤ 1 / (r log (4 / r))`, because `t ↦ t log (4 / t)` is increasing on
`(0, 1)`. Dominated convergence gives `u_ε → u` and `∇u_ε → ∇u` in `L¹(D)`, and
`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub` passes the weak derivative to the limit.
Hence `u` lies in the local class `W^{1,p}` of `D` for every `p ≤ 2`
(`TauCeti.memWkpLoc_logLogInterior`).

On the other hand `u(z) → ∞` as `z → 0` (`TauCeti.tendsto_logLogInterior`), so no function equal
to `u` almost everywhere on `D` is continuous at the origin
(`TauCeti.not_continuousAt_of_ae_eq_logLogInterior`). For `k = 1` and `p ≤ 2`, where `kp ≤ 2`,
membership in the local class `W^{1,p}` therefore does not give a continuous representative
(`TauCeti.exists_memWkpLoc_one_not_continuousOn_of_ae_eq`). For `p > 2` it does, by Morrey's
inequality `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`. So continuity of `W^{1,p}_loc`
functions, needed to define Sobolev maps into a manifold through charts, requires `kp > 2`.

## Implementation notes

The constant `4` keeps the inner logarithm above `1` on `D`, so both logarithms are positive and
the regularised functions satisfy `0 < u_ε ≤ u`. The radial calculus is shared with
`TauCeti.logLogTraceExample`, the same profile placed at a boundary point of the unit disc:
`TauCeti.hasDerivAt_log_log_four_div`, `TauCeti.integrableOn_mul_log_log_four_div_sq` and
`TauCeti.integrableOn_mul_inv_mul_log_four_div_sq`. The bounds `0 < u_ε ≤ u` and the gradient
domination come from `TauCeti.log_log_four_div_pos`, `TauCeti.antitoneOn_log_log_four_div` and
`TauCeti.monotoneOn_mul_log_four_div`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B
  (Sobolev spaces, the borderline case `kp = n` of the Sobolev embedding).
* L. C. Evans, *Partial Differential Equations*, §5.6.3 (the example `log log (1 / |x|)` of an
  unbounded `W^{1,n}` function).
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Topology

namespace TauCeti

/-- The function `u(z) = log log (4 / ‖z‖)`. On the disc `ball 0 (1 / 2)` it lies in the local
class `W^{1,2}`, but it tends to `∞` at the origin. -/
def logLogInterior (z : ℂ) : ℝ :=
  Real.log (Real.log (4 / ‖z‖))

/-- The defining formula of `TauCeti.logLogInterior`. -/
theorem logLogInterior_def (z : ℂ) :
    logLogInterior z = Real.log (Real.log (4 / ‖z‖)) := (rfl)

namespace LogLogInterior

/-- The derivative `s ↦ -(s log (4 / s))⁻¹` of the radial profile `s ↦ log log (4 / s)`. -/
private def profileDeriv (s : ℝ) : ℝ :=
  -(s * Real.log (4 / s))⁻¹

/-- Points below `1` lie below `4 / e`. -/
private theorem lt_four_div_exp_one {s : ℝ} (h1 : s < 1) : s < 4 / Real.exp 1 := by
  rw [lt_div_iff₀ (Real.exp_pos 1)]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

/-- On `(0, 2)` the profile derivative has size `(s log (4 / s))⁻¹`. -/
private theorem abs_profileDeriv {s : ℝ} (h0 : 0 < s) (h2 : s < 2) :
    |profileDeriv s| = (s * Real.log (4 / s))⁻¹ := by
  have := log_four_div_pos h0 h2
  rw [profileDeriv, abs_neg, abs_inv, abs_of_pos (by positivity)]

/-- The size of the profile derivative is antitone on `(0, 1)`. -/
private theorem abs_profileDeriv_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    |profileDeriv b| ≤ |profileDeriv a| := by
  have hb0 : 0 < b := ha.trans_le hab
  have hmono : a * Real.log (4 / a) ≤ b * Real.log (4 / b) :=
    monotoneOn_mul_log_four_div ⟨ha, (lt_four_div_exp_one (hab.trans_lt hb)).le⟩
      ⟨hb0, (lt_four_div_exp_one hb).le⟩ hab
  have hLa := log_four_div_pos ha (by linarith)
  rw [abs_profileDeriv hb0 (by linarith), abs_profileDeriv ha (by linarith)]
  exact inv_anti₀ (by positivity) hmono

/-- The regularisation `u_ε(z) = log log (4 / (‖z‖ + ε))`. -/
private def reg (ε : ℝ) (z : ℂ) : ℝ :=
  Real.log (Real.log (4 / (‖z‖ + ε)))

/-- The classical derivative of `u_ε` off the origin. -/
private def regDeriv (ε : ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  profileDeriv (‖z‖ + ε) • fderiv ℝ (fun w : ℂ => ‖w‖) z

/-- The size `(r log (4 / r))⁻¹`, `r = ‖z‖`, of the gradient of `u`. -/
private def gradBound (z : ℂ) : ℝ :=
  (‖z‖ * Real.log (4 / ‖z‖))⁻¹

private theorem reg_zero : reg 0 = logLogInterior := by
  funext z
  rw [reg, add_zero, logLogInterior_def]

private theorem measurable_reg (ε : ℝ) : Measurable (reg ε) := by
  unfold reg
  fun_prop

private theorem measurable_regDeriv (ε : ℝ) : Measurable (regDeriv ε) := by
  unfold regDeriv profileDeriv
  exact (by fun_prop : Measurable fun z : ℂ => -((‖z‖ + ε) * Real.log (4 / (‖z‖ + ε)))⁻¹).smul
    (measurable_fderiv ℝ _)

private theorem measurable_logLogInterior : Measurable logLogInterior := by
  rw [← reg_zero]
  exact measurable_reg 0

private theorem norm_mem {z : ℂ} {ε : ℝ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 2) : ‖z‖ ≤ ‖z‖ + ε ∧ ‖z‖ + ε < 1 := by
  rw [mem_ball_zero_iff] at hz
  constructor <;> linarith

private theorem norm_fderiv_norm_le (z : ℂ) : ‖fderiv ℝ (fun w : ℂ => ‖w‖) z‖ ≤ 1 := by
  simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := ℂ))

private theorem hasFDerivAt_reg {z : ℂ} {ε : ℝ} (hz0 : z ≠ 0) (hε0 : 0 ≤ ε)
    (h2 : ‖z‖ + ε < 2) : HasFDerivAt (reg ε) (regDeriv ε z) z := by
  have hn : HasFDerivAt (fun w : ℂ => ‖w‖ + ε) (fderiv ℝ (fun w : ℂ => ‖w‖) z) z :=
    ((contDiffAt_norm ℝ hz0 (n := 1)).differentiableAt one_ne_zero).hasFDerivAt.add_const ε
  have hpos : 0 < ‖z‖ + ε := by positivity
  have h := (hasDerivAt_log_log_four_div hpos h2).comp_hasFDerivAt z hn
  exact h

private theorem norm_regDeriv_le {z : ℂ} {ε : ℝ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hz0 : z ≠ 0)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) : ‖regDeriv ε z‖ ≤ gradBound z := by
  obtain ⟨hle, hlt⟩ := norm_mem hz hε0 hε
  have hb := abs_profileDeriv_le (norm_pos_iff.2 hz0) hle hlt
  rw [regDeriv, norm_smul, Real.norm_eq_abs, gradBound,
    ← abs_profileDeriv (norm_pos_iff.2 hz0) (by linarith)]
  calc |profileDeriv (‖z‖ + ε)| * ‖fderiv ℝ (fun w : ℂ => ‖w‖) z‖
      ≤ |profileDeriv (‖z‖ + ε)| * 1 := by gcongr; exact norm_fderiv_norm_le z
    _ ≤ |profileDeriv ‖z‖| := by rw [mul_one]; exact hb

/-- The regularisations are dominated by `u` on the punctured disc. -/
private theorem abs_reg_sub_le {z : ℂ} {ε : ℝ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hz0 : z ≠ 0)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) : |reg ε z - logLogInterior z| ≤ |logLogInterior z| := by
  obtain ⟨hle, hlt⟩ := norm_mem hz hε0 hε
  have h0 := norm_pos_iff.2 hz0
  have hp := log_log_four_div_pos (h0.trans_le hle) (lt_four_div_exp_one hlt)
  have hm : Real.log (Real.log (4 / (‖z‖ + ε))) ≤ Real.log (Real.log (4 / ‖z‖)) :=
    antitoneOn_log_log_four_div ⟨h0, by linarith⟩ ⟨h0.trans_le hle, by linarith⟩ hle
  rw [← reg_zero, reg, reg, add_zero, abs_of_nonpos (by linarith),
    abs_of_pos (log_log_four_div_pos h0 (lt_four_div_exp_one (hle.trans_lt hlt)))]
  linarith

private theorem ae_mem_ne (R : ℝ) : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) R),
    z ∈ ball (0 : ℂ) R ∧ z ≠ 0 := by
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : ℂ)))] with z hz hz0
  exact ⟨hz, hz0⟩

private theorem integrableOn_gradBound_sq :
    IntegrableOn (fun z => gradBound z ^ 2) (ball (0 : ℂ) 2) := by
  refine (integrableOn_fun_norm_addHaar volume
    (f := fun r => ((r * Real.log (4 / r))⁻¹) ^ 2)).2 ?_
  simpa [Complex.finrank_real_complex] using integrableOn_mul_inv_mul_log_four_div_sq

private instance isFiniteMeasure_restrict_ball :
    IsFiniteMeasure (volume.restrict (ball (0 : ℂ) (1 / 2))) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

private theorem integrableOn_gradBound : IntegrableOn gradBound (ball (0 : ℂ) (1 / 2)) := by
  have hm : AEStronglyMeasurable gradBound (volume.restrict (ball (0 : ℂ) (1 / 2))) :=
    Measurable.aestronglyMeasurable (by unfold gradBound; fun_prop)
  exact ((memLp_two_iff_integrable_sq hm).2
    (integrableOn_gradBound_sq.mono_set (ball_subset_ball (by norm_num)))).integrable one_le_two

/-- Each regularisation `u_ε`, `0 < ε < 1 / 2`, has its classical derivative as weak derivative
on the disc: it is continuous there and smooth off the origin. -/
private theorem hasWeakFDerivOn_reg {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    HasWeakFDerivOn volume ⟨ball (0 : ℂ) (1 / 2), isOpen_ball⟩ (reg ε) (regDeriv ε) := by
  refine hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0) ?_ ?_
    fun z hz => hasFDerivAt_reg hz.2 hε0.le (by linarith [(norm_mem hz.1 hε0.le hε).2])
  · intro z hz
    obtain ⟨-, hlt⟩ := norm_mem hz hε0.le hε
    have hc : ContinuousAt (fun s : ℝ => Real.log (Real.log (4 / s))) (‖z‖ + ε) :=
      (hasDerivAt_log_log_four_div (by positivity) (by linarith)).continuousAt
    exact (hc.comp (f := fun w : ℂ => ‖w‖ + ε) (by fun_prop)).continuousWithinAt
  · refine IntegrableOn.locallyIntegrableOn ?_
    refine integrableOn_gradBound.mono' (measurable_regDeriv ε).aestronglyMeasurable ?_
    filter_upwards [ae_mem_ne _] with z hz
    exact norm_regDeriv_le hz.1 hz.2 hε0.le hε

end LogLogInterior

open LogLogInterior

/-- The function `u(z) = log log (4 / ‖z‖)` is square integrable on the disc `ball 0 2`. -/
theorem memLp_logLogInterior :
    MemLp logLogInterior 2 (volume.restrict (ball (0 : ℂ) 2)) := by
  refine (memLp_two_iff_integrable_sq measurable_logLogInterior.aestronglyMeasurable).2 ?_
  refine (integrableOn_fun_norm_addHaar volume (f := fun r => Real.log (Real.log (4 / r)) ^ 2)).2 ?_
  simpa [Complex.finrank_real_complex] using integrableOn_mul_log_log_four_div_sq

/-- On the punctured disc `ball 0 2` the classical derivative of `u(z) = log log (4 / ‖z‖)` has
norm at most `(‖z‖ log (4 / ‖z‖))⁻¹`. -/
theorem norm_fderiv_logLogInterior_le {z : ℂ} (hz : z ∈ ball (0 : ℂ) 2) (hz0 : z ≠ 0) :
    ‖fderiv ℝ logLogInterior z‖ ≤ (‖z‖ * Real.log (4 / ‖z‖))⁻¹ := by
  rw [mem_ball_zero_iff] at hz
  have h := hasFDerivAt_reg hz0 le_rfl (by rwa [add_zero])
  rw [reg_zero] at h
  rw [h.fderiv, regDeriv, norm_smul, Real.norm_eq_abs, add_zero,
    abs_profileDeriv (norm_pos_iff.2 hz0) hz]
  calc (‖z‖ * Real.log (4 / ‖z‖))⁻¹ * ‖fderiv ℝ (fun w : ℂ => ‖w‖) z‖
      ≤ (‖z‖ * Real.log (4 / ‖z‖))⁻¹ * 1 := by
        have := log_four_div_pos (norm_pos_iff.2 hz0) hz
        gcongr
        exact norm_fderiv_norm_le z
    _ = _ := mul_one _

/-- The classical derivative of `u(z) = log log (4 / ‖z‖)` is square integrable on the disc
`ball 0 2`, although it is unbounded near the origin. -/
theorem memLp_fderiv_logLogInterior :
    MemLp (fderiv ℝ logLogInterior) 2 (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm := (measurable_fderiv ℝ logLogInterior).aestronglyMeasurable
    (μ := volume.restrict (ball (0 : ℂ) 2))
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine integrableOn_gradBound_sq.mono' (hm.norm.pow 2) ?_
  filter_upwards [ae_mem_ne _] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_logLogInterior_le hz.1 hz.2) 2

namespace LogLogInterior

/-- Volume restricted to `ball 0 (1 / 2)` is below volume restricted to `ball 0 2`. -/
private theorem restrict_ball_le :
    volume.restrict (ball (0 : ℂ) (1 / 2)) ≤ volume.restrict (ball (0 : ℂ) 2) :=
  Measure.restrict_mono (ball_subset_ball (by norm_num)) le_rfl

/-- For `ε → 0`, `u_ε → u` pointwise on the punctured disc. -/
private theorem continuousAt_reg_zero {z : ℂ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hz0 : z ≠ 0) :
    ContinuousAt (fun ε : ℝ => reg ε z) 0 := by
  obtain ⟨-, hlt⟩ := norm_mem hz le_rfl (by norm_num : (0 : ℝ) < 1 / 2)
  have hp : ContinuousAt (fun s : ℝ => Real.log (Real.log (4 / s))) (‖z‖ + 0) :=
    (hasDerivAt_log_log_four_div (by simpa using norm_pos_iff.2 hz0) (by linarith)).continuousAt
  exact hp.comp (continuousAt_const.add continuousAt_id)

/-- For `ε → 0`, `∇u_ε → ∇u` pointwise on the punctured disc. -/
private theorem continuousAt_regDeriv_zero {z : ℂ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hz0 : z ≠ 0) :
    ContinuousAt (fun ε : ℝ => regDeriv ε z) 0 := by
  obtain ⟨-, hlt⟩ := norm_mem hz le_rfl (by norm_num : (0 : ℝ) < 1 / 2)
  have hpos : 0 < ‖z‖ + 0 := by simpa using norm_pos_iff.2 hz0
  have h0 : ‖z‖ + 0 ≠ 0 := hpos.ne'
  have h4 : 4 / (‖z‖ + 0) ≠ 0 := div_ne_zero four_ne_zero h0
  have hm : (‖z‖ + 0) * Real.log (4 / (‖z‖ + 0)) ≠ 0 :=
    mul_ne_zero h0 (log_four_div_pos hpos (by linarith)).ne'
  have hp : ContinuousAt profileDeriv (‖z‖ + 0) := by
    unfold profileDeriv
    fun_prop (disch := assumption)
  exact (hp.comp (continuousAt_const.add continuousAt_id)).smul continuousAt_const

/-- `u_ε → u` in `L¹` of the disc, dominated by `|u|`. -/
private theorem tendsto_lintegral_enorm_reg_sub {ε : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ ε n)
    (hε : ∀ n, ε n < 1 / 2) (hεt : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z in ball (0 : ℂ) (1 / 2), ‖reg (ε n) z - logLogInterior z‖ₑ) atTop
      (𝓝 0) := by
  have hint := (memLp_logLogInterior.mono_measure restrict_ball_le).integrable one_le_two
  have h := tendsto_lintegral_filter_of_dominated_convergence (l := atTop)
    (μ := volume.restrict (ball (0 : ℂ) (1 / 2)))
    (F := fun n z => ‖reg (ε n) z - logLogInterior z‖ₑ) (f := fun _ => 0)
    (fun z => ‖logLogInterior z‖ₑ)
    (Eventually.of_forall fun n => ((measurable_reg _).sub measurable_logLogInterior).enorm)
    (Eventually.of_forall fun n => by
      filter_upwards [ae_mem_ne _] with z hz
      exact enorm_le_iff_norm_le.2 (abs_reg_sub_le hz.1 hz.2 (hε0 n) (hε n)))
    hint.2.ne ?_
  · simpa using h
  filter_upwards [ae_mem_ne _] with z hz
  have hlim := ((continuousAt_reg_zero hz.1 hz.2).tendsto.comp hεt).sub_const (reg 0 z)
  rw [sub_self, reg_zero] at hlim
  exact (continuous_enorm.tendsto' _ 0 (by simp)).comp hlim

/-- `∇u_ε → ∇u` in `L¹` of the disc, dominated by `2 (r log (4 / r))⁻¹`. -/
private theorem tendsto_lintegral_enorm_regDeriv_sub {ε : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ ε n)
    (hε : ∀ n, ε n < 1 / 2) (hεt : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z in ball (0 : ℂ) (1 / 2),
      ‖regDeriv (ε n) z - fderiv ℝ logLogInterior z‖ₑ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence (l := atTop)
    (μ := volume.restrict (ball (0 : ℂ) (1 / 2)))
    (F := fun n z => ‖regDeriv (ε n) z - fderiv ℝ logLogInterior z‖ₑ) (f := fun _ => 0)
    (fun z => ‖2 * gradBound z‖ₑ)
    (Eventually.of_forall fun n =>
      ((measurable_regDeriv _).sub (measurable_fderiv ℝ _)).enorm)
    (Eventually.of_forall fun n => by
      filter_upwards [ae_mem_ne _] with z hz
      refine enorm_le_iff_norm_le.2 ?_
      have h1 := norm_regDeriv_le hz.1 hz.2 (hε0 n) (hε n)
      have h2 := norm_fderiv_logLogInterior_le (ball_subset_ball (by norm_num) hz.1) hz.2
      have h0 : 0 ≤ gradBound z := (norm_nonneg _).trans h1
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖regDeriv (ε n) z - fderiv ℝ logLogInterior z‖
          ≤ ‖regDeriv (ε n) z‖ + ‖fderiv ℝ logLogInterior z‖ := norm_sub_le _ _
        _ ≤ 2 * gradBound z := by rw [gradBound] at h1 ⊢; linarith)
    (integrableOn_gradBound.const_mul 2).2.ne ?_
  · simpa using h
  filter_upwards [ae_mem_ne _] with z hz
  have hd : regDeriv 0 z = fderiv ℝ logLogInterior z := by
    have h := hasFDerivAt_reg hz.2 le_rfl (by linarith [(norm_mem hz.1 le_rfl (by norm_num)).2])
    rw [reg_zero] at h
    exact h.fderiv.symm
  have hlim := ((continuousAt_regDeriv_zero hz.1 hz.2).tendsto.comp hεt).sub_const (regDeriv 0 z)
  rw [sub_self, hd] at hlim
  exact (continuous_enorm.tendsto' (0 : ℂ →L[ℝ] ℝ) 0 (by simp [enorm_eq_nnnorm])).comp hlim

end LogLogInterior

/-- **The classical derivative of `log log (4 / ‖z‖)` is its weak derivative across the
origin.** On the disc `ball 0 (1 / 2)` the function `u(z) = log log (4 / ‖z‖)`, which is
unbounded at the origin, has its classical derivative as weak derivative. -/
theorem hasWeakFDerivOn_logLogInterior :
    HasWeakFDerivOn volume ⟨ball (0 : ℂ) (1 / 2), isOpen_ball⟩ logLogInterior
      (fderiv ℝ logLogInterior) := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) / 4 with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => by positivity
  have hε : ∀ n, ε n < 1 / 2 := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    simp only [hεdef]
    linarith
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (4 : ℝ) (α := ℕ) (G₀ := ℝ)
    rw [zero_div] at h
    exact h
  have hint := (memLp_logLogInterior.mono_measure restrict_ball_le).integrable one_le_two
  have hDint := (memLp_fderiv_logLogInterior.mono_measure restrict_ball_le).integrable one_le_two
  exact hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop) (u := fun n => reg (ε n))
    (U := fun n => regDeriv (ε n)) (IntegrableOn.locallyIntegrableOn hint)
    (fun v => IntegrableOn.locallyIntegrableOn (hDint.apply_continuousLinearMap v))
    (fun n => hasWeakFDerivOn_reg (hε0 n) (hε n))
    (tendsto_lintegral_enorm_reg_sub (fun n => (hε0 n).le) hε hεt)
    (tendsto_lintegral_enorm_regDeriv_sub (fun n => (hε0 n).le) hε hεt)

/-- **`log log (4 / ‖z‖)` is in the local class `W^{1,p}` for `p ≤ 2`.** On the disc
`ball 0 (1 / 2)` the function `u(z) = log log (4 / ‖z‖)`, unbounded at the origin, lies in the
local Sobolev class `W^{1,p}` for every exponent `p ≤ 2`. -/
theorem memWkpLoc_logLogInterior {p : ENNReal} (hp : p ≤ 2) :
    MemWkpLoc p (ball (0 : ℂ) (1 / 2)) 1 logLogInterior := by
  have hball : MemLpLoc 2 (ball (0 : ℂ) (1 / 2)) logLogInterior := memLpLoc_iff.2 fun K hK _ =>
    memLp_logLogInterior.mono_measure ((Measure.restrict_mono hK le_rfl).trans restrict_ball_le)
  have hDball : MemLpLoc 2 (ball (0 : ℂ) (1 / 2)) (fderiv ℝ logLogInterior) :=
    memLpLoc_iff.2 fun K hK _ => memLp_fderiv_logLogInterior.mono_measure
      ((Measure.restrict_mono hK le_rfl).trans restrict_ball_le)
  have h2 : MemWkpLoc 2 (ball (0 : ℂ) (1 / 2)) 1 logLogInterior :=
    (memWkpLoc_succ_iff_of_isOpen (Ω := ⟨ball (0 : ℂ) (1 / 2), isOpen_ball⟩)).2
      ⟨hball, _, hasWeakFDerivOn_logLogInterior, memWkpLoc_zero_iff.2 hDball⟩
  exact h2.mono_exponent hp

/-- The function `u(z) = log log (4 / ‖z‖)` tends to `∞` at the origin. -/
theorem tendsto_logLogInterior : Tendsto logLogInterior (𝓝[≠] 0) atTop := by
  have h4 : Tendsto (fun y : ℝ => 4 / y) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop four_pos
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (h4.comp (tendsto_norm_nhdsNE_zero (E := ℂ))))

/-- No function equal almost everywhere on the disc `ball 0 (1 / 2)` to
`u(z) = log log (4 / ‖z‖)` is continuous at the origin. -/
theorem not_continuousAt_of_ae_eq_logLogInterior {g : ℂ → ℝ}
    (hg : g =ᵐ[volume.restrict (ball (0 : ℂ) (1 / 2))] logLogInterior) :
    ¬ ContinuousAt g 0 := by
  intro hc
  have hb : ∀ᶠ z in 𝓝[≠] 0, g z < g 0 + 1 :=
    nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (lt_add_one _)))
  have hf : ∀ᶠ z in 𝓝[≠] 0, g 0 + 1 < logLogInterior z :=
    tendsto_logLogInterior.eventually_gt_atTop _
  have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball (0 : ℂ) (1 / 2) :=
    nhdsWithin_le_nhds (ball_mem_nhds _ (by norm_num))
  obtain ⟨o, ho, ho0, hos⟩ := mem_nhdsWithin.1 ((hb.and hf).and hball)
  -- The punctured neighbourhood `o \ {0}` has positive measure and lies in `{g ≠ u} ∩ D`.
  have hpos : 0 < volume (o \ {0}) := by
    rw [measure_sdiff_null (measure_singleton _)]
    exact ho.measure_pos _ ⟨0, ho0⟩
  have hsub : o \ {0} ⊆ {z | ¬ g z = logLogInterior z} ∩ ball (0 : ℂ) (1 / 2) := by
    intro z hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := hos ⟨hz.1, hz.2⟩
    exact ⟨fun h => by linarith, h3⟩
  have hzero := ae_iff.1 hg
  exact hpos.ne' (le_antisymm ((measure_mono hsub).trans
    ((Measure.le_restrict_apply _ _).trans hzero.le)) zero_le)

/-- **For `kp ≤ 2` not every member of the local class `W^{1,p}` has a continuous
representative.** For every
`p ≤ 2` some function in the local class `W^{1,p}` of the disc `ball 0 (1 / 2)` agrees almost
everywhere with no function continuous on that disc; one example is
`u(z) = log log (4 / ‖z‖)`. For `p > 2` Morrey's inequality
`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative` gives a continuous representative. -/
theorem exists_memWkpLoc_one_not_continuousOn_of_ae_eq {p : ENNReal} (hp : p ≤ 2) :
    ∃ f : ℂ → ℝ, MemWkpLoc p (ball (0 : ℂ) (1 / 2)) 1 f ∧
      ∀ g : ℂ → ℝ, g =ᵐ[volume.restrict (ball (0 : ℂ) (1 / 2))] f →
        ¬ ContinuousOn g (ball (0 : ℂ) (1 / 2)) :=
  ⟨logLogInterior, memWkpLoc_logLogInterior hp, fun _g hg hc =>
    not_continuousAt_of_ae_eq_logLogInterior hg
      (hc.continuousAt (ball_mem_nhds _ (by norm_num)))⟩

end TauCeti
