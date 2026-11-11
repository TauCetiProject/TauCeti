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
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.Analysis.Sobolev.W1p.LogLogTraceExample
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable

/-!
# An unbounded function in the local class `W^{1,2}` of the plane

On the disc `D = ball 0 (1 / 2) ⊆ ℂ` let

`u(z) = log log (4 / ‖z‖)`

(`TauCeti.logLogInterior`). With `r = ‖z‖ ∈ (0, 1 / 2)` the inner logarithm exceeds `log 8 > 1`, so
`u` is smooth and positive on the punctured disc, and its gradient has size
`1 / (r log (4 / r))`. In polar coordinates both `u²` and `‖∇u‖²` have integrable radial
profiles, so `u` and its classical derivative are square integrable on `D`
(`TauCeti.memLp_logLogInterior`, `TauCeti.memLp_fderiv_logLogInterior`).

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
inequality `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`; this is why local Sobolev maps
between manifolds are only defined for `kp > 2`.

## Implementation notes

The constant `4` keeps the inner logarithm above `1` on `D`, so both logarithms are positive and
the regularised functions satisfy `0 < u_ε ≤ u`. The radial integrals are those of
`TauCeti.logLogTraceExample`, the same profile placed at a boundary point of the unit disc:
`TauCeti.integrableOn_mul_log_log_four_div_sq` and
`TauCeti.integrableOn_mul_inv_mul_log_four_div_sq`.

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

/-- The radial profile `s ↦ log log (4 / s)`. -/
private def profile (s : ℝ) : ℝ :=
  Real.log (Real.log (4 / s))

/-- The derivative `s ↦ -(s log (4 / s))⁻¹` of the radial profile. -/
private def profileDeriv (s : ℝ) : ℝ :=
  -(s * Real.log (4 / s))⁻¹

/-- For `0 < s < 1` the inner logarithm exceeds `1`, since `4 / s > 4 > e`. -/
private theorem one_lt_log_four_div {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    1 < Real.log (4 / s) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have h4 : 4 < 4 / s := by rw [lt_div_iff₀ h0]; linarith
  linarith [Real.exp_one_lt_d9]

private theorem hasDerivAt_profile {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    HasDerivAt profile (profileDeriv s) s := by
  have hL := (one_lt_log_four_div h0 h1).trans' one_pos
  have h4 : HasDerivAt (fun y : ℝ => 4 / y) (-(4 / s ^ 2)) s := by
    have h := (hasDerivAt_inv h0.ne').const_mul (4 : ℝ)
    simp only [div_eq_mul_inv]
    convert h using 1
    ring
  refine ((h4.log (by positivity)).log hL.ne').congr_deriv ?_
  rw [profileDeriv]
  field_simp

/-- The radial profile is positive on `(0, 1)`. -/
private theorem profile_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < profile s :=
  Real.log_pos (one_lt_log_four_div h0 h1)

/-- The radial profile is antitone on `(0, 1)`. -/
private theorem profile_le_profile {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    profile b ≤ profile a :=
  Real.log_le_log ((one_lt_log_four_div (ha.trans_le hab) hb).trans' one_pos)
    (Real.log_le_log (div_pos four_pos (ha.trans_le hab))
      (div_le_div_of_nonneg_left (by norm_num) ha hab))

/-- `t ↦ t log (4 / t)` is monotone on `(0, 1)`, so the size of the profile derivative is
antitone there. -/
private theorem abs_profileDeriv_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    |profileDeriv b| ≤ |profileDeriv a| := by
  have hb0 : 0 < b := ha.trans_le hab
  have hLb := one_lt_log_four_div hb0 hb
  have hLa := one_lt_log_four_div ha (hab.trans_lt hb)
  have hsplit : Real.log (4 / a) = Real.log (4 / b) + Real.log (b / a) := by
    have h4 : 4 / a = 4 / b * (b / a) := by field_simp
    rw [h4, Real.log_mul (by positivity) (by positivity)]
  have hba : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hmono : a * Real.log (4 / a) ≤ b * Real.log (4 / b) := by
    rw [hsplit, mul_add]
    have : a * Real.log (b / a) ≤ b - a := by
      calc a * Real.log (b / a) ≤ a * (b / a - 1) := by gcongr
        _ = b - a := by field_simp
    nlinarith
  rw [profileDeriv, profileDeriv, abs_neg, abs_neg, abs_inv, abs_inv,
    abs_of_pos (by positivity), abs_of_pos (by positivity)]
  exact inv_anti₀ (by positivity) hmono

/-- The regularisation `u_ε(z) = log log (4 / (‖z‖ + ε))`. -/
private def reg (ε : ℝ) (z : ℂ) : ℝ :=
  profile (‖z‖ + ε)

/-- The classical derivative of `u_ε` off the origin. -/
private def regDeriv (ε : ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  profileDeriv (‖z‖ + ε) • fderiv ℝ (fun w : ℂ => ‖w‖) z

/-- The size `(r log (4 / r))⁻¹`, `r = ‖z‖`, of the gradient of `u`. -/
private def gradBound (z : ℂ) : ℝ :=
  (‖z‖ * Real.log (4 / ‖z‖))⁻¹

private theorem reg_zero : reg 0 = logLogInterior := by
  funext z
  rw [reg, add_zero, profile, logLogInterior_def]

private theorem measurable_reg (ε : ℝ) : Measurable (reg ε) := by
  unfold reg profile
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

private theorem hasFDerivAt_reg {z : ℂ} {ε : ℝ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hz0 : z ≠ 0)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) : HasFDerivAt (reg ε) (regDeriv ε z) z := by
  have hn : HasFDerivAt (fun w : ℂ => ‖w‖ + ε) (fderiv ℝ (fun w : ℂ => ‖w‖) z) z :=
    ((contDiffAt_norm ℝ hz0 (n := 1)).differentiableAt one_ne_zero).hasFDerivAt.add_const ε
  have hpos : 0 < ‖z‖ + ε := by positivity
  exact (hasDerivAt_profile hpos (norm_mem hz hε0 hε).2).comp_hasFDerivAt z hn

private theorem norm_regDeriv_le {z : ℂ} {ε : ℝ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hz0 : z ≠ 0)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) : ‖regDeriv ε z‖ ≤ gradBound z := by
  obtain ⟨hle, hlt⟩ := norm_mem hz hε0 hε
  have hD : ‖fderiv ℝ (fun w : ℂ => ‖w‖) z‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := ℂ))
  have hb := abs_profileDeriv_le (norm_pos_iff.2 hz0) hle hlt
  have hg : gradBound z = |profileDeriv ‖z‖| := by
    have := one_lt_log_four_div (norm_pos_iff.2 hz0) (hle.trans_lt hlt)
    rw [gradBound, profileDeriv, abs_neg, abs_inv, abs_of_pos (by positivity)]
  rw [regDeriv, norm_smul, Real.norm_eq_abs, hg]
  calc |profileDeriv (‖z‖ + ε)| * ‖fderiv ℝ (fun w : ℂ => ‖w‖) z‖
      ≤ |profileDeriv (‖z‖ + ε)| * 1 := by gcongr
    _ ≤ |profileDeriv ‖z‖| := by rw [mul_one]; exact hb

/-- The regularisations are dominated by `u` on the punctured disc. -/
private theorem abs_reg_sub_le {z : ℂ} {ε : ℝ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hz0 : z ≠ 0)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) : |reg ε z - logLogInterior z| ≤ |logLogInterior z| := by
  obtain ⟨hle, hlt⟩ := norm_mem hz hε0 hε
  have h0 := norm_pos_iff.2 hz0
  have hp := profile_pos (h0.trans_le hle) hlt
  have hm := profile_le_profile h0 hle hlt
  rw [← reg_zero, reg, reg, add_zero, abs_of_nonpos (by linarith),
    abs_of_pos (profile_pos h0 (hle.trans_lt hlt))]
  linarith

private theorem ae_mem_ne : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) (1 / 2)),
    z ∈ ball (0 : ℂ) (1 / 2) ∧ z ≠ 0 := by
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : ℂ)))] with z hz hz0
  exact ⟨hz, hz0⟩

private theorem integrableOn_gradBound_sq :
    IntegrableOn (fun z => gradBound z ^ 2) (ball (0 : ℂ) (1 / 2)) := by
  refine (integrableOn_fun_norm_addHaar volume
    (f := fun r => ((r * Real.log (4 / r))⁻¹) ^ 2)).2 ?_
  simpa [Complex.finrank_real_complex] using
    integrableOn_mul_inv_mul_log_four_div_sq.mono_set (Ioo_subset_Ioo_right (by norm_num))

private instance isFiniteMeasure_restrict_ball :
    IsFiniteMeasure (volume.restrict (ball (0 : ℂ) (1 / 2))) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

private theorem integrableOn_gradBound : IntegrableOn gradBound (ball (0 : ℂ) (1 / 2)) := by
  have hm : AEStronglyMeasurable gradBound (volume.restrict (ball (0 : ℂ) (1 / 2))) :=
    Measurable.aestronglyMeasurable (by unfold gradBound; fun_prop)
  exact ((memLp_two_iff_integrable_sq hm).2 integrableOn_gradBound_sq).integrable one_le_two

/-- Each regularisation `u_ε`, `0 < ε < 1 / 2`, has its classical derivative as weak derivative
on the disc: it is continuous there and smooth off the origin. -/
private theorem hasWeakFDerivOn_reg {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    HasWeakFDerivOn volume ⟨ball (0 : ℂ) (1 / 2), isOpen_ball⟩ (reg ε) (regDeriv ε) := by
  refine hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0) ?_ ?_
    fun z hz => hasFDerivAt_reg hz.1 hz.2 hε0.le hε
  · intro z hz
    obtain ⟨-, hlt⟩ := norm_mem hz hε0.le hε
    have hc : ContinuousAt profile (‖z‖ + ε) :=
      (hasDerivAt_profile (by positivity) hlt).continuousAt
    have hn : ContinuousAt (fun w : ℂ => ‖w‖ + ε) z := by fun_prop
    exact (hc.comp (f := fun w : ℂ => ‖w‖ + ε) hn).continuousWithinAt
  · refine IntegrableOn.locallyIntegrableOn ?_
    refine integrableOn_gradBound.mono' (measurable_regDeriv ε).aestronglyMeasurable ?_
    filter_upwards [ae_mem_ne] with z hz
    exact norm_regDeriv_le hz.1 hz.2 hε0.le hε

end LogLogInterior

open LogLogInterior

/-- The function `u(z) = log log (4 / ‖z‖)` is square integrable on the disc `ball 0 (1 / 2)`. -/
theorem memLp_logLogInterior :
    MemLp logLogInterior 2 (volume.restrict (ball (0 : ℂ) (1 / 2))) := by
  refine (memLp_two_iff_integrable_sq measurable_logLogInterior.aestronglyMeasurable).2 ?_
  refine (integrableOn_fun_norm_addHaar volume (f := fun r => Real.log (Real.log (4 / r)) ^ 2)).2 ?_
  simpa [Complex.finrank_real_complex] using
    integrableOn_mul_log_log_four_div_sq.mono_set (Ioo_subset_Ioo_right (by norm_num))

/-- On the punctured disc the classical derivative of `u(z) = log log (4 / ‖z‖)` has norm at most
`(‖z‖ log (4 / ‖z‖))⁻¹`. -/
theorem norm_fderiv_logLogInterior_le {z : ℂ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) (hz0 : z ≠ 0) :
    ‖fderiv ℝ logLogInterior z‖ ≤ (‖z‖ * Real.log (4 / ‖z‖))⁻¹ := by
  have h := hasFDerivAt_reg hz hz0 le_rfl (by norm_num)
  rw [reg_zero] at h
  rw [h.fderiv]
  exact norm_regDeriv_le hz hz0 le_rfl (by norm_num)

/-- The classical derivative of `u(z) = log log (4 / ‖z‖)` is square integrable on the disc
`ball 0 (1 / 2)`, although it is unbounded near the origin. -/
theorem memLp_fderiv_logLogInterior :
    MemLp (fderiv ℝ logLogInterior) 2 (volume.restrict (ball (0 : ℂ) (1 / 2))) := by
  have hm := (measurable_fderiv ℝ logLogInterior).aestronglyMeasurable
    (μ := volume.restrict (ball (0 : ℂ) (1 / 2)))
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine integrableOn_gradBound_sq.mono' (hm.norm.pow 2) ?_
  filter_upwards [ae_mem_ne] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_logLogInterior_le hz.1 hz.2) 2

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
  have hint := memLp_logLogInterior.integrable one_le_two
  have hDint := memLp_fderiv_logLogInterior.integrable one_le_two
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop) (u := fun n => reg (ε n))
    (U := fun n => regDeriv (ε n)) (IntegrableOn.locallyIntegrableOn hint)
    (fun v => IntegrableOn.locallyIntegrableOn (hDint.apply_continuousLinearMap v))
    (fun n => hasWeakFDerivOn_reg (hε0 n) (hε n)) ?_ ?_
  · -- `u_ε → u` in `L¹`, dominated by `|u|`.
    have h := tendsto_lintegral_filter_of_dominated_convergence (l := atTop)
      (μ := volume.restrict (ball (0 : ℂ) (1 / 2)))
      (F := fun n z => ‖reg (ε n) z - logLogInterior z‖ₑ) (f := fun _ => 0)
      (fun z => ‖logLogInterior z‖ₑ)
      (Eventually.of_forall fun n => ((measurable_reg _).sub measurable_logLogInterior).enorm)
      (Eventually.of_forall fun n => by
        filter_upwards [ae_mem_ne] with z hz
        exact enorm_le_iff_norm_le.2 (abs_reg_sub_le hz.1 hz.2 (hε0 n).le (hε n)))
      hint.2.ne ?_
    · simpa using h
    filter_upwards [ae_mem_ne] with z hz
    obtain ⟨hle, hlt⟩ := norm_mem hz.1 le_rfl (by norm_num : (0 : ℝ) < 1 / 2)
    have hc : ContinuousAt (fun ε : ℝ => reg ε z) 0 := by
      have hp : ContinuousAt profile (‖z‖ + 0) :=
        (hasDerivAt_profile (by simpa using norm_pos_iff.2 hz.2) hlt).continuousAt
      exact hp.comp (continuousAt_const.add continuousAt_id)
    have hlim := (hc.tendsto.comp hεt).sub_const (reg 0 z)
    rw [sub_self, reg_zero] at hlim
    exact (continuous_enorm.tendsto' _ 0 (by simp)).comp hlim
  · -- `∇u_ε → ∇u` in `L¹`, dominated by `2 (r log (4 / r))⁻¹`.
    have h := tendsto_lintegral_filter_of_dominated_convergence (l := atTop)
      (μ := volume.restrict (ball (0 : ℂ) (1 / 2)))
      (F := fun n z => ‖regDeriv (ε n) z - fderiv ℝ logLogInterior z‖ₑ) (f := fun _ => 0)
      (fun z => ‖2 * gradBound z‖ₑ)
      (Eventually.of_forall fun n =>
        ((measurable_regDeriv _).sub (measurable_fderiv ℝ _)).enorm)
      (Eventually.of_forall fun n => by
        filter_upwards [ae_mem_ne] with z hz
        refine enorm_le_iff_norm_le.2 ?_
        have h1 := norm_regDeriv_le hz.1 hz.2 (hε0 n).le (hε n)
        have h2 := norm_fderiv_logLogInterior_le hz.1 hz.2
        have h0 : 0 ≤ gradBound z := (norm_nonneg _).trans h1
        rw [Real.norm_of_nonneg (by positivity)]
        calc ‖regDeriv (ε n) z - fderiv ℝ logLogInterior z‖
            ≤ ‖regDeriv (ε n) z‖ + ‖fderiv ℝ logLogInterior z‖ := norm_sub_le _ _
          _ ≤ 2 * gradBound z := by rw [gradBound] at h1 ⊢; linarith)
      (integrableOn_gradBound.const_mul 2).2.ne ?_
    · simpa using h
    filter_upwards [ae_mem_ne] with z hz
    have h0 := norm_pos_iff.2 hz.2
    obtain ⟨hle, hlt⟩ := norm_mem hz.1 le_rfl (by norm_num : (0 : ℝ) < 1 / 2)
    have hd : regDeriv 0 z = fderiv ℝ logLogInterior z := by
      have h := hasFDerivAt_reg hz.1 hz.2 le_rfl (by norm_num)
      rw [reg_zero] at h
      exact h.fderiv.symm
    have hc : ContinuousAt (fun ε : ℝ => regDeriv ε z) 0 := by
      have hL : Real.log (4 / (‖z‖ + 0)) ≠ 0 :=
        (one_lt_log_four_div (by simpa using h0) (by simpa using hle.trans_lt hlt)).trans'
          one_pos |>.ne'
      have hp : ContinuousAt profileDeriv (‖z‖ + 0) := by
        unfold profileDeriv
        refine ((continuousAt_id.mul ((continuousAt_const.div continuousAt_id
          (by simpa using h0.ne')).log (by simp [h0.ne']))).inv₀ ?_).neg
        exact mul_ne_zero (by simpa using h0.ne') hL
      exact (hp.comp (continuousAt_const.add continuousAt_id)).smul continuousAt_const
    have hlim := (hc.tendsto.comp hεt).sub_const (regDeriv 0 z)
    rw [sub_self, hd] at hlim
    exact (continuous_enorm.tendsto' (0 : ℂ →L[ℝ] ℝ) 0
      (by rw [← ofReal_norm, norm_zero, ENNReal.ofReal_zero])).comp hlim

/-- **`log log (4 / ‖z‖)` is in the local class `W^{1,p}` for `p ≤ 2`.** On the disc
`ball 0 (1 / 2)` the function `u(z) = log log (4 / ‖z‖)`, unbounded at the origin, lies in the
local Sobolev class `W^{1,p}` for every exponent `p ≤ 2`. -/
theorem memWkpLoc_logLogInterior {p : ENNReal} (hp : p ≤ 2) :
    MemWkpLoc p (ball (0 : ℂ) (1 / 2)) 1 logLogInterior := by
  have hball : MemLpLoc 2 (ball (0 : ℂ) (1 / 2)) logLogInterior := memLpLoc_iff.2 fun K hK _ =>
    memLp_logLogInterior.mono_measure (Measure.restrict_mono hK le_rfl)
  have hDball : MemLpLoc 2 (ball (0 : ℂ) (1 / 2)) (fderiv ℝ logLogInterior) :=
    memLpLoc_iff.2 fun K hK _ =>
      memLp_fderiv_logLogInterior.mono_measure (Measure.restrict_mono hK le_rfl)
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

/-- **For `kp ≤ 2` the local class `W^{1,p}` has no continuous representatives.** For every
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
