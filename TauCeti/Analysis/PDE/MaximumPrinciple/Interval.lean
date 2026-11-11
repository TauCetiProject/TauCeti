/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Hopf's lemma for weak supersolutions on an interval

On an interval `(x₀, x₁)` consider the divergence-form operator

`L u = -(a u' + b u)' + c u' + d u`

with measurable `a`, `0 < lam ≤ a ≤ Λ`, bounded measurable `b`, square-integrable `c` and
integrable `d`. A function `u` continuous on `[x₀, x₁]` with weak derivative `u' ∈ L²` is a weak
supersolution, `L u ≥ 0`, when

`0 ≤ ∫ (a u' + b u) φ' + (c u' + d u) φ`

for every nonnegative test function `φ` on the interval. This file proves **Hopf's boundary-point
lemma** for such `u`: if `u x₀ = 0` and `u > 0` inside, then `u` leaves `x₀` at a positive linear
rate, `ε t ≤ u (x₀ + t)` for small `t > 0`. No regularity of the coefficients is needed, which is
special to one dimension: in dimension `n ≥ 2` the lemma fails for merely measurable principal
coefficients. Since the boundary value is `0`, no sign condition on `b`, `c` or `d` is needed
either, as in the classical lemma.

The flux `F = a u' + b u` of a supersolution need not be absolutely continuous: its distributional
derivative is a measure. What survives is a monotonicity statement. With `g = c u' + d u`, the
weak inequality says `F' ≤ g`; multiplying by the integrating factor
`ν x = exp (-∫ t in x₀..x, c t / a t)`, which solves `ν' = -(c / a) ν`, cancels the drift and
leaves `(ν F)' ≤ ν e u` with `e = d - c b / a`. Hence

`ν F - ∫ t in x₀..·, ν t * e t * u t`

is almost everywhere antitone (`TauCeti.PDE.exists_ae_mem_antitoneOn_exp_mul_sub_intervalIntegral`,
proved for general `F`, `g` and `m = c / a`). The test function `ψ ν` needed for this is not
smooth, since `c / a` is only square integrable; it is approximated by `ψ νₖ`, with `νₖ` built from
smooth `L²` approximations of `c / a`, and the limit uses the Cauchy–Schwarz inequality against
`F ∈ L²`. The monotone du Bois-Reymond lemma
`MeasureTheory.LocallyIntegrableOn.exists_ae_mem_monotoneOn_of_integral_deriv_mul_nonpos` then
gives the almost-everywhere monotonicity.

Hopf's lemma follows by cases on the sign of the weighted flux `K = ν F - ∫ ν e u` near `x₀`. If
`K` is positive somewhere, it is bounded below by a positive constant to the left of that point,
so `a u' = F - b u` is bounded below near `x₀`, where `u` and `∫ ν e u` are small. Otherwise
`ν F ≤ ∫ ν e u`, which bounds `u'` on `(x₀, z)` by a constant times `max_{[x₀, z]} u`; integrating
from `x₀`, where `u` vanishes, forces `u = 0` near `x₀`, contradicting `u > 0`.

## Main declarations

* `TauCeti.PDE.exists_ae_mem_antitoneOn_exp_mul_sub_intervalIntegral`: if `F' ≤ g` weakly, the
  weighted flux `ν F - ∫ ν (g - m F)` is antitone on a set of full measure.
* `TauCeti.PDE.exists_pos_mul_le_of_integral_flux_mul_deriv_add_nonneg`: **Hopf's boundary-point
  lemma** for weak supersolutions on an interval.
* `TauCeti.PDE.pos_of_hasDerivWithinAt_of_integral_flux_mul_deriv_add_nonneg`: its derivative
  form, the right derivative at `x₀`, when it exists, is positive.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4 (the classical Hopf lemma) and Section 8.1 (weak supersolutions).
* L. Rosales, *Generalizing Hopf's boundary point lemma*, arXiv:1806.07003, Theorem 4.1 (the
  divergence-form Hopf lemma in dimension `n ≥ 2`).
-/

public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ENNReal

namespace TauCeti.PDE

variable {x₀ x₁ : ℝ}

/-- The primitive `x ↦ ∫ t in x₀..x, G t` of a smooth function is smooth, with derivative `G`. -/
private lemma contDiff_primitive {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (x₀ : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in x₀..x, G t) ∧
      ∀ x, HasDerivAt (fun x ↦ ∫ t in x₀..x, G t) (G x) x := by
  have hderiv : ∀ x, HasDerivAt (fun x ↦ ∫ t in x₀..x, G t) (G x) x := fun x ↦
    intervalIntegral.integral_hasDerivAt_right (hG.continuous.intervalIntegrable _ _)
      (hG.continuous.stronglyMeasurableAtFilter _ _) hG.continuous.continuousAt
  refine ⟨contDiff_infty_iff_deriv.mpr ⟨fun x ↦ (hderiv x).differentiableAt, ?_⟩, hderiv⟩
  rw [show deriv (fun x ↦ ∫ t in x₀..x, G t) = G from funext fun x ↦ (hderiv x).deriv]
  exact hG

/-- A primitive from the left endpoint of a function integrable on `Ioo x₀ x₁` is bounded on the
interval by the `L¹` norm. -/
private lemma abs_intervalIntegral_le_integral_abs {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo x₀ x₁))
    {x : ℝ} (hx : x ∈ Ioo x₀ x₁) :
    |∫ t in x₀..x, f t| ≤ ∫ t in Ioo x₀ x₁, |f t| := by
  rw [intervalIntegral.integral_of_le hx.1.le]
  calc |∫ t in Ioc x₀ x, f t| ≤ ∫ t in Ioc x₀ x, |f t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioo x₀ x₁, |f t| := setIntegral_mono_set hf.abs
        (ae_of_all _ fun _ ↦ abs_nonneg _) (Ioc_subset_Ioo_right hx.2).eventuallyLE

/-- **Multiplying a distributional inequality by an integrating factor.** If `F' ≤ g` in the
sense of distributions on `Ioo x₀ x₁`, that is `0 ≤ ∫ F φ' + g φ` for every nonnegative test
function `φ`, and `m` is square integrable, then the same holds for `ν F` and `ν (g - m F)`, where
`ν x = exp (-∫ t in x₀..x, m t)` solves `ν' = -m ν`. -/
private lemma integral_exp_mul_nonneg {F g m ψ : ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (Ioo x₀ x₁))) (hg : IntegrableOn g (Ioo x₀ x₁))
    (hm : MemLp m 2 (volume.restrict (Ioo x₀ x₁)))
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, F x * deriv φ x + g x * φ x)
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo x₀ x₁) (hψ0 : ∀ x, 0 ≤ ψ x) :
    0 ≤ ∫ x in Ioo x₀ x₁,
      exp (-∫ t in x₀..x, m t) * (F x * deriv ψ x + (g x - m x * F x) * ψ x) := by
  set μ := volume.restrict (Ioo x₀ x₁)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hmi : Integrable m μ := hm.integrable one_le_two
  have hFi : Integrable F μ := hF.integrable one_le_two
  -- Bounds on `ψ` and `ψ'`.
  have hψc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ)
    (hψs.trans Ioo_subset_Icc_self)
  obtain ⟨Cψ, hCψ⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hψc.norm
  obtain ⟨Cψ', hCψ'⟩ := (hψ.continuous_deriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    hψc.deriv.norm
  have hψb : ∀ x, |ψ x| ≤ Cψ := fun x ↦ hCψ ⟨x, rfl⟩
  have hψ'b : ∀ x, |deriv ψ x| ≤ Cψ' := fun x ↦ hCψ' ⟨x, rfl⟩
  -- Smooth approximants `G k` of `m` in `L²`.
  have happrox : ∀ k : ℕ, ∃ G : ℝ → ℝ, HasCompactSupport G ∧ ContDiff ℝ ∞ G ∧
      eLpNorm (m - G) 2 μ ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := fun k ↦
    hm.exist_eLpNorm_sub_le (by simp) one_le_two (by positivity)
  choose G hGc hGs hGm using happrox
  have hGL2 : ∀ k, MemLp (G k) 2 μ := fun k ↦ (hGs k).continuous.memLp_of_hasCompactSupport (hGc k)
  have hmG : ∀ k, MemLp (m - G k) 2 μ := fun k ↦ hm.sub (hGL2 k)
  have hmG' : ∀ k, (eLpNorm (m - G k) 2 μ).toReal ≤ 1 / ((k : ℝ) + 1) := fun k ↦
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hGm k)
  have hk0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- The `L¹` distance `η k` from `G k` to `m` on the interval tends to `0`.
  set η : ℕ → ℝ := fun k ↦ ∫ x, |m x - G k x| ∂μ
  have hη0 : ∀ k, 0 ≤ η k := fun k ↦ integral_nonneg fun _ ↦ abs_nonneg _
  have hη : Tendsto η atTop (𝓝 0) := by
    set C := (μ univ ^ (1 - 1 / (2 : ℝ≥0∞).toReal)).toReal
    have hC : Tendsto (fun k : ℕ ↦ C * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hk0.const_mul C
    refine squeeze_zero hη0 (fun k ↦ ?_) hC
    have := (hmG k).integral_norm_le_mul_eLpNorm one_le_two
    simp only [Real.norm_eq_abs, Pi.sub_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hmG' k) ENNReal.toReal_nonneg)
  -- The squared `L²` distance tends to `0`.
  have hL2 : Tendsto (fun k ↦ ∫ x, (m x - G k x) ^ 2 ∂μ) atTop (𝓝 0) := by
    have hk2 : Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      simpa using hk0.pow 2
    refine squeeze_zero (fun k ↦ integral_nonneg fun _ ↦ sq_nonneg _) (fun k ↦ ?_) hk2
    have h2 := (hmG k).norm_toLp_sq
    rw [Lp.norm_toLp] at h2
    simp only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] at h2
    rw [← h2]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hmG' k) 2
  -- The integrating factors `ν` and `ν k`, and their bounds on the interval.
  set M := ∫ x, |m x| ∂μ
  set ν : ℝ → ℝ := fun x ↦ exp (-∫ t in x₀..x, m t)
  set νk : ℕ → ℝ → ℝ := fun k x ↦ exp (-∫ t in x₀..x, G k t)
  have hGint : ∀ k (x : ℝ), IntervalIntegrable (G k) volume x₀ x := fun k x ↦
    (hGs k).continuous.intervalIntegrable _ _
  have hdist : ∀ k, ∀ x ∈ Ioo x₀ x₁,
      |(∫ t in x₀..x, G k t) - ∫ t in x₀..x, m t| ≤ η k := by
    intro k x hx
    have hmx : IntervalIntegrable m volume x₀ x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1.le).2
        (IntegrableOn.mono_set (hmi : IntegrableOn m (Ioo x₀ x₁) volume)
          (Ioc_subset_Ioo_right hx.2))
    rw [← intervalIntegral.integral_sub (hGint k x) hmx]
    refine (abs_intervalIntegral_le_integral_abs (((hGs k).continuous.integrableOn_Icc).mono_set
      Ioo_subset_Icc_self |>.sub hmi) hx).trans (le_of_eq ?_)
    exact integral_congr_ae (ae_of_all _ fun t ↦ abs_sub_comm _ _)
  have hNb : ∀ x ∈ Ioo x₀ x₁, |∫ t in x₀..x, m t| ≤ M := fun x hx ↦
    abs_intervalIntegral_le_integral_abs hmi hx
  have hνb : ∀ x ∈ Ioo x₀ x₁, ν x ≤ exp (M + 1) := fun x hx ↦
    exp_le_exp.2 (by linarith [neg_abs_le (∫ t in x₀..x, m t), hNb x hx])
  have hνkb : ∀ᶠ k in atTop, ∀ x ∈ Ioo x₀ x₁, νk k x ≤ exp (M + 1) := by
    filter_upwards [hη.eventually (ge_mem_nhds one_pos)] with k hk x hx
    refine exp_le_exp.2 ?_
    have h1 := hdist k x hx
    have h2 := hNb x hx
    rw [abs_le] at h1 h2
    linarith
  have hνk : ∀ x ∈ Ioo x₀ x₁, Tendsto (fun k ↦ νk k x) atTop (𝓝 (ν x)) := by
    intro x hx
    refine (continuous_exp.tendsto _).comp (tendsto_neg _ |>.comp ?_)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ hdist k x hx) hη
  -- Integrability on the interval.
  have hψm : AEStronglyMeasurable ψ μ := hψ.continuous.aestronglyMeasurable
  have hψ'm : AEStronglyMeasurable (deriv ψ) μ :=
    (hψ.continuous_deriv (by simp)).aestronglyMeasurable
  set V : ℝ → ℝ := fun x ↦ F x * deriv ψ x + (g x - m x * F x) * ψ x with hV_def
  have hVi : Integrable V μ := by
    have h1 := hFi.mul_bdd hψ'm (ae_of_all _ fun x ↦ hψ'b x)
    have h2 := (hg.sub (hm.integrable_mul hF)).mul_bdd hψm (ae_of_all _ fun x ↦ hψb x)
    exact h1.add h2
  have hνkm : ∀ k, AEStronglyMeasurable (νk k) μ := fun k ↦
    (continuous_exp.comp (contDiff_primitive (hGs k) x₀).1.continuous.neg).aestronglyMeasurable
  have hνkb' : ∀ k, ∀ᵐ x ∂μ, ‖νk k x‖ ≤ exp (∫ t in Ioo x₀ x₁, |G k t|) := by
    intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    refine exp_le_exp.2 ((neg_le_abs _).trans (abs_intervalIntegral_le_integral_abs ?_ hx))
    exact ((hGs k).continuous.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hBi : ∀ k, Integrable (fun x ↦ νk k x * ψ x * (F x * (G k x - m x))) μ := fun k ↦
    (hF.integrable_mul ((hGL2 k).sub hm)).bdd_mul ((hνkm k).mul hψm)
      (by filter_upwards [hνkb' k] with x hx
          rw [norm_mul]
          exact mul_le_mul hx (hψb x) (norm_nonneg _) (exp_pos _).le)
  have hAi : ∀ k, Integrable (fun x ↦ νk k x * V x) μ := fun k ↦
    hVi.bdd_mul (hνkm k) (hνkb' k)
  -- Testing the inequality against `ψ * νk k`.
  have hle : ∀ k, 0 ≤ ∫ x, νk k x * V x ∂μ -
      ∫ x, νk k x * ψ x * (F x * (G k x - m x)) ∂μ := by
    intro k
    obtain ⟨hNk, hNk'⟩ := contDiff_primitive (hGs k) x₀
    have hφ : ContDiff ℝ ∞ fun x ↦ ψ x * νk k x := hψ.mul hNk.neg.exp
    have hφd : ∀ x, deriv (fun x ↦ ψ x * νk k x) x =
        deriv ψ x * νk k x + ψ x * (νk k x * -G k x) := fun x ↦
      ((hψ.differentiable (by simp) x).hasDerivAt.mul (hNk' x).neg.exp).deriv
    have h0 := h _ hφ (tsupport_mul_subset_left.trans hψs)
      (fun x ↦ mul_nonneg (hψ0 x) (exp_pos _).le)
    rw [← integral_sub (hAi k) (hBi k), setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine h0.trans_eq (integral_congr_ae (ae_of_all _ fun x ↦ ?_))
      simp only [hφd, hV_def]
      ring
    · intro x hx
      have h1 : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hψs h')
      have h2 : deriv ψ x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hψs (tsupport_deriv_subset h'))
      simp [hV_def, h1, h2]
  -- The first integral converges by dominated convergence.
  have hA : Tendsto (fun k ↦ ∫ x, νk k x * V x ∂μ) atTop (𝓝 (∫ x, ν x * V x ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ exp (M + 1) * |V x|)
      (Eventually.of_forall fun k ↦ (hAi k).aestronglyMeasurable) ?_
      (hVi.abs.const_mul _) ?_
    · filter_upwards [hνkb] with k hk
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hk x hx) (abs_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hνk x hx).mul_const _
  -- The second integral tends to `0` by the Cauchy–Schwarz inequality.
  have hB : Tendsto (fun k ↦ ∫ x, νk k x * ψ x * (F x * (G k x - m x)) ∂μ) atTop (𝓝 0) := by
    set S : ℕ → ℝ := fun k ↦ ∫ x, |F x| * |G k x - m x| ∂μ
    have hS0 : ∀ k, 0 ≤ S k := fun k ↦ integral_nonneg fun _ ↦ by positivity
    have hS : Tendsto S atTop (𝓝 0) := by
      have hlim : Tendsto (fun k ↦ √((∫ x, F x ^ 2 ∂μ) * ∫ x, (m x - G k x) ^ 2 ∂μ)) atTop
          (𝓝 0) := by
        simpa using ((hL2.const_mul (∫ x, F x ^ 2 ∂μ)).sqrt)
      refine squeeze_zero hS0 (fun k ↦ ?_) hlim
      have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hF.abs
        ((hGL2 k).sub hm).abs
      simp only [Pi.abs_apply, Pi.sub_apply, sq_abs] at hcs
      refine Real.le_sqrt_of_sq_le (hcs.trans_eq ?_)
      congr 1
      exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
    have hbound : ∀ᶠ k in atTop, |∫ x, νk k x * ψ x * (F x * (G k x - m x)) ∂μ| ≤
        exp (M + 1) * Cψ * S k := by
      filter_upwards [hνkb] with k hk
      refine abs_integral_le_integral_abs.trans ?_
      rw [← integral_const_mul]
      have hI : Integrable (fun x ↦ |F x| * |G k x - m x|) μ := by
        simpa [abs_mul] using (hF.integrable_mul ((hGL2 k).sub hm)).abs
      refine integral_mono_ae (hBi k).abs (hI.const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (exp_pos _)]
      have := hk x hx
      have := hψb x
      have : 0 ≤ |F x| * |G k x - m x| := by positivity
      calc νk k x * |ψ x| * (|F x| * |G k x - m x|)
          ≤ exp (M + 1) * Cψ * (|F x| * |G k x - m x|) := by gcongr
      _ = _ := by ring
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound ?_
    simpa using hS.const_mul (exp (M + 1) * Cψ)
  exact ge_of_tendsto (by simpa using hA.sub hB) (Eventually.of_forall hle)

/-- On `Ioo x₀ x₁`, the integrating factor `x ↦ exp (-∫ t in x₀..x, m t)` of a function `m`
integrable there lies between `exp (-M)` and `exp M`, where `M = ∫ t in Ioo x₀ x₁, |m t|`. -/
private lemma exp_neg_intervalIntegral_mem_Icc {m : ℝ → ℝ} (hm : IntegrableOn m (Ioo x₀ x₁))
    {x : ℝ} (hx : x ∈ Ioo x₀ x₁) :
    exp (-∫ t in x₀..x, m t) ∈
      Icc (exp (-∫ t in Ioo x₀ x₁, |m t|)) (exp (∫ t in Ioo x₀ x₁, |m t|)) := by
  have h := abs_le.1 (abs_intervalIntegral_le_integral_abs hm hx)
  exact ⟨exp_le_exp.2 (by linarith), exp_le_exp.2 (by linarith)⟩

/-- **The weighted flux of a supersolution is almost everywhere antitone.** Let `F` and `m` be
square integrable and `g` integrable on `Ioo x₀ x₁`, and suppose `F' ≤ g` in the sense of
distributions there, that is `0 ≤ ∫ F φ' + g φ` for every nonnegative test function `φ`. With the
integrating factor `ν x = exp (-∫ t in x₀..x, m t)`, the function

`x ↦ ν x * F x - ∫ t in x₀..x, ν t * (g t - m t * F t)`

is antitone on a subset of `Ioo x₀ x₁` of full measure.

For the weak form of `-(a u' + b u)' + c u' + d u ≥ 0`, with flux `F = a u' + b u`, `g = c u' + d u`
and `m = c / a`, the drift `c u'` cancels from `g - m F = (d - c b / a) u`. -/
theorem exists_ae_mem_antitoneOn_exp_mul_sub_intervalIntegral {F g m : ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (Ioo x₀ x₁))) (hg : IntegrableOn g (Ioo x₀ x₁))
    (hm : MemLp m 2 (volume.restrict (Ioo x₀ x₁)))
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, F x * deriv φ x + g x * φ x) :
    ∃ s ⊆ Ioo x₀ x₁, (∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), x ∈ s) ∧
      AntitoneOn (fun x ↦ exp (-∫ t in x₀..x, m t) * F x -
        ∫ t in x₀..x, exp (-∫ r in x₀..t, m r) * (g t - m t * F t)) s := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hmi : IntegrableOn m (Ioo x₀ x₁) := hm.integrable one_le_two
  have hFi : IntegrableOn F (Ioo x₀ x₁) := hF.integrable one_le_two
  rcases le_or_gt x₁ x₀ with hx | hx
  · exact ⟨∅, empty_subset _, by simp [Ioo_eq_empty_of_le hx], fun _ h ↦ h.elim⟩
  set M := ∫ t in Ioo x₀ x₁, |m t|
  set ν : ℝ → ℝ := fun x ↦ exp (-∫ t in x₀..x, m t)
  have hνc : ContinuousOn ν (Icc x₀ x₁) := continuous_exp.comp_continuousOn
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hmi
      (left_mem_Icc.2 hx.le)).neg
  have hνm : AEStronglyMeasurable ν (volume.restrict (Ioo x₀ x₁)) :=
    (hνc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hνb : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), ‖ν x‖ ≤ exp M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact (exp_neg_intervalIntegral_mem_Icc hmi hx).2
  -- The weighted right-hand side `w = ν (g - m F)` and its primitive `E`.
  set w : ℝ → ℝ := fun t ↦ ν t * (g t - m t * F t) with hw_def
  have hwi : IntegrableOn w (Ioo x₀ x₁) :=
    (hg.sub (hm.integrable_mul hF)).bdd_mul hνm hνb
  set E : ℝ → ℝ := fun x ↦ ∫ t in x₀..x, w t with hE_def
  have hEc : ContinuousOn E (Icc x₀ x₁) :=
    TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hwi
      (left_mem_Icc.2 hx.le)
  have hEi : IntegrableOn E (Ioo x₀ x₁) :=
    (hEc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hEw := hasWeakLineDerivOn_intervalIntegral_left hwi
  -- The function `-(ν F - E)` has nonnegative distributional derivative.
  have hKi : IntegrableOn (fun x ↦ -(ν x * F x - E x)) (Ioo x₀ x₁) :=
    ((hFi.bdd_mul hνm hνb).sub hEi).neg
  have hder : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ ψ x) →
      ∫ x, deriv ψ x * -(ν x * F x - E x) ≤ 0 := by
    intro ψ hψ hψs hψ0
    have hψc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ)
      (hψs.trans Ioo_subset_Icc_self)
    obtain ⟨Cψ', hCψ'⟩ := (hψ.continuous_deriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
      hψc.deriv.norm
    obtain ⟨Cψ, hCψ⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hψc.norm
    have hψ'm : AEStronglyMeasurable (deriv ψ) (volume.restrict (Ioo x₀ x₁)) :=
      (hψ.continuous_deriv (by simp)).aestronglyMeasurable
    have h0 : ∀ f : ℝ → ℝ, (∀ x, x ∉ Ioo x₀ x₁ → ψ x = 0 → deriv ψ x = 0 → f x = 0) →
        ∫ x in Ioo x₀ x₁, f x = ∫ x, f x := fun f hf ↦
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ hf x hx
        (image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hψs h'))
        (image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hψs (tsupport_deriv_subset h')))
    -- Integration by parts for the primitive `E`.
    have hEparts : ∫ x, deriv ψ x * E x = -∫ x in Ioo x₀ x₁, ψ x * w x := by
      have := hEw.integral_lineDeriv_smul_eq_neg_integral_smul ⟨ψ, hψ, hψc, hψs⟩
      simp only [TauCeti.lineDeriv_one, smul_eq_mul] at this
      rw [h0 _ fun x _ hψx _ ↦ by simp [hψx]]
      exact this
    have hA := integral_exp_mul_nonneg hF hg hm h hψ hψs hψ0
    have hFi' : Integrable (fun x ↦ deriv ψ x * (ν x * F x)) (volume.restrict (Ioo x₀ x₁)) :=
      (hFi.bdd_mul hνm hνb).bdd_mul hψ'm (ae_of_all _ fun x ↦ hCψ' ⟨x, rfl⟩)
    have hEi' : Integrable (fun x ↦ deriv ψ x * E x) (volume.restrict (Ioo x₀ x₁)) :=
      hEi.bdd_mul hψ'm (ae_of_all _ fun x ↦ hCψ' ⟨x, rfl⟩)
    have hwi' : Integrable (fun x ↦ ψ x * w x) (volume.restrict (Ioo x₀ x₁)) :=
      hwi.bdd_mul hψ.continuous.aestronglyMeasurable (ae_of_all _ fun x ↦ hCψ ⟨x, rfl⟩)
    rw [← h0 _ fun x _ _ hψx ↦ by simp [hψx]] at hEparts
    rw [← h0 _ fun x _ _ hψx ↦ by simp [hψx]]
    have hsplit : ∫ x in Ioo x₀ x₁, deriv ψ x * -(ν x * F x - E x) =
        (∫ x in Ioo x₀ x₁, deriv ψ x * E x) - ∫ x in Ioo x₀ x₁, deriv ψ x * (ν x * F x) := by
      rw [← integral_sub hEi' hFi']
      exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
    have hcomb : ∫ x in Ioo x₀ x₁, ν x * (F x * deriv ψ x + (g x - m x * F x) * ψ x) =
        (∫ x in Ioo x₀ x₁, deriv ψ x * (ν x * F x)) + ∫ x in Ioo x₀ x₁, ψ x * w x := by
      rw [← integral_add hFi' hwi']
      exact integral_congr_ae (ae_of_all _ fun x ↦ by simp only [hw_def]; ring)
    rw [hsplit, hEparts]
    linarith
  obtain ⟨s, hs, hsae, hmono⟩ :=
    LocallyIntegrableOn.exists_ae_mem_monotoneOn_of_integral_deriv_mul_nonpos
      hKi.locallyIntegrableOn hder
  exact ⟨s, hs, hsae, fun x hx y hy hxy ↦ neg_le_neg_iff.1 (hmono hx hy hxy)⟩

/-- If `u'` is the weak derivative of a function `u` continuous on `Icc x₀ x₁` and `ε ≤ u'` almost
everywhere on `Ioo x₀ (x₀ + δ)`, then `u` grows at least at rate `ε` from `x₀`. -/
private lemma mul_le_sub_of_ae_le_deriv {u u' : ℝ → ℝ}
    (hu : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo x₀ x₁)) (hcont : ContinuousOn u (Icc x₀ x₁)) {ε δ : ℝ}
    (hδ : x₀ + δ ≤ x₁) (h : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), x < x₀ + δ → ε ≤ u' x)
    {t : ℝ} (ht : t ∈ Ioo 0 δ) :
    ε * t ≤ u (x₀ + t) - u x₀ := by
  have hx : x₀ ≤ x₀ + t := by linarith [ht.1]
  have htx : x₀ + t ∈ Icc x₀ x₁ := ⟨hx, by linarith [ht.2]⟩
  rw [← hu.integral_eq_sub hu' hcont EventuallyEq.rfl (left_mem_Icc.2 (hx.trans htx.2)) htx]
  have hint : IntervalIntegrable u' volume x₀ (x₀ + t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx).2
      (hu'.mono_set (Ioo_subset_Ioo_right htx.2))
  calc ε * t = ∫ _ in x₀..x₀ + t, ε := by simp; ring
    _ ≤ ∫ s in x₀..x₀ + t, u' s := by
      refine intervalIntegral.integral_mono_ae_restrict hx intervalIntegrable_const hint ?_
      rw [EventuallyLE, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo_right htx.2) h, ae_restrict_mem measurableSet_Ioo] with s hs hsI
      exact hs (by linarith [hsI.2, ht.2])

/-- If `u` is continuous on `Icc x₀ x₁`, vanishes at `x₀`, and its weak derivative is bounded
above on each `Ioo x₀ z` by `C` times any upper bound of `u` on `Icc x₀ z`, then `u ≤ 0` somewhere
in `Ioo x₀ x₁`. This is the Gronwall step of Hopf's lemma. -/
private lemma exists_le_zero_of_ae_deriv_le_mul {u u' : ℝ → ℝ} (hx : x₀ < x₁)
    (hu : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ u u' 1)
    (hu' : IntegrableOn u' (Ioo x₀ x₁)) (hcont : ContinuousOn u (Icc x₀ x₁)) (hu₀ : u x₀ = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ Ioo x₀ x₁, ∀ M, 0 ≤ M → (∀ x ∈ Icc x₀ z, u x ≤ M) →
      ∀ᵐ x ∂volume.restrict (Ioo x₀ z), u' x ≤ C * M) :
    ∃ z ∈ Ioo x₀ x₁, u z ≤ 0 := by
  -- A point `z` close enough to `x₀` that `(z - x₀) C < 1`.
  obtain ⟨δ, hδ, hδx, hδC⟩ : ∃ δ > 0, δ < x₁ - x₀ ∧ δ * C < 1 :=
    ⟨min ((x₁ - x₀) / 2) (1 / (2 * (C + 1))), lt_min (by linarith) (by positivity),
      (min_le_left _ _).trans_lt (by linarith),
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hC).trans_lt (by
        rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
        linarith)⟩
  set z := x₀ + δ
  have hz : z ∈ Ioo x₀ x₁ := ⟨by linarith, by linarith⟩
  have hsub : Icc x₀ z ⊆ Icc x₀ x₁ := Icc_subset_Icc_right hz.2.le
  -- The maximum `M` of `u` on `Icc x₀ z`, attained at `y`.
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith))
    (hcont.mono hsub)
  set M := u y
  have hM0 : 0 ≤ M := hu₀ ▸ hmax (left_mem_Icc.2 (by linarith))
  refine ⟨z, hz, (hmax (right_mem_Icc.2 (by linarith))).trans ?_⟩
  have hbound := h z hz M hM0 fun x hx ↦ hmax hx
  have hint : IntervalIntegrable u' volume x₀ y :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hy.1).2
      (hu'.mono_set (Ioo_subset_Ioo_right (hy.2.trans hz.2.le)))
  -- `M = ∫ x in x₀..y, u' x ≤ (y - x₀) C M ≤ δ C M`, which forces `M ≤ 0`.
  have hMle : M ≤ (y - x₀) * (C * M) := by
    have := hu.integral_eq_sub hu' hcont EventuallyEq.rfl (left_mem_Icc.2 hx.le) (hsub hy)
    rw [hu₀, sub_zero] at this
    refine (le_of_eq this.symm).trans ?_
    calc ∫ x in x₀..y, u' x ≤ ∫ _ in x₀..y, C * M :=
          intervalIntegral.integral_mono_ae_restrict hy.1 hint intervalIntegrable_const (by
            rw [EventuallyLE, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
            exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hy.2) hbound)
      _ = (y - x₀) * (C * M) := by simp; ring
  have : (y - x₀) * (C * M) ≤ δ * C * M := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [hy.2]) hC) hM0
  nlinarith

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval.** Let `u` be continuous
on `Icc x₀ x₁` with weak derivative `u' ∈ L²(x₀, x₁)`, and let `u` be a weak supersolution of the
divergence-form equation

`-(a u' + b u)' + c u' + d u ≥ 0` on `Ioo x₀ x₁`,

that is `0 ≤ ∫ (a u' + b u) φ' + (c u' + d u) φ` for every nonnegative test function `φ` on the
interval. Here `a` is measurable with `0 < lam ≤ a ≤ Λ`, `b` is measurable and bounded, `c` is
square integrable and `d` is integrable on the interval; no continuity of the coefficients and no
sign condition on `b`, `c` or `d` is assumed. If `u x₀ = 0` and `u > 0` on `Ioo x₀ x₁`, then `u`
leaves `x₀` at a positive linear rate: `ε t ≤ u (x₀ + t)` for some `ε > 0` and all small `t > 0`.

Square integrability of `c` is what makes the drift term `c u'` integrable for `u' ∈ L²`. -/
theorem exists_pos_mul_le_of_integral_flux_mul_deriv_add_nonneg {u u' a b c d : ℝ → ℝ}
    {lam Λ β : ℝ} (hx : x₀ < x₁) (hu : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ u u' 1)
    (hu' : MemLp u' 2 (volume.restrict (Ioo x₀ x₁))) (hcont : ContinuousOn u (Icc x₀ x₁))
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁))) (hlam : 0 < lam)
    (haΛ : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), lam ≤ a x ∧ a x ≤ Λ)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hbβ : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), |b x| ≤ β)
    (hc : MemLp c 2 (volume.restrict (Ioo x₀ x₁))) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, (a x * u' x + b x * u x) * deriv φ x + (c x * u' x + d x * u x) * φ x)
    (hu₀ : u x₀ = 0) (hpos : ∀ x ∈ Ioo x₀ x₁, 0 < u x) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u (x₀ + t) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by simp [hx])
  have hu'i : IntegrableOn u' (Ioo x₀ x₁) := hu'.integrable one_le_two
  -- `u` is bounded and measurable on the interval.
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hum : AEStronglyMeasurable u (volume.restrict (Ioo x₀ x₁)) :=
    (hcont.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hUb : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), ‖u x‖ ≤ U := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hU x (Ioo_subset_Icc_self hx)
  -- The flux `F`, the right-hand side `g` and the integrating exponent `m = c / a`.
  set F : ℝ → ℝ := fun x ↦ a x * u' x + b x * u x with hF_def
  set g : ℝ → ℝ := fun x ↦ c x * u' x + d x * u x with hg_def
  set m : ℝ → ℝ := fun x ↦ c x / a x with hm_def
  have hF : MemLp F 2 (volume.restrict (Ioo x₀ x₁)) := by
    refine MemLp.add (hu'.of_le_mul (ha.mul hu'.aestronglyMeasurable) (c := Λ) ?_)
      (MemLp.of_bound (hb.mul hum) (β * U) ?_)
    · filter_upwards [haΛ] with x hx
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hlam.trans_le hx.1)]
      exact mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _)
    · filter_upwards [hbβ, hUb] with x hbx hux
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul hbx hux (norm_nonneg _) ((abs_nonneg _).trans hbx)
  have hg : IntegrableOn g (Ioo x₀ x₁) := (hc.integrable_mul hu').add (hd.mul_bdd hum hUb)
  have hm : MemLp m 2 (volume.restrict (Ioo x₀ x₁)) := by
    refine hc.of_le_mul (hc.aemeasurable.div ha.aemeasurable).aestronglyMeasurable (c := lam⁻¹) ?_
    filter_upwards [haΛ] with x hx
    rw [norm_div, Real.norm_eq_abs (a x), abs_of_pos (hlam.trans_le hx.1), div_eq_mul_inv,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hlam hx.1) (norm_nonneg _)
  have hmi : IntegrableOn m (Ioo x₀ x₁) := hm.integrable one_le_two
  obtain ⟨s, hs, hsae, hanti⟩ := exists_ae_mem_antitoneOn_exp_mul_sub_intervalIntegral hF hg hm
    (by simpa only [hF_def, hg_def] using hsuper)
  -- The integrating factor `ν`, the weighted right-hand side `w` and its primitive `E`.
  set Mm := ∫ t in Ioo x₀ x₁, |m t|
  set ν : ℝ → ℝ := fun x ↦ exp (-∫ t in x₀..x, m t)
  have hν : ∀ x ∈ Ioo x₀ x₁, ν x ∈ Icc (exp (-Mm)) (exp Mm) := fun x hx ↦
    exp_neg_intervalIntegral_mem_Icc hmi hx
  set w : ℝ → ℝ := fun t ↦ ν t * (g t - m t * F t) with hw_def
  set E : ℝ → ℝ := fun x ↦ ∫ t in x₀..x, w t with hE_def
  set K : ℝ → ℝ := fun x ↦ ν x * F x - E x with hK_def
  have hνm : AEStronglyMeasurable ν (volume.restrict (Ioo x₀ x₁)) :=
    ((continuous_exp.comp_continuousOn
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hmi
      (left_mem_Icc.2 hx.le)).neg).mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hwi : IntegrableOn w (Ioo x₀ x₁) := (hg.sub (hm.integrable_mul hF)).bdd_mul hνm
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact (hν x hx).2)
  have hEc : ContinuousOn E (Icc x₀ x₁) :=
    TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hwi
      (left_mem_Icc.2 hx.le)
  -- The ellipticity constants satisfy `0 < lam ≤ Λ`.
  have hΛ : 0 < Λ := by
    obtain ⟨x, hx⟩ := haΛ.exists
    linarith [hx.1, hx.2]
  by_cases hcase : ∃ y ∈ s, 0 < K y
  · -- The weighted flux is positive somewhere: then it is bounded below near `x₀`, and so is `u'`.
    obtain ⟨y, hys, hκ⟩ := hcase
    obtain ⟨δ₁, hδ₁, hE⟩ := Metric.continuousWithinAt_iff.1 (hEc x₀ (left_mem_Icc.2 hx.le))
      (K y / 2) (half_pos hκ)
    set p := K y / (2 * exp Mm)
    have hp : 0 < p := by positivity
    obtain ⟨δ₂, hδ₂, hus⟩ := Metric.continuousWithinAt_iff.1 (hcont x₀ (left_mem_Icc.2 hx.le))
      (p / (2 * (|β| + 1))) (by positivity)
    have hy := hs hys
    refine ⟨p / (2 * Λ), by positivity, min (min δ₁ δ₂) (y - x₀),
      lt_min (lt_min hδ₁ hδ₂) (by linarith [hy.1]), fun t ht ↦ ?_⟩
    have := mul_le_sub_of_ae_le_deriv (ε := p / (2 * Λ)) hu hu'i hcont
      (by linarith [min_le_right (min δ₁ δ₂) (y - x₀), hy.2]) ?_ ht
    · rwa [hu₀, sub_zero] at this
    filter_upwards [hsae, haΛ, hbβ] with x hxs hax hbx hxδ
    have hxI := hs hxs
    have hxy : x ≤ y := by linarith [min_le_right (min δ₁ δ₂) (y - x₀)]
    have hdist : dist x x₀ < min δ₁ δ₂ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hxI.1])]
      linarith [min_le_left (min δ₁ δ₂) (y - x₀)]
    have hxIcc : x ∈ Icc x₀ x₁ := Ioo_subset_Icc_self hxI
    -- `ν F = K + E ≥ K y / 2`, so `F ≥ p`.
    have hKx : K y ≤ K x := hanti hxs hys hxy
    have hEx : |E x| < K y / 2 := by
      simpa [hE_def, Real.dist_eq] using hE hxIcc (hdist.trans_le (min_le_left _ _))
    have hνx := hν x hxI
    have hνF : K y / 2 ≤ ν x * F x := by
      have : ν x * F x = K x + E x := by simp [hK_def]
      linarith [(abs_lt.1 hEx).1]
    have hFp : p ≤ F x := by
      by_contra hlt
      rw [not_le] at hlt
      have h1 : ν x * F x < exp Mm * p := by
        rcases le_or_gt 0 (F x) with h0 | h0
        · calc ν x * F x ≤ exp Mm * F x := mul_le_mul_of_nonneg_right hνx.2 h0
            _ < exp Mm * p := mul_lt_mul_of_pos_left hlt (exp_pos _)
        · calc ν x * F x < 0 := mul_neg_of_pos_of_neg (exp_pos _) h0
            _ < exp Mm * p := by positivity
      have h2 : exp Mm * p = K y / 2 := by
        simp only [p]
        field_simp
      linarith
    -- `b u ≤ p / 2` near `x₀`, so `a u' ≥ p / 2` and `u' ≥ p / (2 Λ)`.
    have hux : |u x| < p / (2 * (|β| + 1)) := by
      simpa [hu₀, Real.dist_eq] using hus hxIcc (hdist.trans_le (min_le_right _ _))
    have hbu : b x * u x ≤ p / 2 := by
      have hβ0 : 0 ≤ |β| := abs_nonneg _
      calc b x * u x ≤ |b x| * |u x| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ |β| * (p / (2 * (|β| + 1))) :=
            mul_le_mul (hbx.trans (le_abs_self _)) hux.le (abs_nonneg _) hβ0
        _ ≤ p / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
            nlinarith
    have hau : p / 2 ≤ a x * u' x := by
      have : F x = a x * u' x + b x * u x := rfl
      linarith
    have ha0 : 0 < a x := hlam.trans_le hax.1
    have hu'0 : 0 < u' x := pos_of_mul_pos_right (by linarith) ha0.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hax.2]
  · -- The weighted flux is nonpositive almost everywhere: a Gronwall argument shows `u = 0` near
    -- `x₀`, contradicting `u > 0`.
    simp only [not_exists, not_and, not_lt] at hcase
    -- The zeroth-order coefficient `e` left after the drift cancels: `g - m F = e u`.
    set e : ℝ → ℝ := fun x ↦ d x - m x * b x with he_def
    have hei : IntegrableOn e (Ioo x₀ x₁) := hd.sub (hmi.mul_bdd hb hbβ)
    have hgmF : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), g x - m x * F x = e x * u x := by
      filter_upwards [haΛ] with x hx
      have ha0 : a x ≠ 0 := (hlam.trans_le hx.1).ne'
      simp only [hg_def, hm_def, hF_def, he_def]
      field_simp
      ring
    set Me := ∫ t in Ioo x₀ x₁, |e t|
    have hMe : 0 ≤ Me := integral_nonneg fun _ ↦ abs_nonneg _
    -- The primitive `E` is bounded by `exp Mm * M * Me` on `Ioo x₀ z` if `u ≤ M` there.
    have hEb : ∀ z ∈ Ioo x₀ x₁, ∀ M, 0 ≤ M → (∀ x ∈ Icc x₀ z, u x ≤ M) → ∀ x ∈ Ioo x₀ z,
        |E x| ≤ exp Mm * M * Me := by
      intro z hz M hM0 hM x hx
      have hxI : x ∈ Ioo x₀ x₁ := ⟨hx.1, hx.2.trans hz.2⟩
      have hsub : Ioc x₀ x ⊆ Ioo x₀ x₁ := Ioc_subset_Ioo_right hxI.2
      simp only [hE_def]
      rw [intervalIntegral.integral_of_le hx.1.le]
      calc |∫ t in Ioc x₀ x, w t| ≤ ∫ t in Ioc x₀ x, |w t| := abs_integral_le_integral_abs
        _ ≤ ∫ t in Ioc x₀ x, exp Mm * M * |e t| := by
          refine integral_mono_ae (hwi.mono_set hsub).abs
            ((hei.mono_set hsub).abs.const_mul _) ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hgmF,
            ae_restrict_mem measurableSet_Ioc] with t ht htI
          have htI' := hsub htI
          have hut : |u t| ≤ M := by
            rw [abs_of_pos (hpos t htI')]
            exact hM t ⟨htI.1.le, htI.2.trans hx.2.le⟩
          simp only [hw_def, ht, abs_mul, abs_of_pos (show 0 < ν t from exp_pos _)]
          calc ν t * (|e t| * |u t|) ≤ exp Mm * (|e t| * M) := by
                gcongr
                exact (hν t htI').2
            _ = exp Mm * M * |e t| := by ring
        _ = exp Mm * M * ∫ t in Ioc x₀ x, |e t| := integral_const_mul _ _
        _ ≤ exp Mm * M * Me := mul_le_mul_of_nonneg_left (setIntegral_mono_set hei.abs
            (ae_of_all _ fun _ ↦ abs_nonneg _) hsub.eventuallyLE) (by positivity)
    have hder : ∀ z ∈ Ioo x₀ x₁, ∀ M, 0 ≤ M → (∀ x ∈ Icc x₀ z, u x ≤ M) →
        ∀ᵐ x ∂volume.restrict (Ioo x₀ z), u' x ≤ (exp Mm * exp Mm * Me + |β|) / lam * M := by
      intro z hz M hM0 hM
      have hsub : Ioo x₀ z ⊆ Ioo x₀ x₁ := Ioo_subset_Ioo_right hz.2.le
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsae,
        ae_restrict_of_ae_restrict_of_subset hsub haΛ,
        ae_restrict_of_ae_restrict_of_subset hsub hbβ,
        ae_restrict_mem measurableSet_Ioo] with x hxs hax hbx hxz
      have hxI := hs hxs
      have hνx := hν x hxI
      have hux0 : 0 ≤ u x := (hpos x hxI).le
      have huxM : u x ≤ M := hM x ⟨hxz.1.le, hxz.2.le⟩
      -- `ν F = K + E ≤ |E|`, so `F ≤ exp Mm * |E|`.
      have hνF : ν x * F x ≤ exp Mm * M * Me := by
        have h1 : ν x * F x = K x + E x := by simp [hK_def]
        linarith [hcase x hxs, le_abs_self (E x), hEb z hz M hM0 hM x hxz]
      have hFx : F x ≤ exp Mm * (exp Mm * M * Me) := by
        rcases le_or_gt (F x) 0 with h0 | h0
        · exact h0.trans (by positivity)
        · have h2 : exp (-Mm) * F x ≤ ν x * F x := mul_le_mul_of_nonneg_right hνx.1 h0.le
          have h3 : exp Mm * exp (-Mm) = 1 := by rw [← exp_add]; simp
          nlinarith [exp_pos Mm]
      -- Hence `a u' = F - b u ≤ (exp Mm * exp Mm * Me + |β|) M` and `u' ≤ C M`.
      have hau : a x * u' x ≤ (exp Mm * exp Mm * Me + |β|) * M := by
        have hF' : F x = a x * u' x + b x * u x := rfl
        have hbu : -(b x * u x) ≤ |β| * M := by
          calc -(b x * u x) ≤ |b x| * |u x| := by rw [← abs_mul]; exact neg_le_abs _
            _ ≤ |β| * M := mul_le_mul (hbx.trans (le_abs_self _))
                (by rwa [abs_of_nonneg hux0]) (abs_nonneg _) (abs_nonneg _)
        nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
      rcases le_or_gt (u' x) 0 with h0 | h0
      · nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ exp Mm * exp Mm * Me + |β|) hM0]
      · nlinarith [hax.1]
    obtain ⟨z, hz, hz0⟩ := exists_le_zero_of_ae_deriv_le_mul hx hu hu'i hcont hu₀
      (by positivity) hder
    exact absurd hz0 (not_le.2 (hpos z hz))

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval, derivative form.** Under
the hypotheses of `exists_pos_mul_le_of_integral_flux_mul_deriv_add_nonneg`, if `u` has a right
derivative `D` at `x₀`, then `D > 0`. -/
theorem pos_of_hasDerivWithinAt_of_integral_flux_mul_deriv_add_nonneg {u u' a b c d : ℝ → ℝ}
    {lam Λ β : ℝ} (hx : x₀ < x₁) (hu : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ u u' 1)
    (hu' : MemLp u' 2 (volume.restrict (Ioo x₀ x₁))) (hcont : ContinuousOn u (Icc x₀ x₁))
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁))) (hlam : 0 < lam)
    (haΛ : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), lam ≤ a x ∧ a x ≤ Λ)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hbβ : ∀ᵐ x ∂volume.restrict (Ioo x₀ x₁), |b x| ≤ β)
    (hc : MemLp c 2 (volume.restrict (Ioo x₀ x₁))) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo x₀ x₁ → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, (a x * u' x + b x * u x) * deriv φ x + (c x * u' x + d x * u x) * φ x)
    (hu₀ : u x₀ = 0) (hpos : ∀ x ∈ Ioo x₀ x₁, 0 < u x) {D : ℝ}
    (hD : HasDerivWithinAt u D (Ioi x₀) x₀) :
    0 < D := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_pos_mul_le_of_integral_flux_mul_deriv_add_nonneg hx hu hu'
    hcont ha hlam haΛ hb hbβ hc hd hsuper hu₀ hpos
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp hD
  rw [sdiff_singleton_eq_self (by simp)] at hslope
  refine hε.trans_le (ge_of_tendsto hslope ?_)
  -- For `x₀ < t < x₀ + δ` the slope at `x₀` is at least `ε`.
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right x₀ hδ)] with t ht
  have h' := h (t - x₀) ⟨sub_pos.2 ht.1, by linarith [ht.2]⟩
  rw [add_sub_cancel] at h'
  rw [slope_def_field, hu₀, sub_zero, le_div_iff₀ (sub_pos.2 ht.1)]
  exact h'

end TauCeti.PDE
