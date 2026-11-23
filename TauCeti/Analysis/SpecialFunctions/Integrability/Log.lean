/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.Log.InvLog

/-!
# Integrability of logarithms

On a finite-dimensional real normed space with an additive Haar measure, every natural power
`x ↦ (log ‖x‖) ^ k` is locally integrable. Its only singularity is at the origin, where it is
dominated by a multiple of `‖x‖ ^ (-1 / 2)`, which is locally integrable in every positive
dimension. In the plane, for `k = 1`, this is the local integrability of the logarithmic
fundamental solution of the Laplacian. On the real line it says that `t ↦ (log t) ^ k` is interval
integrable, as needed for the logarithmic radial integrals defining the polylogarithms.

The principal complex logarithm of a real-meromorphic function `f : ℝ → ℂ` is interval integrable,
even across zeros and poles of `f`: its real part is Mathlib's interval integrable `log ‖f‖` and its
imaginary part is bounded by `π`. For the affine family `t ↦ Log (1 - t z)` as `z` varies over a
bounded set `‖z‖ ≤ R`, translating `log |t - Re(z⁻¹)|` yields a uniform `L^k` bound on every
bounded interval `(a, b]`, even though the singularity `t = z⁻¹` moves.

On the half-line `[1, ∞)` the iterated logarithm `t ↦ log (log t)` is locally integrable as well:
its singularity at `t = 1` is integrable, by Mathlib's `Real.integrableOn_log_log_mul_rpow`. This
is the integrability that Abelian arguments against `log log t` need, as in Mertens' theorems.

Near the origin, for `R < c`, every power of the radial profile `log log (c / r)` is integrable on
`(0, R)`, since `|log log (c / r)|` grows at most like `|log r|`, and so is
`(r (log (c / r))^p)⁻¹` for `p > 1`, the derivative of `r ↦ ((p - 1) (log (c / r))^(p - 1))⁻¹`,
which is continuous on `[0, R]`. Against the planar polar weight `r dr` these give the radial
integrals behind the unbounded `W^{1,2}` functions `log log (c / ‖z‖)` of the plane: the square
of the profile and the square of its derivative `-(r log (c / r))⁻¹`.

## Main declarations

* `TauCeti.locallyIntegrable_log_norm_pow`: `x ↦ (log ‖x‖) ^ k` is locally integrable.
* `TauCeti.locallyIntegrable_log_norm`: `x ↦ log ‖x‖` is locally integrable.
* `TauCeti.intervalIntegrable_log_pow`: `t ↦ (log t) ^ k` is interval integrable.
* `TauCeti.integrable_log_abs_sub_restrict_Icc_prod`: `(x, y) ↦ log |x - y|` is integrable
  on bounded rectangles.
* `MeromorphicOn.intervalIntegrable_clog`: `t ↦ Log (f t)` is interval integrable for
  real-meromorphic `f : ℝ → ℂ`; `AnalyticOnNhd.intervalIntegrable_clog` is the analytic case.
* `TauCeti.setLIntegral_abs_log_abs_sub_pow_le`,
  `TauCeti.setLIntegral_norm_clog_one_sub_mul_pow_le`, and
  `TauCeti.exists_setLIntegral_norm_clog_one_sub_mul_pow_le`: uniform `L^k` bounds for translated
  real logarithms and for `t ↦ Log (1 - t z)` on `(a, b]` over bounded `z`.
* `TauCeti.locallyIntegrableOn_log_log`: `t ↦ log (log t)` is locally integrable on `[1, ∞)`.
* `TauCeti.integrableOn_log_log_const_div_pow`: `(log log (c / r))^k` is integrable on `(0, R)`.
* `TauCeti.integrableOn_inv_mul_log_const_div_rpow`: `(r (log (c / r))^p)⁻¹`, `p > 1`, is
  integrable on `(0, R)`.
* `TauCeti.integrableOn_mul_log_log_const_div_sq`,
  `TauCeti.integrableOn_mul_inv_mul_log_const_div_sq`: the planar radial integrands
  `r (log log (c / r))²` and `r (r log (c / r))⁻²` are integrable on `(0, R)`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.3 (the example `log log (1 / |x|)` of an
  unbounded `W^{1,n}` function).
-/

public section

namespace TauCeti

open MeasureTheory
open scoped Topology

/-- On a finite-dimensional real normed space with an additive Haar measure, every natural power
`x ↦ (log ‖x‖) ^ k` is locally integrable. -/
theorem locallyIntegrable_log_norm_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] (k : ℕ) :
    LocallyIntegrable (fun x : E ↦ Real.log ‖x‖ ^ k) μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simpa [norm_of_subsingleton] using locallyIntegrable_const (μ := μ) ((0 : ℝ) ^ k)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using locallyIntegrable_const (μ := μ) (1 : ℝ)
  -- With `ε = 1 / (2 k)` we have `|log ‖x‖| ≤ ‖x‖ ^ (-ε) / ε + ‖x‖`, hence
  -- `|log ‖x‖| ^ k ≤ 2 ^ (k - 1) * ((2 k) ^ k * ‖x‖ ^ (-1 / 2) + ‖x‖ ^ k)`.
  set ε : ℝ := 1 / (2 * k) with hε_def
  have hε : 0 < ε := by positivity
  have hpow : LocallyIntegrable
      (fun x : E ↦ 2 ^ (k - 1) * (2 * k : ℝ) ^ k * ‖x‖ ^ (-(1 / 2 : ℝ))) μ :=
    locallyIntegrable_of_norm_le_rpow (C := 2 ^ (k - 1) * (2 * k : ℝ) ^ k) (α := 1 / 2)
      Module.finrank_pos
      (by linarith [(Nat.one_le_cast (α := ℝ)).2 (Module.finrank_pos (R := ℝ) (M := E))])
      (.of_forall fun x ↦ by rw [Real.norm_of_nonneg (by positivity)])
      (by fun_prop : Measurable _).aestronglyMeasurable
  have hpoly : LocallyIntegrable (fun x : E ↦ 2 ^ (k - 1) * ‖x‖ ^ k) μ :=
    (by fun_prop : Continuous fun x : E ↦ (2 : ℝ) ^ (k - 1) * ‖x‖ ^ k).locallyIntegrable
  refine (hpow.add hpoly).mono
    (by fun_prop : Measurable fun x : E ↦ Real.log ‖x‖ ^ k).aestronglyMeasurable
    (.of_forall fun x ↦ ?_)
  have hx := norm_nonneg x
  have hlog : |Real.log ‖x‖| ≤ ‖x‖ ^ (-ε) / ε + ‖x‖ := by
    have hlow := Real.neg_rpow_div_le_log hx hε
    rw [neg_div] at hlow
    rw [abs_le]
    constructor <;> linarith [Real.log_le_self hx, div_nonneg (Real.rpow_nonneg hx (-ε)) hε.le]
  have hrpow : (‖x‖ ^ (-ε) / ε) ^ k = (2 * k : ℝ) ^ k * ‖x‖ ^ (-(1 / 2 : ℝ)) := by
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [div_pow, ← Real.rpow_natCast (‖x‖ ^ (-ε)) k, ← Real.rpow_mul hx, hε_def, one_div,
      inv_pow, div_inv_eq_mul, mul_comm]
    congr 2
    field_simp
  rw [norm_pow, Real.norm_eq_abs, Pi.add_apply, Real.norm_of_nonneg (by positivity)]
  calc |Real.log ‖x‖| ^ k ≤ (‖x‖ ^ (-ε) / ε + ‖x‖) ^ k := pow_le_pow_left₀ (abs_nonneg _) hlog k
    _ ≤ 2 ^ (k - 1) * ((‖x‖ ^ (-ε) / ε) ^ k + ‖x‖ ^ k) := add_pow_le (by positivity) hx k
    _ = _ := by rw [hrpow]; ring

/-- The singular part of the logarithmic kernel is square integrable over the whole space.
It is supported on the closed unit ball. -/
theorem memLp_two_posLog_inv_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] : MemLp (fun z : E ↦ Real.posLog ‖z‖⁻¹) 2 μ := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  have hloc := locallyIntegrable_log_norm_pow (E := E) (μ := μ) 2
  have h := hloc.integrableOn_isCompact (isCompact_closedBall 0 1)
  rw [← integrable_indicator_iff measurableSet_closedBall] at h
  convert h using 1
  funext z
  rw [Real.posLog_apply, Real.log_inv]
  by_cases hz : ‖z‖ ≤ 1
  · rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hz),
      max_eq_right (neg_nonneg.mpr (Real.log_nonpos (norm_nonneg z) hz)), neg_sq]
  · rw [Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_zero_right] using hz),
      max_eq_left (neg_nonpos.mpr (Real.log_nonneg (le_of_not_ge hz))), zero_pow (by decide)]

/-- On a finite-dimensional real normed space with an additive Haar measure, `x ↦ log ‖x‖` is
locally integrable. -/
theorem locallyIntegrable_log_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] :
    LocallyIntegrable (fun x : E ↦ Real.log ‖x‖) μ := by
  simpa using locallyIntegrable_log_norm_pow (μ := μ) 1

/-- Every natural power `t ↦ (log t) ^ k` of the real logarithm is interval integrable on every
interval. For `k = 1` this is Mathlib's `intervalIntegrable_log'`. -/
theorem intervalIntegrable_log_pow (k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ Real.log t ^ k) volume a b := by
  simpa [Real.norm_eq_abs, Real.log_abs] using
    ((locallyIntegrable_log_norm_pow (E := ℝ) (μ := volume) k).integrableOn_isCompact
      (isCompact_uIcc (a := a) (b := b))).intervalIntegrable

/-- The logarithmic interaction `(x, y) ↦ log |x - y|` is Lebesgue integrable on every
product of two closed bounded real intervals. -/
theorem integrable_log_abs_sub_restrict_Icc_prod (a b c d : ℝ) :
    Integrable (fun z : ℝ × ℝ ↦ Real.log |z.1 - z.2|)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) := by
  let ν : Measure ℝ := volume.restrict (Set.Icc c d)
  let g := (Set.Icc (a - d) (b - c)).indicator Real.log
  have hgOn : IntegrableOn Real.log (Set.Icc (a - d) (b - c)) volume := by
    simpa only [Real.norm_eq_abs, Real.log_abs] using
      (locallyIntegrable_log_norm (E := ℝ) (μ := volume)).integrableOn_isCompact
        (isCompact_Icc (a := a - d) (b := b - c))
  have hg : Integrable g volume := hgOn.integrable_indicator measurableSet_Icc
  have hprod : Integrable (fun z : ℝ × ℝ ↦ g z.2) (ν.prod volume) := hg.comp_snd ν
  have hsub : Integrable (fun z : ℝ × ℝ ↦ g (z.1 - z.2)) (volume.prod ν) :=
    ((measurePreserving_prod_sub_swap volume ν).integrable_comp hprod.aestronglyMeasurable).mpr
      hprod
  refine (hsub.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)).congr ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with z hz
  rcases hz with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  have hz' : z.1 - z.2 ∈ Set.Icc (a - d) (b - c) :=
    ⟨sub_le_sub hx₁ hy₂, sub_le_sub hx₂ hy₁⟩
  simp only [g, Set.indicator_of_mem hz', Real.log_abs]

/-- The principal complex logarithm of a real-meromorphic function `f : ℝ → ℂ` is interval
integrable, even across zeros and poles of `f`: its real part `log ‖f‖` has only integrable
logarithmic singularities, and its imaginary part `arg f` is bounded by `π`. -/
theorem _root_.MeromorphicOn.intervalIntegrable_clog {f : ℝ → ℂ} {a b : ℝ}
    (hf : MeromorphicOn f (Set.uIcc a b)) :
    IntervalIntegrable (fun t ↦ Complex.log (f t)) volume a b := by
  -- `f` is continuous off the countable, hence null, set `S` of its non-analytic points.
  set S := {t | AnalyticAt ℝ f t}ᶜ ∩ Set.uIcc a b
  have hS : S.Countable := hf.countable_compl_analyticAt_inter
  have hcont : ContinuousOn f (Set.uIoc a b \ S) := fun t ht ↦
    (of_not_not fun h ↦ ht.2 ⟨h, Set.uIoc_subset_uIcc ht.1⟩ :
      AnalyticAt ℝ f t).continuousAt.continuousWithinAt
  have hmeas :
      AEStronglyMeasurable (fun t ↦ Complex.log (f t)) (volume.restrict (Set.uIoc a b)) := by
    rw [← Measure.restrict_congr_set (sdiff_null_ae_eq_self (hS.measure_zero volume))]
    exact (Complex.measurable_log.comp_aemeasurable
      (hcont.aemeasurable (measurableSet_uIoc.diff hS.measurableSet))).aestronglyMeasurable
  refine (hf.intervalIntegrable_log_norm.norm.add
    (intervalIntegrable_const (c := Real.pi))).mono_fun' hmeas (.of_forall fun t ↦ ?_)
  calc ‖Complex.log (f t)‖ ≤ |(Complex.log (f t)).re| + |(Complex.log (f t)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ‖Real.log ‖f t‖‖ + Real.pi := by
        rw [Complex.log_re, Complex.log_im, Real.norm_eq_abs]
        gcongr
        exact Complex.abs_arg_le_pi _

/-- The principal complex logarithm of a real-analytic function `f : ℝ → ℂ` is interval
integrable, even across zeros of `f`. This is the analytic case of
`MeromorphicOn.intervalIntegrable_clog`. -/
theorem _root_.AnalyticOnNhd.intervalIntegrable_clog {f : ℝ → ℂ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Set.uIcc a b)) :
    IntervalIntegrable (fun t ↦ Complex.log (f t)) volume a b :=
  hf.meromorphicOn.intervalIntegrable_clog

/-- Translating by `s ∈ [c, d]` bounds the Lebesgue integral of `|log |t - s|| ^ k` over `(a, b]`
by the integral of `|log ‖u‖| ^ k` over `[a - d, b - c]`. -/
theorem setLIntegral_abs_log_abs_sub_pow_le (k : ℕ) {a b c d s : ℝ} (hs : s ∈ Set.Icc c d) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (|Real.log (|t - s|)| ^ k) ≤
      ∫⁻ u in Set.Icc (a - d) (b - c), ENNReal.ofReal (|Real.log ‖u‖| ^ k) := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Icc,
    ← lintegral_add_right_eq_self
      ((Set.Icc (a - d) (b - c)).indicator fun u ↦ ENNReal.ofReal (|Real.log ‖u‖| ^ k)) (-s)]
  refine lintegral_mono fun t ↦ ?_
  by_cases ht : t ∈ Set.Ioc a b
  · have hmem : t - s ∈ Set.Icc (a - d) (b - c) :=
      ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩
    rw [Set.indicator_of_mem ht, ← sub_eq_add_neg, Set.indicator_of_mem hmem, Real.norm_eq_abs]
  · simp [ht]

/-- On `(a, b]`, when `0 < r ≤ ‖z‖ ≤ R`, shifting by `Re(z⁻¹) ∈ [-r⁻¹, r⁻¹]` bounds the `L^k`
integral of `t ↦ Complex.log (1 - t * z)` uniformly in `z`. -/
theorem setLIntegral_norm_clog_one_sub_mul_pow_le (k : ℕ) (a b : ℝ) {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hzr : r ≤ ‖z‖) (hzR : ‖z‖ ≤ R) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ k) ≤
      ENNReal.ofReal
        ((2 : ℝ) ^ (k - 1) *
          (Real.log (1 + max |a| |b| * R) + |Real.log r| + Real.log (1 + R) + Real.pi) ^ k) *
          volume (Set.Ioc a b) +
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) *
          ∫⁻ u in Set.Icc (a - r⁻¹) (b + r⁻¹), ENNReal.ofReal (|Real.log ‖u‖| ^ k) := by
  have hz_pos : 0 < ‖z‖ := hr.trans_le hzr
  have : 0 ≤ R := hz_pos.le.trans hzR
  set T : ℝ := max |a| |b|
  have hT : 0 ≤ T := le_max_of_le_left (abs_nonneg a)
  set M : ℝ := Real.log (1 + T * R) + |Real.log r| + Real.log (1 + R) + Real.pi
  have hM0 : 0 ≤ M := by
    linarith [Real.two_le_pi,
      Real.log_nonneg (by linarith [mul_nonneg hT this] : (1 : ℝ) ≤ 1 + T * R),
      abs_nonneg (Real.log r), Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + R)]
  have hs : (z⁻¹).re ∈ Set.Icc (-r⁻¹) r⁻¹ := by
    rw [Set.mem_Icc, ← abs_le]
    exact (Complex.abs_re_le_norm z⁻¹).trans ((norm_inv z).trans_le (inv_anti₀ hr hzr))
  have hlogz : |Real.log ‖z‖| ≤ |Real.log r| + Real.log (1 + R) := by
    have hlow := Real.log_le_log hr hzr
    have hhigh := Real.log_le_log hz_pos (by linarith : ‖z‖ ≤ 1 + R)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log r), abs_nonneg (Real.log r),
      Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + R)]
  have hae : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc a b),
      ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ k) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * M ^ k) +
          ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) *
            ENNReal.ofReal (|Real.log (|t - (z⁻¹).re|)| ^ k) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume (z⁻¹).re)] with t ht hts
    have htT : |t| ≤ T := abs_le_max_abs_abs ht.1.le ht.2
    have hlogt : Real.log (1 + |t| * ‖z‖) ≤ Real.log (1 + T * R) :=
      Real.log_le_log (by positivity) (by linarith [mul_le_mul htT hzR hz_pos.le hT])
    have hbound : ‖Complex.log (1 - t * z)‖ ≤ M + |Real.log (|t - (z⁻¹).re|)| :=
      (Complex.norm_log_one_sub_ofReal_mul_le z hts).trans (by linarith)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal <| (pow_le_pow_left₀ (norm_nonneg _) hbound k).trans <| by
      simpa [mul_add] using add_pow_le hM0 (abs_nonneg _) k
  refine (lintegral_mono_ae hae).trans ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
    lintegral_const_mul _ (by fun_prop)]
  gcongr _ + _ * ?_
  have hsub := setLIntegral_abs_log_abs_sub_pow_le k (a := a) (b := b) hs
  rwa [sub_neg_eq_add] at hsub

open scoped ENNReal in
/-- Over any bounded ball `‖z‖ ≤ R`, every natural power `‖Complex.log (1 - t * z)‖ ^ k` has a
uniform finite Lebesgue integral on `(a, b]` independent of `z`. -/
theorem exists_setLIntegral_norm_clog_one_sub_mul_pow_le (k : ℕ) (a b R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ z : ℂ, ‖z‖ ≤ R →
      ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ k) ≤ C := by
  set T : ℝ := max |a| |b|
  have hT : 0 ≤ T := le_max_of_le_left (abs_nonneg a)
  set R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right R 0
  set r : ℝ := (2 * (T + 1))⁻¹ with hr_def
  have hr : 0 < r := by positivity
  set M : ℝ := Real.log (1 + T * R') + |Real.log r| + Real.log (1 + R') + Real.pi
  have hM : 1 ≤ M := by
    linarith [Real.two_le_pi,
      Real.log_nonneg (by linarith [mul_nonneg hT hR'] : (1 : ℝ) ≤ 1 + T * R'),
      abs_nonneg (Real.log r), Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + R')]
  set I : ℝ≥0∞ := ∫⁻ u in Set.Icc (a - r⁻¹) (b + r⁻¹), ENNReal.ofReal (|Real.log ‖u‖| ^ k)
  have hI : I < ∞ := lt_of_le_of_lt
    (lintegral_mono fun u ↦ le_of_eq <| by
      rw [← ofReal_norm, norm_pow, Real.norm_eq_abs (Real.log _)])
    ((locallyIntegrable_log_norm_pow (E := ℝ) (μ := volume) k).integrableOn_isCompact
      isCompact_Icc).hasFiniteIntegral
  have hvol : volume (Set.Ioc a b) < ∞ := by simp [Real.volume_Ioc]
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * M ^ k) * volume (Set.Ioc a b) +
      ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) * I,
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne⟩, fun z hz ↦ ?_⟩
  rcases le_or_gt ‖z‖ r with hsmall | hlarge
  · refine (setLIntegral_mono' measurableSet_Ioc
        (g := fun _ ↦ ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * M ^ k)) fun t ht ↦ ?_).trans ?_
    · have htT : |t| ≤ T := abs_le_max_abs_abs ht.1.le ht.2
      have htz : ‖-((t : ℂ) * z)‖ ≤ 1 / 2 := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine (mul_le_mul htT hsmall (norm_nonneg z) hT).trans ?_
        rw [hr_def, ← one_div, mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      have hlog : ‖Complex.log (1 - t * z)‖ ≤ M := by
        have h := Complex.norm_log_one_add_half_le_self (z := -((t : ℂ) * z)) htz
        rw [← sub_eq_add_neg] at h
        linarith [norm_nonneg (-((t : ℂ) * z))]
      exact ENNReal.ofReal_le_ofReal <| (pow_le_pow_left₀ (norm_nonneg _) hlog k).trans <|
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact le_self_add
  · exact setLIntegral_norm_clog_one_sub_mul_pow_le k a b hr hlarge.le
      (hz.trans (le_max_left R 0))

/-- `t ↦ log (log t)` is locally integrable on `[1, ∞)`: its logarithmic singularity at `t = 1`
is integrable. This lets Abelian integrals `∫_1^∞ t ^ (-s) f(t) dt` treat `log (log t)` like any
other locally integrable weight up to the endpoint `t = 1`. -/
theorem locallyIntegrableOn_log_log :
    LocallyIntegrableOn (fun t : ℝ ↦ Real.log (Real.log t)) (Set.Ici 1) := by
  rw [locallyIntegrableOn_iff isClosed_Ici.isLocallyClosed]
  intro k hk hkc
  obtain ⟨T, hT⟩ := hkc.isBounded.bddAbove
  have h2 : IntegrableOn (fun t : ℝ ↦ Real.log (Real.log t) * t ^ (-(2 : ℝ)))
      (Set.Icc 1 (max T 1)) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (μ := volume)).mpr
      (Real.integrableOn_log_log_mul_rpow one_lt_two)).mono_set Set.Icc_subset_Ici_self
  refine ((h2.mul_continuousOn (Real.continuous_rpow_const zero_le_two).continuousOn
    isCompact_Icc).mono_set fun x hx ↦ ⟨hk hx, (hT hx).trans (le_max_left _ _)⟩).congr_fun
    (fun t ht ↦ ?_) hkc.measurableSet
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le (hk ht)
  beta_reduce
  rw [mul_assoc, ← Real.rpow_add ht0, neg_add_cancel, Real.rpow_zero, mul_one]

/-- For `R < c` every power of the radial profile `log log (c / r)` is integrable on `(0, R)`:
there `|log log (c / r)| ≤ |log log (c / R)| + |log c| + |log r|`, and the powers of `log r` are
integrable near the origin. -/
theorem integrableOn_log_log_const_div_pow (k : ℕ) {c R : ℝ} (hR : R < c) :
    IntegrableOn (fun r : ℝ => Real.log (Real.log (c / r)) ^ k) (Set.Ioo 0 R) := by
  rcases le_or_gt R 0 with hR0 | hR0
  · simp [Set.Ioo_eq_empty_of_le hR0]
  obtain ⟨K, hK⟩ : ∃ K, K = |Real.log (Real.log (c / R))| + |Real.log c| := ⟨_, rfl⟩
  have hlog : IntegrableOn (fun r : ℝ => Real.log r ^ k) (Set.Icc 0 R) := by
    simpa [Real.norm_eq_abs, Real.log_abs] using
      (locallyIntegrable_log_norm_pow (E := ℝ) (μ := volume) k).integrableOn_isCompact
        isCompact_Icc
  have hdom : IntegrableOn (fun r : ℝ => 2 ^ (k - 1) * (K ^ k + |Real.log r ^ k|))
      (Set.Icc 0 R) :=
    ((integrableOn_const (by simp)).add hlog.abs).const_mul _
  refine (hdom.mono_set Set.Ioo_subset_Icc_self).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun r ⟨h0, hr⟩ => ?_
  have hc : 0 < c := hR0.trans hR
  set L := Real.log (c / r)
  have hℓ : 0 < Real.log (c / R) := Real.log_div_pos hR0 hR
  have hℓL : Real.log (c / R) ≤ L := Real.log_le_log (div_pos hc hR0)
    (div_le_div_of_nonneg_left hc.le h0 hr.le)
  -- `log (log (c / R)) ≤ log L ≤ L = log c - log r`.
  have hup : Real.log L ≤ |Real.log c| + |Real.log r| := by
    have hLr : L = Real.log c - Real.log r := Real.log_div hc.ne' h0.ne'
    linarith [Real.log_le_self (hℓ.trans_le hℓL).le, le_abs_self (Real.log c),
      neg_abs_le (Real.log r)]
  have hlow : Real.log (Real.log (c / R)) ≤ Real.log L := Real.log_le_log hℓ hℓL
  have habs : |Real.log L| ≤ K + |Real.log r| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log (Real.log (c / R))), abs_nonneg (Real.log c),
      abs_nonneg (Real.log r), abs_nonneg (Real.log (Real.log (c / R)))]
  rw [norm_pow, Real.norm_eq_abs, abs_pow]
  calc |Real.log L| ^ k ≤ (K + |Real.log r|) ^ k := pow_le_pow_left₀ (abs_nonneg _) habs k
    _ ≤ 2 ^ (k - 1) * (K ^ k + |Real.log r| ^ k) :=
      add_pow_le (by rw [hK]; positivity) (abs_nonneg _) k

/-- For `R < c` and `p > 1` the function `(r (log (c / r))^p)⁻¹` is integrable on `(0, R)`: it is
the derivative of `r ↦ ((p - 1) (log (c / r))^(p - 1))⁻¹`, which is continuous on `[0, R]` and
vanishes at `0`. -/
theorem integrableOn_inv_mul_log_const_div_rpow {c R p : ℝ} (hR : R < c) (hp : 1 < p) :
    IntegrableOn (fun r : ℝ => (r * Real.log (c / r) ^ p)⁻¹) (Set.Ioo 0 R) := by
  rcases le_or_gt R 0 with hR0 | hR0
  · simp [Set.Ioo_eq_empty_of_le hR0]
  have hc : 0 < c := hR0.trans hR
  have hp1 : 0 < p - 1 := sub_pos.2 hp
  set G : ℝ → ℝ := fun r => ((p - 1) * Real.log (c / r) ^ (p - 1))⁻¹
  have hcont : ContinuousOn G (Set.Icc 0 R) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | h0
    · -- `G 0 = 0`, and `G r → 0` as `r → 0⁺` because `log (c / r) → ∞`.
      have hG0 : G 0 = 0 := by simp [G, Real.zero_rpow hp1.ne']
      refine ContinuousWithinAt.mono ?_ Set.Icc_subset_Ici_self
      rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hG0]
      have hL : Filter.Tendsto (fun r : ℝ => Real.log (c / r)) (𝓝[>] 0) Filter.atTop := by
        have h : Filter.Tendsto (fun r : ℝ => Real.log c + -Real.log r) (𝓝[>] 0)
            Filter.atTop :=
          Filter.tendsto_atTop_add_const_left _ _
            (Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
        refine h.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        rw [Real.log_div hc.ne' hr.ne', sub_eq_add_neg]
      exact (((tendsto_rpow_atTop hp1).comp hL).const_mul_atTop hp1).inv_tendsto_atTop
    · have hL : 0 < Real.log (c / r) := Real.log_div_pos h0 (hr.2.trans_lt hR)
      exact ((((continuousAt_const (y := c)).div continuousAt_id h0.ne').log
        (div_pos hc h0).ne').rpow_const (.inl hL.ne') |>.const_mul (p - 1) |>.inv₀
        (mul_pos hp1 (Real.rpow_pos_of_pos hL _)).ne').continuousWithinAt
  have hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) R,
      HasDerivAt G ((r * Real.log (c / r) ^ p)⁻¹) r := by
    rintro r ⟨h0, hr⟩
    have hL : 0 < Real.log (c / r) := Real.log_div_pos h0 (hr.trans hR)
    have h := (((Real.hasDerivAt_log_const_div hc.ne' h0.ne').rpow_const
      (p := p - 1) (.inl hL.ne')).const_mul (p - 1)).inv
        (mul_pos hp1 (Real.rpow_pos_of_pos hL _)).ne'
    refine h.congr_deriv ?_
    rw [Real.rpow_sub_one hL.ne' (p - 1), Real.rpow_sub_one hL.ne' p]
    have : 0 < Real.log (c / r) ^ p := by positivity
    field_simp
  exact (intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv fun r hr =>
    inv_nonneg.2 (mul_nonneg hr.1.le (Real.rpow_nonneg (Real.log_div_pos hr.1
      (hr.2.trans hR)).le _))).mono_set Set.Ioo_subset_Ioc_self

/-- For `R < c` the planar radial integrand `r (log log (c / r))²` is integrable on `(0, R)`. This
is the radial form of square integrability of `log log (c / ‖z‖)` on a disc of radius `R` about
the singularity. -/
theorem integrableOn_mul_log_log_const_div_sq {c R : ℝ} (hR : R < c) :
    IntegrableOn (fun r : ℝ => r * Real.log (Real.log (c / r)) ^ 2) (Set.Ioo 0 R) :=
  IntegrableOn.continuousOn_mul_of_subset continuousOn_id
    (integrableOn_log_log_const_div_pow 2 hR) isCompact_Icc measurableSet_Ioo
    Set.Ioo_subset_Icc_self

/-- For `R < c` the planar radial integrand `r (r log (c / r))⁻²` is integrable on `(0, R)`. This
is the radial form of square integrability of the gradient of `log log (c / ‖z‖)`. -/
theorem integrableOn_mul_inv_mul_log_const_div_sq {c R : ℝ} (hR : R < c) :
    IntegrableOn (fun r : ℝ => r * ((r * Real.log (c / r))⁻¹) ^ 2) (Set.Ioo 0 R) := by
  refine (integrableOn_inv_mul_log_const_div_rpow hR one_lt_two).congr_fun
    (fun r hr => ?_) measurableSet_Ioo
  have h0 : r ≠ 0 := hr.1.ne'
  simp only [Real.rpow_two]
  field_simp

end TauCeti
