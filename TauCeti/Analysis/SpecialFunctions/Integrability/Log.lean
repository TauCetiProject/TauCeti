/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
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
import TauCeti.Analysis.SpecialFunctions.Complex.LogBounds

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
bounded set `‖z‖ ≤ R`, translating `log |t - Re(z⁻¹)|` yields a uniform `L²` bound on every
bounded interval `(a, b]`, even though the singularity `t = z⁻¹` moves.

On the half-line `[1, ∞)` the iterated logarithm `t ↦ log (log t)` is locally integrable as well:
its singularity at `t = 1` is integrable, by Mathlib's `Real.integrableOn_log_log_mul_rpow`. This
is the integrability that Abelian arguments against `log log t` need, as in Mertens' theorems.

## Main declarations

* `TauCeti.locallyIntegrable_log_norm_pow`: `x ↦ (log ‖x‖) ^ k` is locally integrable.
* `TauCeti.locallyIntegrable_log_norm`: `x ↦ log ‖x‖` is locally integrable.
* `TauCeti.intervalIntegrable_log_pow`: `t ↦ (log t) ^ k` is interval integrable.
* `MeromorphicOn.intervalIntegrable_clog`: `t ↦ Log (f t)` is interval integrable for
  real-meromorphic `f : ℝ → ℂ`; `AnalyticOnNhd.intervalIntegrable_clog` is the analytic case.
* `TauCeti.setLIntegral_abs_log_abs_sub_pow_le`,
  `TauCeti.setLIntegral_norm_log_one_sub_ofReal_mul_sq_le`, and
  `TauCeti.exists_setLIntegral_norm_log_one_sub_ofReal_mul_sq_le`: uniform `L^k` bound for
  translated real logarithms and uniform `L²` bounds for `t ↦ Log (1 - t z)` on `(a, b]` over
  bounded `z`.
* `TauCeti.locallyIntegrableOn_log_log`: `t ↦ log (log t)` is locally integrable on `[1, ∞)`.
-/

public section

namespace TauCeti

open MeasureTheory

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

/-- Translating `s ∈ [-R, R]` keeps the `L^k` integral of `|log |t - s||` on `(a, b]` uniformly
bounded by the `L^k` integral of `|log ‖u‖|` on `[a - R, b + R]`. -/
theorem setLIntegral_abs_log_abs_sub_pow_le (k : ℕ) {a b R s : ℝ} (hs : |s| ≤ R) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (|Real.log (|t - s|)| ^ k) ≤
      ∫⁻ u in Set.Icc (a - R) (b + R), ENNReal.ofReal (|Real.log ‖u‖| ^ k) := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Icc,
    ← lintegral_add_right_eq_self
      ((Set.Icc (a - R) (b + R)).indicator fun u ↦ ENNReal.ofReal (|Real.log ‖u‖| ^ k)) (-s)]
  refine lintegral_mono fun t ↦ ?_
  by_cases ht : t ∈ Set.Ioc a b
  · have hmem : t - s ∈ Set.Icc (a - R) (b + R) := by
      rw [abs_le] at hs
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [Set.indicator_of_mem ht, ← sub_eq_add_neg, Set.indicator_of_mem hmem, Real.norm_eq_abs]
  · simp [ht]

/-- On `(a, b]`, when `0 < r ≤ ‖z‖ ≤ R`, shifting by `Re(z⁻¹) ∈ [-r⁻¹, r⁻¹]` bounds the `L²`
integral of `t ↦ Complex.log (1 - t * z)` uniformly in `z`. -/
theorem setLIntegral_norm_log_one_sub_ofReal_mul_sq_le (a b : ℝ) {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hzr : r ≤ ‖z‖) (hzR : ‖z‖ ≤ R) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ 2) ≤
      ENNReal.ofReal
        (2 * (Real.log (1 + max |a| |b| * R) + |Real.log r| + Real.log (1 + R) + Real.pi) ^ 2) *
          volume (Set.Ioc a b) +
        ENNReal.ofReal 2 *
          ∫⁻ u in Set.Icc (a - r⁻¹) (b + r⁻¹), ENNReal.ofReal (|Real.log ‖u‖| ^ 2) := by
  have hz_pos : 0 < ‖z‖ := hr.trans_le hzr
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz_pos
  have : 0 ≤ R := hz_pos.le.trans hzR
  set T : ℝ := max |a| |b|
  have hT : 0 ≤ T := le_max_of_le_left (abs_nonneg a)
  set M : ℝ := Real.log (1 + T * R) + |Real.log r| + Real.log (1 + R) + Real.pi
  have hs : |(z⁻¹).re| ≤ r⁻¹ :=
    (Complex.abs_re_le_norm z⁻¹).trans ((norm_inv z).trans_le (inv_anti₀ hr hzr))
  have hlogz : |Real.log ‖z‖| ≤ |Real.log r| + Real.log (1 + R) := by
    have hlow := Real.log_le_log hr hzr
    have hhigh := Real.log_le_log hz_pos (by linarith : ‖z‖ ≤ 1 + R)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log r), abs_nonneg (Real.log r),
      Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + R)]
  have hae : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc a b),
      ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ 2) ≤
        ENNReal.ofReal (2 * M ^ 2) +
          ENNReal.ofReal 2 * ENNReal.ofReal (|Real.log (|t - (z⁻¹).re|)| ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (by rw [ae_iff]; simp : ∀ᵐ t : ℝ, t ≠ (z⁻¹).re)] with t ht hts
    have htT : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1, neg_abs_le a, le_max_left |a| |b|],
      by linarith [ht.2, le_abs_self b, le_max_right |a| |b|]⟩
    have hlogt : Real.log (1 + |t| * ‖z‖) ≤ Real.log (1 + T * R) :=
      Real.log_le_log (by positivity) (by linarith [mul_le_mul htT hzR hz_pos.le hT])
    have hbound : ‖Complex.log (1 - t * z)‖ ≤ M + |Real.log (|t - (z⁻¹).re|)| :=
      (Complex.norm_log_one_sub_ofReal_mul_le hz0 hts).trans (by linarith)
    have hsq : ‖Complex.log (1 - t * z)‖ ^ 2 ≤
        2 * M ^ 2 + 2 * (|Real.log (|t - (z⁻¹).re|)| ^ 2) := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hbound 2,
        sq_nonneg (M - |Real.log (|t - (z⁻¹).re|)|)]
    rw [← ENNReal.ofReal_mul zero_le_two, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hsq
  have hm : Measurable fun t : ℝ ↦ ENNReal.ofReal (|Real.log (|t - (z⁻¹).re|)| ^ 2) := by fun_prop
  refine (lintegral_mono_ae hae).trans ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
    lintegral_const_mul _ hm]
  gcongr _ + _ * ?_
  exact setLIntegral_abs_log_abs_sub_pow_le 2 hs

open scoped ENNReal in
/-- Over any bounded ball `‖z‖ ≤ R`, the `L²` integral of `t ↦ Complex.log (1 - t * z)` on `(a, b]`
is uniformly bounded by a finite constant independent of `z`. -/
theorem exists_setLIntegral_norm_log_one_sub_ofReal_mul_sq_le (a b R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ z : ℂ, ‖z‖ ≤ R →
      ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ 2) ≤ C := by
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
  set I₂ : ℝ≥0∞ := ∫⁻ u in Set.Icc (a - r⁻¹) (b + r⁻¹), ENNReal.ofReal (|Real.log ‖u‖| ^ 2)
  have hI₂ : I₂ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun u ↦ ?_)
      ((locallyIntegrable_log_norm_pow (E := ℝ) (μ := volume) 2).integrableOn_isCompact
        isCompact_Icc).hasFiniteIntegral
    rw [← ofReal_norm, Real.norm_eq_abs, sq_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hvol : volume (Set.Ioc a b) < ∞ := by simp [Real.volume_Ioc]
  refine ⟨ENNReal.ofReal (2 * M ^ 2) * volume (Set.Ioc a b) + ENNReal.ofReal 2 * I₂,
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI₂.ne⟩, fun z hz ↦ ?_⟩
  rcases le_or_gt ‖z‖ r with hsmall | hlarge
  · refine (setLIntegral_mono' measurableSet_Ioc (g := fun _ ↦ ENNReal.ofReal (2 * M ^ 2))
        fun t ht ↦ ?_).trans ?_
    · have htT : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1, neg_abs_le a, le_max_left |a| |b|],
        by linarith [ht.2, le_abs_self b, le_max_right |a| |b|]⟩
      have htz : ‖-((t : ℂ) * z)‖ ≤ 1 / 2 := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine (mul_le_mul htT hsmall (norm_nonneg z) hT).trans ?_
        rw [hr_def, ← one_div, mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      have hlog : ‖Complex.log (1 - t * z)‖ ≤ M := by
        have h := Complex.norm_log_one_add_half_le_self (z := -((t : ℂ) * z)) htz
        rw [← sub_eq_add_neg] at h
        linarith
      exact ENNReal.ofReal_le_ofReal
        ((pow_le_pow_left₀ (norm_nonneg _) hlog 2).trans (by nlinarith))
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact le_self_add
  · exact setLIntegral_norm_log_one_sub_ofReal_mul_sq_le a b hr hlarge.le
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

end TauCeti
