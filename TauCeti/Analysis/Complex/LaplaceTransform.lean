/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.Floor

/-!
# Truncated Laplace transforms of bounded functions

For `f : ℝ → ℂ`, this file studies the Laplace transform `G z = ∫ t in Ici 0, f t * exp (-z t)`
and its truncations `G_T z = ∫ t in 0..T, f t * exp (-z t)`:

* each truncation is entire (`differentiable_intervalIntegral_mul_cexp_neg_mul`), and, for `f`
  bounded on `[0, ∞)`, the full transform is holomorphic on `0 < re z`
  (`differentiableOn_integral_mul_cexp_neg_mul`), being a locally uniform limit of truncations;
* if `‖f‖ ≤ M` on `[0, ∞)`, the tail bound `‖G z - G_T z‖ ≤ M exp (-T re z) / re z` holds for
  `0 < re z` (`norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le`), and if `‖f‖ ≤ M` on
  `[0, T]`, then `‖G_T z‖ ≤ M exp (-T re z) / (-re z)` for `re z < 0`
  (`norm_intervalIntegral_mul_cexp_neg_mul_le_of_re_neg`).

The substitution `x = exp t` identifies `∫ x in u..v, x ^ (-z - 1)` with the truncated Laplace
transform `∫ t in log u..log v, exp (-z t)` of the constant function `1`
(`intervalIntegral_ofReal_cpow_neg_sub_one`); this links Dirichlet series, via integrals against
`x ^ (-z - 1)`, to Laplace transforms of step functions `t ↦ a ⌊exp t⌋₊`.

For a uniform step function `t ↦ c ⌊t / h⌋₊` of step length `h > 0`, the truncated Laplace
transform over `[0, N * h]` (`intervalIntegral_floor_div_mul_cexp_neg_mul`) and, for bounded `c`
and `0 < re z`, the full Laplace transform on `[0, ∞)` (`integral_floor_div_mul_cexp_neg_mul`)
factor as the entire single-step integral `∫ u in 0..h, exp (-z u)` times the power series of `c`
evaluated at `exp (-h z)`.

These are the analytic inputs of Newman's contour argument for his Tauberian theorem and of its
boundary sharpness constructions.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology Complex Interval

namespace TauCeti

variable {f : ℝ → ℂ} {M T : ℝ}

/-- Multiplying by the exponential kernel `cexp (-z t)` does not change interval integrability. -/
theorem intervalIntegrable_mul_cexp_neg_mul_iff {a b : ℝ} (z : ℂ) :
    IntervalIntegrable (fun t : ℝ ↦ f t * cexp (-z * t)) volume a b ↔
      IntervalIntegrable f volume a b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mul_continuousOn (g := fun t : ℝ ↦ cexp (-z * t)) (by fun_prop)⟩
  have := h.mul_continuousOn (g := fun t : ℝ ↦ cexp (z * t)) (by fun_prop)
  simpa [mul_assoc, ← Complex.exp_add] using this

/-- Multiplying by the exponential kernel `cexp (-z t)` does not change almost-everywhere strong
measurability. -/
theorem aestronglyMeasurable_mul_cexp_neg_mul_iff {μ : Measure ℝ} (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ ↦ f t * cexp (-z * t)) μ ↔ AEStronglyMeasurable f μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mul (g := fun t : ℝ ↦ cexp (-z * t))
    (by fun_prop : Continuous _).aestronglyMeasurable⟩
  have := h.mul (g := fun t : ℝ ↦ cexp (z * t)) (by fun_prop : Continuous _).aestronglyMeasurable
  simpa [Pi.mul_def, mul_assoc, ← Complex.exp_add] using this

/-- **Truncated Laplace transforms are entire.** The function
`z ↦ ∫ t in a..b, f t * exp (-z t)` is complex differentiable everywhere. If `f` is not
interval integrable on `[a, b]`, it is identically `0`. -/
theorem differentiable_intervalIntegral_mul_cexp_neg_mul {a b : ℝ} :
    Differentiable ℂ fun z : ℂ ↦ ∫ t in a..b, f t * cexp (-z * t) := by
  by_cases hf : IntervalIntegrable f volume a b
  swap
  · have : (fun z : ℂ ↦ ∫ t in a..b, f t * cexp (-z * t)) = fun _ ↦ 0 :=
      funext fun z ↦ intervalIntegral.integral_undef
        ((intervalIntegrable_mul_cexp_neg_mul_iff z).not.mpr hf)
    rw [this]
    exact differentiable_const _
  intro z₀
  -- On `Ι a b` we have `|t| ≤ C` and, for `z` within distance `1` of `z₀`, `‖exp (-z t)‖ ≤ K`;
  -- so the `z`-derivative `-t f t exp (-z t)` of the integrand is dominated by `C * K * ‖f t‖`.
  set C := max |a| |b|
  set K := Real.exp ((‖z₀‖ + 1) * C)
  have habs : ∀ t ∈ Ι a b, |t| ≤ C := by
    intro t ht
    rcases le_total a b with hab | hab
    · rw [uIoc_of_le hab] at ht
      exact abs_le_max_abs_abs ht.1.le ht.2
    · rw [uIoc_of_ge hab] at ht
      exact (abs_le_max_abs_abs ht.1.le ht.2).trans_eq (max_comm _ _)
  have hexp : ∀ t ∈ Ι a b, ∀ z ∈ ball z₀ 1, ‖cexp (-z * t)‖ ≤ K := by
    intro t ht z hz
    rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
    refine Real.exp_le_exp.mpr ?_
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_sub_norm_le z z₀
      rw [mem_ball_iff_norm] at hz
      linarith
    calc -z.re * t ≤ |z.re| * |t| := (le_abs_self _).trans_eq (by rw [abs_mul, abs_neg])
      _ ≤ (‖z₀‖ + 1) * C :=
          mul_le_mul ((Complex.abs_re_le_norm z).trans hz') (habs t ht) (abs_nonneg _)
            (by positivity)
  have hcont : ∀ z : ℂ, Continuous fun t : ℝ ↦ cexp (-z * t) := fun z ↦ by fun_prop
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun z t ↦ f t * (cexp (-z * t) * (-(t : ℂ))))
    (bound := fun t ↦ C * K * ‖f t‖) (ball_mem_nhds z₀ one_pos)
    (.of_forall fun z ↦ hf.def'.aestronglyMeasurable.mul (hcont z).aestronglyMeasurable)
    (hf.mul_continuousOn (hcont z₀).continuousOn)
    (hf.def'.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ ↦
      cexp (-z₀ * t) * (-(t : ℂ))).aestronglyMeasurable)
    (.of_forall fun t ht z hz ↦ ?_) (hf.norm.const_mul _)
    (.of_forall fun t _ z _ ↦ ?_)).2.differentiableAt
  · rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    calc ‖f t‖ * (‖cexp (-z * t)‖ * |t|) ≤ ‖f t‖ * (K * C) := by
          gcongr
          exacts [hexp t ht z hz, habs t ht]
      _ = C * K * ‖f t‖ := by ring
  · have h := ((hasDerivAt_id' z).neg.mul_const (t : ℂ)).cexp.const_mul (f t)
    simpa using h

/-- **Substitution `x = exp t`.** For `0 < u` and `0 < v`, the integral of `x ^ (-z - 1)` over
`[u, v]` is the truncated Laplace transform `∫ t in log u..log v, exp (-z t)` of the constant
function `1`. -/
theorem intervalIntegral_ofReal_cpow_neg_sub_one {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (z : ℂ) :
    ∫ x in u..v, (x : ℂ) ^ (-z - 1) = ∫ t in Real.log u..Real.log v, cexp (-z * t) := by
  have hg : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (-z - 1))
      (Real.exp '' [[Real.log u, Real.log v]]) := by
    rintro _ ⟨t, -, rfl⟩
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (Real.exp_pos t).ne')).continuousWithinAt
  have h := intervalIntegral.integral_deriv_smul_comp' (fun t _ ↦ Real.hasDerivAt_exp t)
    Real.continuous_exp.continuousOn hg
  rw [Real.exp_log hu, Real.exp_log hv] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [Function.comp_apply, Complex.real_smul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'), ← Complex.ofReal_log (Real.exp_pos t).le,
    Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  ring_nf

/-- Pointwise bound on the Laplace integrand: if `‖w‖ ≤ M`, then
`‖w * exp (-z t)‖ ≤ M * exp (-re z * t)` for real `t`. -/
theorem norm_mul_cexp_neg_mul_le {w z : ℂ} {t : ℝ} (h : ‖w‖ ≤ M) :
    ‖w * cexp (-z * t)‖ ≤ M * Real.exp (-z.re * t) := by
  rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- For `0 < re z`, the Laplace integrand of a function bounded on `[0, ∞)` is integrable there. -/
theorem integrableOn_mul_cexp_neg_mul (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ ↦ f t * cexp (-z * t)) (Ici 0) := by
  refine Integrable.mono' (((integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (exp_neg_integrableOn_Ioi 0 hz)).const_mul M)
    (hf.mul (by fun_prop : Continuous fun t : ℝ ↦ cexp (-z * t)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ici fun t ht ↦ ?_)
  exact norm_mul_cexp_neg_mul_le (hbound t ht)

/-- **Tail bound.** For `0 < re z` and `0 ≤ T`, the Laplace transform of a function bounded by
`M` on `[0, ∞)` differs from its truncation at `T` by at most `M exp (-T re z) / re z`. -/
theorem norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) {z : ℂ} (hz : 0 < z.re) (hT : 0 ≤ T) :
    ‖(∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) - ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖ ≤
      M * Real.exp (-z.re * T) / z.re := by
  have hint := integrableOn_mul_cexp_neg_mul hf hbound hz
  rw [integral_Ici_eq_integral_Ioi, ← intervalIntegral.integral_interval_add_Ioi
    ((integrableOn_Ici_iff_integrableOn_Ioi).mp hint) (hint.mono_set (Ioi_subset_Ici hT)),
    add_sub_cancel_left]
  calc ‖∫ t in Ioi T, f t * cexp (-z * t)‖ ≤ ∫ t in Ioi T, M * Real.exp (-z.re * t) := by
        refine norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi (by linarith) T).const_mul M)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
            norm_mul_cexp_neg_mul_le (hbound t (hT.trans (le_of_lt ht))))
    _ = M * Real.exp (-z.re * T) / z.re := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith), neg_div_neg_eq, mul_div_assoc]

/-- **Left half-plane bound.** For `re z < 0` and `0 ≤ T`, the truncated Laplace transform of a
function bounded by `M` on `[0, T]` is at most `M exp (-T re z) / (-re z)`. -/
theorem norm_intervalIntegral_mul_cexp_neg_mul_le_of_re_neg
    (hbound : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) {z : ℂ} (hz : z.re < 0) (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖ ≤ M * Real.exp (-z.re * T) / -z.re := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 ⟨le_rfl, hT⟩)
  have hg : IntegrableOn (fun t : ℝ ↦ M * Real.exp (-z.re * t)) (Iic T) :=
    (integrableOn_exp_mul_Iic (by linarith) T).const_mul M
  calc ‖∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖
      ≤ ∫ t in (0 : ℝ)..T, M * Real.exp (-z.re * t) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall fun t ht ↦
          norm_mul_cexp_neg_mul_le (hbound t (Ioc_subset_Icc_self ht)))
          ((by fun_prop : Continuous fun t : ℝ ↦ M * Real.exp (-z.re * t)).intervalIntegrable _ _)
    _ ≤ ∫ t in Iic T, M * Real.exp (-z.re * t) := by
        rw [intervalIntegral.integral_of_le hT]
        exact setIntegral_mono_set hg (.of_forall fun t ↦ by positivity)
          (.of_forall fun t ht ↦ (Ioc_subset_Iic_self ht : t ∈ Iic T))
    _ = M * Real.exp (-z.re * T) / -z.re := by
        rw [integral_const_mul, integral_exp_mul_Iic (by linarith), mul_div_assoc]

/-- **Holomorphy of the Laplace transform.** If `f` is bounded on `[0, ∞)`, its Laplace transform
`z ↦ ∫ t in Ici 0, f t * exp (-z t)` is complex differentiable on the half-plane `0 < re z`. -/
theorem differentiableOn_integral_mul_cexp_neg_mul
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) {z | 0 < z.re} := by
  by_cases hf : AEStronglyMeasurable f (volume.restrict (Ici 0))
  swap
  · have : (fun z : ℂ ↦ ∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) = fun _ ↦ 0 :=
      funext fun z ↦ integral_undef fun h ↦
        hf ((aestronglyMeasurable_mul_cexp_neg_mul_iff z).1 h.aestronglyMeasurable)
    rw [this]
    exact differentiableOn_const _
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 (mem_Ici.mpr le_rfl))
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  -- The truncations at `n : ℕ` converge to the transform uniformly on each `{c < re z}`.
  refine TendstoLocallyUniformlyOn.differentiableOn (φ := atTop)
    (F := fun (n : ℕ) (z : ℂ) ↦ ∫ t in (0 : ℝ)..n, f t * cexp (-z * t)) ?_
    (.of_forall fun n ↦
      differentiable_intervalIntegral_mul_cexp_neg_mul.differentiableOn) hopen
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε z₀ hz₀
  have hc : 0 < z₀.re / 2 := half_pos hz₀
  refine ⟨{z | z₀.re / 2 < z.re}, mem_nhdsWithin_of_mem_nhds
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (half_lt_self hz₀)), ?_⟩
  have hlim : Tendsto (fun n : ℕ ↦ M * Real.exp (-(z₀.re / 2) * n) / (z₀.re / 2)) atTop (𝓝 0) := by
    have := ((Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg
      (neg_lt_zero.mpr hc))).const_mul M).div_const (z₀.re / 2)
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hn
  calc _ ≤ M * Real.exp (-z.re * n) / z.re :=
        norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le hf hbound (hc.trans hz) n.cast_nonneg
    _ ≤ M * Real.exp (-(z₀.re / 2) * n) / (z₀.re / 2) := by
        gcongr

/-- **Truncated Laplace transform of a uniform step function.** For `h > 0`, `c : ℕ → ℂ`,
`N : ℕ`, and `z : ℂ`, the Laplace integral of `t ↦ c ⌊t / h⌋₊` over `[0, N * h]` factors as the
single-step integral `∫ u in 0..h, exp (-z * u)` times the `N`-th partial sum of the power series
`∑ c n * exp (-h * z) ^ n`. -/
theorem intervalIntegral_floor_div_mul_cexp_neg_mul (c : ℕ → ℂ) {h : ℝ} (hh : 0 < h)
    (N : ℕ) (z : ℂ) :
    ∫ t in (0 : ℝ)..((N : ℝ) * h), c ⌊t / h⌋₊ * cexp (-z * t) =
      (∫ u in (0 : ℝ)..h, cexp (-z * u)) * ∑ n ∈ Finset.range N, c n * cexp (-(h : ℂ) * z) ^ n := by
  have hfloor {n : ℕ} {t : ℝ} (ht : t ∈ Ioo ((n : ℝ) * h) (((n + 1 : ℕ) : ℝ) * h)) :
      ⌊t / h⌋₊ = n := by
    have h1 : (n : ℝ) < t / h := (lt_div_iff₀ hh).mpr ht.1
    have h2 : t / h < (n : ℝ) + 1 :=
      (div_lt_iff₀ hh).mpr (by simpa only [Nat.cast_add, Nat.cast_one] using ht.2)
    exact (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans h1.le)).mpr ⟨h1.le, h2⟩
  have hle (n : ℕ) : (n : ℝ) * h ≤ ((n + 1 : ℕ) : ℝ) * h := by
    gcongr
    exact_mod_cast Nat.le_succ n
  have hint (n : ℕ) : IntervalIntegrable (fun t : ℝ ↦ c ⌊t / h⌋₊ * cexp (-z * t)) volume
      ((n : ℝ) * h) (((n + 1 : ℕ) : ℝ) * h) := by
    refine ((by fun_prop : Continuous fun t : ℝ ↦ c n * cexp (-z * t)).intervalIntegrable
      _ _).congr_uIoo fun t ht ↦ ?_
    rw [uIoo_of_le (hle n)] at ht
    simp only [hfloor ht]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ ↦ c ⌊t / h⌋₊ * cexp (-z * t)) (μ := volume)
    (a := fun k : ℕ ↦ (k : ℝ) * h) (n := N) fun k _ ↦ hint k
  simp only [Nat.cast_zero, zero_mul] at hsum
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hcongr : ∫ t in ((n : ℝ) * h)..(((n + 1 : ℕ) : ℝ) * h), c ⌊t / h⌋₊ * cexp (-z * t) =
      ∫ t in ((n : ℝ) * h)..(((n + 1 : ℕ) : ℝ) * h), c n * cexp (-z * t) :=
    intervalIntegral.integral_congr_Ioo_of_le (hle n) fun t ht ↦ by rw [hfloor ht]
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hshift := intervalIntegral.integral_comp_add_left (f := fun t : ℝ ↦ cexp (-z * t))
    ((n : ℝ) * h) (a := (0 : ℝ)) (b := h)
  have hhi : (n : ℝ) * h + h = ((n + 1 : ℕ) : ℝ) * h := by push_cast; ring
  rw [add_zero, hhi] at hshift
  rw [← hshift]
  have hexp (u : ℝ) : cexp (-z * ((n : ℝ) * h + u : ℝ)) =
      cexp (-(h : ℂ) * z) ^ n * cexp (-z * u) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hexp, intervalIntegral.integral_const_mul]
  ring

/-- **Laplace transform of a bounded uniform step function.** For `h > 0`, a bounded sequence
`c : ℕ → ℂ`, and `0 < re z`, the Laplace transform of `t ↦ c ⌊t / h⌋₊` on `[0, ∞)` factors as
`(∫ u in 0..h, exp (-z * u)) * ∑' n, c n * exp (-h * z) ^ n`. -/
theorem integral_floor_div_mul_cexp_neg_mul {c : ℕ → ℂ} (hbound : ∀ n, ‖c n‖ ≤ M) {h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ici (0 : ℝ), c ⌊t / h⌋₊ * cexp (-z * t) =
      (∫ u in (0 : ℝ)..h, cexp (-z * u)) * ∑' n, c n * cexp (-(h : ℂ) * z) ^ n := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ c ⌊t / h⌋₊) (volume.restrict (Ici 0)) :=
    (measurable_from_nat.comp (measurable_id.div_const h).nat_floor).aestronglyMeasurable
  have hint := integrableOn_mul_cexp_neg_mul hmeas (fun t _ ↦ hbound _) hz
  have hnorm_lt : ‖cexp (-(h : ℂ) * z)‖ < 1 := by
    rw [Complex.norm_exp, ← Complex.ofReal_neg, Complex.re_ofReal_mul]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hsumm : Summable fun n : ℕ ↦ c n * cexp (-(h : ℂ) * z) ^ n := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg _) hnorm_lt).mul_left M) fun n ↦ ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)
  have hlim1 : Tendsto (fun N : ℕ ↦ ∫ t in (0 : ℝ)..((N : ℝ) * h), c ⌊t / h⌋₊ * cexp (-z * t))
      atTop (𝓝 (∫ t in Ici (0 : ℝ), c ⌊t / h⌋₊ * cexp (-z * t))) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact intervalIntegral_tendsto_integral_Ioi 0 ((integrableOn_Ici_iff_integrableOn_Ioi).mp hint)
      (tendsto_natCast_atTop_atTop.atTop_mul_const hh)
  have hlim2 : Tendsto (fun N : ℕ ↦ ∫ t in (0 : ℝ)..((N : ℝ) * h), c ⌊t / h⌋₊ * cexp (-z * t))
      atTop (𝓝 ((∫ u in (0 : ℝ)..h, cexp (-z * u)) * ∑' n, c n * cexp (-(h : ℂ) * z) ^ n)) := by
    simp_rw [intervalIntegral_floor_div_mul_cexp_neg_mul c hh]
    exact hsumm.hasSum.tendsto_sum_nat.const_mul _
  exact tendsto_nhds_unique hlim1 hlim2

end TauCeti
