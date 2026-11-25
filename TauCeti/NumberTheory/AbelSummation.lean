/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Lemmas
public import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.SpecialFunctions.LogIntegral

/-!
# Consequences of Abel summation for partial sums

Mathlib's `Mathlib/NumberTheory/AbelSummation.lean` proves the summation-by-parts identity
`∑_{k ≤ x} f k c k = f x ∑_{k ≤ x} c k - ∫ f' (t) ∑_{k ≤ t} c k dt` and derives convergence
criteria from it. This file records the elementary properties of the partial-sum step function
`t ↦ ∑_{1 ≤ k ≤ t} c k` that such arguments need, and draws three further consequences from growth
hypotheses on partial sums; the last of them, for the weight `1 / log t`, starts its partial sums
at `k = 2`, where `log k > 0`.

* **The step function.** It vanishes for `t < 1`, hence is `O(g)` near `0` for every `g`, and it
  is locally integrable on `[0, ∞)`. Together with a bound `O(t ^ r)` at infinity (see
  `Asymptotics.IsBigO.comp_natFloor_rpow`) these are the hypotheses of Mathlib's Mellin-transform
  criteria, through which the partial-summation integral of an `L`-series is studied.
* **A logarithmic weight.** Mathlib's `summable_mul_of_bigO_atTop'` converts a bound on the partial
  sums of a sequence into the convergence of a weighted series, provided the weight is
  differentiable and the derivative of the weight against the partial sums admits an integrable
  majorant. This file performs that conversion once, for the weight `(t (1 + log t) ^ 3)⁻¹` and
  partial sums growing like `t log t`. The weight is written with `1 + log t` rather than `log t`
  so that it stays positive and smooth at `t = 1`, where Abel summation starts. Its derivative
  against an `O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, which is integrable at
  infinity by comparison with Mathlib's log-Cauchy density
  `integrableOn_Ioi_zero_inv_mul_one_add_log_sq`.
* **A power weight.** If the partial sums grow like `κ x`, then the partial sums weighted by
  `n ^ τ`, for an exponent `τ > -1`, grow like `κ x ^ (τ + 1) / (τ + 1)`. This is the step that
  moves a Tauberian conclusion for the coefficients `a n n ^ (1 - σ)` back to the coefficients
  `a n`.
* **The weight `1 / log t`.** If the partial sums `∑_{2 ≤ k ≤ t} c k` are `log t + O(1)`, with
  error at most `C` on `t ≥ 2`, then `∑_{2 ≤ k ≤ x} c k / log k = log log x + B + O(1 / log x)` for
  a constant `B`, with error at most `2 C / log x` on `x ≥ 2`. This is the partial-summation step
  from Mertens' first theorem to his second, for the coefficients `log p / p` on the primes as for
  the von Mangoldt coefficients `Λ(n) / n`. Writing `S(t) = log t + R(t)`, the main part `log t`
  integrates against `1 / (t log² t)` to `log log x`, the integral of `R(t) / (t log² t)` over
  `[2, ∞)` converges absolutely and enters `B`, and its tail beyond `x` is at most `C / log x`.
  This estimate is stated for an arbitrary measurable `S`, so that the same argument serves the
  partial sums over `ℕ` here and those over the prime ideals of a number field in
  `TauCeti.NumberTheory.LFunctions.Mertens`.

## Main declarations

* `TauCeti.sum_Icc_one_natFloor_eq_zero`: `∑_{1 ≤ k ≤ t} c k = 0` for `t < 1`.
* `TauCeti.abs_sum_Icc_one_natFloor_le`: the trivial bound `|∑_{1 ≤ k ≤ t} c k| ≤ t` for
  `t ≥ 0` when `|c k| ≤ 1`.
* `TauCeti.isBigO_sum_Icc_natFloor_nhdsGT_zero`: the step function is `O(g)` as `t → 0⁺`.
* `TauCeti.locallyIntegrableOn_sum_Icc_natFloor`: the step function is locally integrable on
  `[0, ∞)`.
* `TauCeti.intervalIntegrable_mul_sum_Icc`: weighted by a function locally integrable on
  `[1, ∞)`, the step function is interval integrable between any two reals.
* `TauCeti.summable_div_mul_one_add_log_cube`: if the partial sums `∑_{1 ≤ k ≤ t} u k` of a
  nonnegative sequence are `O(t log t)`, then `∑ u n / (n (1 + log n) ^ 3)` converges.
* `TauCeti.sum_Icc_rpow_mul_eq`: the exact Abel-summation identity for the weight `t ^ τ`.
* `TauCeti.tendsto_rpow_inv_mul_sum_Icc_rpow_mul`: if `x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then
  `(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)` for `τ > -1`.
* `TauCeti.sum_Icc_div_log_eq`: the exact Abel-summation identity for the weight `1 / log t`.
* `TauCeti.exists_abs_div_log_add_integral_sub_log_log_sub_le`: if a measurable `S` satisfies
  `S(t) = log t + O(1)`, then `S(x) / log x + ∫_2^x S(t) / (t log² t) dt` is
  `log log x + B + O(1 / log x)`.
* `TauCeti.exists_abs_sum_Icc_div_log_sub_log_log_sub_le`: if `∑_{2 ≤ k ≤ t} c k = log t + O(1)`,
  then `∑_{2 ≤ k ≤ x} c k / log k = log log x + B + O(1 / log x)`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, proof of Theorem 3.4(b), pp. 40–41.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology

variable {t : ℝ}

/-! ### The partial-sum step function -/

/-- The partial-sum step function `t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, c k` vanishes below `1`. -/
theorem sum_Icc_one_natFloor_eq_zero {M : Type*} [AddCommMonoid M] (c : ℕ → M) (ht : t < 1) :
    ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k = 0 := by
  simp [Nat.floor_eq_zero.mpr ht]

/-- The trivial bound on the partial-sum step function: if `|c k| ≤ 1` for every `k`, then
`|∑ k ∈ Icc 1 ⌊t⌋₊, c k| ≤ t` for `t ≥ 0`. -/
theorem abs_sum_Icc_one_natFloor_le {c : ℕ → ℝ} (hc : ∀ k, |c k| ≤ 1) (ht : 0 ≤ t) :
    |∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k| ≤ t := by
  calc |∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k| ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, |c k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ hc k
    _ ≤ t := by simpa using Nat.floor_le ht

/-- The partial-sum step function `t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, c k` vanishes near `0`, so it is `O(g)`
as `t → 0⁺` for every `g`. -/
theorem isBigO_sum_Icc_natFloor_nhdsGT_zero {E F : Type*} [SeminormedAddCommGroup E] [Norm F]
    (c : ℕ → E) (g : ℝ → F) :
    (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) =O[𝓝[>] 0] g := by
  refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  exact (sum_Icc_one_natFloor_eq_zero c ht.2).symm

/-- The partial-sum step function `t ↦ ∑ k ∈ Icc m ⌊t⌋₊, c k` is locally integrable on
`[0, ∞)`. -/
theorem locallyIntegrableOn_sum_Icc_natFloor {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) (m : ℕ) :
    LocallyIntegrableOn (fun t : ℝ ↦ ∑ k ∈ Finset.Icc m ⌊t⌋₊, c k) (Ici 0) := by
  simpa using locallyIntegrableOn_mul_sum_Icc c le_rfl (m := m) (locallyIntegrableOn_const 1)

/-- The partial-sum step function `t ↦ ∑ k ∈ Icc 1 ⌊t⌋₊, c k`, weighted by a function locally
integrable on `[1, ∞)`, is interval integrable between any two reals: it vanishes below `1`. -/
theorem intervalIntegrable_mul_sum_Icc {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜}
    (hf : LocallyIntegrableOn f (Ici 1)) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ f t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) volume a b := by
  have key (b : ℝ) :
      IntervalIntegrable (fun t ↦ f t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) volume 1 b := by
    rcases le_or_gt 1 b with hb | hb
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr <|
        integrableOn_mul_sum_Icc c zero_le_one
          (hf.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc)
    · refine IntervalIntegrable.symm ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr ?_)
      exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr <|
        integrableOn_zero.congr_fun (fun t ht ↦ by simp [Nat.floor_eq_zero.mpr ht.2])
          measurableSet_Ioo
  exact (key a).symm.trans (key b)

/-! ### The comparison weight -/

/-- The weight `(t (1 + log t) ^ 3)⁻¹` against which a partial-sum bound is summed. -/
private noncomputable def decayWeight (t : ℝ) : ℝ := (t * (1 + Real.log t) ^ 3)⁻¹

/-- `1 + log t` is positive to the right of `exp (-1)`, so the comparison weight is positive on a
neighbourhood of `Ici 1`. -/
private lemma one_add_log_pos (ht : Real.exp (-1) < t) : 0 < 1 + Real.log t := by
  have h := Real.log_lt_log (Real.exp_pos _) ht
  rw [Real.log_exp] at h
  linarith

private lemma exp_neg_one_lt_one : Real.exp (-1) < 1 :=
  Real.exp_lt_one_iff.2 (by norm_num)

private lemma decayWeight_pos (ht : Real.exp (-1) < t) : 0 < decayWeight t := by
  have h := one_add_log_pos ht
  have ht0 : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht
  exact inv_pos.2 (by positivity)

private lemma hasDerivAt_decayWeight (ht : Real.exp (-1) < t) :
    HasDerivAt decayWeight
      (-(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2)) t := by
  have hlog := one_add_log_pos ht
  have ht0 : (0 : ℝ) < t := lt_trans (Real.exp_pos _) ht
  have ht0' : t ≠ 0 := ht0.ne'
  have hlog' : (1 : ℝ) + Real.log t ≠ 0 := hlog.ne'
  have h1 : HasDerivAt (fun u : ℝ ↦ 1 + Real.log u) t⁻¹ t :=
    (Real.hasDerivAt_log ht0').const_add 1
  refine ((hasDerivAt_id' (x := t)).fun_mul (h1.fun_pow 3) |>.inv
    (by positivity)).congr_deriv ?_
  push_cast
  field_simp

/-- On a neighbourhood of `Ici 1` the comparison weight is positive, so taking its norm changes
nothing. -/
private lemma norm_decayWeight_eventuallyEq (ht : 1 ≤ t) :
    (fun u : ℝ ↦ ‖decayWeight u‖) =ᶠ[𝓝 t] decayWeight := by
  have hmem : t ∈ Ioi (Real.exp (-1)) := lt_of_lt_of_le exp_neg_one_lt_one ht
  filter_upwards [isOpen_Ioi.mem_nhds hmem] with u hu
  exact Real.norm_of_nonneg (decayWeight_pos hu).le

private lemma differentiableAt_norm_decayWeight (ht : 1 ≤ t) :
    DifferentiableAt ℝ (fun u : ℝ ↦ ‖decayWeight u‖) t :=
  (norm_decayWeight_eventuallyEq ht).differentiableAt_iff.2
    (hasDerivAt_decayWeight (lt_of_lt_of_le exp_neg_one_lt_one ht)).differentiableAt

private lemma deriv_norm_decayWeight (ht : 1 ≤ t) :
    deriv (fun u : ℝ ↦ ‖decayWeight u‖) t =
      -(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2) := by
  rw [(norm_decayWeight_eventuallyEq ht).deriv_eq]
  exact (hasDerivAt_decayWeight (lt_of_lt_of_le exp_neg_one_lt_one ht)).deriv

private lemma locallyIntegrableOn_deriv_norm_decayWeight :
    LocallyIntegrableOn (deriv fun u : ℝ ↦ ‖decayWeight u‖) (Ici 1) := by
  refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
  have hne : ∀ u ∈ Ici (1 : ℝ), u ≠ 0 := fun u hu ↦ by
    have : (1 : ℝ) ≤ u := hu
    linarith
  have hlog : ∀ u ∈ Ici (1 : ℝ), 1 + Real.log u ≠ 0 := fun u hu ↦ by
    have : (1 : ℝ) ≤ u := hu
    exact (one_add_log_pos (lt_of_lt_of_le exp_neg_one_lt_one this)).ne'
  refine ContinuousOn.congr (f := fun u : ℝ ↦
    -(((1 + Real.log u) ^ 3 + 3 * (1 + Real.log u) ^ 2) / (u * (1 + Real.log u) ^ 3) ^ 2)) ?_
    fun u hu ↦ deriv_norm_decayWeight hu
  have hcont : ContinuousOn (fun u : ℝ ↦ 1 + Real.log u) (Ici 1) :=
    continuousOn_const.add (Real.continuousOn_log.comp continuousOn_id fun u hu ↦ hne u hu)
  refine (((hcont.pow 3).add ((hcont.pow 2).const_smul (3 : ℝ))).div
    ((continuousOn_id.mul (hcont.pow 3)).pow 2) fun u hu ↦ ?_).neg.congr fun _ _ ↦ by
      simp [smul_eq_mul]
  exact pow_ne_zero 2 (mul_ne_zero (hne u hu) (pow_ne_zero 3 (hlog u hu)))

/-! ### The hypotheses of Abel summation -/

/-- The boundedness hypothesis of Abel summation: an `O(t log t)` partial sum times the comparison
weight is bounded, because `log t ≤ (1 + log t) ^ 3` for `t ≥ 1`. -/
private lemma decayWeight_mul_le {C S : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hS : S ≤ C * t * Real.log t) : decayWeight t * S ≤ C := by
  have hL : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hu : (0 : ℝ) < 1 + Real.log t := by linarith
  have hkey : (t * (1 + Real.log t) ^ 3)⁻¹ * (C * t * Real.log t) =
      C * (Real.log t / (1 + Real.log t) ^ 3) := by
    field_simp
  have hratio : Real.log t / (1 + Real.log t) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [pow_pos hu 3, pow_pos hu 2, sq_nonneg (Real.log t)]
  rw [decayWeight]
  calc (t * (1 + Real.log t) ^ 3)⁻¹ * S
      ≤ (t * (1 + Real.log t) ^ 3)⁻¹ * (C * t * Real.log t) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = C * (Real.log t / (1 + Real.log t) ^ 3) := hkey
    _ ≤ C := by nlinarith

/-- The majorant hypothesis of Abel summation: the derivative of the comparison weight times an
`O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, because
`log t (4 + log t) ≤ 4 (1 + log t) ^ 2`. -/
private lemma norm_deriv_decayWeight_mul_le {C S : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hS : S ≤ C * t * Real.log t) :
    ‖-(((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2) * S‖ ≤
      4 * C * ‖(t * (1 + Real.log t) ^ 2)⁻¹‖ := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hL : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hu : (0 : ℝ) < 1 + Real.log t := by linarith
  have hX : (0 : ℝ) < (1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2 := by
    have h3 := pow_pos hu 3
    have h2 := pow_pos hu 2
    linarith
  have hY : (0 : ℝ) < (t * (1 + Real.log t) ^ 3) ^ 2 :=
    pow_pos (mul_pos ht0 (pow_pos hu 3)) 2
  have hdiv : (0 : ℝ) ≤ ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
      (t * (1 + Real.log t) ^ 3) ^ 2 := le_of_lt (div_pos hX hY)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hdiv,
    abs_of_nonneg hS0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t * (1 + Real.log t) ^ 2)⁻¹)]
  have hkey : ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
      (t * (1 + Real.log t) ^ 3) ^ 2 * (C * t * Real.log t) =
        C * Real.log t * (4 + Real.log t) / (t * (1 + Real.log t) ^ 4) := by
    field_simp
    ring
  have hgoal : 4 * C * (t * (1 + Real.log t) ^ 2)⁻¹ =
      4 * C * (1 + Real.log t) ^ 2 / (t * (1 + Real.log t) ^ 4) := by
    field_simp
  calc ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
        (t * (1 + Real.log t) ^ 3) ^ 2 * S
      ≤ ((1 + Real.log t) ^ 3 + 3 * (1 + Real.log t) ^ 2) /
          (t * (1 + Real.log t) ^ 3) ^ 2 * (C * t * Real.log t) :=
        mul_le_mul_of_nonneg_left hS hdiv
    _ = C * Real.log t * (4 + Real.log t) / (t * (1 + Real.log t) ^ 4) := hkey
    _ ≤ 4 * C * (1 + Real.log t) ^ 2 / (t * (1 + Real.log t) ^ 4) := by
        gcongr ?_ / _
        nlinarith [mul_nonneg hC hL, mul_nonneg hC (mul_nonneg hL hL)]
    _ = 4 * C * (t * (1 + Real.log t) ^ 2)⁻¹ := hgoal.symm

/-! ### The weighted series -/

/-- **Abel summation turns an `O(t log t)` growth bound into a convergent series.** If the partial
sums of a nonnegative sequence `u` satisfy `∑_{1 ≤ k ≤ t} u k = O(t log t)`, then
`∑ u n / (n (1 + log n) ^ 3)` converges: summation by parts against the weight
`(t (1 + log t) ^ 3)⁻¹` leaves the integrable majorant `(t (1 + log t) ^ 2)⁻¹`. -/
theorem summable_div_mul_one_add_log_cube {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hgrowth : (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, u k) =O[atTop] fun t : ℝ ↦ t * Real.log t) :
    Summable fun n : ℕ ↦ u n / (n * (1 + Real.log n) ^ 3) := by
  have hnorm : ∀ k : ℕ, ‖u k‖ = u k := fun k ↦ Real.norm_of_nonneg (hu k)
  obtain ⟨C, hC⟩ := hgrowth.bound
  have hbound : ∀ᶠ v : ℝ in atTop,
      ∑ k ∈ Finset.Icc 1 ⌊v⌋₊, u k ≤ max C 0 * v * Real.log v := by
    filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with v hv hv1
    have h0 : (0 : ℝ) ≤ Real.log v := Real.log_nonneg hv1
    have hle : ∑ k ∈ Finset.Icc 1 ⌊v⌋₊, u k ≤ C * (v * Real.log v) := by
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ hu k),
        Real.norm_of_nonneg (by positivity)] at hv
      exact hv
    nlinarith [le_max_left C 0, mul_nonneg (by linarith : (0 : ℝ) ≤ v) h0]
  have hbdd : (fun n : ℕ ↦ ‖decayWeight n‖ * ∑ k ∈ Finset.Icc 1 n, ‖u k‖) =O[atTop]
      fun _ : ℕ ↦ (1 : ℝ) := by
    refine .of_bound (max C 0) ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound,
      eventually_ge_atTop 1] with n hn hn1
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    rw [Nat.floor_natCast] at hn
    simp only [hnorm, norm_one, mul_one]
    rw [Real.norm_of_nonneg (le_of_lt (decayWeight_pos
      (lt_of_lt_of_le exp_neg_one_lt_one hn1')))]
    rw [Real.norm_of_nonneg (mul_nonneg (le_of_lt (decayWeight_pos
      (lt_of_lt_of_le exp_neg_one_lt_one hn1'))) (Finset.sum_nonneg fun k _ ↦ hu k))]
    exact decayWeight_mul_le hn1' (le_max_right C 0) (by linarith [hn])
  have hg1 : (fun v : ℝ ↦ deriv (fun w : ℝ ↦ ‖decayWeight w‖) v *
      ∑ k ∈ Finset.Icc 1 ⌊v⌋₊, ‖u k‖) =O[atTop]
        fun v : ℝ ↦ (v * (1 + Real.log v) ^ 2)⁻¹ := by
    refine .of_bound (4 * max C 0) ?_
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with v hv hv1
    simp only [hnorm]
    rw [deriv_norm_decayWeight hv1]
    exact norm_deriv_decayWeight_mul_le hv1 (le_max_right C 0)
      (Finset.sum_nonneg fun k _ ↦ hu k) hv
  have habel : Summable fun n : ℕ ↦ decayWeight n * u n :=
    summable_mul_of_bigO_atTop' (f := decayWeight) u
      (fun v hv ↦ differentiableAt_norm_decayWeight hv)
      locallyIntegrableOn_deriv_norm_decayWeight hbdd hg1
      integrableAtFilter_inv_mul_one_add_log_sq
  refine habel.congr fun n ↦ ?_
  rw [decayWeight, inv_mul_eq_div]

/-! ### Partial sums against a power weight -/

/-- Restricting a sequence to `n ≥ 1` does not change its sums over `Icc 0 m` against a weight,
provided the weight is read from `Icc 1 m`. -/
private lemma sum_Icc_zero_mul_ite (g c : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 0 m, g k * (if k = 0 then 0 else c k) =
      ∑ n ∈ Finset.Icc 1 m, g n * c n := by
  rw [Finset.sum_Icc_zero_eq_sum_Icc_one (by simp)]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp [hn0]

/-- The Abel-summation identity `sum_mul_eq_sub_integral_mul₀` for the weight `t ^ τ`:
`∑_{1 ≤ n ≤ x} n ^ τ c n = x ^ τ S(x) - τ ∫ t in 1..x, t ^ (τ - 1) S(t)`, where
`S(t) = ∑_{1 ≤ n ≤ t} c n`. For `x < 1` both sides are `0`. -/
theorem sum_Icc_rpow_mul_eq (c : ℕ → ℝ) (τ : ℝ) (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ τ * c n =
      x ^ τ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n -
        τ * ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n := by
  rcases lt_or_ge x 1 with hx | hx
  · -- the sums are empty and the integrand vanishes off the single point `1`
    have h0 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.2 hx
    have hint : ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n = 0 := by
      refine (intervalIntegral.integral_congr_ae (g := fun _ ↦ 0) ?_).trans (by simp)
      filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem MeasureTheory.volume] with t ht
        ht'
      rw [Set.uIoc_of_ge hx.le] at ht'
      have ht1 : t < 1 := lt_of_le_of_ne ht'.2 ht
      simp [Nat.floor_eq_zero.2 ht1]
    simp [h0, hint]
  have hderiv : deriv (fun u : ℝ ↦ u ^ τ) = fun t ↦ τ * t ^ (τ - 1) :=
    funext fun t ↦ Real.deriv_rpow_const t τ
  have habel := sum_mul_eq_sub_integral_mul₀ (f := fun u : ℝ ↦ u ^ τ)
    (fun n ↦ if n = 0 then 0 else c n) (by simp) x
    (fun t ht ↦ (Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt)
    (by
      refine ContinuousOn.integrableOn_Icc (fun t ht ↦ ?_)
      rw [hderiv]
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).const_mul
        τ).continuousWithinAt)
  have hsum (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then 0 else c k) =
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n := by
    simpa using sum_Icc_zero_mul_ite (fun _ ↦ 1) c ⌊t⌋₊
  simp only [sum_Icc_zero_mul_ite, hsum, hderiv] at habel
  rw [habel, intervalIntegral.integral_of_le hx, ← integral_const_mul]
  congr 2
  funext t
  ring

/-- The partial sums of `c`, minus a linear function, are interval integrable from `1` to any
`x`, being a step function minus a continuous function. -/
theorem intervalIntegrable_sum_Icc_sub_mul (c : ℕ → ℝ) (κ x : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n - κ * t) volume 1 x := by
  have hS_int : IntervalIntegrable (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n) volume 1 x := by
    simpa using intervalIntegrable_mul_sum_Icc c (f := fun _ ↦ (1 : ℝ))
      (locallyIntegrableOn_const 1) 1 x
  exact hS_int.sub ((continuous_const.mul continuous_id).intervalIntegrable 1 x)

/-- The Abel-summation identity `sum_Icc_rpow_mul_eq`, with the partial sums `S t` split as
`(S t - κ t) + κ t` inside the integral and everything divided by `x ^ (τ + 1)`. It holds for
every exponent `τ ≠ -1`. -/
theorem sum_Icc_rpow_mul_eq_div_add_integral_sub_mul {c : ℕ → ℝ} {κ τ : ℝ} (hτ : τ ≠ -1)
    {x : ℝ} (hx : 1 ≤ x) :
    x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n -
        τ * ((∫ t in (1 : ℝ)..x, t ^ (τ - 1) *
          (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n - κ * t)) / x ^ (τ + 1)) -
        τ * κ / (τ + 1) + τ * κ / (τ + 1) * (x ^ (τ + 1))⁻¹ =
      (x ^ (τ + 1))⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ τ * c n := by
  have hE_int := intervalIntegrable_sum_Icc_sub_mul c κ x
  set S : ℝ → ℝ := fun t ↦ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n
  set E : ℝ → ℝ := fun t ↦ S t - κ * t with hE
  have hτ1 : τ + 1 ≠ 0 := fun h ↦ hτ (by linarith)
  have hx0 : 0 < x := by linarith
  have h0 : (0 : ℝ) ∉ uIcc 1 x := by
    rw [uIcc_of_le hx]
    exact fun h ↦ by linarith [h.1]
  have hcont : ContinuousOn (fun t : ℝ ↦ t ^ (τ - 1)) (uIcc 1 x) := fun t ht ↦ by
    rw [uIcc_of_le hx] at ht
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt
  have hsplit : ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * S t =
      (∫ t in (1 : ℝ)..x, t ^ (τ - 1) * E t) + κ * ((x ^ (τ + 1) - 1) / (τ + 1)) := by
    have hκ : ∫ t in (1 : ℝ)..x, t ^ τ = (x ^ (τ + 1) - 1) / (τ + 1) := by
      rw [integral_rpow (Or.inr ⟨hτ, h0⟩), Real.one_rpow]
    rw [← hκ, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hE_int.continuousOn_mul hcont)
        ((intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul κ)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [hE]
    rw [Real.rpow_sub_one ht0.ne']
    field_simp
    ring
  rw [sum_Icc_rpow_mul_eq c τ x, hsplit, Real.rpow_add_one hx0.ne']
  field_simp
  ring

/-- **Partial sums weighted by a power.** If the partial sums of `c` grow like `κ x`, that is
`x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then for every exponent `τ > -1` the partial sums weighted by `n ^ τ`
grow like `κ x ^ (τ + 1) / (τ + 1)`:
`(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)`. No sign condition on `c` is needed. -/
theorem tendsto_rpow_inv_mul_sum_Icc_rpow_mul {c : ℕ → ℝ} {κ τ : ℝ} (hτ : -1 < τ)
    (h : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n) atTop (𝓝 κ)) :
    Tendsto (fun x : ℝ ↦ (x ^ (τ + 1))⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ) ^ τ * c n) atTop
      (𝓝 (κ / (τ + 1))) := by
  have hτ1 : 0 < τ + 1 := by linarith
  have hI := (isLittleO_integral_rpow_sub_one_mul hτ
    (fun x _ ↦ intervalIntegrable_sum_Icc_sub_mul c κ x)
    ((isLittleO_sub_mul_iff_tendsto_div (eventually_ne_atTop 0)).mpr
      (by simpa [div_eq_mul_inv, mul_comm] using h))).tendsto_div_nhds_zero
  have hpow : Tendsto (fun x : ℝ ↦ (x ^ (τ + 1))⁻¹) atTop (𝓝 0) :=
    (tendsto_rpow_atTop hτ1).inv_tendsto_atTop
  have hlim := ((h.sub (hI.const_mul τ)).sub_const (τ * κ / (τ + 1))).add
    (hpow.const_mul (τ * κ / (τ + 1)))
  have hval : κ - τ * 0 - τ * κ / (τ + 1) + τ * κ / (τ + 1) * 0 = κ / (τ + 1) := by
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact sum_Icc_rpow_mul_eq_div_add_integral_sub_mul hτ.ne' hx

/-! ### The weight `1 / log t` -/

/-- Restricting a sequence to `k ≥ 2` turns sums over `Icc 0 n` into sums over `Icc 2 n`. -/
private lemma sum_Icc_zero_ite_two_le (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, (if 2 ≤ k then g k else 0) = ∑ k ∈ Finset.Icc 2 n, g k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The Abel-summation identity `sum_mul_eq_sub_integral_mul₁` for the weight `1 / log t`:
`∑_{2 ≤ k ≤ x} c k / log k = S(x) / log x + ∫_2^x S(t) / (t log² t) dt`, where
`S(t) = ∑_{2 ≤ k ≤ t} c k`. For `x < 2` both sides are `0`. -/
theorem sum_Icc_div_log_eq (c : ℕ → ℝ) (x : ℝ) :
    ∑ k ∈ Finset.Icc 2 ⌊x⌋₊, c k / Real.log k =
      (∑ k ∈ Finset.Icc 2 ⌊x⌋₊, c k) / Real.log x +
        ∫ t in Ioc 2 x, (∑ k ∈ Finset.Icc 2 ⌊t⌋₊, c k) * (t⁻¹ / Real.log t ^ 2) := by
  have hIcc : Icc (2 : ℝ) x ⊆ Ioi 1 := fun t ht ↦ one_lt_two.trans_le ht.1
  have habel := sum_mul_eq_sub_integral_mul₁ (f := fun t ↦ (Real.log t)⁻¹)
    (fun k ↦ if 2 ≤ k then c k else 0) (by simp) (by simp) x
    (fun t ht ↦ Real.differentiableOn_inv_log.differentiableAt (Ioi_mem_nhds (hIcc ht)))
    (by
      rw [Real.deriv_inv_log]
      refine ContinuousOn.integrableOn_Icc ?_
      simpa only [neg_div] using ((Real.continuousOn_inv_div_log_pow 2).mono hIcc).fun_neg)
  have hsum (n : ℕ) : ∑ k ∈ Finset.Icc 0 n, (Real.log k)⁻¹ * (if 2 ≤ k then c k else 0) =
      ∑ k ∈ Finset.Icc 2 n, c k / Real.log k := by
    simp_rw [mul_ite, mul_zero, sum_Icc_zero_ite_two_le, div_eq_inv_mul]
  simp only [hsum, sum_Icc_zero_ite_two_le, Real.deriv_inv_log] at habel
  rw [habel, sub_eq_add_neg, ← integral_neg]
  congr 1
  · ring
  · refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    ring

/-- If `S` differs from `log t` by at most `C` for `t ≥ 2`, then the error weighted by
`1 / (t log² t)` is integrable on `(a, ∞)` for `a ≥ 2`, and its integral there is at most
`C / log a`. -/
private lemma integrableOn_Ioi_sub_log_mul {S : ℝ → ℝ} {C a : ℝ} (hS : Measurable S)
    (h : ∀ t : ℝ, 2 ≤ t → |S t - Real.log t| ≤ C) (ha : 2 ≤ a) :
    IntegrableOn (fun t ↦ (S t - Real.log t) * (t⁻¹ / Real.log t ^ 2)) (Ioi a) ∧
      |∫ t in Ioi a, (S t - Real.log t) * (t⁻¹ / Real.log t ^ 2)| ≤ C / Real.log a := by
  have ha1 : (1 : ℝ) < a := by linarith
  -- The integrand is dominated by `C / (t log² t)`, which is integrable at infinity.
  have hle : ∀ᵐ t ∂volume.restrict (Ioi a),
      ‖(S t - Real.log t) * (t⁻¹ / Real.log t ^ 2)‖ ≤ C * (t⁻¹ / Real.log t ^ 2) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : a < t) ↦ ?_
    have hw : 0 ≤ t⁻¹ / Real.log t ^ 2 := div_nonneg (inv_nonneg.mpr (by linarith)) (sq_nonneg _)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right (h t (ha.trans ht.le)) hw
  refine ⟨((integrableOn_inv_div_log_sq_Ioi ha1).const_mul C).mono'
    ((hS.sub Real.measurable_log).mul
      (measurable_inv.div (Real.measurable_log.pow_const 2))).aestronglyMeasurable hle, ?_⟩
  rw [div_eq_mul_inv, ← integral_inv_div_log_sq_Ioi ha1, ← integral_const_mul,
    ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le ((integrableOn_inv_div_log_sq_Ioi ha1).const_mul C) hle

/-- **The right-hand side of partial summation against `1 / log`.** If a measurable `S` differs
from `log t` by at most `C` for every `t ≥ 2`, then there is a constant `B` with
`|S(x) / log x + ∫_2^x S(t) / (t log² t) dt - log log x - B| ≤ 2 C / log x` for every `x ≥ 2`.
When `S` is the partial-sum function of a sequence `c`, the left-hand expression is
`∑_{2 ≤ k ≤ x} c k / log k` by Abel summation (`sum_Icc_div_log_eq` over `ℕ`,
`primeSummatory_div_log_eq_div_log_add_integral` over the prime ideals of a number field). -/
theorem exists_abs_div_log_add_integral_sub_log_log_sub_le {S : ℝ → ℝ} {C : ℝ}
    (hS : Measurable S) (h : ∀ t : ℝ, 2 ≤ t → |S t - Real.log t| ≤ C) :
    ∃ B, ∀ x : ℝ, 2 ≤ x →
      |S x / Real.log x + (∫ t in Ioc 2 x, S t * (t⁻¹ / Real.log t ^ 2)) -
        Real.log (Real.log x) - B| ≤ 2 * C / Real.log x := by
  set R : ℝ → ℝ := fun t ↦ (S t - Real.log t) * (t⁻¹ / Real.log t ^ 2)
  have hRint {a : ℝ} (ha : 2 ≤ a) := integrableOn_Ioi_sub_log_mul hS h ha
  refine ⟨1 - Real.log (Real.log 2) + ∫ t in Ioi 2, R t, fun x hx ↦ ?_⟩
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hIcc : Icc (2 : ℝ) x ⊆ Ioi 1 := fun t ht ↦ one_lt_two.trans_le ht.1
  -- Split `S t / (t log² t)` as `1 / (t log t)` plus `R t`, and integrate the first part.
  have hmain : ∫ t in Ioc 2 x, S t * (t⁻¹ / Real.log t ^ 2) =
      Real.log (Real.log x) - Real.log (Real.log 2) + ∫ t in Ioc 2 x, R t := by
    have hint₁ : IntegrableOn (fun t : ℝ ↦ t⁻¹ / Real.log t) (Ioc 2 x) := by
      simpa only [pow_one] using
        ((Real.continuousOn_inv_div_log_pow 1).mono hIcc).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self
    rw [← integral_inv_div_log one_lt_two (by linarith), intervalIntegral.integral_of_le hx,
      ← integral_add hint₁ ((hRint le_rfl).1.mono_set Ioc_subset_Ioi_self)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    field_simp
    ring
  -- Split the integral of `R` over `(2, ∞)` at `x`.
  have hsplit : ∫ t in Ioc 2 x, R t = (∫ t in Ioi 2, R t) - ∫ t in Ioi x, R t := by
    rw [← Ioc_union_Ioi_eq_Ioi hx, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi ((hRint le_rfl).1.mono_set Ioc_subset_Ioi_self) (hRint hx).1]
    ring
  have hSx : |S x / Real.log x - 1| ≤ C / Real.log x := by
    rw [← div_self hlogx.ne', ← sub_div, abs_div, abs_of_pos hlogx]
    exact div_le_div_of_nonneg_right (h x hx) hlogx.le
  rw [hmain, hsplit]
  calc _ = |(S x / Real.log x - 1) - ∫ t in Ioi x, R t| := by congr 1; ring
    _ ≤ |S x / Real.log x - 1| + |∫ t in Ioi x, R t| := abs_sub _ _
    _ ≤ 2 * C / Real.log x := by rw [mul_div_assoc]; linarith [(hRint hx).2]

/-- **Partial sums weighted by `1 / log`.** If the partial sums `∑_{2 ≤ k ≤ t} c k` differ from
`log t` by at most `C` for every `t ≥ 2`, then there is a constant `B` with
`|∑_{2 ≤ k ≤ x} c k / log k - log log x - B| ≤ 2 C / log x` for every `x ≥ 2`. Applied to the
coefficients `log p / p` on the primes, this turns Mertens' first theorem into his second. -/
theorem exists_abs_sum_Icc_div_log_sub_log_log_sub_le {c : ℕ → ℝ} {C : ℝ}
    (h : ∀ t : ℝ, 2 ≤ t → |∑ k ∈ Finset.Icc 2 ⌊t⌋₊, c k - Real.log t| ≤ C) :
    ∃ B, ∀ x : ℝ, 2 ≤ x →
      |∑ k ∈ Finset.Icc 2 ⌊x⌋₊, c k / Real.log k - Real.log (Real.log x) - B| ≤
        2 * C / Real.log x := by
  obtain ⟨B, hB⟩ := exists_abs_div_log_add_integral_sub_log_log_sub_le
    (S := fun t ↦ ∑ k ∈ Finset.Icc 2 ⌊t⌋₊, c k)
    ((measurable_from_nat (f := fun n ↦ ∑ k ∈ Finset.Icc 2 n, c k)).comp Nat.measurable_floor) h
  exact ⟨B, fun x hx ↦ by simpa only [← sum_Icc_div_log_eq] using hB x hx⟩

end TauCeti
