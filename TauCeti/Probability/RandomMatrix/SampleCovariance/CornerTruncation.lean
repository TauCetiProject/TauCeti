/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.MeasureTheory.Function.EventualBound

/-!
# Truncation of random arrays with a finite fourth moment

Let `x (i, j)` be an array of random variables with a common law `ν` of finite fourth moment,
and let `p n = O(n)`. Almost surely, every entry of the top-left `p n × n` corner of the array is
eventually at most `δ √n` in norm, for every fixed `δ > 0`. The level `δ` can moreover be replaced
by a deterministic sequence `δ n → 0` with `δ n √n → ∞`, so that almost surely the corners
eventually coincide with their truncations at the levels `δ n √n`.

This is the first step in the proof that the largest eigenvalue of a sample covariance matrix
converges to the edge of the Marchenko–Pastur law under a fourth moment: the truncated entries
are again identically distributed, and independent if the original ones are, and they are
bounded by `δ n √n`, which makes moments of growing order accessible to the trace method.

Neither independence nor any centring is needed here.

## Main statements

* `TauCeti.Probability.ae_eventually_forall_norm_le_mul_sqrt`: for fixed `δ > 0`, almost surely
  the corner entries are eventually at most `δ √n` in norm.
* `TauCeti.Probability.exists_tendsto_zero_ae_eventually_forall_norm_le_mul_sqrt`: the same with
  a deterministic level `δ n → 0` satisfying `δ n √n → ∞`.

## Implementation notes

The fixed-level statement is a first Borel–Cantelli argument over the entries. Since eventually
`p n ≤ C n`, the entry `(i, j)` can belong to the `n`-th corner only if `n ≥ j + 1` and
`C n ≥ i + 1`, that is, `n ≥ max (j + 1) ((i + 1) / C)`. The probabilities that it exceeds `δ`
times the square root of this lower bound are summable: the number of entries whose lower bound
is below `T` is at most `C T²`, and `∫ ‖z‖⁴ dν` is finite. The deterministic level comes from
`TauCeti.MeasureTheory.exists_tendsto_zero_ae_eventually_le`.

## References

* Y. Q. Yin, Z. D. Bai and P. R. Krishnaiah, *On the limit of the largest eigenvalue of the
  large dimensional sample covariance matrix*, Probab. Theory Related Fields 78 (1988),
  509–521, the truncation step.
* Z. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  second edition, Springer, 2010, the truncation step in the proof of Theorem 5.8.
-/

public section

open Filter MeasureTheory ProbabilityTheory Asymptotics Set
open scoped ENNReal Topology

namespace TauCeti.Probability

/-- For `C > 0`, the entries `(i, j)` with `max (j + 1) ((i + 1) / C) < f z` number at most
`C (f z)²`. -/
private theorem tsum_indicator_max_lt_le {E : Type*} {C : ℝ} (hC : 0 < C) (f : E → ℝ) (z : E) :
    ∑' ij : ℕ × ℕ,
        {z | max ((ij.2 : ℝ) + 1) (((ij.1 : ℝ) + 1) / C) < f z}.indicator (1 : E → ℝ≥0∞) z ≤
      ENNReal.ofReal (C * f z ^ 2) := by
  set F : Finset (ℕ × ℕ) := Finset.range ⌊C * f z⌋₊ ×ˢ Finset.range ⌊f z⌋₊
  have hmem (ij : ℕ × ℕ) (h : max ((ij.2 : ℝ) + 1) (((ij.1 : ℝ) + 1) / C) < f z) : ij ∈ F := by
    rw [max_lt_iff, div_lt_iff₀ hC] at h
    simp only [F, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_of_succ_le (Nat.le_floor (by push_cast; linarith)),
      Nat.lt_of_succ_le (Nat.le_floor (by push_cast; linarith))⟩
  rw [tsum_eq_sum (s := F) fun ij hij ↦ indicator_of_notMem (fun h ↦ hij (hmem ij h)) _]
  refine (Finset.sum_le_card_nsmul F _ 1 fun ij _ ↦ indicator_le_self' (by simp) z).trans ?_
  have hcard : ((⌊C * f z⌋₊ * ⌊f z⌋₊ : ℕ) : ℝ) ≤ C * f z ^ 2 := by
    rcases le_or_gt 0 (f z) with hz | hz
    · push_cast
      nlinarith [Nat.floor_le (mul_nonneg hC.le hz), Nat.floor_le hz,
        Nat.cast_nonneg (α := ℝ) ⌊C * f z⌋₊]
    · simp only [Nat.floor_of_nonpos hz.le, mul_zero, Nat.cast_zero]
      positivity
  simpa [F, ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {P : Measure Ω} {ν : Measure E} {x : ℕ × ℕ → Ω → E} {p : ℕ → ℕ}

/-- **Truncation at a fixed level.** If the entries of an array have a common law with finite
fourth moment and `p n = O(n)`, then for every `δ > 0`, almost surely all entries of the top-left
`p n × n` corner are eventually at most `δ √n` in norm. -/
theorem ae_eventually_forall_norm_le_mul_sqrt (hx : ∀ ij, HasLaw (x ij) ν P)
    (h4 : Integrable (fun z ↦ ‖z‖ ^ 4) ν) (hp : (fun n ↦ (p n : ℝ)) =O[atTop] fun n ↦ (n : ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < p n, ∀ j < n, ‖x (i, j) ω‖ ≤ δ * √n := by
  obtain ⟨C₀, hC₀⟩ := hp.bound
  set C := max C₀ 1
  have hC : 0 < C := lt_max_of_lt_right one_pos
  have hpC : ∀ᶠ n in atTop, (p n : ℝ) ≤ C * n := hC₀.mono fun n hn ↦ by
    simpa using hn.trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (norm_nonneg _))
  -- The entry `ij` is bad when it exceeds `δ` times the square root of its corner-index bound.
  set m : ℕ × ℕ → ℝ := fun ij ↦ max ((ij.2 : ℝ) + 1) (((ij.1 : ℝ) + 1) / C)
  have hmeas (ij : ℕ × ℕ) : MeasurableSet {z : E | m ij < ‖z‖ ^ 2 / δ ^ 2} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hsum : ∑' ij, P {ω | m ij < ‖x ij ω‖ ^ 2 / δ ^ 2} ≠ ∞ := by
    have hint : Integrable (fun z ↦ C / δ ^ 4 * ‖z‖ ^ 4) ν := h4.const_mul _
    refine ne_of_lt (lt_of_le_of_lt ?_ hint.lintegral_lt_top)
    calc ∑' ij, P {ω | m ij < ‖x ij ω‖ ^ 2 / δ ^ 2}
        = ∫⁻ z, ∑' ij, {z | m ij < ‖z‖ ^ 2 / δ ^ 2}.indicator 1 z ∂ν := by
          rw [lintegral_tsum fun ij ↦ (measurable_one.indicator (hmeas ij)).aemeasurable]
          simp_rw [lintegral_indicator_one (hmeas _)]
          exact tsum_congr fun ij ↦ (hx ij).measure_eq (hmeas ij)
      _ ≤ ∫⁻ z, ENNReal.ofReal (C / δ ^ 4 * ‖z‖ ^ 4) ∂ν := by
          refine lintegral_mono fun z ↦ (tsum_indicator_max_lt_le hC _ z).trans_eq ?_
          congr 1
          field_simp
  filter_upwards [ae_finite_setOfPred_mem hsum] with ω hF
  -- The finitely many bad entries are eventually below `δ √n` because `√n → ∞`.
  have hsqrt : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, ∀ ij ∈ {ij | m ij < ‖x ij ω‖ ^ 2 / δ ^ 2}, ‖x ij ω‖ ≤ δ * √n :=
    (eventually_all_finite hF).2 fun ij _ ↦ (hsqrt.const_mul_atTop hδ).eventually_ge_atTop _
  filter_upwards [hlarge, hpC] with n hn hpn i hi j hj
  by_cases hij : m (i, j) < ‖x (i, j) ω‖ ^ 2 / δ ^ 2
  · exact hn _ hij
  -- A good entry is at most `δ` times the square root of its corner-index bound, which is `≤ n`.
  have hmn : m (i, j) ≤ n := by
    have hi' : ((i : ℝ) + 1) ≤ p n := by exact_mod_cast hi
    have hj' : ((j : ℝ) + 1) ≤ n := by exact_mod_cast hj
    exact max_le hj' ((div_le_iff₀ hC).2 (by linarith))
  have hsq : ‖x (i, j) ω‖ ^ 2 ≤ (δ * √n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_comm]
    exact (div_le_iff₀ (by positivity)).1 ((not_lt.1 hij).trans hmn)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Truncation at a deterministic vanishing level.** If the entries of an array have a common
law with finite fourth moment and `p n = O(n)`, then there is a deterministic sequence `δ n → 0`
with `δ n √n → ∞` such that, almost surely, all entries of the top-left `p n × n` corner are
eventually at most `δ n √n` in norm. -/
theorem exists_tendsto_zero_ae_eventually_forall_norm_le_mul_sqrt [SFinite P]
    (hx : ∀ ij, HasLaw (x ij) ν P) (h4 : Integrable (fun z ↦ ‖z‖ ^ 4) ν)
    (hp : (fun n ↦ (p n : ℝ)) =O[atTop] fun n ↦ (n : ℝ)) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ Tendsto (fun n ↦ δ n * √n) atTop atTop ∧
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < p n, ∀ j < n, ‖x (i, j) ω‖ ≤ δ n * √n := by
  -- The largest normalized corner entry is almost surely eventually below every `ε > 0`.
  set Y : ℕ → Ω → ℝ := fun n ω ↦ ⨆ ij : Fin (p n) × Fin n, ‖x (ij.1, ij.2) ω‖ / √n
  have hY (n : ℕ) : AEMeasurable (Y n) P :=
    AEMeasurable.iSup fun ij ↦ (hx _).aemeasurable.norm.div_const _
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Y n ω ≤ ε := by
    filter_upwards [ae_eventually_forall_norm_le_mul_sqrt hx h4 hp hε] with ω hω
    filter_upwards [hω, eventually_gt_atTop 0] with n hn hn0
    refine Real.iSup_le (fun ij ↦ ?_) hε.le
    rw [div_le_iff₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn0))]
    exact hn _ ij.1.isLt _ ij.2.isLt
  obtain ⟨δ₀, hδ₀, hYδ₀⟩ := MeasureTheory.exists_tendsto_zero_ae_eventually_le hY hsmall
  -- Raising `δ₀ n` to at least `n ^ (-1/4)` makes the truncation level tend to infinity.
  have hroot : Tendsto (fun n : ℕ ↦ √√(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨fun n ↦ max (δ₀ n) (√√(n : ℝ))⁻¹, by simpa using hδ₀.max hroot.inv_tendsto_atTop, ?_, ?_⟩
  · refine tendsto_atTop_mono' atTop ?_ hroot
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < √√(n : ℝ) := Real.sqrt_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 hn))
    calc √√(n : ℝ) = (√√(n : ℝ))⁻¹ * (√√(n : ℝ) * √√(n : ℝ)) :=
          (inv_mul_cancel_left₀ hpos.ne' _).symm
      _ = (√√(n : ℝ))⁻¹ * √(n : ℝ) := by rw [Real.mul_self_sqrt (Real.sqrt_nonneg _)]
      _ ≤ max (δ₀ n) (√√(n : ℝ))⁻¹ * √(n : ℝ) := by gcongr; exact le_max_right _ _
  · filter_upwards [hYδ₀] with ω hω
    filter_upwards [hω, eventually_gt_atTop 0] with n hn hn0 i hi j hj
    have hentry : ‖x (i, j) ω‖ / √n ≤ Y n ω :=
      le_ciSup (f := fun ij : Fin (p n) × Fin n ↦ ‖x (ij.1, ij.2) ω‖ / √n)
        (Set.finite_range _).bddAbove (⟨i, hi⟩, ⟨j, hj⟩)
    rw [div_le_iff₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn0))] at hentry
    exact hentry.trans (by gcongr; exact hn.trans (le_max_left _ _))

end TauCeti.Probability
