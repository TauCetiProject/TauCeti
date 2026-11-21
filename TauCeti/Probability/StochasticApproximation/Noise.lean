/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecificLimits.Averaging
public import TauCeti.Probability.Martingale.DifferenceSeries

/-!
# The scalar noise lemma of stochastic approximation

Let `ℱ` be a filtration on a finite measure space, `α t` adapted step sizes and `w t` a noise
which is `ℱ (t + 1)`-measurable and square-integrable, with conditional mean `P[w t | ℱ t] = 0`
and conditional second moment `P[(w t) ^ 2 | ℱ t] ≤ B t`. Assume that almost surely the bounds
`B t` are bounded in `t`, `∑ α t = ∞` and `∑ (α t) ^ 2 < ∞`. The noise lemma says that the
averaged noise

`W (t + 1) = (1 - α t) W t + α t w t`

tends to `0` almost surely, for steps `α t ≥ 0` and any initial value `W 0`; the usual bound
`α t ≤ 1` holds automatically from some time on, since `α t → 0`. For
`α t = 1 / (t + 1)`, `W t` is the running average of `w 0, …, w (t - 1)`, and the lemma is the
strong law of large numbers for martingale differences of bounded conditional variance. In
stochastic approximation it controls the accumulated noise of each coordinate of the iteration.

The bounds `B t` and the sum `∑ (α t) ^ 2` are only almost surely bounded, not by constants, so
the martingale `∑_{s < t} α s w s` need not be bounded in `L²`. For each `k` we cut it off from the
first time at which the conditional second moment or the running sum of the squared steps
exceeds `k`. The truncated martingale has second moment at most `k ^ 2` times the total
mass, so it converges almost surely, and almost every path is never cut off for `k` large
enough. Summation by parts then shows that `W t → 0` wherever the series `∑ α t w t`
converges and `∑ α t = ∞`.

## Main results

* `TauCeti.exists_ae_tendsto_sum_range_mul`: the series `∑ α t w t` converges almost surely
  (no sign or size condition on `α` is needed here).
* `TauCeti.ae_tendsto_zero_noise`: the noise lemma, `W t → 0` almost surely.

## References

* J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Mach. Learn. **16**
  (1994), 185–202, Lemma 1, where `∑ (α t) ^ 2` is bounded by a constant.
-/

public section

open Filter Finset Topology MeasureTheory

namespace TauCeti

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℕ m₀}
  {α w : ℕ → Ω → ℝ}

/-- The event that up to time `s` the conditional second moments of the noise stay at most `k`
and the sum of the squared steps is at most `k`. -/
private def truncSet (P : Measure Ω) (ℱ : Filtration ℕ m₀) (α w : ℕ → Ω → ℝ) (k s : ℕ) :
    Set Ω :=
  {ω | (∀ r ≤ s, P[w r ^ 2 | ℱ r] ω ≤ (k : ℝ)) ∧ ∑ q ∈ range (s + 1), α q ω ^ 2 ≤ (k : ℝ)}

private lemma mem_truncSet {k s : ℕ} {ω : Ω} : ω ∈ truncSet P ℱ α w k s ↔
    (∀ r ≤ s, P[w r ^ 2 | ℱ r] ω ≤ (k : ℝ)) ∧ ∑ q ∈ range (s + 1), α q ω ^ 2 ≤ (k : ℝ) :=
  Iff.rfl

private lemma measurableSet_truncSet (hα : Adapted ℱ α) (k s : ℕ) :
    MeasurableSet[ℱ s] (truncSet P ℱ α w k s) := by
  simp only [truncSet, Set.ofPred_and]
  refine MeasurableSet.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun hr ↦
      measurableSet_le (stronglyMeasurable_condExp.measurable.mono (ℱ.mono hr) le_rfl)
        measurable_const
  · exact measurableSet_le (Finset.measurable_fun_sum _ fun q hq ↦
      ((hα q).mono (ℱ.mono (Nat.lt_succ_iff.1 (mem_range.1 hq))) le_rfl).pow_const 2)
      measurable_const

/-- The step `α s`, set to `0` off the truncation event at time `s`. -/
private noncomputable def truncStep (P : Measure Ω) (ℱ : Filtration ℕ m₀) (α w : ℕ → Ω → ℝ)
    (k s : ℕ) : Ω → ℝ :=
  (truncSet P ℱ α w k s).indicator (α s)

private lemma stronglyMeasurable_truncStep (hα : Adapted ℱ α) (k s : ℕ) :
    StronglyMeasurable[ℱ s] (truncStep P ℱ α w k s) :=
  ((hα s).indicator (measurableSet_truncSet hα k s)).stronglyMeasurable

/-- The truncated step is bounded by `k + 1`. -/
private lemma abs_truncStep_le (k s : ℕ) (ω : Ω) : |truncStep P ℱ α w k s ω| ≤ k + 1 := by
  by_cases h : ω ∈ truncSet P ℱ α w k s
  · rw [truncStep, Set.indicator_of_mem h]
    have hsq : α s ω ^ 2 ≤ k :=
      (single_le_sum (fun q _ ↦ sq_nonneg (α q ω)) (self_mem_range_succ s)).trans
        (mem_truncSet.1 h).2
    nlinarith [sq_abs (α s ω), abs_nonneg (α s ω)]
  · rw [truncStep, Set.indicator_of_notMem h, abs_zero]
    positivity

/-- Where the truncated step is nonzero, the conditional second moment of the noise is at
most `k`. -/
private lemma truncStep_sq_mul_condExp_le (k s : ℕ) (ω : Ω) :
    truncStep P ℱ α w k s ω ^ 2 * P[w s ^ 2 | ℱ s] ω ≤ k * truncStep P ℱ α w k s ω ^ 2 := by
  by_cases h : ω ∈ truncSet P ℱ α w k s
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right ((mem_truncSet.1 h).1 s le_rfl) (sq_nonneg _)
  · simp [truncStep, Set.indicator_of_notMem h]

/-- The squared truncated steps sum to at most `k`. -/
private lemma sum_truncStep_sq_le (k t : ℕ) (ω : Ω) :
    ∑ s ∈ range t, truncStep P ℱ α w k s ω ^ 2 ≤ k := by
  induction t with
  | zero => simp
  | succ t ih =>
    by_cases h : ω ∈ truncSet P ℱ α w k t
    · refine (sum_le_sum fun s _ ↦ ?_).trans (mem_truncSet.1 h).2
      by_cases hs : ω ∈ truncSet P ℱ α w k s
      · rw [truncStep, Set.indicator_of_mem hs]
      · rw [truncStep, Set.indicator_of_notMem hs]
        simp [sq_nonneg]
    · rwa [sum_range_succ, truncStep, Set.indicator_of_notMem h, zero_pow two_ne_zero, add_zero]

private lemma integrable_truncStep_sq [IsFiniteMeasure P] (hα : Adapted ℱ α) (k s : ℕ) :
    Integrable (fun ω ↦ truncStep P ℱ α w k s ω ^ 2) P :=
  Integrable.of_bound
    (((stronglyMeasurable_truncStep hα k s).mono (ℱ.le s)).aestronglyMeasurable.pow 2)
    ((k + 1) ^ 2) (ae_of_all _ fun ω ↦ by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncStep_le k s ω) 2)

private lemma stronglyMeasurable_truncStep_mul (hα : Adapted ℱ α)
    (hw : ∀ t, Measurable[ℱ (t + 1)] (w t)) (k s : ℕ) :
    StronglyMeasurable[ℱ (s + 1)] fun ω ↦ truncStep P ℱ α w k s ω * w s ω :=
  ((stronglyMeasurable_truncStep hα k s).mono (ℱ.mono s.le_succ)).mul (hw s).stronglyMeasurable

private lemma memLp_truncStep_mul (hα : Adapted ℱ α) (hw : ∀ t, Measurable[ℱ (t + 1)] (w t))
    (hw₂ : ∀ t, MemLp (w t) 2 P) (k s : ℕ) :
    MemLp (fun ω ↦ truncStep P ℱ α w k s ω * w s ω) 2 P :=
  (hw₂ s).of_le_mul (c := k + 1)
    ((stronglyMeasurable_truncStep_mul hα hw k s).mono (ℱ.le _)).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ by
      rw [norm_mul, Real.norm_eq_abs (truncStep P ℱ α w k s ω)]
      exact mul_le_mul_of_nonneg_right (abs_truncStep_le k s ω) (norm_nonneg _))

/-- The truncated noise terms are martingale differences. -/
private lemma condExp_truncStep_mul [IsFiniteMeasure P] (hα : Adapted ℱ α)
    (hw : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw₂ : ∀ t, MemLp (w t) 2 P)
    (hw_condExp : ∀ t, P[w t | ℱ t] =ᵐ[P] 0) (k s : ℕ) :
    P[fun ω ↦ truncStep P ℱ α w k s ω * w s ω | ℱ s] =ᵐ[P] 0 :=
  -- For real functions `f • g` is `f * g` by `smul_eq_mul`.
  condExp_smul_eq_zero_of_condExp_eq_zero
    (stronglyMeasurable_truncStep hα k s).aestronglyMeasurable
    ((memLp_truncStep_mul hα hw hw₂ k s).integrable one_le_two)
    ((hw₂ s).integrable one_le_two) (hw_condExp s)

/-- The second moment of a truncated noise term is at most `k` times that of the truncated
step. -/
private lemma integral_truncStep_mul_sq_le [IsFiniteMeasure P] (hα : Adapted ℱ α)
    (hw : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw₂ : ∀ t, MemLp (w t) 2 P) (k s : ℕ) :
    ∫ ω, (truncStep P ℱ α w k s ω * w s ω) ^ 2 ∂P ≤
      k * ∫ ω, truncStep P ℱ α w k s ω ^ 2 ∂P := by
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (f := fun ω ↦ truncStep P ℱ α w k s ω ^ 2) (g := w s ^ 2) (m := ℱ s) (μ := P)
    ((stronglyMeasurable_truncStep hα k s).pow 2)
    ((memLp_truncStep_mul hα hw hw₂ k s).integrable_sq.congr
      (ae_of_all _ fun ω ↦ mul_pow _ _ 2)) (hw₂ s).integrable_sq
  calc ∫ ω, (truncStep P ℱ α w k s ω * w s ω) ^ 2 ∂P
      = ∫ ω, P[(fun ω ↦ truncStep P ℱ α w k s ω ^ 2) * w s ^ 2 | ℱ s] ω ∂P := by
        rw [integral_condExp (ℱ.le s)]
        simp only [mul_pow, Pi.mul_apply, Pi.pow_apply]
    _ = ∫ ω, truncStep P ℱ α w k s ω ^ 2 * P[w s ^ 2 | ℱ s] ω ∂P := integral_congr_ae hpull
    _ ≤ ∫ ω, k * truncStep P ℱ α w k s ω ^ 2 ∂P := by
        refine integral_mono_of_nonneg ?_ ((integrable_truncStep_sq hα k s).const_mul _)
          (ae_of_all _ fun ω ↦ truncStep_sq_mul_condExp_le k s ω)
        filter_upwards [condExp_nonneg (m := ℱ s) (μ := P) (f := w s ^ 2)
          (ae_of_all _ fun ω ↦ sq_nonneg (w s ω))] with ω hω
        exact mul_nonneg (sq_nonneg _) hω
    _ = k * ∫ ω, truncStep P ℱ α w k s ω ^ 2 ∂P := integral_const_mul _ _

/-- For every cutoff `k`, the truncated noise series converges almost surely: its terms are
martingale differences whose second moments sum to at most `k ^ 2 P univ`. -/
private lemma exists_ae_tendsto_sum_range_truncStep_mul [IsFiniteMeasure P] (hα : Adapted ℱ α)
    (hw : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw₂ : ∀ t, MemLp (w t) 2 P)
    (hw_condExp : ∀ t, P[w t | ℱ t] =ᵐ[P] 0) (k : ℕ) :
    ∀ᵐ ω ∂P, ∃ L, Tendsto (fun t ↦ ∑ s ∈ range t, truncStep P ℱ α w k s ω * w s ω) atTop
      (𝓝 L) := by
  refine exists_ae_tendsto_sum_range_of_summable_integral_sq
    (stronglyMeasurable_truncStep_mul hα hw k) (memLp_truncStep_mul hα hw hw₂ k)
    (condExp_truncStep_mul hα hw hw₂ hw_condExp k)
    (summable_of_sum_range_le (c := k * (k * P.real Set.univ))
      (fun s ↦ integral_nonneg fun ω ↦ sq_nonneg _) fun t ↦ ?_)
  calc ∑ s ∈ range t, ∫ ω, (truncStep P ℱ α w k s ω * w s ω) ^ 2 ∂P
      ≤ ∑ s ∈ range t, k * ∫ ω, truncStep P ℱ α w k s ω ^ 2 ∂P :=
        sum_le_sum fun s _ ↦ integral_truncStep_mul_sq_le hα hw hw₂ k s
    _ = k * ∫ ω, ∑ s ∈ range t, truncStep P ℱ α w k s ω ^ 2 ∂P := by
        rw [← mul_sum, integral_finsetSum _ fun s _ ↦ integrable_truncStep_sq hα k s]
    _ ≤ k * ∫ _, (k : ℝ) ∂P :=
        mul_le_mul_of_nonneg_left (integral_mono (integrable_finsetSum _ fun s _ ↦
          integrable_truncStep_sq hα k s) (integrable_const _) fun ω ↦ sum_truncStep_sq_le k t ω)
          (Nat.cast_nonneg k)
    _ = k * (k * P.real Set.univ) := by
        rw [integral_const, smul_eq_mul, mul_comm (P.real Set.univ)]

/-- **Convergence of the noise series.** If the steps `α t` are adapted and almost surely
square-summable, and the noise `w t` is an `ℱ (t + 1)`-measurable square-integrable martingale
difference whose conditional second moments are almost surely bounded in `t`, then the series
`∑ α t w t` converges almost surely. -/
theorem exists_ae_tendsto_sum_range_mul [IsFiniteMeasure P] {B : ℕ → Ω → ℝ}
    (hα : Adapted ℱ α) (hw : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw₂ : ∀ t, MemLp (w t) 2 P)
    (hw_condExp : ∀ t, P[w t | ℱ t] =ᵐ[P] 0) (hw_sq : ∀ t, P[w t ^ 2 | ℱ t] ≤ᵐ[P] B t)
    (hB : ∀ᵐ ω ∂P, BddAbove (Set.range fun t ↦ B t ω))
    (hα_sq : ∀ᵐ ω ∂P, Summable fun t ↦ α t ω ^ 2) :
    ∀ᵐ ω ∂P, ∃ c, Tendsto (fun t ↦ ∑ s ∈ range t, α s ω * w s ω) atTop (𝓝 c) := by
  -- Almost every path is never cut off once `k` dominates its bounds.
  filter_upwards [ae_all_iff.2 (exists_ae_tendsto_sum_range_truncStep_mul hα hw hw₂ hw_condExp),
    ae_all_iff.2 hw_sq, hB, hα_sq] with ω hω hωB ⟨b, hb⟩ hωα
  obtain ⟨k, hk⟩ := exists_nat_ge (max b (∑' t, α t ω ^ 2))
  obtain ⟨L, hL⟩ := hω k
  refine ⟨L, hL.congr fun t ↦ sum_congr rfl fun s _ ↦ ?_⟩
  have hmem : ω ∈ truncSet P ℱ α w k s := mem_truncSet.2
    ⟨fun r _ ↦ (hωB r).trans ((hb ⟨r, rfl⟩).trans ((le_max_left _ _).trans hk)),
      (hωα.sum_le_tsum _ fun _ _ ↦ sq_nonneg _).trans ((le_max_right _ _).trans hk)⟩
  rw [truncStep, Set.indicator_of_mem hmem]

/-- **The noise lemma.** Let the steps `α t ≥ 0` be adapted, with `∑ α t = ∞` and
`∑ (α t) ^ 2 < ∞` almost surely, and let the noise `w t` be an `ℱ (t + 1)`-measurable
square-integrable martingale difference whose conditional second moments are bounded by `B t`,
with `B` almost surely bounded in `t`. Then the averaged noise
`W (t + 1) = (1 - α t) W t + α t w t` tends to `0` almost surely, whatever `W 0` is. The usual
condition `α t ≤ 1` is not needed: it holds from some time on, since `α t → 0`. -/
theorem ae_tendsto_zero_noise [IsFiniteMeasure P] {B W : ℕ → Ω → ℝ}
    (hα : Adapted ℱ α) (hα₀ : ∀ t ω, 0 ≤ α t ω)
    (hw : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw₂ : ∀ t, MemLp (w t) 2 P)
    (hw_condExp : ∀ t, P[w t | ℱ t] =ᵐ[P] 0) (hw_sq : ∀ t, P[w t ^ 2 | ℱ t] ≤ᵐ[P] B t)
    (hB : ∀ᵐ ω ∂P, BddAbove (Set.range fun t ↦ B t ω))
    (hα_sum : ∀ᵐ ω ∂P, ¬Summable fun t ↦ α t ω)
    (hα_sq : ∀ᵐ ω ∂P, Summable fun t ↦ α t ω ^ 2)
    (hW : ∀ t ω, W (t + 1) ω = (1 - α t ω) * W t ω + α t ω * w t ω) :
    ∀ᵐ ω ∂P, Tendsto (fun t ↦ W t ω) atTop (𝓝 0) := by
  filter_upwards [exists_ae_tendsto_sum_range_mul hα hw hw₂ hw_condExp hw_sq hB hα_sq, hα_sum,
    hα_sq] with ω ⟨L, hL⟩ hω hω₂
  have h1 : ∀ᶠ t in atTop, α t ω ≤ 1 :=
    (hω₂.tendsto_atTop_zero.eventually (ge_mem_nhds zero_lt_one)).mono fun t ht ↦
      (le_abs_self _).trans ((sq_le_one_iff_abs_le_one _).1 ht)
  exact tendsto_zero_of_tendsto_sum_range_smul (w := fun t ↦ w t ω) (W := fun t ↦ W t ω)
    (.of_forall fun t ↦ hα₀ t ω) h1 hω (by simpa only [smul_eq_mul] using hL)
    fun t ↦ by simp only [smul_eq_mul]; exact hW t ω

end TauCeti
