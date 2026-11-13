/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Elementary
import TauCeti.Probability.Moments.Chebyshev

/-!
# Probability bounds from elementary Brownian energy

The probability that a predictable Brownian increment sum exceeds `ε` is at most
`δ / ε²` plus the probability that its pathwise square energy exceeds `δ`.
Unlike the usual isometry bound, this estimate needs no small expected energy.
It is the estimate used to identify limits of elementary stochastic integrals when
integrands converge in probability in square energy.

The proof discards an interval as soon as including it would exceed the energy budget.
That decision is known at its left endpoint. The retained energy is bounded by `δ`,
and the sum is unchanged whenever the original total energy is at most `δ`.
Only filtered pre-Brownian laws are needed, not continuous paths or usual filtrations.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*}

/-- The pathwise square energy of predictable heights on a finite deterministic grid.
Repeated grid dates contribute zero. -/
def elementaryEnergy (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, a i ω ^ 2 * ((τ (i + 1) : ℝ) - τ i)

theorem elementaryEnergy_def (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    elementaryEnergy τ a n ω =
      ∑ i ∈ range n, a i ω ^ 2 * ((τ (i + 1) : ℝ) - τ i) := (rfl)

@[simp]
theorem elementaryEnergy_zero (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (ω : Ω) :
    elementaryEnergy τ a 0 ω = 0 := by
  simp [elementaryEnergy_def]

/-- Appending an interval adds its squared height times its length. -/
theorem elementaryEnergy_succ (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    elementaryEnergy τ a (n + 1) ω =
      elementaryEnergy τ a n ω + a n ω ^ 2 * ((τ (n + 1) : ℝ) - τ n) := by
  simp only [elementaryEnergy_def, sum_range_succ]

variable {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ} {n : ℕ}

/-- Energy is nondecreasing through the last date of a nondecreasing grid. -/
theorem monotoneOn_elementaryEnergy (hτ : MonotoneOn τ (Iic n)) (ω : Ω) :
    MonotoneOn (fun j ↦ elementaryEnergy τ a j ω) (Iic n) := by
  intro i hi j hj hij
  simp only [mem_Iic] at hi hj
  apply sum_le_sum_of_subset_of_nonneg (range_mono hij)
  intro k hk _
  have hk' := mem_range.mp hk
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
    (hτ (by simp only [mem_Iic]; omega) (by simpa using hk'.trans_le hj)
      (Nat.le_succ k))))

/-- On a nondecreasing grid energy is nonnegative. -/
theorem elementaryEnergy_nonneg (hτ : MonotoneOn τ (Iic n)) (ω : Ω) :
    0 ≤ elementaryEnergy τ a n ω := by
  simpa using monotoneOn_elementaryEnergy (a := a) hτ ω (by simp) (by simp) (Nat.zero_le n)

variable {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
variable {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Square-integrable heights give integrable finite-grid energy. -/
theorem integrable_elementaryEnergy (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    Integrable (elementaryEnergy τ a n) P := by
  exact integrable_finsetSum _ fun i hi ↦ ((ha₂ i (mem_range.mp hi)).integrable_sq).mul_const _

/-- The elementary Brownian isometry expressed as expected pathwise energy. -/
theorem IsFilteredPreBrownianReal.integral_sq_sum_mul_sub_eq_integral_elementaryEnergy
    (hW : IsFilteredPreBrownianReal ℱ W P) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    ∫ ω, (∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω)) ^ 2 ∂P =
      ∫ ω, elementaryEnergy τ a n ω ∂P := by
  rw [hW.integral_sq_sum_mul_sub hτ ha ha₂]
  simp only [elementaryEnergy_def, integral_finsetSum _
    (fun i hi ↦ ((ha₂ i (mem_range.mp hi)).integrable_sq).mul_const _), integral_mul_const]

/-- The energy including interval `j` is already known at its left endpoint `τ j`.
This permits energy truncation without anticipation. -/
theorem stronglyMeasurable_elementaryEnergy (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) {j : ℕ} (hj : j < n) :
    StronglyMeasurable[ℱ (τ j)] (elementaryEnergy τ a (j + 1)) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
  exact (((ha i (hij.trans_lt hj)).mono
    (ℱ.mono (hτ (mem_Iic.mpr (hij.trans hj.le)) (mem_Iic.mpr hj.le) hij))).pow 2).mul
      stronglyMeasurable_const

/-- Retain precisely the intervals whose inclusion stays within the original cumulative
energy budget, setting heights on zero-length intervals to zero as well.
This auxiliary holding is used only in the probability estimate. -/
private def energyCutoff (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (δ : ℝ) (i : ℕ) : Ω → ℝ :=
  if τ i < τ (i + 1) then {ω | elementaryEnergy τ a (i + 1) ω ≤ δ}.indicator (a i)
  else 0

private theorem energyCutoff_eq_of_elementaryEnergy_le (hτ : MonotoneOn τ (Iic n))
    {δ : ℝ} {ω : Ω} (hE : elementaryEnergy τ a n ω ≤ δ) {i : ℕ} (hi : i < n) :
    energyCutoff τ a δ i ω = if τ i < τ (i + 1) then a i ω else 0 := by
  have hiδ := (monotoneOn_elementaryEnergy (a := a) hτ ω
    (mem_Iic.mpr (Nat.succ_le_of_lt hi)) (by simp) (Nat.succ_le_of_lt hi)).trans hE
  by_cases hstep : τ i < τ (i + 1) <;> simp [energyCutoff, hstep, hiδ]

private theorem energyCutoff_mul_sub_eq_of_elementaryEnergy_le
    (hτ : MonotoneOn τ (Iic n)) {δ : ℝ} {ω : Ω}
    (hE : elementaryEnergy τ a n ω ≤ δ) {i : ℕ} (hi : i < n)
    (g : ℝ → ℝ) (f : ℝ≥0 → ℝ) :
    g (energyCutoff τ a δ i ω) * (f (τ (i + 1)) - f (τ i)) =
      g (a i ω) * (f (τ (i + 1)) - f (τ i)) := by
  rw [energyCutoff_eq_of_elementaryEnergy_le hτ hE hi]
  split_ifs with hstep
  · rfl
  · have heq : τ (i + 1) = τ i := le_antisymm (le_of_not_gt hstep)
      (hτ (mem_Iic.mpr hi.le) (mem_Iic.mpr (Nat.succ_le_of_lt hi)) (Nat.le_succ i))
    simp [heq]

private theorem stronglyMeasurable_energyCutoff (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (δ : ℝ) {i : ℕ} (hi : i < n) :
    StronglyMeasurable[ℱ (τ i)] (energyCutoff τ a δ i) := by
  by_cases hstep : τ i < τ (i + 1)
  · simp only [energyCutoff, hstep, ite_true]
    exact (ha i hi).indicator (measurableSet_le
      (stronglyMeasurable_elementaryEnergy hτ ha hi).measurable measurable_const)
  · simpa only [energyCutoff, hstep, ite_false] using
      (stronglyMeasurable_zero : StronglyMeasurable[ℱ (τ i)] (fun _ : Ω ↦ (0 : ℝ)))

private theorem memLp_energyCutoff [IsFiniteMeasure P] (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (δ : ℝ)
    {i : ℕ} (hi : i < n) : MemLp (energyCutoff τ a δ i) 2 P := by
  by_cases hstep : τ i < τ (i + 1)
  · have hdt : 0 < (τ (i + 1) : ℝ) - τ i := sub_pos.mpr (NNReal.coe_lt_coe.mpr hstep)
    refine MemLp.of_bound ((stronglyMeasurable_energyCutoff hτ ha δ hi).mono
      (ℱ.le _)).aestronglyMeasurable (Real.sqrt (δ / ((τ (i + 1) : ℝ) - τ i)))
      (.of_forall fun ω ↦ ?_)
    simp only [energyCutoff, hstep, ite_true, Set.indicator_apply, mem_ofPred_eq]
    split_ifs with hE
    · have hterm : a i ω ^ 2 * ((τ (i + 1) : ℝ) - τ i) ≤ δ := by
        rw [elementaryEnergy_succ] at hE
        have hnonneg := elementaryEnergy_nonneg (a := a)
          (hτ.mono (Iic_subset_Iic.mpr hi.le)) ω
        linarith
      simpa only [Real.norm_eq_abs] using Real.abs_le_sqrt ((le_div_iff₀ hdt).2 hterm)
    · simp [Real.sqrt_nonneg]
  · simpa only [energyCutoff, hstep, ite_false] using
      (MemLp.zero : MemLp (fun _ : Ω ↦ (0 : ℝ)) 2 P)

private theorem elementaryEnergy_energyCutoff_le (hτ : MonotoneOn τ (Iic n))
    {δ : ℝ} (hδ : 0 ≤ δ) (ω : Ω) :
    elementaryEnergy τ (energyCutoff τ a δ) n ω ≤ δ := by
  induction n with
  | zero => simpa using hδ
  | succ n ih =>
    by_cases hn : elementaryEnergy τ a (n + 1) ω ≤ δ
    · have heq : elementaryEnergy τ (energyCutoff τ a δ) (n + 1) ω =
          elementaryEnergy τ a (n + 1) ω := by
        apply sum_congr rfl
        intro i hi
        exact energyCutoff_mul_sub_eq_of_elementaryEnergy_le hτ hn (mem_range.mp hi)
          (fun x ↦ x ^ 2) (fun t ↦ (t : ℝ))
      rw [heq]
      exact hn
    · rw [elementaryEnergy_succ]
      have hzero : energyCutoff τ a δ n ω = 0 := by
        by_cases hstep : τ n < τ (n + 1) <;> simp [energyCutoff, hstep, hn]
      simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
      exact ih (hτ.mono (Iic_subset_Iic.mpr (Nat.le_succ n)))

private theorem measure_abs_sum_mul_sub_energyCutoff_ge_le
    (hW : IsFilteredPreBrownianReal ℱ W P) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    P {ω | ε ≤ |∑ i ∈ range n,
      energyCutoff τ a δ i ω * (W (τ (i + 1)) ω - W (τ i) ω)|} ≤
        ENNReal.ofReal (δ / ε ^ 2) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let b := energyCutoff τ a δ
  have hb (i : ℕ) (hi : i < n) : StronglyMeasurable[ℱ (τ i)] (b i) :=
    stronglyMeasurable_energyCutoff hτ ha δ hi
  have hb₂ (i : ℕ) (hi : i < n) : MemLp (b i) 2 P :=
    memLp_energyCutoff hτ ha δ hi
  have hbE : Integrable (elementaryEnergy τ b n) P := integrable_elementaryEnergy hb₂
  have hsecond : ∫ ω, (∑ i ∈ range n, b i ω * (W (τ (i + 1)) ω - W (τ i) ω)) ^ 2 ∂P ≤ δ := by
    rw [hW.integral_sq_sum_mul_sub_eq_integral_elementaryEnergy hτ hb hb₂]
    exact (integral_mono_ae hbE (integrable_const δ)
      (.of_forall (elementaryEnergy_energyCutoff_le hτ hδ))).trans_eq (by simp)
  have hcheb := TauCeti.meas_ge_le_integral_norm_sq_div_sq
    (Y := fun ω ↦ ∑ i ∈ range n, b i ω * (W (τ (i + 1)) ω - W (τ i) ω))
    (by simpa only [Real.norm_eq_abs, sq_abs] using
      (hW.memLp_sum_mul_sub hτ hb hb₂).integrable_sq) hε
  simp only [Real.norm_eq_abs, sq_abs] at hcheb
  exact hcheb.trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hsecond (sq_nonneg ε)))

/-- **The elementary energy-to-probability estimate.** For heights known at the left
endpoints, large Brownian gains require either large energy or a fluctuation with probability
at most `δ / ε²`. No moment hypothesis on the original heights is imposed. -/
theorem IsFilteredPreBrownianReal.measure_abs_sum_mul_sub_ge_le
    (hW : IsFilteredPreBrownianReal ℱ W P) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    P {ω | ε ≤ |∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω)|} ≤
      ENNReal.ofReal (δ / ε ^ 2) + P {ω | δ < elementaryEnergy τ a n ω} := by
  let b := energyCutoff τ a δ
  have hevent : {ω | ε ≤ |∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω)|} ⊆
      {ω | ε ≤ |∑ i ∈ range n, b i ω * (W (τ (i + 1)) ω - W (τ i) ω)|} ∪
        {ω | δ < elementaryEnergy τ a n ω} := by
    intro ω hω
    by_cases hE : δ < elementaryEnergy τ a n ω
    · exact Or.inr hE
    · left
      have hsum : (∑ i ∈ range n, b i ω * (W (τ (i + 1)) ω - W (τ i) ω)) =
          ∑ i ∈ range n, a i ω * (W (τ (i + 1)) ω - W (τ i) ω) := by
        apply sum_congr rfl
        intro i hi
        exact energyCutoff_mul_sub_eq_of_elementaryEnergy_le hτ (le_of_not_gt hE)
          (mem_range.mp hi) id (fun t ↦ W t ω)
      simpa only [mem_ofPred_eq, hsum] using hω
  calc
    _ ≤ P ({ω | ε ≤ |∑ i ∈ range n, b i ω * (W (τ (i + 1)) ω - W (τ i) ω)|} ∪
        {ω | δ < elementaryEnergy τ a n ω}) := measure_mono hevent
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add
      (measure_abs_sum_mul_sub_energyCutoff_ge_le hW hτ ha hε hδ) le_rfl

/-- Convergence to zero in pathwise square energy in probability implies convergence to
zero in probability of elementary Brownian integrals. Grids and their sizes may vary;
no uniform expected-energy bound is needed. -/
theorem IsFilteredPreBrownianReal.tendstoInMeasure_sum_mul_sub_of_energy
    (hW : IsFilteredPreBrownianReal ℱ W P) {ι : Type*} {l : Filter ι}
    {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0} {height : ι → ℕ → Ω → ℝ}
    (hgrid : ∀ k, MonotoneOn (grid k) (Iic (N k)))
    (hheight : ∀ k i, i < N k → StronglyMeasurable[ℱ (grid k i)] (height k i))
    (henergy : TendstoInMeasure P (fun k ↦ elementaryEnergy (grid k) (height k) (N k))
      l (fun _ ↦ 0)) :
    TendstoInMeasure P (fun k ω ↦ ∑ i ∈ range (N k),
      height k i ω * (W (grid k (i + 1)) ω - W (grid k i) ω)) l (fun _ ↦ 0) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine tendstoInMeasure_iff_measureReal_norm.2 fun ε hε ↦ ?_
  simp only [sub_zero, Real.norm_eq_abs]
  refine tendsto_order.2 ⟨fun c hc ↦ Filter.Eventually.of_forall (fun _ ↦
    hc.trans_le measureReal_nonneg), fun c hc ↦ ?_⟩
  let δ := c * ε ^ 2 / 2
  have hδ : 0 < δ := by positivity
  have htail := (tendstoInMeasure_iff_measureReal_norm.1 henergy) δ hδ
  simp only [sub_zero, Real.norm_eq_abs] at htail
  have hc₂ : 0 < c / 2 := by positivity
  filter_upwards [htail.eventually (gt_mem_nhds hc₂)] with k hk
  have hbound := hW.measure_abs_sum_mul_sub_ge_le (hgrid k) (hheight k) hε hδ.le
  have hreal := ENNReal.toReal_mono (by finiteness) hbound
  simp only [ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top _ _),
    ENNReal.toReal_ofReal (div_nonneg hδ.le (sq_nonneg ε)), ← measureReal_def] at hreal
  have htail_le : P.real {ω | δ < elementaryEnergy (grid k) (height k) (N k) ω} ≤
      P.real {ω | δ ≤ |elementaryEnergy (grid k) (height k) (N k) ω|} :=
    measureReal_mono (fun ω hω ↦ by
      simp only [mem_ofPred_eq] at hω ⊢
      exact hω.le.trans (le_abs_self _))
  have hquot : δ / ε ^ 2 = c / 2 := by
    dsimp [δ]
    field_simp
  linarith

end TauCeti.Probability
