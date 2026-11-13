/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.GridExponential.Basic
import TauCeti.Probability.Martingale.Basic

/-!
# Continuous-time elementary exponential densities

For left-measurable heights on a finite deterministic grid, the exponential of Brownian
gains minus half their elapsed square energy is a true martingale at every observation
time, not just at the trading dates. It is positive, starts at one and freezes after the
last trading date. Its paths are continuous whenever the Brownian paths are. Bounded heights
give square-integrable values with second moments controlled by clipped elapsed trading time.

The construction uses finite sums and conditional Gaussian exponential moments, without
a completed stochastic integral. These densities provide continuous-time approximants for
changes of measure with bounded predictable drifts. Heights may be random and dependent;
no Gaussian law for their weighted Brownian gains is asserted.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*}

/-- The finite-grid exponential likelihood observed at time `t`. Both Brownian increments
and their half-energy normalization are clipped at that observation time. -/
def gridExponentialProcess (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  gridExponential (fun j ↦ min t (τ j)) θ W n ω

theorem gridExponentialProcess_def (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridExponentialProcess τ θ W n t ω =
      gridExponential (fun j ↦ min t (τ j)) θ W n ω := (rfl)

/-- The likelihood is the exponential of the clipped gains minus half their energy. -/
theorem gridExponentialProcess_eq_exp (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridExponentialProcess τ θ W n t ω =
      exp (∑ j ∈ range n, (θ j ω * (W (min t (τ (j + 1))) ω - W (min t (τ j)) ω) -
        θ j ω ^ 2 * ((min t (τ (j + 1)) : ℝ≥0) - min t (τ j)) / 2)) :=
  gridExponential_def (fun j ↦ min t (τ j)) θ W n ω

/-- An empty grid gives the unit process. -/
@[simp]
theorem gridExponentialProcess_zero (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) : gridExponentialProcess τ θ W 0 = 1 := by
  funext t
  exact gridExponential_zero _ θ W

/-- Zero heights give the unit density process. -/
@[simp]
theorem gridExponentialProcess_zero_height (τ : ℕ → ℝ≥0)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) : gridExponentialProcess τ 0 W n = 1 := by
  funext t
  exact gridExponential_zero_height _ W n

/-- Every elementary density is strictly positive. -/
theorem gridExponentialProcess_pos (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    0 < gridExponentialProcess τ θ W n t ω := gridExponential_pos _ θ W n ω

/-- Only the active clipped dates, heights and integrator values affect the likelihood. -/
theorem gridExponentialProcess_congr {τ σ : ℕ → ℝ≥0} {θ η : ℕ → Ω → ℝ}
    {W V : ℝ≥0 → Ω → ℝ} {n : ℕ} {s t : ℝ≥0} {ω : Ω}
    (hτ : ∀ j ≤ n, min t (τ j) = min s (σ j))
    (hθ : ∀ j < n, θ j ω = η j ω)
    (hW : ∀ j ≤ n, W (min t (τ j)) ω = V (min s (σ j)) ω) :
    gridExponentialProcess τ θ W n t ω = gridExponentialProcess σ η V n s ω := by
  simp only [gridExponentialProcess_def]
  exact gridExponential_congr hτ hθ hW

/-- Before the first trading date, the likelihood equals one. -/
theorem gridExponentialProcess_eq_one_of_le {τ : ℕ → ℝ≥0} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ)
    {t : ℝ≥0} (ht : t ≤ τ 0) :
    gridExponentialProcess τ θ W n t = 1 := by
  ext ω
  rw [gridExponentialProcess_eq_exp]
  have hmin (j : ℕ) (hj : j ≤ n) : min t (τ j) = t :=
    min_eq_left (ht.trans (hτ (by simp) hj (Nat.zero_le _)))
  simp only [Pi.one_apply]
  rw [← exp_zero]
  congr 1
  apply sum_eq_zero
  intro j hj
  simp [hmin j (by have := mem_range.mp hj; omega), hmin (j + 1) (mem_range.mp hj)]

/-- After the last trading date, the likelihood is the sampled grid likelihood. -/
theorem gridExponentialProcess_eq_gridExponential_of_ge {τ : ℕ → ℝ≥0} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ)
    {t : ℝ≥0} (ht : τ n ≤ t) :
    gridExponentialProcess τ θ W n t = gridExponential τ θ W n := by
  ext ω
  have hmin (j : ℕ) (hj : j ≤ n) : min t (τ j) = τ j :=
    min_eq_right ((hτ hj (by simp) hj).trans ht)
  rw [gridExponentialProcess_def]
  exact gridExponential_congr hmin (fun _ _ ↦ rfl) (fun j hj ↦ by rw [hmin j hj])

private theorem gridExponentialProcess_eq_prefix_of_le {τ : ℕ → ℝ≥0} {j n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hjn : j ≤ n)
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} (ht : t ≤ τ j) :
    gridExponentialProcess τ θ W n t = gridExponentialProcess τ θ W j t := by
  ext ω
  rw [gridExponentialProcess_eq_exp, gridExponentialProcess_eq_exp]
  congr 1
  symm
  apply sum_subset (range_mono hjn)
  intro k hkn hkj
  have hkn' := mem_range.mp hkn
  have hjk : j ≤ k := by simpa only [mem_range, not_lt] using hkj
  have hmin (l : ℕ) (hjl : j ≤ l) (hln : l ≤ n) : min t (τ l) = t :=
    min_eq_left (ht.trans (hτ hjn hln hjl))
  simp [hmin k hjk (by omega), hmin (k + 1) (by omega) (by omega)]

/-- At an interior trading date, the process is the corresponding sampled likelihood. -/
@[simp]
theorem gridExponentialProcess_grid_date {τ : ℕ → ℝ≥0} {j n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hjn : j ≤ n)
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) :
    gridExponentialProcess τ θ W n (τ j) = gridExponential τ θ W j := by
  rw [gridExponentialProcess_eq_prefix_of_le hτ hjn θ W le_rfl]
  exact gridExponentialProcess_eq_gridExponential_of_ge
    (hτ.mono (Set.Iic_subset_Iic.mpr hjn)) θ W le_rfl

/-- The elementary density starts at one, including a nonzero first trading date. -/
@[simp]
theorem gridExponentialProcess_zero_time (τ : ℕ → ℝ≥0)
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    gridExponentialProcess τ θ W n 0 = 1 := by
  ext ω
  simp [gridExponentialProcess_eq_exp]

private def stepExponential (a : Ω → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (u t : ℝ≥0) (ω : Ω) : ℝ :=
  exp (a ω * (W (max u t) ω - W u ω) - a ω ^ 2 * ((max u t : ℝ≥0) - u) / 2)

private theorem stepExponential_of_le (a : Ω → ℝ) (W : ℝ≥0 → Ω → ℝ)
    {u t : ℝ≥0} (ht : t ≤ u) : stepExponential a W u t = 1 := by
  ext ω
  simp [stepExponential, max_eq_left ht]

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {a X : Ω → ℝ} {u : ℝ≥0} {K : ℝ}

private theorem integrable_mul_stepExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (ha : Measurable[ℱ u] a)
    (hX : Measurable[ℱ u] X) (hXi : Integrable X P) (t : ℝ≥0) :
    Integrable (X * stepExponential a W u t) P := by
  exact hW.integrable_mul_exp_sub (le_max_left u t) ha hX hXi

private theorem stronglyMeasurable_stepExponential (hW : Adapted ℱ W)
    (ha : Measurable[ℱ u] a) (t : ℝ≥0) :
    StronglyMeasurable[ℱ t] (stepExponential a W u t) := by
  by_cases hut : u ≤ t
  · unfold stepExponential
    simp only [max_eq_right hut]
    exact (((ha.mono (ℱ.mono hut) le_rfl).mul
      ((hW t).sub (hW.measurable_le hut))).sub
        (((ha.mono (ℱ.mono hut) le_rfl).pow_const 2).mul_const _
          |>.div_const 2)).exp.stronglyMeasurable
  · rw [stepExponential_of_le a W (le_of_not_ge hut)]
    exact stronglyMeasurable_const

private theorem condExp_stepExponential_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (ha : Measurable[ℱ u] a)
    {s t : ℝ≥0} (hus : u ≤ s) (hst : s ≤ t) :
    P[stepExponential a W u t | ℱ s] =ᵐ[P] stepExponential a W u s := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hi : Integrable (stepExponential a W u s) P := by
    simpa only [one_mul] using
      integrable_mul_stepExponential (X := 1) hW ha measurable_const (integrable_const 1) s
  have hc := hW.condExp_mul_exp_sub hst
    (ha.mono (ℱ.mono hus) le_rfl)
    (stronglyMeasurable_stepExponential hW.adapted ha s).measurable hi
  have heq : (fun ω ↦ stepExponential a W u s ω *
      exp (a ω * (W t ω - W s ω) - a ω ^ 2 * ((t : ℝ) - s) / 2)) =
      stepExponential a W u t := by
    ext ω
    simp only [stepExponential, max_eq_right hus, max_eq_right (hus.trans hst), ← exp_add]
    congr 1
    ring
  rwa [heq] at hc

private theorem martingale_stepExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (ha : Measurable[ℱ u] a) :
    Martingale (stepExponential a W u) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨stronglyMeasurable_stepExponential hW.adapted ha, fun s t hst ↦ ?_⟩
  by_cases hus : u ≤ s
  · exact condExp_stepExponential_of_le hW ha hus hst
  have hsu : s ≤ u := le_of_not_ge hus
  rw [stepExponential_of_le a W hsu]
  by_cases htu : t ≤ u
  · rw [stepExponential_of_le a W htu,
      condExp_of_stronglyMeasurable (ℱ.le s) stronglyMeasurable_one (integrable_const 1)]
  · calc
      P[stepExponential a W u t | ℱ s]
          =ᵐ[P] P[P[stepExponential a W u t | ℱ u] | ℱ s] :=
            (condExp_condExp_of_le (ℱ.mono hsu) (ℱ.le u)).symm
      _ =ᵐ[P] P[stepExponential a W u u | ℱ s] :=
        condExp_congr_ae (condExp_stepExponential_of_le hW ha le_rfl (le_of_not_ge htu))
      _ = 1 := by
        rw [stepExponential_of_le a W le_rfl,
          condExp_of_stronglyMeasurable (ℱ.le s) stronglyMeasurable_one (integrable_const 1)]

/-- Appending an interval multiplies the likelihood by its clipped exponential factor. -/
theorem gridExponentialProcess_succ (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridExponentialProcess τ θ W (n + 1) t ω = gridExponentialProcess τ θ W n t ω *
      exp (θ n ω * (W (min t (τ (n + 1))) ω - W (min t (τ n)) ω) -
        θ n ω ^ 2 * ((min t (τ (n + 1)) : ℝ≥0) - min t (τ n)) / 2) := by
  exact gridExponential_succ (fun j ↦ min t (τ j)) θ W n ω

/-- Inside a trading interval, only that interval contributes beyond the sampled likelihood. -/
theorem gridExponentialProcess_eq_mul_exp {τ : ℕ → ℝ≥0} {j n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hjn : j < n)
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) {t : ℝ≥0}
    (ht : t ∈ Set.Icc (τ j) (τ (j + 1))) (ω : Ω) :
    gridExponentialProcess τ θ W n t ω = gridExponential τ θ W j ω *
      exp (θ j ω * (W t ω - W (τ j) ω) - θ j ω ^ 2 * ((t : ℝ) - τ j) / 2) := by
  rw [gridExponentialProcess_eq_prefix_of_le hτ hjn θ W ht.2,
    gridExponentialProcess_succ, min_eq_left ht.2, min_eq_right ht.1,
    gridExponentialProcess_eq_gridExponential_of_ge
      (hτ.mono (Set.Iic_subset_Iic.mpr (Nat.le_of_lt hjn))) θ W ht.1]

private theorem stepExponential_min_eq {u v : ℝ≥0} (huv : u ≤ v)
    (a : Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    stepExponential a W u (min v t) ω =
      exp (a ω * (W (min t v) ω - W (min t u) ω) -
        a ω ^ 2 * ((min t v : ℝ≥0) - min t u) / 2) := by
  by_cases htu : t ≤ u
  · have hmin : min v t = t := min_eq_right (htu.trans huv)
    simp [stepExponential, hmin, max_eq_left htu, min_eq_left htu,
      min_eq_left (htu.trans huv)]
  · have hut : u ≤ t := le_of_not_ge htu
    rw [stepExponential, max_eq_right (le_min huv hut), min_eq_right hut, min_comm v t]

private theorem gridExponentialProcess_succ_eq_add {τ : ℕ → ℝ≥0} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic (n + 1)))
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    gridExponentialProcess τ θ W (n + 1) t = gridExponentialProcess τ θ W n t +
      gridExponential τ θ W n *
        (stepExponential (θ n) W (τ n) (min (τ (n + 1)) t) - 1) := by
  have hstep := stepExponential_min_eq
    (hτ (Nat.le_succ n) (by simp) (Nat.le_succ n)) (θ n) W t
  by_cases htn : t ≤ τ n
  · have hzero := stepExponential_of_le (θ n) W
      ((min_le_right (τ (n + 1)) t).trans htn)
    ext ω
    rw [gridExponentialProcess_succ, ← hstep ω]
    simp [hzero]
  · have hfreeze := gridExponentialProcess_eq_gridExponential_of_ge
      (hτ.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ n))) θ W (le_of_not_ge htn)
    ext ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply,
      gridExponentialProcess_succ, ← hstep ω, hfreeze]
    ring

/-- Predictable elementary exponential likelihoods are strongly adapted, without
probabilistic or boundedness assumptions. -/
theorem _root_.MeasureTheory.Adapted.stronglyAdapted_gridExponentialProcess
    (hW : Adapted ℱ W) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) :
    StronglyAdapted ℱ (gridExponentialProcess τ θ W n) := by
  induction n with
  | zero => simp only [gridExponentialProcess_zero]; exact stronglyAdapted_const _ _
  | succ n ih =>
    intro t
    have hm := (ih (hτ.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ n)))
      (fun j hj ↦ hθ j (by omega)) t).mul
      ((stronglyMeasurable_stepExponential hW (hθ n (by omega))
        (min (τ (n + 1)) t)).mono (ℱ.mono (min_le_right _ _)))
    convert hm using 1
    ext ω
    rw [gridExponentialProcess_succ]
    exact congrArg (gridExponentialProcess τ θ W n t ω * ·)
      (stepExponential_min_eq (hτ (Nat.le_succ n) (by simp) (Nat.le_succ n))
        (θ n) W t ω).symm

/-- Predictable grid heights give a true martingale at all observation times.
Neither path regularity nor usual filtration conditions are required. -/
theorem IsFilteredPreBrownianReal.martingale_gridExponentialProcess
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) :
    Martingale (gridExponentialProcess τ θ W n) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  induction n with
  | zero =>
    rw [gridExponentialProcess_zero]
    exact martingale_const ℱ P (1 : ℝ)
  | succ n ih =>
    have hτn := hτ.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ n))
    have hθn := fun j (hj : j < n) ↦ hθ j (by omega)
    have hm := ((martingale_stepExponential hW (hθ n (by omega))).const_min (τ (n + 1))).sub
      (martingale_const ℱ P (1 : ℝ))
    have hzero : ∀ t ≤ τ n,
        stepExponential (θ n) W (τ n) (min (τ (n + 1)) t) - 1 = 0 := by
      intro t ht
      rw [stepExponential_of_le (θ n) W ((min_le_right _ _).trans ht), sub_self]
    have hmul : ∀ t, Integrable (gridExponential τ θ W n *
        (stepExponential (θ n) W (τ n) (min (τ (n + 1)) t) - 1)) P := by
      intro t
      have hi := integrable_mul_stepExponential hW (hθ n (by omega))
        (hW.adapted.measurable_gridExponential hτn hθn)
        (hW.integrable_gridExponential hτn hθn) (min (τ (n + 1)) t)
      simpa only [mul_sub, mul_one] using
        hi.sub (hW.integrable_gridExponential hτn hθn)
    have hprod := hm.mul_left_of_eq_zero hzero
      (hW.adapted.measurable_gridExponential hτn hθn).stronglyMeasurable hmul
    convert (ih hτn hθn).add hprod using 1
    ext t ω
    exact congrFun (gridExponentialProcess_succ_eq_add hτ θ W t) ω

/-- Every elementary exponential likelihood has expectation one at every time. -/
theorem IsFilteredPreBrownianReal.integral_gridExponentialProcess
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) (t : ℝ≥0) :
    ∫ ω, gridExponentialProcess τ θ W n t ω ∂P = 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have h := (hW.martingale_gridExponentialProcess hτ hθ).setIntegral_eq
    (zero_le (a := t)) MeasurableSet.univ
  simpa using h.symm

/-- At every observation time, the elementary density is the conditional expectation
of the terminal grid likelihood. -/
theorem IsFilteredPreBrownianReal.gridExponentialProcess_ae_eq_condExp
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j)) (t : ℝ≥0) :
    gridExponentialProcess τ θ W n t =ᵐ[P] P[gridExponential τ θ W n | ℱ t] := by
  have hc := (hW.martingale_gridExponentialProcess hτ hθ).condExp_ae_eq
    (le_max_left t (τ n))
  rw [gridExponentialProcess_eq_gridExponential_of_ge hτ θ W (le_max_right t (τ n))] at hc
  exact hc.symm

/-- Elementary density values are square-integrable at every observation time. -/
theorem IsFilteredPreBrownianReal.memLp_two_gridExponentialProcess
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j < n, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (t : ℝ≥0) :
    MemLp (gridExponentialProcess τ θ W n t) 2 P := by
  exact ((hW.memLp_two_gridExponential hτ hθ hK).condExp (by norm_num)).ae_eq
    (hW.gridExponentialProcess_ae_eq_condExp hτ hθ t).symm

/-- The second moment is controlled by elapsed trading time clipped at the observation time,
not by the number of grid intervals or the unobserved terminal date. -/
theorem IsFilteredPreBrownianReal.integral_sq_gridExponentialProcess_le
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hθ : ∀ j < n, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j < n, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (t : ℝ≥0) :
    ∫ ω, gridExponentialProcess τ θ W n t ω ^ 2 ∂P ≤
      exp (K ^ 2 * ((min t (τ n) : ℝ≥0) - min t (τ 0))) := by
  have h2θ := fun j (hj : j < n) ↦ (hθ j hj).const_mul 2
  have hm := hW.martingale_gridExponentialProcess hτ h2θ
  have hi := (hm.integrable t).mul_const
    (exp (K ^ 2 * ((min t (τ n) : ℝ≥0) - min t (τ 0))))
  have hs := (memLp_two_iff_integrable_sq
    ((hW.adapted.stronglyAdapted_gridExponentialProcess hτ hθ t).mono
      (ℱ.le t)).aestronglyMeasurable).mp (hW.memLp_two_gridExponentialProcess hτ hθ hK t)
  have hb : ∀ᵐ ω ∂P, gridExponentialProcess τ θ W n t ω ^ 2 ≤
      gridExponentialProcess τ (fun j ω ↦ 2 * θ j ω) W n t ω *
        exp (K ^ 2 * ((min t (τ n) : ℝ≥0) - min t (τ 0))) := by
    filter_upwards [ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (hK j))] with ω hω
    simp only [gridExponentialProcess_def]
    exact gridExponential_sq_le (fun i hi j hj hij ↦ min_le_min_left t (hτ hi hj hij)) ω hω
  refine (integral_mono_ae hs hi hb).trans_eq ?_
  rw [integral_mul_const, hW.integral_gridExponentialProcess hτ h2θ t, one_mul]

/-- Continuous Brownian paths give continuous elementary density paths. -/
theorem continuous_gridExponentialProcess (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW : Continuous (W · ω)) (n : ℕ) :
    Continuous (fun t ↦ gridExponentialProcess τ θ W n t ω) := by
  simp only [gridExponentialProcess_eq_exp]
  fun_prop

end TauCeti.Probability
