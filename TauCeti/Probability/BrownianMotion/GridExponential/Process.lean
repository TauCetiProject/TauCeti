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

For bounded left-measurable heights on a finite deterministic grid, the exponential of
Brownian gains minus half their elapsed square energy is a true martingale at every
observation time, not just at the trading dates. It is positive, starts at one and freezes
after the last trading date. Its paths are continuous whenever the Brownian paths are.

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
  exp (∑ j ∈ range n, (θ j ω * (W (min t (τ (j + 1))) ω - W (min t (τ j)) ω) -
    θ j ω ^ 2 * ((min t (τ (j + 1)) : ℝ≥0) - min t (τ j)) / 2))

theorem gridExponentialProcess_def (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridExponentialProcess τ θ W n t ω =
      exp (∑ j ∈ range n, (θ j ω * (W (min t (τ (j + 1))) ω - W (min t (τ j)) ω) -
        θ j ω ^ 2 * ((min t (τ (j + 1)) : ℝ≥0) - min t (τ j)) / 2)) := (rfl)

/-- An empty grid gives the unit process. -/
@[simp]
theorem gridExponentialProcess_zero (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) : gridExponentialProcess τ θ W 0 = 1 := by
  ext t ω
  simp [gridExponentialProcess_def]

/-- Zero heights give the unit density process. -/
@[simp]
theorem gridExponentialProcess_zero_height (τ : ℕ → ℝ≥0)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) : gridExponentialProcess τ 0 W n = 1 := by
  ext t ω
  simp [gridExponentialProcess_def]

/-- Every elementary density is strictly positive. -/
theorem gridExponentialProcess_pos (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    0 < gridExponentialProcess τ θ W n t ω := exp_pos _

/-- Before the first trading date, the likelihood equals one. -/
theorem gridExponentialProcess_of_le {τ : ℕ → ℝ≥0} (hτ : Monotone τ)
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) {t : ℝ≥0} (ht : t ≤ τ 0) :
    gridExponentialProcess τ θ W n t = 1 := by
  ext ω
  simp [gridExponentialProcess_def, min_eq_left (ht.trans (hτ (Nat.zero_le _)))]

/-- After the last trading date, the likelihood is the sampled grid likelihood. -/
theorem gridExponentialProcess_of_ge {τ : ℕ → ℝ≥0} (hτ : Monotone τ)
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) {t : ℝ≥0} (ht : τ n ≤ t) :
    gridExponentialProcess τ θ W n t = gridExponential τ θ W n := by
  ext ω
  rw [gridExponentialProcess_def, gridExponential_def]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hjn : j + 1 ≤ n := mem_range.mp hj
  rw [min_eq_right ((hτ hjn).trans ht),
    min_eq_right ((hτ (Nat.le_of_succ_le hjn)).trans ht)]

/-- The elementary density starts at one, including a nonzero first trading date. -/
@[simp]
theorem gridExponentialProcess_start {τ : ℕ → ℝ≥0} (hτ : Monotone τ)
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    gridExponentialProcess τ θ W n 0 = 1 :=
  gridExponentialProcess_of_le hτ θ W n (zero_le (a := τ 0))

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
    (ha : Measurable[ℱ u] a) (hK : ∀ᵐ ω ∂P, |a ω| ≤ K)
    (hX : Measurable[ℱ u] X) (hXi : Integrable X P) (t : ℝ≥0) :
    Integrable (X * stepExponential a W u t) P := by
  let d : ℝ := (max u t : ℝ≥0) - u
  let Y := fun ω ↦ X ω * exp (-(a ω ^ 2 * d / 2))
  have hd : 0 ≤ d := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (le_max_left _ _))
  have hYm : Measurable[ℱ u] Y :=
    hX.mul ((ha.pow_const 2 |>.mul_const d |>.div_const 2).neg.exp)
  have ham : Measurable a := ha.mono (ℱ.le _) le_rfl
  have hYi : Integrable Y P := hXi.mul_bdd (by fun_prop) (c := 1) (by
    filter_upwards [] with ω
    simpa only [norm_eq_abs, abs_exp, exp_le_one_iff] using
      neg_nonpos.mpr (div_nonneg (mul_nonneg (sq_nonneg _) hd) (by positivity)))
  have hi := integrable_mul_exp_of_indep_gaussian (ℱ.le _) hYm ha
    (hW.adapted.measurable.sub hW.adapted.measurable)
    (hW.indep_sub (le_max_left u t)) (hW.hasLaw_sub_of_le (le_max_left u t)) hYi hK
  convert hi using 1
  ext ω
  simp only [Pi.mul_apply, Pi.sub_apply, stepExponential, Y, d, mul_assoc, ← exp_add]
  congr 2
  ring

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
    (ha : Measurable[ℱ u] a) (hK : ∀ᵐ ω ∂P, |a ω| ≤ K)
    {s t : ℝ≥0} (hus : u ≤ s) (hst : s ≤ t) :
    P[stepExponential a W u t | ℱ s] =ᵐ[P] stepExponential a W u s := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hi : Integrable (stepExponential a W u s) P := by
    simpa only [one_mul] using
      integrable_mul_stepExponential (X := 1) hW ha hK measurable_const (integrable_const 1) s
  let d : ℝ := (t : ℝ) - s
  let Y := fun ω ↦ stepExponential a W u s ω * exp (-(a ω ^ 2 * d / 2))
  have has := ha.mono (ℱ.mono hus) le_rfl
  have hYm : Measurable[ℱ s] Y :=
    (stronglyMeasurable_stepExponential hW.adapted ha s).measurable.mul
      ((has.pow_const 2 |>.mul_const d |>.div_const 2).neg.exp)
  have hd : 0 ≤ d := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
  have ham : Measurable a := ha.mono (ℱ.le _) le_rfl
  have hYi : Integrable Y P := hi.mul_bdd (by fun_prop) (c := 1) (by
    filter_upwards [] with ω
    simpa only [norm_eq_abs, abs_exp, exp_le_one_iff] using
      neg_nonpos.mpr (div_nonneg (mul_nonneg (sq_nonneg _) hd) (by positivity)))
  have hc := condExp_mul_exp_of_indep_gaussian (ℱ.le _) hYm has
    (hW.adapted.measurable.sub hW.adapted.measurable)
    (hW.indep_sub hst) (hW.hasLaw_sub_of_le hst) hYi hK
  have heq : (fun ω ↦ Y ω * exp (a ω * (W t ω - W s ω))) =
      stepExponential a W u t := by
    ext ω
    simp only [Y, stepExponential, max_eq_right hus, max_eq_right (hus.trans hst),
      ← exp_add]
    congr 1
    dsimp [d]
    ring
  simp only [Pi.sub_apply] at hc
  rw [heq] at hc
  filter_upwards [hc] with ω hω
  rw [hω, zero_mul, zero_add, NNReal.coe_sub hst]
  dsimp only [Y, d]
  rw [mul_assoc, ← exp_add]
  simp [show -(a ω ^ 2 * ((t : ℝ) - s) / 2) +
    ((t : ℝ) - s) * a ω ^ 2 / 2 = 0 by ring]

private theorem martingale_stepExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (ha : Measurable[ℱ u] a) (hK : ∀ᵐ ω ∂P, |a ω| ≤ K) :
    Martingale (stepExponential a W u) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨stronglyMeasurable_stepExponential hW.adapted ha, fun s t hst ↦ ?_⟩
  by_cases hus : u ≤ s
  · exact condExp_stepExponential_of_le hW ha hK hus hst
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
        condExp_congr_ae (condExp_stepExponential_of_le hW ha hK le_rfl (le_of_not_ge htu))
      _ = 1 := by
        rw [stepExponential_of_le a W le_rfl,
          condExp_of_stronglyMeasurable (ℱ.le s) stronglyMeasurable_one (integrable_const 1)]

/-- Appending an interval multiplies the likelihood by its clipped exponential factor. -/
theorem gridExponentialProcess_succ (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridExponentialProcess τ θ W (n + 1) t ω = gridExponentialProcess τ θ W n t ω *
      exp (θ n ω * (W (min t (τ (n + 1))) ω - W (min t (τ n)) ω) -
        θ n ω ^ 2 * ((min t (τ (n + 1)) : ℝ≥0) - min t (τ n)) / 2) := by
  rw [gridExponentialProcess_def, gridExponentialProcess_def, sum_range_succ, exp_add]

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

private theorem gridExponentialProcess_succ_eq_add {τ : ℕ → ℝ≥0} (hτ : Monotone τ)
    (θ : ℕ → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) :
    gridExponentialProcess τ θ W (n + 1) t = gridExponentialProcess τ θ W n t +
      gridExponential τ θ W n *
        (stepExponential (θ n) W (τ n) (min (τ (n + 1)) t) - 1) := by
  have hstep := stepExponential_min_eq (hτ (Nat.le_succ n)) (θ n) W t
  by_cases htn : t ≤ τ n
  · have hzero := stepExponential_of_le (θ n) W
      ((min_le_right (τ (n + 1)) t).trans htn)
    ext ω
    rw [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, hzero, Pi.one_apply, sub_self,
      mul_zero, add_zero, gridExponentialProcess_succ, ← hstep ω, hzero, Pi.one_apply, mul_one]
  · have hfreeze := gridExponentialProcess_of_ge hτ θ W n (le_of_not_ge htn)
    ext ω
    rw [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply,
      gridExponentialProcess_succ, ← hstep ω, hfreeze]
    ring

/-- Bounded predictable grid heights give a true martingale at all observation times.
Neither path regularity nor usual filtration conditions are required. -/
theorem IsFilteredPreBrownianReal.martingale_gridExponentialProcess
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ}
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) :
    Martingale (gridExponentialProcess τ θ W n) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  induction n with
  | zero =>
    rw [gridExponentialProcess_zero]
    exact martingale_const ℱ P (1 : ℝ)
  | succ n ih =>
    have hm := ((martingale_stepExponential hW (hθ n) (hK n)).const_min (τ (n + 1))).sub
      (martingale_const ℱ P (1 : ℝ))
    have hzero : ∀ t ≤ τ n,
        stepExponential (θ n) W (τ n) (min (τ (n + 1)) t) - 1 = 0 := by
      intro t ht
      rw [stepExponential_of_le (θ n) W ((min_le_right _ _).trans ht), sub_self]
    have hmul : ∀ t, Integrable (gridExponential τ θ W n *
        (stepExponential (θ n) W (τ n) (min (τ (n + 1)) t) - 1)) P := by
      intro t
      have hi := integrable_mul_stepExponential hW (hθ n) (hK n)
        (hW.adapted.measurable_gridExponential hτ hθ n)
        (hW.integrable_gridExponential hτ hθ hK n) (min (τ (n + 1)) t)
      simpa only [mul_sub, mul_one] using
        hi.sub (hW.integrable_gridExponential hτ hθ hK n)
    have hprod := hm.mul_left_of_eq_zero hzero
      (hW.adapted.measurable_gridExponential hτ hθ n).stronglyMeasurable hmul
    convert ih.add hprod using 1
    ext t ω
    exact congrFun (gridExponentialProcess_succ_eq_add hτ θ W n t) ω

/-- Every elementary exponential likelihood has expectation one at every time. -/
theorem IsFilteredPreBrownianReal.integral_gridExponentialProcess
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ}
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) (t : ℝ≥0) :
    ∫ ω, gridExponentialProcess τ θ W n t ω ∂P = 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have h := (hW.martingale_gridExponentialProcess hτ hθ hK n).setIntegral_eq
    (zero_le (a := t)) MeasurableSet.univ
  simpa [gridExponentialProcess_start hτ] using h.symm

/-- Elementary density values are square-integrable at every observation time. -/
theorem IsFilteredPreBrownianReal.memLp_two_gridExponentialProcess
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ}
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) (t : ℝ≥0) :
    MemLp (gridExponentialProcess τ θ W n t) 2 P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hc := (hW.martingale_gridExponentialProcess hτ hθ hK n).condExp_ae_eq
    (le_max_left t (τ n))
  rw [gridExponentialProcess_of_ge hτ θ W n (le_max_right t (τ n))] at hc
  exact ((hW.memLp_two_gridExponential hτ hθ hK n).condExp (by norm_num)).ae_eq hc

/-- The second-moment bound is uniform over observation times and depends on elapsed
trading time, not the number of grid intervals. -/
theorem IsFilteredPreBrownianReal.integral_sq_gridExponentialProcess_le
    (hW : IsFilteredPreBrownianReal ℱ W P) {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ}
    (hτ : Monotone τ) (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ) (t : ℝ≥0) :
    ∫ ω, gridExponentialProcess τ θ W n t ω ^ 2 ∂P ≤
      exp (K ^ 2 * ((τ n : ℝ) - τ 0)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hc := (hW.martingale_gridExponentialProcess hτ hθ hK n).condExp_ae_eq
    (le_max_left t (τ n))
  rw [gridExponentialProcess_of_ge hτ θ W n (le_max_right t (τ n))] at hc
  have hi := (hW.memLp_two_gridExponential hτ hθ hK n).integrable_norm_rpow
    (by norm_num) (by norm_num)
  have hb := integral_norm_condExp_rpow_le (m := ℱ t) (by norm_num : (1 : ℝ) ≤ 2) hi
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hb
  have heq := integral_congr_ae (hc.fun_comp (fun x : ℝ ↦ x ^ 2))
  simp only [Function.comp_apply] at heq
  rw [heq] at hb
  exact hb.trans (hW.integral_sq_gridExponential_le hτ hθ hK n)

/-- Continuous Brownian paths give continuous elementary density paths. -/
theorem continuous_gridExponentialProcess (τ : ℕ → ℝ≥0) (θ : ℕ → Ω → ℝ)
    {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW : Continuous (W · ω)) (n : ℕ) :
    Continuous (fun t ↦ gridExponentialProcess τ θ W n t ω) := by
  simp only [gridExponentialProcess_def]
  fun_prop

end TauCeti.Probability
