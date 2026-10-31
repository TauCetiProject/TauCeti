/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Simple self-financing trading

For stock and bond prices sampled at rebalancing dates, `IsSimpleSelfFinancing` says
that buying the next positions costs exactly the liquidation value of the old ones.
The cumulative-gains characterization and its within-interval version express wealth
as initial cost plus the two elementary trading integrals. These identities are pathwise:
they can be applied to each sample path outside a common null set, without imposing
moment assumptions on the prices or holdings.

`simpleHolding` turns finitely many coefficients known at their left endpoints into a
predictable process on the half-open trading intervals `(t_j,t_{j+1}]`. Its value at the
origin is zero, as is customary for elementary integrands; initial cost is accounted for
separately. No general stochastic integral or continuous-time admissibility is asserted.

`financingBondHolding` constructs the unique bond positions financing any prescribed stock
positions and initial bond holding when bond prices at rebalancing dates are nonzero.
Negative positions are allowed, so the construction includes short sales and borrowing.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal

namespace TauCeti.Finance

variable {a b a' b' S β : ℕ → ℝ}

/-- The elementary gain from stock positions `a j` over the first `n` trading intervals.
Here `S j` is the price at the `j`th rebalancing date. -/
def simpleGain (a S : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, a j * (S (j + 1) - S j)

/-- The elementary integral is the sum of positions times price increments. -/
theorem simpleGain_def (a S : ℕ → ℝ) (n : ℕ) :
    simpleGain a S n = ∑ j ∈ Finset.range n, a j * (S (j + 1) - S j) := (rfl)

/-- There are no trading gains before the first interval. -/
@[simp] theorem simpleGain_zero (a S : ℕ → ℝ) : simpleGain a S 0 = 0 := by
  simp [simpleGain]

/-- One more interval adds the gain on that interval. -/
theorem simpleGain_succ (a S : ℕ → ℝ) (n : ℕ) :
    simpleGain a S (n + 1) = simpleGain a S n + a n * (S (n + 1) - S n) := by
  simp [simpleGain, Finset.sum_range_succ]

/-- A simple stock/bond strategy is self-financing if every rebalance preserves wealth
at the prices prevailing at that rebalance. All sequences are sampled at the same dates. -/
def IsSimpleSelfFinancing (a b S β : ℕ → ℝ) : Prop :=
  ∀ n, a (n + 1) * S (n + 1) + b (n + 1) * β (n + 1) =
    a n * S (n + 1) + b n * β (n + 1)

/-- Self-financing is precisely preservation of wealth at every rebalance. -/
theorem isSimpleSelfFinancing_iff (a b S β : ℕ → ℝ) :
    IsSimpleSelfFinancing a b S β ↔
      ∀ n, a (n + 1) * S (n + 1) + b (n + 1) * β (n + 1) =
        a n * S (n + 1) + b n * β (n + 1) := Iff.rfl

/-- Wealth of a self-financing simple strategy is initial cost plus cumulative gains. -/
theorem IsSimpleSelfFinancing.value_eq (h : IsSimpleSelfFinancing a b S β) (n : ℕ) :
    a n * S n + b n * β n =
      a 0 * S 0 + b 0 * β 0 + simpleGain a S n + simpleGain b β n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [h n, simpleGain_succ, simpleGain_succ]
    linarith

/-- The cumulative-gains identity at every date is equivalent to cost-free rebalancing. -/
theorem isSimpleSelfFinancing_iff_value_eq (a b S β : ℕ → ℝ) :
    IsSimpleSelfFinancing a b S β ↔
      ∀ n, a n * S n + b n * β n =
        a 0 * S 0 + b 0 * β 0 + simpleGain a S n + simpleGain b β n := by
  refine ⟨fun h ↦ h.value_eq, fun h n ↦ ?_⟩
  have hn := h n
  have hn' := h (n + 1)
  rw [simpleGain_succ, simpleGain_succ] at hn'
  linarith

/-- During interval `n`, mark the positions at current prices `s` and `p`.
Wealth is initial cost plus the completed gains and the two current partial gains. -/
theorem IsSimpleSelfFinancing.value_eq_of_current_prices
    (h : IsSimpleSelfFinancing a b S β) (n : ℕ) (s p : ℝ) :
    a n * s + b n * p = a 0 * S 0 + b 0 * β 0 +
      simpleGain a S n + simpleGain b β n + a n * (s - S n) + b n * (p - β n) := by
  have := h.value_eq n
  linarith

/-- Adding simple self-financing strategies preserves self-financing. -/
theorem IsSimpleSelfFinancing.add
    (h : IsSimpleSelfFinancing a b S β) (h' : IsSimpleSelfFinancing a' b' S β) :
    IsSimpleSelfFinancing (a + a') (b + b') S β := by
  intro n
  have hn := h n
  have hn' := h' n
  simp only [Pi.add_apply]
  linear_combination hn + hn'

/-- Scaling all positions, including by a negative amount, preserves self-financing. -/
theorem IsSimpleSelfFinancing.smul (h : IsSimpleSelfFinancing a b S β) (c : ℝ) :
    IsSimpleSelfFinancing (c • a) (c • b) S β := by
  intro n
  have hn := h n
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination c * hn

/-- Bond positions obtained by paying for every change in stock positions from the bond. -/
def financingBondHolding (a S β : ℕ → ℝ) (b₀ : ℝ) : ℕ → ℝ
  | 0 => b₀
  | n + 1 => financingBondHolding a S β b₀ n +
      (a n - a (n + 1)) * S (n + 1) / β (n + 1)

/-- The prescribed initial bond holding is retained. -/
@[simp] theorem financingBondHolding_zero (a S β : ℕ → ℝ) (b₀ : ℝ) :
    financingBondHolding a S β b₀ 0 = b₀ := (rfl)

/-- The bond finances the stock purchase at the next date's price. -/
@[simp] theorem financingBondHolding_succ (a S β : ℕ → ℝ) (b₀ : ℝ) (n : ℕ) :
    financingBondHolding a S β b₀ (n + 1) = financingBondHolding a S β b₀ n +
      (a n - a (n + 1)) * S (n + 1) / β (n + 1) := (rfl)

/-- Nonzero bond prices suffice to finance any prescribed stock positions. -/
theorem isSimpleSelfFinancing_financingBondHolding (a S β : ℕ → ℝ) (b₀ : ℝ)
    (hβ : ∀ n, β (n + 1) ≠ 0) :
    IsSimpleSelfFinancing a (financingBondHolding a S β b₀) S β := by
  intro n
  rw [financingBondHolding_succ]
  field_simp [hβ n]
  ring

/-- With the stock positions and initial bond holding fixed, self-financing uniquely
determines the bond positions. -/
theorem IsSimpleSelfFinancing.bondHolding_eq (h : IsSimpleSelfFinancing a b S β)
    (hβ : ∀ n, β (n + 1) ≠ 0) : b = financingBondHolding a S β (b 0) := by
  funext n
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := h n
    rw [financingBondHolding_succ, ← ih]
    apply (mul_right_cancel₀ (hβ n))
    field_simp [hβ n]
    linarith

/-- The finite elementary holding process on `(t_j,t_{j+1}]`, with zero value elsewhere. -/
def simpleHolding {Ω : Type*} (t : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (n : ℕ)
    (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, (Ioc (t j) (t (j + 1))).indicator (fun _ ↦ a j ω) u

/-- Explicit finite-interval representation of the elementary holding process. -/
theorem simpleHolding_def {Ω : Type*} (t : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (n : ℕ)
    (u : ℝ≥0) (ω : Ω) : simpleHolding t a n u ω =
      ∑ j ∈ Finset.range n, (Ioc (t j) (t (j + 1))).indicator (fun _ ↦ a j ω) u := (rfl)

/-- An elementary integrand has no contribution at time zero. -/
@[simp] theorem simpleHolding_zero {Ω : Type*} (t : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : simpleHolding t a n 0 ω = 0 := by
  simp [simpleHolding]

/-- With no trading intervals the elementary holding is zero. -/
@[simp] theorem simpleHolding_zero_intervals {Ω : Type*} (t : ℕ → ℝ≥0)
    (a : ℕ → Ω → ℝ) : simpleHolding t a 0 = 0 := by
  funext u ω
  simp [simpleHolding]

/-- Coefficients selected at the preceding rebalancing dates give predictable holdings. -/
theorem isStronglyPredictable_simpleHolding {Ω : Type*} {m : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 m) (t : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ)
    (ha : ∀ j, StronglyMeasurable[ℱ (t j)] (a j)) (n : ℕ) :
    IsStronglyPredictable ℱ (simpleHolding t a n) := by
  unfold IsStronglyPredictable
  convert (Finset.stronglyMeasurable_sum (Finset.range n) fun j _ ↦
    (ha j).isStronglyPredictable_indicator_Ioc (t (j + 1))) using 1
  ext ⟨u, ω⟩
  simp [simpleHolding, Function.uncurry]

/-- On a nondecreasing grid the holding on `(t_j,t_{j+1}]` is the coefficient
chosen at `t_j`, including the right endpoint and excluding the left endpoint. -/
theorem simpleHolding_eq {Ω : Type*} {t : ℕ → ℝ≥0} (ht : Monotone t)
    (a : ℕ → Ω → ℝ) {n j : ℕ} (hj : j < n) {u : ℝ≥0}
    (hu : u ∈ Ioc (t j) (t (j + 1))) (ω : Ω) : simpleHolding t a n u ω = a j ω := by
  unfold simpleHolding
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem hu _
  · intro i _ hij
    apply indicator_of_notMem
    intro hi
    rcases lt_or_gt_of_ne hij with h | h
    · have := ht (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hi.2.trans this)) hu.1
    · have := ht (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hu.2.trans this)) hi.1
  · simp [hj]

/-- The finite-sum self-financing formula at any time in a trading interval, for each
sample path satisfying the rebalancing contract. The sums cover completed intervals,
and the last two terms are the gains since the current interval's left endpoint. -/
theorem simpleHolding_value_eq {Ω : Type*} {t : ℕ → ℝ≥0} (ht : Monotone t)
    (a b : ℕ → Ω → ℝ) (S β : ℝ≥0 → Ω → ℝ) {n j : ℕ} (hj : j < n)
    {u : ℝ≥0} (hu : u ∈ Ioc (t j) (t (j + 1))) (ω : Ω)
    (h : IsSimpleSelfFinancing (fun i ↦ a i ω) (fun i ↦ b i ω)
      (fun i ↦ S (t i) ω) (fun i ↦ β (t i) ω)) :
    simpleHolding t a n u ω * S u ω + simpleHolding t b n u ω * β u ω =
      a 0 ω * S (t 0) ω + b 0 ω * β (t 0) ω +
        simpleGain (fun i ↦ a i ω) (fun i ↦ S (t i) ω) j +
        simpleGain (fun i ↦ b i ω) (fun i ↦ β (t i) ω) j +
        a j ω * (S u ω - S (t j) ω) + b j ω * (β u ω - β (t j) ω) := by
  rw [simpleHolding_eq ht a hj hu, simpleHolding_eq ht b hj hu]
  exact h.value_eq_of_current_prices j (S u ω) (β u ω)

/-- Financing preserves measurability at each trading date. Consequently its bond positions,
as well as its prescribed stock positions, can be used in `simpleHolding`. -/
theorem stronglyMeasurable_financingBondHolding {Ω : Type*} {m : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 m) {t : ℕ → ℝ≥0} (ht : Monotone t)
    (a S β : ℕ → Ω → ℝ) (b₀ : Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[ℱ (t n)] (a n))
    (hS : ∀ n, StronglyMeasurable[ℱ (t n)] (S n))
    (hβ : ∀ n, StronglyMeasurable[ℱ (t n)] (β n))
    (hb₀ : StronglyMeasurable[ℱ (t 0)] b₀) (n : ℕ) :
    StronglyMeasurable[ℱ (t n)] (fun ω ↦
      financingBondHolding (fun j ↦ a j ω) (fun j ↦ S j ω) (fun j ↦ β j ω) (b₀ ω) n) := by
  induction n with
  | zero => simpa only [financingBondHolding_zero] using hb₀
  | succ n ih =>
    simp_rw [financingBondHolding_succ]
    exact (ih.mono (ℱ.mono (ht (Nat.le_succ n)))).add
      ((((ha n).mono (ℱ.mono (ht (Nat.le_succ n)))).sub (ha (n + 1))).mul
        (hS (n + 1)) |>.div (hβ (n + 1)))

end TauCeti.Finance
