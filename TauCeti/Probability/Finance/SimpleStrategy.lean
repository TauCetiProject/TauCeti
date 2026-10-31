/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Predictable
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Simple trading strategies and the self-financing formula

A market has a stock with price process `S` and a bond with price process `β`. A *simple
strategy* trades only at finitely many dates `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ n`: on the interval
`(τ j, τ (j + 1)]` it holds `a j` shares of stock and `b j` shares of bond, chosen at time `τ j`.
Only the dates `τ 0, …, τ n` matter, so monotonicity is assumed on indices up to `n` only.
As a process, the stock holding is

`a_t = ∑_{j < n} a j · 1_{(τ j, τ (j + 1)]}(t)`  (`TauCeti.Finance.simpleHolding`),

which is predictable when each `a j` is `ℱ (τ j)`-measurable
(`TauCeti.Finance.isStronglyPredictable_simpleHolding`). Its gains from trading in a price process
`X` up to time `t` are the elementary integral

`∫₀ᵗ a dX = ∑_{j < n} a j · (X (τ (j + 1) ⊓ t) - X (τ j ⊓ t))`  (`TauCeti.Finance.simpleGains`),

an adapted process when `X` is adapted and each `a j` is `ℱ (τ j)`-measurable
(`TauCeti.Finance.stronglyAdapted_simpleGains`). At a rebalancing date the gains are the discrete
transform `∑_{i < j} a i · (X (τ (i + 1)) - X (τ i))`
(`TauCeti.Finance.simpleGains_apply_eq_sum`), and after the last date they stay at their terminal
value (`TauCeti.Finance.simpleGains_of_ge`).

The strategy is *self-financing* (`TauCeti.Finance.IsSelfFinancing`) when every rebalancing is
paid for by the old position: at each date `τ (j + 1)` with `j + 1 < n`, the new portfolio costs
what the old one is worth, `a (j + 1) S + b (j + 1) β = a j S + b j β`. Equivalently, at the start
of each interval the portfolio costs the initial cost plus the gains so far
(`TauCeti.Finance.isSelfFinancing_iff_forall_lt`); in particular the final portfolio is worth the
initial cost plus the total discrete gains at the last date
(`TauCeti.Finance.IsSelfFinancing.terminal_wealth_eq`). For a strictly increasing partition, the
**simple-strategy formula** says that self-financing holds exactly when the wealth
`V_t = a_t S_t + b_t β_t` satisfies

`V_t = V₀ + ∫₀ᵗ a dS + ∫₀ᵗ b dβ`  for all `t ∈ (τ 0, τ n]`,

where `V₀ = a 0 S (τ 0) + b 0 β (τ 0)` is the initial cost
(`TauCeti.Finance.isSelfFinancing_iff_forall_mem_Ioc`). This is the continuous-time
self-financing equation, specialized to a simple strategy whose stochastic integrals are
elementary sums. A variant with closed intervals needs only a monotone partition
(`TauCeti.Finance.isSelfFinancing_iff_forall_mem_Icc`).

Self-financing does not depend on the unit of account: multiplying both prices by a process that
does not vanish at the rebalancing dates preserves it (`TauCeti.Finance.isSelfFinancing_mul_iff`).
In particular, when the bond price does not vanish on `[τ 0, τ n]`, the discounted wealth of a
self-financing strategy, measured in bond shares, is the initial discounted cost plus the gains
from the discounted stock `S / β` alone (`TauCeti.Finance.isSelfFinancing_iff_discounted`).
The bond holding is therefore determined by the stock holding and the initial capital `v`: when
the bond price does not vanish at the trading dates, `TauCeti.Finance.selfFinancingBond` completes
any stock holding to a self-financing strategy of initial cost `v`, uniquely
(`TauCeti.Finance.IsSelfFinancing.eq_selfFinancingBond`), and the completed bond holding is again
chosen at the start of each interval (`TauCeti.Finance.stronglyMeasurable_selfFinancingBond`).
Self-financing strategies are closed under sums and scaling (`TauCeti.Finance.IsSelfFinancing.add`,
`TauCeti.Finance.IsSelfFinancing.smul`).

All identities here are pathwise, for every `ω`, and the time index is any linear order. The
elementary integral is the value that the stochastic integral of a simple predictable integrand
takes; approximation of general strategies by simple ones is not addressed here.

## References

* H. Föllmer, A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, 4th ed.,
  de Gruyter, 2016, §5.1.
* P. E. Protter, *Stochastic Integration and Differential Equations*, 2nd ed., Springer, 2005,
  §II.2.
-/

public section

noncomputable section

open MeasureTheory Finset

namespace TauCeti.Finance

variable {Ω ι : Type*} {τ : ℕ → ι} {n j : ℕ} {t : ι}
  {a a₁ a₂ b b₁ b₂ : ℕ → Ω → ℝ} {S β X N : ι → Ω → ℝ} {v : Ω → ℝ}

/-! ### Simple holdings and their gains -/

section Gains

variable [LinearOrder ι]

/-- The holding process of a simple strategy that holds `a j` units on the interval
`(τ j, τ (j + 1)]`, for `j < n`, and nothing outside `(τ 0, τ n]`:
`a_t = ∑_{j < n} a j · 1_{(τ j, τ (j + 1)]}(t)`. -/
def simpleHolding (τ : ℕ → ι) (n : ℕ) (a : ℕ → Ω → ℝ) (t : ι) (ω : Ω) : ℝ :=
  ∑ j ∈ range n, (Set.Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j ω) t

/-- Unfolding lemma for `simpleHolding`. -/
theorem simpleHolding_def (τ : ℕ → ι) (n : ℕ) (a : ℕ → Ω → ℝ) (t : ι) (ω : Ω) :
    simpleHolding τ n a t ω =
      ∑ j ∈ range n, (Set.Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j ω) t :=
  (rfl)

/-- The gains from trading a price process `X` with a simple strategy holding `a j` units on
`(τ j, τ (j + 1)]`: the elementary integral
`∫₀ᵗ a dX = ∑_{j < n} a j · (X (τ (j + 1) ⊓ t) - X (τ j ⊓ t))`. -/
def simpleGains (τ : ℕ → ι) (n : ℕ) (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (t : ι) (ω : Ω) : ℝ :=
  ∑ j ∈ range n, a j ω * (X (min (τ (j + 1)) t) ω - X (min (τ j) t) ω)

/-- Unfolding lemma for `simpleGains`. -/
theorem simpleGains_def (τ : ℕ → ι) (n : ℕ) (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (t : ι) (ω : Ω) :
    simpleGains τ n a X t ω =
      ∑ j ∈ range n, a j ω * (X (min (τ (j + 1)) t) ω - X (min (τ j) t) ω) :=
  (rfl)

/-- On the interval `(τ j, τ (j + 1)]` of a partition monotone up to `n`, the simple holding is
`a j`. -/
theorem simpleHolding_of_mem_Ioc (hτ : MonotoneOn τ (Set.Iic n)) (hj : j < n)
    (ht : t ∈ Set.Ioc (τ j) (τ (j + 1))) (ω : Ω) : simpleHolding τ n a t ω = a j ω := by
  rw [simpleHolding_def, sum_eq_single_of_mem j (mem_range.2 hj), Set.indicator_of_mem ht]
  intro i hi hij
  refine Set.indicator_of_notMem (fun hit ↦ ?_) _
  -- Intervals with different indices are disjoint.
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact (hit.2.trans (hτ (hij.trans hj) hj.le hij)).not_gt ht.1
  · exact (ht.2.trans (hτ (hij.trans (mem_range.1 hi)) (mem_range.1 hi).le hij)).not_gt hit.1

/-- Outside `(τ 0, τ n]` a simple strategy over a partition monotone up to `n` holds nothing. -/
@[simp]
theorem simpleHolding_of_notMem_Ioc (hτ : MonotoneOn τ (Set.Iic n))
    (ht : t ∉ Set.Ioc (τ 0) (τ n)) (ω : Ω) : simpleHolding τ n a t ω = 0 := by
  refine sum_eq_zero fun i hi ↦ Set.indicator_of_notMem (fun hit ↦ ht ?_) _
  exact Set.Ioc_subset_Ioc (hτ (Nat.zero_le n) (mem_range.1 hi).le (Nat.zero_le i))
    (hτ (mem_range.1 hi) Set.self_mem_Iic (mem_range.1 hi)) hit

/-- The gains over a partition monotone up to `n` vanish up to its first date. -/
@[simp]
theorem simpleGains_of_le (hτ : MonotoneOn τ (Set.Iic n)) (ht : t ≤ τ 0) (X : ι → Ω → ℝ)
    (ω : Ω) : simpleGains τ n a X t ω = 0 := by
  refine sum_eq_zero fun i hi ↦ ?_
  have h₀ : t ≤ τ i := ht.trans (hτ (Nat.zero_le n) (mem_range.1 hi).le (Nat.zero_le i))
  have h₁ : t ≤ τ (i + 1) := ht.trans (hτ (Nat.zero_le n) (mem_range.1 hi) (Nat.zero_le _))
  simp [h₀, h₁]

/-- After the last date of a partition monotone up to `n`, the gains stay at their terminal
value. -/
theorem simpleGains_of_ge (hτ : MonotoneOn τ (Set.Iic n)) (ht : τ n ≤ t) (X : ι → Ω → ℝ)
    (ω : Ω) : simpleGains τ n a X t ω = simpleGains τ n a X (τ n) ω := by
  refine sum_congr rfl fun i hi ↦ ?_
  have h₀ : τ i ≤ τ n := hτ (mem_range.1 hi).le Set.self_mem_Iic (mem_range.1 hi).le
  have h₁ : τ (i + 1) ≤ τ n := hτ (mem_range.1 hi) Set.self_mem_Iic (mem_range.1 hi)
  simp [h₀, h₁, h₀.trans ht, h₁.trans ht]

/-- The gains from trading a constant price vanish. -/
@[simp]
theorem simpleGains_const (τ : ℕ → ι) (n : ℕ) (a : ℕ → Ω → ℝ) (x : Ω → ℝ) (t : ι) (ω : Ω) :
    simpleGains τ n a (fun _ ↦ x) t ω = 0 := by
  simp [simpleGains_def]

/-- Inside the interval `[τ j, τ (j + 1)]` of a partition monotone up to `n`, the gains grow by
the position `a j` times the price change since `τ j`. -/
theorem simpleGains_of_mem_Icc (hτ : MonotoneOn τ (Set.Iic n)) (hj : j < n)
    (ht : t ∈ Set.Icc (τ j) (τ (j + 1))) (X : ι → Ω → ℝ) (ω : Ω) :
    simpleGains τ n a X t ω = simpleGains τ n a X (τ j) ω + a j ω * (X t ω - X (τ j) ω) := by
  have hjj : τ j ≤ τ (j + 1) := hτ hj.le hj (Nat.le_succ j)
  rw [← sub_eq_iff_eq_add', simpleGains_def, simpleGains_def, ← sum_sub_distrib,
    sum_eq_single_of_mem j (mem_range.2 hj)]
  · simp [ht.1, ht.2, hjj]
  · intro i hi hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · -- An interval before `τ j` has been traded completely at both times.
      have h₁ : τ (i + 1) ≤ τ j := hτ (hij.trans hj) hj.le hij
      have h₀ : τ i ≤ τ j := hτ (hij.trans hj).le hj.le hij.le
      simp [h₀, h₁, h₀.trans ht.1, h₁.trans ht.1]
    · -- An interval after `τ (j + 1)` has not been traded yet at either time.
      have h₀ : τ (j + 1) ≤ τ i := hτ hj (mem_range.1 hi).le hij
      have h₁ : τ (j + 1) ≤ τ (i + 1) := hτ hj (mem_range.1 hi) (Nat.succ_le_succ hij.le)
      simp [ht.2.trans h₀, ht.2.trans h₁, hjj.trans h₀, hjj.trans h₁]

/-- At a rebalancing date `τ j`, `j ≤ n`, of a partition monotone up to `n`, the gains are the
discrete transform `∑_{i < j} a i · (X (τ (i + 1)) - X (τ i))`. -/
theorem simpleGains_apply_eq_sum (hτ : MonotoneOn τ (Set.Iic n)) (hj : j ≤ n) (X : ι → Ω → ℝ)
    (ω : Ω) :
    simpleGains τ n a X (τ j) ω = ∑ i ∈ range j, a i ω * (X (τ (i + 1)) ω - X (τ i) ω) := by
  induction j with
  | zero => simp [simpleGains_of_le hτ le_rfl]
  | succ j ih =>
    rw [simpleGains_of_mem_Icc hτ hj ⟨hτ (Nat.le_of_succ_le hj) hj (Nat.le_succ j), le_rfl⟩,
      ih (Nat.le_of_succ_le hj), sum_range_succ]

/-- The gains are additive in the strategy. -/
@[simp]
theorem simpleGains_add (τ : ℕ → ι) (n : ℕ) (a₁ a₂ : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (t : ι)
    (ω : Ω) :
    simpleGains τ n (a₁ + a₂) X t ω = simpleGains τ n a₁ X t ω + simpleGains τ n a₂ X t ω := by
  simp only [simpleGains_def, Pi.add_apply, add_mul, sum_add_distrib]

/-- The gains scale with the strategy. -/
@[simp]
theorem simpleGains_smul (τ : ℕ → ι) (n : ℕ) (c : ℝ) (a : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) (t : ι)
    (ω : Ω) : simpleGains τ n (c • a) X t ω = c * simpleGains τ n a X t ω := by
  simp only [simpleGains_def, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

/-- The simple holding is additive in the strategy. -/
@[simp]
theorem simpleHolding_add (τ : ℕ → ι) (n : ℕ) (a₁ a₂ : ℕ → Ω → ℝ) (t : ι) (ω : Ω) :
    simpleHolding τ n (a₁ + a₂) t ω = simpleHolding τ n a₁ t ω + simpleHolding τ n a₂ t ω := by
  simp only [simpleHolding_def, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases ht : t ∈ Set.Ioc (τ j) (τ (j + 1)) <;> simp [ht]

/-- The simple holding scales with the strategy. -/
@[simp]
theorem simpleHolding_smul (τ : ℕ → ι) (n : ℕ) (c : ℝ) (a : ℕ → Ω → ℝ) (t : ι) (ω : Ω) :
    simpleHolding τ n (c • a) t ω = c * simpleHolding τ n a t ω := by
  simp only [simpleHolding_def, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases ht : t ∈ Set.Ioc (τ j) (τ (j + 1)) <;> simp [ht]

/-! ### Measurability -/

section Measurability

variable {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}

/-- A simple holding whose position on `(τ j, τ (j + 1)]` is chosen at time `τ j` is
predictable. -/
theorem isStronglyPredictable_simpleHolding [OrderBot ι]
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) :
    IsStronglyPredictable ℱ (simpleHolding τ n a) := by
  have huncurry : Function.uncurry (simpleHolding τ n a) = fun p : ι × Ω ↦
      ∑ j ∈ range n, (Set.Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1 :=
    funext fun p ↦ simpleHolding_def τ n a p.1 p.2
  rw [IsStronglyPredictable, huncurry]
  refine Finset.stronglyMeasurable_fun_sum _ fun j hj ↦ Measurable.stronglyMeasurable ?_
  intro B hB
  have hA : MeasurableSet[ℱ (τ j)] (a j ⁻¹' B) := (ha j (mem_range.1 hj)).measurable hB
  have hI : MeasurableSet[ℱ.predictable] (Set.Ioc (τ j) (τ (j + 1)) ×ˢ (a j ⁻¹' B)) :=
    measurableSet_predictable_Ioc_prod _ _ hA
  have hU : MeasurableSet[ℱ.predictable] (Set.Ioc (τ j) (τ (j + 1)) ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ
  by_cases h0 : (0 : ℝ) ∈ B
  · convert hI.union hU.compl using 1
    ext ⟨s, ω⟩
    by_cases hs : s ∈ Set.Ioc (τ j) (τ (j + 1)) <;> simp [hs, h0]
  · convert hI using 1
    ext ⟨s, ω⟩
    by_cases hs : s ∈ Set.Ioc (τ j) (τ (j + 1)) <;> simp [hs, h0]

/-- The gains of a simple strategy over a partition monotone up to `n`, with each position chosen
at the start of its interval, are adapted when the price is. -/
theorem stronglyAdapted_simpleGains (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) (hX : StronglyAdapted ℱ X) :
    StronglyAdapted ℱ (simpleGains τ n a X) := by
  intro t
  refine Finset.stronglyMeasurable_fun_sum _ fun j hj ↦ ?_
  by_cases hjt : τ j ≤ t
  · exact ((ha j (mem_range.1 hj)).mono (ℱ.mono hjt)).mul
      ((hX.stronglyMeasurable_le (min_le_right _ _)).sub
        (hX.stronglyMeasurable_le (min_le_right _ _)))
  · -- The interval `(τ j, τ (j + 1)]` has not started yet, so its gains vanish at time `t`.
    have ht : t ≤ τ j := (not_le.1 hjt).le
    convert stronglyMeasurable_const (b := (0 : ℝ)) using 1
    ext ω
    rw [min_eq_right (ht.trans (hτ (mem_range.1 hj).le (mem_range.1 hj) (Nat.le_succ j))),
      min_eq_right ht, sub_self, mul_zero]

end Measurability

end Gains

/-! ### Self-financing strategies -/

/-- A simple strategy holding `a j` shares of stock and `b j` shares of bond on
`(τ j, τ (j + 1)]` is **self-financing** for the prices `S` and `β` if every rebalancing is paid
for by the old position: at each date `τ (j + 1)` with `j + 1 < n`, the new portfolio costs what
the old one is worth. -/
def IsSelfFinancing (τ : ℕ → ι) (n : ℕ) (a b : ℕ → Ω → ℝ) (S β : ι → Ω → ℝ) : Prop :=
  ∀ j, j + 1 < n → ∀ ω, a (j + 1) ω * S (τ (j + 1)) ω + b (j + 1) ω * β (τ (j + 1)) ω =
    a j ω * S (τ (j + 1)) ω + b j ω * β (τ (j + 1)) ω

/-- Unfolding lemma for `IsSelfFinancing`. -/
theorem isSelfFinancing_iff :
    IsSelfFinancing τ n a b S β ↔ ∀ j, j + 1 < n → ∀ ω,
      a (j + 1) ω * S (τ (j + 1)) ω + b (j + 1) ω * β (τ (j + 1)) ω =
        a j ω * S (τ (j + 1)) ω + b j ω * β (τ (j + 1)) ω :=
  Iff.rfl

/-- Self-financing strategies are closed under addition. -/
theorem IsSelfFinancing.add (h₁ : IsSelfFinancing τ n a₁ b₁ S β)
    (h₂ : IsSelfFinancing τ n a₂ b₂ S β) : IsSelfFinancing τ n (a₁ + a₂) (b₁ + b₂) S β := by
  intro j hj ω
  simp only [Pi.add_apply]
  linear_combination h₁ j hj ω + h₂ j hj ω

/-- Self-financing strategies are closed under scaling. -/
theorem IsSelfFinancing.smul (h : IsSelfFinancing τ n a b S β) (c : ℝ) :
    IsSelfFinancing τ n (c • a) (c • b) S β := by
  intro j hj ω
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination c * h j hj ω

/-- **The terminal wealth** of a self-financing strategy: the final portfolio `(a n, b n)`, valued
at the last date `τ (n + 1)`, is worth the initial cost plus the discrete gains from trading the
stock and the bond. -/
theorem IsSelfFinancing.terminal_wealth_eq (h : IsSelfFinancing τ (n + 1) a b S β) (ω : Ω) :
    a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω =
      a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω +
        ∑ i ∈ range (n + 1), a i ω * (S (τ (i + 1)) ω - S (τ i) ω) +
        ∑ i ∈ range (n + 1), b i ω * (β (τ (i + 1)) ω - β (τ i) ω) := by
  induction n with
  | zero => simp only [zero_add, sum_range_one]; ring
  | succ n ih =>
    rw [sum_range_succ _ (n + 1), sum_range_succ _ (n + 1)]
    linear_combination ih (fun j hj ω ↦ h j (by omega) ω) + h n (by omega) ω

/-- Self-financing does not depend on the unit of account: multiplying both prices by a process
that does not vanish at the rebalancing dates `τ (j + 1)`, `j + 1 < n`, preserves it. -/
theorem isSelfFinancing_mul_iff (hN : ∀ j, j + 1 < n → ∀ ω, N (τ (j + 1)) ω ≠ 0) :
    IsSelfFinancing τ n a b (S * N) (β * N) ↔ IsSelfFinancing τ n a b S β := by
  refine forall₂_congr fun j hj ↦ forall_congr' fun ω ↦ ?_
  simp only [Pi.mul_apply]
  constructor
  · intro h
    refine mul_right_cancel₀ (hN j hj ω) ?_
    linear_combination h
  · intro h
    linear_combination N (τ (j + 1)) ω * h

/-! ### The simple-strategy formula -/

section Formula

variable [LinearOrder ι]

/-- On `[τ j, τ (j + 1)]`, the wealth formula for the portfolio `(a j, b j)` reduces to its value
at `τ j`. -/
private theorem wealth_eq_iff_of_mem_Icc (hτ : MonotoneOn τ (Set.Iic n)) (hj : j < n)
    (ht : t ∈ Set.Icc (τ j) (τ (j + 1))) (ω : Ω) :
    a j ω * S t ω + b j ω * β t ω = a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω +
        simpleGains τ n a S t ω + simpleGains τ n b β t ω ↔
      a j ω * S (τ j) ω + b j ω * β (τ j) ω = a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω +
        simpleGains τ n a S (τ j) ω + simpleGains τ n b β (τ j) ω := by
  rw [simpleGains_of_mem_Icc hτ hj ht, simpleGains_of_mem_Icc hτ hj ht]
  constructor <;> intro h <;> linarith

/-- A strategy over a partition monotone up to `n` is self-financing exactly when each of its
portfolios `(a j, b j)` costs, at the start `τ j` of its interval, the initial cost plus the gains
so far. -/
theorem isSelfFinancing_iff_forall_lt (hτ : MonotoneOn τ (Set.Iic n)) :
    IsSelfFinancing τ n a b S β ↔ ∀ j < n, ∀ ω,
      a j ω * S (τ j) ω + b j ω * β (τ j) ω = a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω +
        simpleGains τ n a S (τ j) ω + simpleGains τ n b β (τ j) ω := by
  -- Over `[τ j, τ (j + 1)]` the gains grow by the change in value of the portfolio `(a j, b j)`.
  have step : ∀ j, j + 1 < n → ∀ (c : ℕ → Ω → ℝ) (X : ι → Ω → ℝ) ω,
      simpleGains τ n c X (τ (j + 1)) ω =
        simpleGains τ n c X (τ j) ω + c j ω * (X (τ (j + 1)) ω - X (τ j) ω) :=
    fun j hj c X ω ↦ simpleGains_of_mem_Icc hτ (by omega)
      ⟨hτ (Nat.le_of_succ_le hj.le) hj.le (Nat.le_succ j), le_rfl⟩ X ω
  constructor
  · intro h j hj ω
    induction j with
    | zero => simp [simpleGains_of_le hτ le_rfl]
    | succ j ih =>
      have := h j hj ω
      rw [step j hj a S ω, step j hj b β ω]
      linarith [ih (by omega)]
  · intro h j hj ω
    have h₀ := h j (by omega) ω
    have h₁ := h (j + 1) hj ω
    rw [step j hj a S ω, step j hj b β ω] at h₁
    linarith

/-- **The simple-strategy formula**, closed-interval form: a strategy over a partition monotone up
to `n` is self-financing exactly when, on each interval `[τ j, τ (j + 1)]`, the value of the
portfolio `(a j, b j)` is the initial cost plus the gains from trading the stock and the bond. -/
theorem isSelfFinancing_iff_forall_mem_Icc (hτ : MonotoneOn τ (Set.Iic n)) :
    IsSelfFinancing τ n a b S β ↔ ∀ j < n, ∀ ω, ∀ t ∈ Set.Icc (τ j) (τ (j + 1)),
      a j ω * S t ω + b j ω * β t ω = a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω +
        simpleGains τ n a S t ω + simpleGains τ n b β t ω := by
  rw [isSelfFinancing_iff_forall_lt hτ]
  refine forall₂_congr fun j hj ↦ forall_congr' fun ω ↦ ⟨fun h t ht ↦ ?_, fun h ↦ ?_⟩
  · exact (wealth_eq_iff_of_mem_Icc hτ hj ht ω).2 h
  · have hjj : τ j ≤ τ (j + 1) := hτ hj.le hj (Nat.le_succ j)
    exact (wealth_eq_iff_of_mem_Icc hτ hj ⟨le_rfl, hjj⟩ ω).1 (h _ ⟨le_rfl, hjj⟩)

/-- **The simple-strategy formula**: a strategy over a partition strictly increasing up to `n` is
self-financing exactly when its wealth `V_t = a_t S_t + b_t β_t` satisfies
`V_t = V₀ + ∫₀ᵗ a dS + ∫₀ᵗ b dβ` throughout `(τ 0, τ n]`, where `V₀ = a 0 S (τ 0) + b 0 β (τ 0)`
is the initial cost and the integrals are the elementary gains. -/
theorem isSelfFinancing_iff_forall_mem_Ioc (hτ : StrictMonoOn τ (Set.Iic n)) :
    IsSelfFinancing τ n a b S β ↔ ∀ ω, ∀ t ∈ Set.Ioc (τ 0) (τ n),
      simpleHolding τ n a t ω * S t ω + simpleHolding τ n b t ω * β t ω =
        a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω +
          simpleGains τ n a S t ω + simpleGains τ n b β t ω := by
  rw [isSelfFinancing_iff_forall_mem_Icc hτ.monotoneOn]
  constructor
  · intro h ω t ht
    obtain ⟨j, hj, ht⟩ : ∃ j < n, t ∈ Set.Ioc (τ j) (τ (j + 1)) := by
      -- Frozen after `n`, the partition is monotone and its intervals cover `(τ 0, τ n]`.
      have hcover :=
        (Set.monotoneOn_iff_monotone.1 hτ.monotoneOn).IicExtend.biUnion_Ico_Ioc_map_succ 0 n
      simp only [Set.IicExtend_apply, Nat.min_zero, min_self, Order.succ_eq_add_one,
        Set.mem_Ico, Nat.zero_le, true_and] at hcover
      rw [← hcover] at ht
      simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨j, hj, ht⟩ := ht
      rw [min_eq_right hj.le, min_eq_right (Nat.add_one_le_of_lt hj)] at ht
      exact ⟨j, hj, ht⟩
    rw [simpleHolding_of_mem_Ioc hτ.monotoneOn hj ht, simpleHolding_of_mem_Ioc hτ.monotoneOn hj ht]
    exact h j hj ω t (Set.Ioc_subset_Icc_self ht)
  · intro h j hj ω t ht
    -- The wealth formula at `τ (j + 1)`, the right end of the nonempty interval
    -- `(τ j, τ (j + 1)]`, already determines the value of the portfolio `(a j, b j)`.
    have hmem : τ (j + 1) ∈ Set.Ioc (τ j) (τ (j + 1)) :=
      ⟨hτ (Set.mem_Iic.2 hj.le) (Set.mem_Iic.2 hj) (Nat.lt_succ_self j), le_rfl⟩
    have hend := h ω (τ (j + 1))
      ⟨hτ (Nat.zero_le n) hj (Nat.succ_pos j), hτ.monotoneOn hj Set.self_mem_Iic hj⟩
    rw [simpleHolding_of_mem_Ioc hτ.monotoneOn hj hmem,
      simpleHolding_of_mem_Ioc hτ.monotoneOn hj hmem] at hend
    exact (wealth_eq_iff_of_mem_Icc hτ.monotoneOn hj ht ω).2
      ((wealth_eq_iff_of_mem_Icc hτ.monotoneOn hj (Set.Ioc_subset_Icc_self hmem) ω).1 hend)

/-- **The discounted simple-strategy formula**: when the bond price does not vanish on
`[τ 0, τ n]`, a strategy over a partition monotone up to `n` is self-financing exactly when, on
each interval `[τ j, τ (j + 1)]`, the discounted value of the portfolio `(a j, b j)` is the
discounted initial cost plus the gains from trading the discounted stock `S / β`. -/
theorem isSelfFinancing_iff_discounted (hτ : MonotoneOn τ (Set.Iic n))
    (hβ : ∀ t ∈ Set.Icc (τ 0) (τ n), ∀ ω, β t ω ≠ 0) :
    IsSelfFinancing τ n a b S β ↔ ∀ j < n, ∀ ω, ∀ t ∈ Set.Icc (τ j) (τ (j + 1)),
      (a j ω * S t ω + b j ω * β t ω) / β t ω =
        (a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω) / β (τ 0) ω + simpleGains τ n a (S / β) t ω := by
  have hdate : ∀ k ≤ n, τ k ∈ Set.Icc (τ 0) (τ n) := fun k hk ↦
    ⟨hτ (Nat.zero_le n) hk (Nat.zero_le k), hτ hk Set.self_mem_Iic hk⟩
  rw [← isSelfFinancing_mul_iff (N := β⁻¹) fun j hj ω ↦ inv_ne_zero (hβ _ (hdate _ hj.le) ω),
    ← div_eq_mul_inv S β, isSelfFinancing_iff_forall_mem_Icc hτ]
  refine forall₂_congr fun j hj ↦ forall_congr' fun ω ↦ forall₂_congr fun t ht ↦ ?_
  have ht₀ : t ∈ Set.Icc (τ 0) (τ n) :=
    ⟨(hdate j hj.le).1.trans ht.1, ht.2.trans (hdate (j + 1) hj).2⟩
  -- Measured in bond shares, the bond is worth `1` throughout `[τ 0, τ n]`, so it brings no gains.
  have hone : ∀ s ∈ Set.Icc (τ 0) (τ n), (β * β⁻¹) s ω = 1 :=
    fun s hs ↦ mul_inv_cancel₀ (hβ s hs ω)
  have hgains : simpleGains τ n b (β * β⁻¹) t ω = 0 := by
    rw [simpleGains_of_mem_Icc hτ hj ht, simpleGains_apply_eq_sum hτ hj.le, hone t ht₀,
      hone _ (hdate j hj.le), sub_self, mul_zero, add_zero]
    exact sum_eq_zero fun i hi ↦ by
      rw [hone _ (hdate (i + 1) ((mem_range.1 hi).trans hj)),
        hone _ (hdate i ((mem_range.1 hi).trans hj).le), sub_self, mul_zero]
  rw [hgains, hone t ht₀, hone _ (hdate 0 (Nat.zero_le n))]
  simp only [Pi.div_apply, add_div, mul_div_assoc, div_self (hβ t ht₀ ω),
    div_self (hβ _ (hdate 0 (Nat.zero_le n)) ω), mul_one, add_zero]

end Formula

/-! ### The self-financing bond holding -/

/-- The bond holding that completes the stock holding `a` to a self-financing strategy with
initial cost `v`, when the bond price does not vanish at the trading dates: on
`(τ j, τ (j + 1)]` it is the discounted wealth at `τ j`, namely the discounted initial capital plus
the discrete gains from the discounted stock, minus the discounted value of the stock position
`a j`. -/
def selfFinancingBond (τ : ℕ → ι) (v : Ω → ℝ) (a : ℕ → Ω → ℝ) (S β : ι → Ω → ℝ) (j : ℕ)
    (ω : Ω) : ℝ :=
  v ω / β (τ 0) ω +
      ∑ i ∈ range j, a i ω * (S (τ (i + 1)) ω / β (τ (i + 1)) ω - S (τ i) ω / β (τ i) ω) -
    a j ω * (S (τ j) ω / β (τ j) ω)

/-- Unfolding lemma for `selfFinancingBond`. -/
theorem selfFinancingBond_def (τ : ℕ → ι) (v : Ω → ℝ) (a : ℕ → Ω → ℝ) (S β : ι → Ω → ℝ)
    (j : ℕ) (ω : Ω) :
    selfFinancingBond τ v a S β j ω = v ω / β (τ 0) ω +
        ∑ i ∈ range j, a i ω * (S (τ (i + 1)) ω / β (τ (i + 1)) ω - S (τ i) ω / β (τ i) ω) -
      a j ω * (S (τ j) ω / β (τ j) ω) :=
  (rfl)

/-- The strategy completed by `selfFinancingBond` costs `v` initially, when the initial bond price
does not vanish. -/
theorem mul_add_mul_selfFinancingBond_zero (hβ : ∀ ω, β (τ 0) ω ≠ 0) (ω : Ω) :
    a 0 ω * S (τ 0) ω + selfFinancingBond τ v a S β 0 ω * β (τ 0) ω = v ω := by
  rw [selfFinancingBond_def]
  field_simp [hβ ω]
  simp

/-- The strategy completed by `selfFinancingBond` is self-financing, when the bond price does not
vanish at the trading dates `τ j`, `j < n`. -/
theorem isSelfFinancing_selfFinancingBond (hβ : ∀ j < n, ∀ ω, β (τ j) ω ≠ 0) :
    IsSelfFinancing τ n a (selfFinancingBond τ v a S β) S β := by
  intro j hj ω
  simp only [selfFinancingBond_def, sum_range_succ]
  field_simp [hβ j (by omega) ω, hβ (j + 1) hj ω, hβ 0 (by omega) ω]
  ring

/-- A self-financing strategy with stock holding `a` and initial cost `v` has the bond holding
`selfFinancingBond τ v a S β` on every interval `(τ j, τ (j + 1)]`, `j < n`, when the bond price
does not vanish at the dates `τ 0, …, τ j`. -/
theorem IsSelfFinancing.eq_selfFinancingBond (h : IsSelfFinancing τ n a b S β)
    (hβ : ∀ i ≤ j, ∀ ω, β (τ i) ω ≠ 0) (hv : ∀ ω, a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω = v ω)
    (hj : j < n) (ω : Ω) : b j ω = selfFinancingBond τ v a S β j ω := by
  induction j with
  | zero =>
    refine mul_right_cancel₀ (hβ 0 le_rfl ω) ?_
    linear_combination hv ω -
      mul_add_mul_selfFinancingBond_zero (a := a) (S := S) (v := v) (hβ 0 le_rfl) ω
  | succ j ih =>
    refine mul_right_cancel₀ (hβ (j + 1) le_rfl ω) ?_
    linear_combination h j hj ω -
      isSelfFinancing_selfFinancingBond (n := j + 2) (a := a) (S := S) (v := v)
        (fun i hi ↦ hβ i (by omega)) j (by omega) ω +
      β (τ (j + 1)) ω * ih (fun i hi ↦ hβ i (by omega)) (by omega)

/-- The bond holding completing a stock holding chosen at the start of each interval is again
chosen at the start of its interval, when the initial capital is known at `τ 0` and the prices
are adapted. -/
theorem stronglyMeasurable_selfFinancingBond [Preorder ι] {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ι mΩ}
    (hτ : MonotoneOn τ (Set.Iic j)) (hv : StronglyMeasurable[ℱ (τ 0)] v)
    (ha : ∀ i ≤ j, StronglyMeasurable[ℱ (τ i)] (a i)) (hS : StronglyAdapted ℱ S)
    (hβ : StronglyAdapted ℱ β) :
    StronglyMeasurable[ℱ (τ j)] (selfFinancingBond τ v a S β j) := by
  have hle : ∀ i ≤ j, τ i ≤ τ j := fun i hi ↦ hτ hi Set.self_mem_Iic hi
  have hdisc : ∀ i ≤ j, StronglyMeasurable[ℱ (τ j)] fun ω ↦ S (τ i) ω / β (τ i) ω :=
    fun i hi ↦ (hS.stronglyMeasurable_le (hle i hi)).div (hβ.stronglyMeasurable_le (hle i hi))
  have hgains : StronglyMeasurable[ℱ (τ j)] fun ω ↦
      ∑ i ∈ range j, a i ω * (S (τ (i + 1)) ω / β (τ (i + 1)) ω - S (τ i) ω / β (τ i) ω) :=
    Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
      ((ha i (mem_range.1 hi).le).mono (ℱ.mono (hle i (mem_range.1 hi).le))).mul
        ((hdisc (i + 1) (mem_range.1 hi)).sub (hdisc i (mem_range.1 hi).le))
  exact ((hv.mono (ℱ.mono (hle 0 (Nat.zero_le j)))).div
      (hβ.stronglyMeasurable_le (hle 0 (Nat.zero_le j)))).add hgains |>.sub
    ((ha j le_rfl).mul (hdisc j le_rfl))

end TauCeti.Finance
