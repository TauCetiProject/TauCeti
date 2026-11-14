/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic

/-!
# Associativity of elementary integration

Integrating a simple holding against the gains of another simple holding multiplies
these holdings. For different trading grids the product is a sum of positions on the
intersections of their trading intervals. `simpleGains_simpleGains_eq_sum` gives the
corresponding gains formula against an arbitrary price path, including observation
times inside a trading interval. `simpleHolding_mul_eq_sum` identifies its integrand
as the product holding, and `simpleGains_simpleGains` gives the common-grid form.

The identities are pathwise and need no regularity, measurability or integrability
of the price or holdings. Nondecreasing grids may have repeated dates, and either
grid may be empty. These are the elementary substitution identities used when
extending integration by approximation and localization.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition,
  Springer, 2005, Chapter II, §2.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

open Finset Set

namespace TauCeti.Finance

variable {Ω ι : Type*} [LinearOrder ι]
  {τ ρ : ℕ → ι} {n m : ℕ} {a b : ℕ → Ω → ℝ} {X : ι → Ω → ℝ}

/-- Multiplication of simple holdings gives positions on the intersections of their
trading intervals. Unlike the gains formula, this identity needs no order condition
on either grid: reversed intervals are already empty. -/
theorem simpleHolding_mul_eq_sum (t : ι) (ω : Ω) :
    simpleHolding ρ m b t ω * simpleHolding τ n a t ω =
      ∑ j ∈ range m, ∑ i ∈ range n,
        (Set.Ioc (max (τ i) (ρ j)) (min (τ (i + 1)) (ρ (j + 1)))).indicator
          (fun _ ↦ b j ω * a i ω) t := by
  rw [simpleHolding_def ρ, simpleHolding_def τ, sum_mul]
  simp_rw [mul_sum]
  refine sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ ?_
  rw [← Set.inter_indicator_mul, Set.Ioc_inter_Ioc, max_comm, min_comm]

private theorem clipped_increment_increment (f : ι → ℝ) {l u c d : ι}
    (hlu : l ≤ u) (hcd : c ≤ d) (t : ι) :
    (f (min u (min d t)) - f (min l (min d t))) -
        (f (min u (min c t)) - f (min l (min c t))) =
      if max l c ≤ min u d then
        f (min (min u d) t) - f (min (max l c) t) else 0 := by
  grind

/-- Integrating one simple strategy against another's gains gives positions
`b j * a i` on the intersections `(max (τ i) (ρ j), min (τ (i+1)) (ρ (j+1))]`.
Disjoint intervals contribute zero; an intersection reduced to a point also has
zero gains. Both grids may be any nondecreasing grids, possibly with repeated dates
or empty, and the observation time is arbitrary. -/
theorem simpleGains_simpleGains_eq_sum (hτ : MonotoneOn τ (Set.Iic n))
    (hρ : MonotoneOn ρ (Set.Iic m)) (t : ι) (ω : Ω) :
    simpleGains ρ m b (simpleGains τ n a X) t ω =
      ∑ j ∈ range m, ∑ i ∈ range n,
        if max (τ i) (ρ j) ≤ min (τ (i + 1)) (ρ (j + 1)) then
          (b j ω * a i ω) *
            (X (min (min (τ (i + 1)) (ρ (j + 1))) t) ω -
              X (min (max (τ i) (ρ j)) t) ω)
        else 0 := by
  classical
  simp only [simpleGains_def, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun j hj ↦ sum_congr rfl fun i hi ↦ ?_
  have hi := mem_range.mp hi
  have hj := mem_range.mp hj
  have h := clipped_increment_increment (fun u ↦ X u ω)
    (hτ hi.le hi (Nat.le_succ i)) (hρ hj.le hj (Nat.le_succ j)) t
  rw [← mul_sub, h]
  split_ifs <;> ring

/-- On one trading grid, substitution multiplies the two positions interval by
interval. This holds for any price path, including jumps at trading dates. -/
@[simp]
theorem simpleGains_simpleGains (hτ : MonotoneOn τ (Set.Iic n)) (t : ι) (ω : Ω) :
    simpleGains τ n b (simpleGains τ n a X) t ω =
      simpleGains τ n (fun j ω ↦ b j ω * a j ω) X t ω := by
  rw [simpleGains_def τ n b,
    simpleGains_def τ n (fun j ω ↦ b j ω * a j ω)]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj := mem_range.mp hj
  have hstep : ∀ u ∈ Icc (τ j) (τ (j + 1)),
      simpleGains τ n a X u ω - simpleGains τ n a X (τ j) ω =
        a j ω * (X u ω - X (τ j) ω) := by
    intro u hu
    rw [simpleGains_of_mem_Icc hτ hj hu]
    ring
  by_cases ht : t ≤ τ j
  · have ht' : t ≤ τ (j + 1) := ht.trans (hτ hj.le hj (Nat.le_succ j))
    simp [min_eq_right ht, min_eq_right ht']
  · have ht : τ j ≤ t := (not_le.mp ht).le
    rw [min_eq_left ht, hstep _ ⟨le_min (hτ hj.le hj (Nat.le_succ j)) ht, min_le_left _ _⟩]
    ring

end TauCeti.Finance
