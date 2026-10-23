/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Factorials in p-adic fields

The integers `n!` converge to zero at every finite place, although none is zero. This provides
one sequence of rational parameters that simultaneously contracts every local unipotent
one-parameter subgroup. Divisibility by each fixed prime power suffices for the convergence.

## Main results

* `TauCeti.tendsto_padic_natCast_factorial`: the factorials tend to zero in `ℚ_[p]`.
* `Padic.norm_factorial_mul`: `‖(p k)!‖ = p ^ (-k) ‖k!‖` in `ℚ_[p]`, by Legendre's formula.
-/

public section

namespace TauCeti

open Filter Topology

/-- The factorials, viewed in a fixed p-adic field, tend to zero. -/
theorem tendsto_padic_natCast_factorial (p : ℕ) [hp : Fact p.Prime] :
    Tendsto (fun n : ℕ ↦ (n.factorial : ℚ_[p])) atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ ↦ (p : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := (hpow.eventually (gt_mem_nhds hε)).exists
  refine ⟨p ^ k, fun n hn ↦ ?_⟩
  have hd : (p : ℤ) ^ k ∣ (n.factorial : ℤ) := by
    exact_mod_cast Nat.dvd_factorial (pow_pos hp.out.pos _) hn
  have hnorm := (Padic.norm_int_le_pow_iff_dvd (p := p) (n.factorial : ℤ) k).mpr hd
  simp only [Int.cast_natCast, zpow_neg, zpow_natCast, ← inv_pow] at hnorm
  simpa only [dist_zero_right] using hnorm.trans_lt hk

end TauCeti

namespace Padic

open Nat

variable {p : ℕ} [Fact p.Prime]

/-- The factorial of `p k` has `p`-adic norm `p ^ (-k) ‖k!‖`: by Legendre's formula, passing from
`k!` to `(p k)!` raises the valuation by `k`. -/
theorem norm_factorial_mul (k : ℕ) :
    ‖((p * k)! : ℚ_[p])‖ = (p : ℝ) ^ (-(k : ℤ)) * ‖(k ! : ℚ_[p])‖ := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [norm_natCast_eq_zpow (factorial_ne_zero _), norm_natCast_eq_zpow (factorial_ne_zero _),
    padicValNat_factorial_mul, ← zpow_add₀ hp]
  congr 1
  push_cast
  ring

end Padic
