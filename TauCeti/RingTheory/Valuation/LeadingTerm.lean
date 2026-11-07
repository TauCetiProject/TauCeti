/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Finset.Order

/-!
# The leading term of a polynomial dominates at large arguments

Let `ν` be a valuation with values in a linearly ordered group with zero. At an element `t` with
`ν t ≥ 1`, the leading term of a polynomial `p` dominates the value of `p(t)` as soon as each
lower coefficient has value below `ν (leadingCoeff p) * ν t`:
`ν (p.eval t) = ν (leadingCoeff p) * ν t ^ natDegree p`. Over a division ring this holds at every
`t` of large enough value. This is the non-monic form of `Valuation.map_eval_eq_of_one_lt`, which
assumes `p` monic with integral coefficients and `1 < ν t`.

## Main results

* `Valuation.map_eval_eq_leadingCoeff_mul_pow`: the leading term dominates when the lower
  coefficients are small compared with `ν (leadingCoeff p) * ν t`.
* `Valuation.exists_map_eval_eq_leadingCoeff_mul_pow`: over a division ring, the leading term
  dominates at every `t` whose value exceeds a bound depending on `p`.
-/

public section

namespace Valuation

open Polynomial

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **The leading term of a polynomial dominates its value at a large argument**: if `ν t ≥ 1` and
every coefficient of `p` below the leading one has value less than `ν (leadingCoeff p) * ν t`, then
`ν (p.eval t) = ν (leadingCoeff p) * ν t ^ natDegree p`. -/
theorem map_eval_eq_leadingCoeff_mul_pow {L : Type*} [Ring L] (ν : Valuation L Γ₀) {p : L[X]}
    {t : L} (ht : 1 ≤ ν t) (hp : ∀ i < p.natDegree, ν (p.coeff i) < ν p.leadingCoeff * ν t) :
    ν (p.eval t) = ν p.leadingCoeff * ν t ^ p.natDegree := by
  set n := p.natDegree with hn
  have ht0 : 0 < ν t := zero_lt_one.trans_le ht
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · simp [eval_eq_sum_range, ← hn, h0, leadingCoeff]
  have hlc : ν p.leadingCoeff ≠ 0 := by
    rintro h
    simpa [h] using hp 0 h0
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + p.leadingCoeff * t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ]
    rfl
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (p.leadingCoeff * t ^ n) := by
    refine ν.map_sum_lt (by rw [map_mul, map_pow]; exact mul_ne_zero hlc (pow_ne_zero _ ht0.ne'))
      fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [map_mul, map_mul, map_pow, map_pow]
    calc ν (p.coeff i) * ν t ^ i < ν p.leadingCoeff * ν t * ν t ^ i :=
          mul_lt_mul_of_pos_right (hp i hi) (pow_pos ht0 i)
      _ = ν p.leadingCoeff * ν t ^ (i + 1) := by rw [pow_succ', mul_assoc]
      _ ≤ ν p.leadingCoeff * ν t ^ n := by
        gcongr ν p.leadingCoeff * ?_
        exact pow_le_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_mul, map_pow]

/-- **The leading term of a polynomial dominates at every large enough argument**: over a division
ring, there is a bound `R` such that `ν (p.eval t) = ν (leadingCoeff p) * ν t ^ natDegree p`
whenever `R < ν t`. -/
theorem exists_map_eval_eq_leadingCoeff_mul_pow {K : Type*} [DivisionRing K] (ν : Valuation K Γ₀)
    (p : K[X]) :
    ∃ R : Γ₀, ∀ t : K, R < ν t → ν (p.eval t) = ν p.leadingCoeff * ν t ^ p.natDegree := by
  obtain ⟨M, hM⟩ := ((Finset.range p.natDegree).image
    fun i ↦ ν (p.coeff i) / ν p.leadingCoeff).exists_le
  refine ⟨max 1 M, fun t ht ↦ ν.map_eval_eq_leadingCoeff_mul_pow
    ((le_max_left _ _).trans ht.le) fun i hi ↦ ?_⟩
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hi
  have hlc : 0 < ν p.leadingCoeff := by
    rw [zero_lt_iff, ne_eq, ν.zero_iff, leadingCoeff_eq_zero]
    exact hp
  have hi' := (hM _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))).trans_lt
    ((le_max_right _ _).trans_lt ht)
  rwa [div_lt_iff₀ hlc, mul_comm] at hi'

end Valuation
