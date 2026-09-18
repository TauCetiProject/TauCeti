/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.FinrankPrime

/-!
# Units of a number field of prime degree

A unit of the ring of integers whose value in `K` is rational is torsion: every infinite place
takes the same value on it, and the product formula forces that value to be `1`. In a number
field of prime degree, a unit with absolute value different from `1` at some infinite place
therefore lies in no proper subfield, and generates `K` over `ℚ`. This is what lets a statement
about integral primitive elements of `K` apply to every non-torsion unit when the degree is
prime.

## Main results

* `NumberField.Units.mem_torsion_of_mem_bot`: a unit with rational value is torsion.
* `NumberField.Units.adjoin_eq_top_of_finrank_prime`: in prime degree, a unit with absolute
  value different from `1` at an infinite place generates `K` over `ℚ`.
-/

public section

open NumberField NumberField.InfinitePlace
open scoped NumberField

namespace NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- A unit whose value in `K` is rational is torsion: every infinite place takes the same value
on it, and the product formula forces that value to be `1`. -/
theorem mem_torsion_of_mem_bot {v : (𝓞 K)ˣ} (hv : (v : K) ∈ (⊥ : IntermediateField ℚ K)) :
    v ∈ torsion K := by
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hv
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact coe_ne_zero v (by rw [← hq, map_zero])
  have hval : ∀ w : InfinitePlace K, w v = ‖q‖ := fun w => by
    rw [← hq, eq_ratCast, InfinitePlace.map_ratCast]
  have hlog : (Module.finrank ℚ K : ℝ) * Real.log ‖q‖ = 0 := by
    have h := sum_mult_mul_log v
    simp_rw [hval] at h
    rwa [← Finset.sum_mul, ← Nat.cast_sum, sum_mult_eq] at h
  have h1 : ‖q‖ = 1 :=
    Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr hq0)
      ((mul_eq_zero.mp hlog).resolve_left (by exact_mod_cast Module.finrank_pos.ne'))
  exact (mem_torsion K).mpr fun w => by rw [hval, h1]

/-- **Prime degree makes a competing unit a generator.** In a number field of prime degree, a
unit whose absolute value at some infinite place is not `1` generates `K` over `ℚ`. -/
theorem adjoin_eq_top_of_finrank_prime (hp : Nat.Prime (Module.finrank ℚ K))
    {w : InfinitePlace K} {v : (𝓞 K)ˣ} (hv : w v ≠ 1) :
    Algebra.adjoin ℚ {((v : 𝓞 K) : K)} = ⊤ :=
  Algebra.adjoin_singleton_eq_top_of_finrank_prime hp fun h =>
    hv ((mem_torsion K).mp (mem_torsion_of_mem_bot h) w)

end NumberField.Units
