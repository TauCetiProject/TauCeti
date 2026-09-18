/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Units of a number field

Basic facts about the units of the ring of integers of a number field `K`, beyond Mathlib's
`Mathlib.NumberTheory.NumberField.Units.Basic`.

## Main results

* `TauCeti.NumberField.Units.mem_torsion_of_mem_bot`: a unit whose image in `K` lies in the
  base field `ℚ` is torsion.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- A unit whose image in `K` lies in the base field `ℚ` is torsion. -/
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

end TauCeti.NumberField.Units
