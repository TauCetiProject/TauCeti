/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Norm
import TauCeti.NumberTheory.NumberField.Minpoly

/-!
# Units of a number field

Basic facts about the units of the ring of integers of a number field `K`, beyond Mathlib's
`Mathlib.NumberTheory.NumberField.Units.Basic`.

The norm of a unit is `±1`, so the constant coefficient of its minimal polynomial over `ℤ` is
`±1`. The units of `ℤ` are `±1`, so a unit of `𝓞 K` whose image in `K` is rational is a root of
unity: its absolute value is the same at every infinite place, and the product formula forces
that value to be `1`. Read the other way, a non-torsion unit lies outside the base field `ℚ`,
which is what field-generation and primitive-element arguments about units need, for instance
to see that a non-torsion unit of a field of prime degree generates the field.

## Main results

* `TauCeti.NumberField.Units.coeff_zero_minpoly_eq_one_or_neg_one`: the constant coefficient
  of the minimal polynomial of a unit is `±1`.
* `TauCeti.NumberField.Units.mem_torsion_of_mem_bot`: a unit whose image in `K` lies in the
  base field `ℚ` is torsion.
* `NumberField.InfinitePlace.exists_torsion_mul_embedding_eq_abs`: a torsion sign makes a
  unit's real embedding equal its absolute value at a real place.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- At a real place, multiply a unit by a torsion unit so that its real embedding is its
(positive) absolute value. -/
theorem exists_torsion_mul_embedding_eq_abs (w : InfinitePlace K) (hw : w.IsReal)
    (v : (𝓞 K)ˣ) :
    ∃ ε : torsion K,
      embedding_of_isReal hw ((ε.1 * v : (𝓞 K)ˣ) : K) = w v := by
  let φ := embedding_of_isReal hw
  have hv : |φ (v : K)| = w v := by
    simpa [Real.norm_eq_abs] using (norm_embedding_of_isReal hw (v : K))
  by_cases h : 0 ≤ φ (v : K)
  · refine ⟨1, ?_⟩
    simpa [φ, abs_of_nonneg h] using hv
  · refine ⟨⟨-1, neg_one_mem_torsion⟩, ?_⟩
    have hneg : φ (v : K) < 0 := lt_of_not_ge h
    simpa [φ, abs_of_neg hneg] using hv

end NumberField.InfinitePlace

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

open scoped IntermediateField in
/-- The constant coefficient of the minimal polynomial of a unit is `±1`. -/
theorem coeff_zero_minpoly_eq_one_or_neg_one (v : (𝓞 K)ˣ) :
    (minpoly ℤ (v : 𝓞 K)).coeff 0 = 1 ∨ (minpoly ℤ (v : 𝓞 K)).coeff 0 = -1 := by
  have hint : IsIntegral ℚ ((v : 𝓞 K) : K) := IsIntegral.of_finite ℚ _
  -- The norm of `v` from `ℚ(v)` is `±` the constant coefficient, and its norm from `K` is a
  -- power of that; the latter is a unit of `ℤ`.
  have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (IntermediateField.adjoin.powerBasis hint)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen,
    RingOfIntegers.minpoly_rat_coe, Polynomial.coeff_map, eq_intCast] at hpb
  have hadj := Algebra.norm_eq_norm_adjoin ℚ ((v : 𝓞 K) : K)
  rw [← Algebra.coe_norm_int, hpb] at hadj
  have hZ : Algebra.norm ℤ (v : 𝓞 K) =
      ((-1) ^ (IntermediateField.adjoin.powerBasis hint).dim * (minpoly ℤ (v : 𝓞 K)).coeff 0) ^
        Module.finrank ℚ⟮((v : 𝓞 K) : K)⟯ K := by
    exact_mod_cast hadj
  have hu : IsUnit (((-1) ^ (IntermediateField.adjoin.powerBasis hint).dim *
      (minpoly ℤ (v : 𝓞 K)).coeff 0) ^ Module.finrank ℚ⟮((v : 𝓞 K) : K)⟯ K) := by
    rw [← hZ]
    exact v.isUnit.map (Algebra.norm ℤ)
  rw [isUnit_pow_iff Module.finrank_pos.ne'] at hu
  exact Int.isUnit_iff.mp (isUnit_of_mul_isUnit_right hu)

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
