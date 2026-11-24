/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.Order.Filter.TendstoCofinite
import Mathlib.NumberTheory.NumberField.Norm
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.RingTheory.RootsOfUnity.CyclotomicUnits

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

* `TauCeti.NumberField.Units.val_unitsMap_algebraMap_ringOfIntegers_subfield`: the image in
  `(𝓞 K)ˣ` of an integral unit of a subfield `F` has the same value in `K`.
* `TauCeti.NumberField.Units.val_map_algebraMap_ringOfIntegers_subfield`: the image in `Kˣ` of
  an integral unit of a subfield `F` has the same value in `K`.
* `TauCeti.NumberField.Units.coeff_zero_minpoly_eq_one_or_neg_one`: the constant coefficient
  of the minimal polynomial of a unit is `±1`.
* `TauCeti.NumberField.Units.mem_torsion_of_mem_bot`: a unit whose image in `K` lies in the
  base field `ℚ` is torsion.
* `IsPrimitiveRoot.one_sub_zpow_eq_one_of_val_eq`: for `ζ` a primitive `p ^ a`-th root of unity
  in a field of characteristic zero, an integer power of `1 - ζ` that is the value of an integral
  unit is `1`.
* `Units.prod_norm_embedding_eq_one`: the absolute values of the conjugates of a unit have
  product `|N(u)| = 1`.
* `NumberField.InfinitePlace.exists_torsion_mul_embedding_eq_abs`: a torsion sign makes a
  unit's real embedding equal its absolute value at a real place.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K]

/-- At a real place, multiply a unit by a torsion unit so that its real embedding is its
(positive) absolute value. -/
theorem exists_torsion_mul_embedding_eq_abs (w : InfinitePlace K) (hw : w.IsReal)
    (v : (𝓞 K)ˣ) :
    ∃ ε : torsion K,
      embedding_of_isReal hw ((ε.val * v : (𝓞 K)ˣ) : K) = w v := by
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

namespace Units

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute values of the conjugates of a unit `u` have product `|N(u)| = 1`. -/
@[simp]
theorem prod_norm_embedding_eq_one (u : (𝓞 K)ˣ) : ∏ σ : K →+* ℂ, ‖σ u‖ = 1 := by
  simp [NumberField.prod_norm_embedding_eq_abs_norm, ← Rat.cast_abs, NumberField.Units.norm]

end Units

namespace IsPrimitiveRoot

variable {K : Type*} [Field K]

/-- If `ζ` is a primitive `p ^ a`-th root of unity in a field of characteristic zero, `p` prime, and
the value of an integral unit is an integer power of `1 - ζ`, then that power is `1`. -/
theorem one_sub_zpow_eq_one_of_val_eq [CharZero K] {p a : ℕ} [hp : Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (p ^ a)) {w : (𝓞 K)ˣ} {n : ℤ}
    (hw : ((w : 𝓞 K) : K) = (1 - ζ) ^ n) : (1 - ζ) ^ n = 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- At level `1`, `ζ = 1`, so `1 - ζ = 0` and only its zeroth power is the value of a unit.
    rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hζ
    subst hζ
    rcases eq_or_ne n 0 with rfl | hn
    · exact zpow_zero _
    · simp [zero_zpow n hn] at hw
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt ha
  have hint : IsIntegral ℤ ζ := .of_pow (pow_pos hp.out.pos _) (hζ.pow_eq_one ▸ isIntegral_one)
  set z : 𝓞 K := ⟨ζ, hint⟩
  have hzζ : (z : K) = ζ := RingOfIntegers.coe_mk hint
  have hz : IsPrimitiveRoot z (p ^ (0 + k + 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 K) K) ?_
      RingOfIntegers.coe_injective
    rwa [← RingOfIntegers.coe_eq_algebraMap, hzζ]
  -- `1 - z` is not a unit of `𝓞 K`, since `p` is not.
  have hnu : ¬IsUnit (1 - z) := by
    rw [← IsUnit.neg_iff, neg_sub]
    exact hz.not_isUnit_sub_one
  -- So no positive power of `1 - ζ` is the value of an integral unit.
  have key (m : ℕ) (v : (𝓞 K)ˣ) (hv : ((v : 𝓞 K) : K) = (1 - ζ) ^ m) : m = 0 := by
    by_contra hm
    have hvz : (1 - z) ^ m = v := RingOfIntegers.coe_injective (by simp [hv, hzζ])
    exact hnu ((isUnit_pow_iff hm).1 (hvz ▸ v.isUnit))
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [key m w (by rw [hw, zpow_natCast]), Nat.cast_zero, zpow_zero]
  · rw [key m w⁻¹ ?_, Nat.cast_zero, neg_zero, zpow_zero]
    have hmul : (((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * ((w : 𝓞 K) : K) = 1 := by
      simp [RingOfIntegers.coe_eq_algebraMap]
    rw [eq_inv_of_mul_eq_one_left hmul, hw, zpow_neg, inv_inv, zpow_natCast]

end IsPrimitiveRoot

namespace TauCeti.NumberField.Units

section Coe

variable {K : Type*} [Field K]

/-- The image in `(𝓞 K)ˣ` of an integral unit of a subfield `F` has the same value in `K`. -/
theorem val_unitsMap_algebraMap_ringOfIntegers_subfield (F : Subfield K) (u : (𝓞 F)ˣ) :
    (((Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom u : (𝓞 K)ˣ) : 𝓞 K) : K) =
      (((u : 𝓞 F) : F) : K) := by
  simp [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
    IsScalarTower.algebraMap_apply (𝓞 F) F K, Subfield.algebraMap_ofSubfield]

/-- The image in `Kˣ` of an integral unit of a subfield `F` has the same value in `K`. -/
theorem val_map_algebraMap_ringOfIntegers_subfield (F : Subfield K) (u : (𝓞 F)ˣ) :
    ((Units.map (algebraMap (𝓞 F) K).toMonoidHom u : Kˣ) : K) = (((u : 𝓞 F) : F) : K) := by
  rw [← val_unitsMap_algebraMap_ringOfIntegers_subfield]
  simp [← IsScalarTower.algebraMap_apply]

end Coe

variable {K : Type*} [Field K] [NumberField K]

/-- The coercion from units of the ring of integers to the number field has finite fibers. -/
instance : Filter.TendstoCofinite (fun u : (𝓞 K)ˣ ↦ (u : K)) :=
  Filter.tendstoCofinite_of_injective (Units.coe_injective K)

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
