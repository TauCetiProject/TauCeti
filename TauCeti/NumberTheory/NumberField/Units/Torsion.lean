/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Torsion units of a number field

A number field with a real infinite place has no roots of unity other than `±1`: a primitive root
of unity of order greater than `2` has no real embedding
(`IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt`). So the torsion subgroup of the
units is `{1, -1}` and the torsion order is `2`. This generalises Mathlib's
`NumberField.Units.torsionOrder_eq_two_of_odd_finrank`, which obtains the real place from odd
degree, to every field with a real place, in particular to the real quadratic fields.

For an arbitrary number field `K`, the torsion order `w` is bounded by the degree: `K` contains a
primitive `w`-th root of unity, which generates a subfield of degree `φ(w)`, so `φ(w) ≤ [K : ℚ]`.
When the unit rank is `0` (for `ℚ` and the imaginary quadratic fields) every unit is torsion.

## Main results

* `TauCeti.NumberField.Units.torsion_eq_one_or_neg_one_of_isReal`: with a real place, every
  torsion unit is `1` or `-1`.
* `TauCeti.NumberField.Units.torsionOrder_eq_two_of_isReal`: with a real place, the torsion
  order is `2`.
* `TauCeti.NumberField.Units.torsion_eq_one_or_neg_one_of_torsionOrder_eq_two`: with torsion
  order `2`, every torsion unit is `1` or `-1`.
* `TauCeti.NumberField.Units.exists_isPrimitiveRoot_torsionOrder`: `K` contains a primitive root
  of unity of order `torsionOrder K`.
* `TauCeti.NumberField.Units.totient_torsionOrder_le_finrank`: `φ(torsionOrder K) ≤ [K : ℚ]`.
* `TauCeti.NumberField.Units.torsion_eq_top_of_rank_eq_zero`: in unit rank `0`, every unit is
  torsion.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- In a number field with a real infinite place, every torsion unit is `1` or `-1`. -/
theorem torsion_eq_one_or_neg_one_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (x : torsion K) : (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  classical
  -- A root of unity of order greater than `2` would leave no real place.
  have hpos : nrRealPlaces K ≠ 0 := by
    have : Nonempty {w : InfinitePlace K // w.IsReal} := ⟨⟨w, hw⟩⟩
    exact Fintype.card_ne_zero
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · -- The order of `x` in `K` is its order as a unit.
    rw [← orderOf_units,
      ← orderOf_injective (algebraMap (𝓞 K) K).toMonoidHom RingOfIntegers.coe_injective] at hc
    exact absurd (IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf _))
      hpos
  · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
    · exact absurd hi (orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)).ne'
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]

/-- In a number field with a real infinite place, the torsion order is `2`. -/
theorem torsionOrder_eq_two_of_isReal {w : InfinitePlace K} (hw : w.IsReal) :
    torsionOrder K = 2 := by
  classical
  let := Fintype.ofFinite (torsion K)
  rw [torsionOrder, Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact torsion_eq_one_or_neg_one_of_isReal hw x

omit [NumberField K] in
/-- In a number field with torsion order `2`, every torsion unit is `1` or `-1`. -/
theorem torsion_eq_one_or_neg_one_of_torsionOrder_eq_two (h : torsionOrder K = 2)
    (x : torsion K) : (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  have hx : ((x : (𝓞 K)ˣ) : 𝓞 K) * ((x : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [← Units.val_mul, ← sq, ← h, pow_torsionOrder_eq_one K x.2, Units.val_one]
  rcases mul_self_eq_one_iff.mp hx with hx | hx
  · exact .inl (Units.ext hx)
  · exact .inr (Units.ext hx)

/-- A number field contains a primitive root of unity of order `torsionOrder K`, namely a
generator of the cyclic group `torsion K`.

Adapted from the first step of Mathlib's proof of `IsCyclotomicExtension.Rat.torsionOrder_eq`. -/
theorem exists_isPrimitiveRoot_torsionOrder : ∃ ζ : K, IsPrimitiveRoot ζ (torsionOrder K) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K :=
    IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_coe_iff] at hμ
  exact ⟨_, hμ⟩

/-- **The degree bounds the roots of unity.** A number field `K` contains the cyclotomic field
of order `torsionOrder K`, whose degree over `ℚ` is `φ(torsionOrder K)`; hence
`φ(torsionOrder K) ≤ [K : ℚ]`. -/
theorem totient_torsionOrder_le_finrank : (torsionOrder K).totient ≤ finrank ℚ K := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_torsionOrder (K := K)
  simpa using hζ.lcm_totient_le_finrank hζ
    (Polynomial.cyclotomic.irreducible_rat (by simpa using torsionOrder_pos K))

/-- **In unit rank zero every unit is a root of unity.** If the unit rank of `K` is `0`, as for
`ℚ` and the imaginary quadratic fields, then every unit of `𝓞 K` is torsion. -/
theorem torsion_eq_top_of_rank_eq_zero (h : rank K = 0) : torsion K = ⊤ := by
  have : IsEmpty (Fin (rank K)) := by rw [h]; infer_instance
  have := (equivFinRank K).symm.isEmpty
  exact (Subgroup.eq_top_iff' _).mpr fun u =>
    dirichletUnitTheorem.logEmbedding_eq_zero_iff.mp (funext isEmptyElim)

end TauCeti.NumberField.Units
