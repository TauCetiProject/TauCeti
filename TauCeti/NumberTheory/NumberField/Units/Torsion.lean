/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Torsion units of a number field

The torsion subgroup of the units of a number field `K` is cyclic, so `K` contains a primitive
root of unity of order `torsionOrder K`. That root generates a cyclotomic subfield of degree
`φ(torsionOrder K)`, which bounds the totient of the torsion order by the degree of `K`. When the
unit rank is zero, Dirichlet's unit theorem leaves only the torsion: every unit is a root of
unity. These are the inputs to the count of roots of unity in a quadratic field.

A number field with a real infinite place has no roots of unity other than `±1`: a primitive root
of unity of order greater than `2` has no real embedding
(`IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt`). So the torsion subgroup of the
units is `{1, -1}` and the torsion order is `2`. This generalises Mathlib's
`NumberField.Units.torsionOrder_eq_two_of_odd_finrank`, which obtains the real place from odd
degree, to every field with a real place, in particular to the real quadratic fields.

## Main results

* `TauCeti.NumberField.Units.exists_isPrimitiveRoot_torsionOrder`: `K` contains a primitive
  root of unity of order `torsionOrder K`.
* `TauCeti.NumberField.Units.totient_torsionOrder_le_finrank`: `φ(torsionOrder K) ≤ [K : ℚ]`.
* `TauCeti.NumberField.Units.torsion_eq_top_of_rank_eq_zero`: with unit rank zero, every unit
  is torsion.
* `TauCeti.NumberField.Units.torsion_eq_one_or_neg_one_of_isReal`: with a real place, every
  torsion unit is `1` or `-1`.
* `TauCeti.NumberField.Units.torsionOrder_eq_two_of_isReal`: with a real place, the torsion
  order is `2`.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- A number field contains a primitive root of unity whose order is the torsion order: a
generator of the cyclic torsion subgroup of the units. -/
theorem exists_isPrimitiveRoot_torsionOrder : ∃ ζ : K, IsPrimitiveRoot ζ (torsionOrder K) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K :=
    IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  exact ⟨_, hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)⟩

/-- The totient of the torsion order is at most the degree: a primitive root of unity of order
`torsionOrder K` generates a subfield of degree `φ(torsionOrder K)`. -/
theorem totient_torsionOrder_le_finrank : (torsionOrder K).totient ≤ Module.finrank ℚ K := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_torsionOrder (K := K)
  simpa using hζ.lcm_totient_le_finrank hζ
    (Polynomial.cyclotomic.irreducible_rat (by simp [torsionOrder_pos]))

/-- **With unit rank zero, every unit is a root of unity.** Dirichlet's unit theorem writes a
unit as a torsion unit times a product over an empty fundamental system. -/
theorem torsion_eq_top_of_rank_eq_zero (h : rank K = 0) : torsion K = ⊤ := by
  have : IsEmpty (Fin (rank K)) := by
    rw [h]
    infer_instance
  simpa [Set.range_eq_empty] using closure_fundSystem_sup_torsion_eq_top K

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

end TauCeti.NumberField.Units
