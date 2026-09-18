/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Torsion units of a number field with a real place

A number field with a real infinite place has no roots of unity other than `±1`: a primitive root
of unity of order greater than `2` has no real embedding
(`NumberField.InfinitePlace.nrRealPlaces_eq_zero_of_two_lt`). So the torsion subgroup of the
units is `{1, -1}` and the torsion order is `2`. This generalises Mathlib's
`NumberField.Units.torsionOrder_eq_two_of_odd_finrank`, which obtains the real place from odd
degree, to every field with a real place, in particular to the real quadratic fields.

## Main results

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

/-- In a number field with a real infinite place, every torsion unit is `1` or `-1`. -/
theorem torsion_eq_one_or_neg_one_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (x : torsion K) : (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  classical
  -- A root of unity of order greater than `2` would leave no real place.
  have hpos : nrRealPlaces K ≠ 0 := by
    have : Nonempty {w : InfinitePlace K // w.IsReal} := ⟨⟨w, hw⟩⟩
    exact Fintype.card_ne_zero
  -- The order of `x` in `K` is its order as a unit.
  have hord : orderOf ((x : (𝓞 K)ˣ) : K) = orderOf (x : (𝓞 K)ˣ) :=
    orderOf_injective ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K)))
      (Units.coe_injective K) _
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · rw [← hord] at hc
    exact absurd (IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf _))
      hpos
  · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
    · exact absurd hi (orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)).ne'
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · -- A unit of order `2` squares to `1` in the domain `𝓞 K`, so it is `-1`.
      have h2 : ((x : (𝓞 K)ˣ) : 𝓞 K) * ((x : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
        rw [← Units.val_mul, ← sq, ← hi, pow_orderOf_eq_one, Units.val_one]
      rcases mul_self_eq_one_iff.mp h2 with h | h
      · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))

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
