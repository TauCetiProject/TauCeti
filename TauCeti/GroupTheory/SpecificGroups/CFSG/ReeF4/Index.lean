/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SuzukiRee

/-!
# The index of the Ree family of type `F₄`

`TauCeti.LieTypeIndex` names the Ree family of type `F₄` by its constructor `reeF4 m`, whose
field order is `2 ^ (2m+1)`. This file selects that constructor and validates it, giving the
restricted index domain `TauCeti.ReeF4LieIndex` on which the family's carrier, Steinberg
endomorphism and candidate group are built, together with the numerical facts a consumer of that
domain needs: its diagram is `F₄`, its rank is four, its characteristic is two, and its field
order is at least eight.

The last of those is the index-level shape of the exclusion of `m = 0`. That parameter would name
`²F₄(2)`, which is not on the classification list: it is not simple, its derived subgroup being
the Tits group `²F₄(2)'`, which the list carries under the separate constructor `tits`. So a
`ReeF4LieIndex` always has `1 ≤ m`, hence field order `2 ^ (2m+1) ≥ 8`.

The rank-four diagram `F₄` has two long and two short simple roots, Bourbaki nodes `1` and `2`
being the long ones. The exceptional isogeny of characteristic two exchanges the two lengths, and
`TauCeti.ReeF4LieIndex.exponent_eq` records the resulting exponents at the four numbered nodes as
a worked consequence of the root-length predicate of `TauCeti.DynkinType`, not as a second table.

The selector is a constructor test, not a mathematical property of a group. Nothing here asserts
that a named group is finite or simple.

## Main definitions

* `TauCeti.LieTypeIndex.IsReeF4`: the constructor selector, with
  `TauCeti.LieTypeIndex.isReeF4_iff_exists` naming the constructor and its parameter.
* `TauCeti.ReeF4LieIndex`: a validated index in the family.

## Main results

* `TauCeti.ReeF4LieIndex.exists_eq_of`: the eliminator matching the introduction form.
* `TauCeti.ReeF4LieIndex.dynkinType_eq`, `TauCeti.ReeF4LieIndex.rank_eq_four` and
  `TauCeti.ReeF4LieIndex.characteristic_eq_two`: the diagram, rank and characteristic.
* `TauCeti.ReeF4LieIndex.eight_le_fieldOrder`: the field order is at least eight.
* `TauCeti.ReeF4LieIndex.fieldOrder_eq_two_pow`: the field order is two to the recorded exponent.
* `TauCeti.ReeF4LieIndex.exponent_eq`: the exceptional isogeny raises the parameter of the two
  long simple root subgroups to the first power and that of the two short ones to the second.

## References

The family name, its parameter convention and the separation of `²F₄(2)'` from the uniform family
follow Gorenstein--Lyons--Solomon, *The Classification of the Finite Simple Groups*, Number 1,
§2.2, and Conway et al., *Atlas of Finite Groups*. The diagram numbering is the Bourbaki one of
`TauCeti.DynkinType`.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Index`, with the same declaration
-- order.

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index names the Ree family of type `F₄`, `²F₄(2^(2m+1))`.

This is a constructor selector, not a mathematical property of a group. It is false on the Tits
constructor, which shares the `F₄` diagram and the characteristic-two exceptional isogeny but is
listed under its own name; the exclusion of `²F₄(2)` comes from the enclosing
`TauCeti.ValidLieTypeIndex`. No finiteness or simplicity is asserted here. -/
def IsReeF4 (d : LieTypeIndex) : Prop := ∃ m, d = .reeF4 m

/-- **The selector names the Ree type-`F₄` constructor**: an index satisfies it exactly when it is
`reeF4 m` for a parameter `m`, which is the form a consumer holding an abstract index needs. -/
@[simp] theorem isReeF4_iff_exists (d : LieTypeIndex) : d.IsReeF4 ↔ ∃ m, d = .reeF4 m :=
  Iff.rfl

instance : DecidablePred IsReeF4 := fun d => by
  rw [isReeF4_iff_exists]
  cases d <;>
    simp only [reduceCtorEq, exists_const, reeF4.injEq, exists_eq'] <;>
    infer_instance

/-- The Ree family of type `F₄` uses a half-Frobenius, so it carries no diagram automorphism. -/
theorem usesHalfFrobenius_of_isReeF4 {d : LieTypeIndex} (h : d.IsReeF4) :
    d.UsesHalfFrobenius := by
  obtain ⟨m, rfl⟩ := (isReeF4_iff_exists d).mp h
  simp [usesHalfFrobenius_iff]

/-- `²F₄(2)` is not on the classification list: it is not simple, and its derived subgroup is the
Tits group, which the list carries under the separate constructor `tits`. -/
example : ¬(reeF4 0).Valid := by simp

/-- `²F₄(8)`, the smallest member of the family, is on the classification list. -/
example : (reeF4 1).Valid := by simp

end LieTypeIndex

/-- A validated index in the Ree family of type `F₄`, `²F₄(2^(2m+1))`.

The outer subtype is important: `²F₄(2)`, the parameter `m = 0`, is excluded from the
classification list, since it is not simple and its derived subgroup is the Tits group, so
`²F₄(2)` is not a `ReeF4LieIndex`. The Tits group itself, the Suzuki family `²B₂` and the Ree
family `²G₂` are excluded too; they are the other three constructors of
`TauCeti.SuzukiReeIndex`. -/
abbrev ReeF4LieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsReeF4}

namespace ReeF4LieIndex

/-- Introduce a valid Ree index of type `F₄`, `²F₄(2^(2m+1))`. Validity forces `1 ≤ m`. -/
abbrev of (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid) : ReeF4LieIndex :=
  ⟨⟨.reeF4 m, hvalid⟩, (LieTypeIndex.isReeF4_iff_exists _).mpr ⟨m, rfl⟩⟩

/-- Every Ree index of type `F₄` is of the introduction form. This is the eliminator matching `of`,
so a consumer never repeats the case split over the other constructors. -/
theorem exists_eq_of (d : ReeF4LieIndex) :
    ∃ (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid), d = of m hvalid := by
  obtain ⟨⟨d, hvalid⟩, hs⟩ := d
  revert hvalid hs
  cases d
  case reeF4 m => exact fun hvalid _ => ⟨m, hvalid, rfl⟩
  all_goals exact fun _ hs => by simp at hs

/-- The Ree family of type `F₄` is built on the rank-four diagram `F₄`. -/
@[simp] theorem dynkinType_eq (d : ReeF4LieIndex) : d.1.dynkinType = .F4 := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.dynkinType_reeF4 m

/-- The Ree family of type `F₄` has rank four, that being the rank of `F₄`. -/
@[simp] theorem rank_eq_four (d : ReeF4LieIndex) : d.1.rank = 4 :=
  congrArg DynkinType.rank d.dynkinType_eq

/-- The Ree family of type `F₄` lives in characteristic two. -/
@[simp] theorem characteristic_eq_two (d : ReeF4LieIndex) : d.1.characteristic = 2 := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.characteristic_reeF4 m

/-- **The field order of a valid Ree index of type `F₄` is at least eight.** The one smaller value
the constructor could take is `²F₄(2)`, which is excluded from the classification list. -/
theorem eight_le_fieldOrder (d : ReeF4LieIndex) : 8 ≤ d.1.fieldOrder := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  have hm : 1 ≤ m := by simpa using hvalid
  calc (8 : ℕ) = 2 ^ (2 * 1 + 1) := by norm_num
    _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (of m hvalid).1.fieldOrder := (LieTypeIndex.fieldOrder_reeF4 m).symm

-- This specialization is what a construction on a carrier defined over `𝔽₂` needs: there the
-- characteristic is the numeral `2` rather than a projection of the index, and the index's own
-- algebraic closure depends on that projection, so the two cannot be exchanged by rewriting
-- inside such a statement.
/-- **The field order of a Ree index of type `F₄` is the recorded power of two.** This is the
characteristic-two reading of `TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow`. -/
theorem fieldOrder_eq_two_pow (d : ReeF4LieIndex) : d.1.fieldOrder = 2 ^ d.1.fieldExponent := by
  rw [d.1.fieldOrder_eq_characteristic_pow, d.characteristic_eq_two]

/-- A Ree index of type `F₄` is a Suzuki--Ree index: its Steinberg map is an odd power of a
half-Frobenius. -/
abbrev toSuzukiReeIndex (d : ReeF4LieIndex) : SuzukiReeIndex :=
  ⟨d.1, LieTypeIndex.usesHalfFrobenius_of_isReeF4 d.2⟩

/-- **The exponents of the exceptional isogeny on the four numbered simple root subgroups**: the
first power at the two long simple roots, Bourbaki nodes `1` and `2`, and the second power at the
two short ones. This is the `F₄` reading of the general convention
`TauCeti.SuzukiReeIndex.exponent_of_isLongSimpleRoot`, whose long-root predicate is the
Bourbaki-numbered one of `TauCeti.DynkinType`. -/
@[simp] theorem exponent_eq (d : ReeF4LieIndex) (i : Fin d.1.rank) :
    d.toSuzukiReeIndex.exponent i = if (i : ℕ) < 2 then 1 else 2 := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  -- The index type `Fin d.1.rank` depends on the diagram, so `dynkinType_eq` cannot be rewritten
  -- with directly under the binder; the `F₄` root-length predicate is read off by `congrFun`.
  have hlong : (of m hvalid).1.dynkinType.IsLongSimpleRoot i ↔ (i : ℕ) < 2 :=
    Iff.of_eq (congrFun DynkinType.isLongSimpleRoot_F4 i)
  by_cases h : (i : ℕ) < 2
  · have hi : (of m hvalid).toSuzukiReeIndex.exponent i = 1 :=
      SuzukiReeIndex.exponent_of_isLongSimpleRoot (of m hvalid).toSuzukiReeIndex i (hlong.mpr h)
    simp [hi, h]
  · have hi : (of m hvalid).toSuzukiReeIndex.exponent i = 2 :=
      (SuzukiReeIndex.exponent_of_not_isLongSimpleRoot (of m hvalid).toSuzukiReeIndex i
        (hlong.not.mpr h)).trans (characteristic_eq_two (of m hvalid))
    simp [hi, h]

end ReeF4LieIndex

end TauCeti
