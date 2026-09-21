/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SuzukiRee

/-!
# The index of the Tits group

`TauCeti.LieTypeIndex.tits` is the separate classification-list entry for the Tits group
`²F₄(2)'`. It uses the same type-`F₄` diagram and characteristic-two exceptional isogeny as
the Ree family `²F₄(2^(2m+1))`, but its Steinberg endomorphism is the exceptional isogeny itself:
the field order is two and the field exponent is one.

This file gives that constructor its own validated index type. The distinction from the `reeF4`
constructor is mathematical rather than cosmetic: `²F₄(2)` is not simple, while its derived
subgroup is the Tits group named by this index. A construction receiving a
`TauCeti.TitsLieIndex` therefore cannot accidentally receive a positive-parameter Ree-family
index, even though the two branches use the same ambient carrier and special isogeny.

The exceptional isogeny raises the parameters of the two long simple root subgroups to the first
power and those of the two short simple root subgroups to the second. The theorem
`TauCeti.TitsLieIndex.exponent_eq` derives this numbered formula from the root-length predicate on
`TauCeti.DynkinType.F4`, rather than recording a second root-length table.

Nothing here constructs a group or asserts finiteness or simplicity.

## Main definitions

* `TauCeti.LieTypeIndex.IsTits`: the constructor selector.
* `TauCeti.TitsLieIndex`: the validated index consisting only of the Tits constructor.

## Main results

* `TauCeti.TitsLieIndex.eq_of`: every Tits index is its canonical introduction form.
* `TauCeti.TitsLieIndex.dynkinType_eq`, `rank_eq_four`, `characteristic_eq_two`,
  `fieldOrder_eq_two`, and `fieldExponent_eq_one`: the diagram and field data.
* `TauCeti.TitsLieIndex.exponent_eq`: the exceptional-isogeny exponents at the four numbered
  simple roots.

## References

The separate Tits entry and the `²F₄` parameter convention follow D. Gorenstein, R. Lyons and
R. Solomon, *The Classification of the Finite Simple Groups*, Number 1, §2.2, and J. H. Conway
et al., *Atlas of Finite Groups*. The diagram numbering is Bourbaki's.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Index`, with the same selector,
-- validated-subtype, and numbered-data interface.

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index is the separate Tits constructor.

This is a constructor selector, not a mathematical property of a group. In particular, it is
false on every member of the Ree family of type `F₄`, including at the level of raw parameters. -/
def IsTits (d : LieTypeIndex) : Prop := d = .tits

/-- The Tits selector holds exactly at the Tits constructor. -/
@[simp] theorem isTits_iff (d : LieTypeIndex) : d.IsTits ↔ d = .tits := Iff.rfl

instance : DecidablePred IsTits := fun d => by
  rw [isTits_iff]
  infer_instance

/-- The Tits index uses a half-Frobenius, so it carries no diagram automorphism. -/
theorem usesHalfFrobenius_of_isTits {d : LieTypeIndex} (h : d.IsTits) :
    d.UsesHalfFrobenius := by
  rw [(isTits_iff d).mp h]
  simp [usesHalfFrobenius_iff]

end LieTypeIndex

/-- The validated index of the Tits group `²F₄(2)'`.

This is a subtype of `TauCeti.ValidLieTypeIndex`, as required of every index passed to a
carrier-valued construction. Its constructor selector excludes the uniform Ree family of type
`F₄`, whose members use the same diagram and exceptional isogeny. -/
abbrev TitsLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTits}

namespace TitsLieIndex

/-- Introduce the Tits index. -/
abbrev of : TitsLieIndex := ⟨⟨.tits, by simp⟩, (LieTypeIndex.isTits_iff _).mpr rfl⟩

/-- Every Tits index is the canonical introduction form. -/
theorem eq_of (d : TitsLieIndex) : d = of := by
  obtain ⟨⟨d, hvalid⟩, hd⟩ := d
  revert hvalid hd
  cases d
  case tits => exact fun _ _ => rfl
  all_goals exact fun _ hd => by simp at hd

/-- The Tits construction uses the rank-four diagram `F₄`. -/
@[simp] theorem dynkinType_eq (d : TitsLieIndex) : d.1.dynkinType = .F4 := by
  rw [d.eq_of]
  exact LieTypeIndex.dynkinType_tits

/-- The Tits construction has rank four, that being the rank of `F₄`. -/
@[simp] theorem rank_eq_four (d : TitsLieIndex) : d.1.rank = 4 :=
  congrArg DynkinType.rank d.dynkinType_eq

/-- The Tits construction lives in characteristic two. -/
@[simp] theorem characteristic_eq_two (d : TitsLieIndex) : d.1.characteristic = 2 := by
  rw [d.eq_of]
  exact LieTypeIndex.characteristic_tits

/-- The field order attached to the Tits index is two. -/
@[simp] theorem fieldOrder_eq_two (d : TitsLieIndex) : d.1.fieldOrder = 2 := by
  rw [d.eq_of]
  exact LieTypeIndex.fieldOrder_tits

/-- The field exponent attached to the Tits index is one, so its Steinberg map is the
half-Frobenius itself. -/
@[simp] theorem fieldExponent_eq_one (d : TitsLieIndex) : d.1.fieldExponent = 1 := by
  rw [d.eq_of]
  exact LieTypeIndex.fieldExponent_tits

/-- A Tits index is a Suzuki--Ree index: its Steinberg map is an odd power of a
half-Frobenius. -/
abbrev toSuzukiReeIndex (d : TitsLieIndex) : SuzukiReeIndex :=
  ⟨d.1, LieTypeIndex.usesHalfFrobenius_of_isTits d.2⟩

/-- **The exponents of the exceptional isogeny on the four numbered simple root subgroups**: the
first power at the two long simple roots, Bourbaki nodes `1` and `2`, and the second power at the
two short ones. This is the `F₄` specialization of
`TauCeti.SuzukiReeIndex.exponent_of_isLongSimpleRoot`. -/
@[simp] theorem exponent_eq (d : TitsLieIndex) (i : Fin d.1.rank) :
    d.toSuzukiReeIndex.exponent i = if (i : ℕ) < 2 then 1 else 2 := by
  obtain rfl := d.eq_of
  have hlong : of.1.dynkinType.IsLongSimpleRoot i ↔ (i : ℕ) < 2 :=
    Iff.of_eq (congrFun DynkinType.isLongSimpleRoot_F4 i)
  by_cases h : (i : ℕ) < 2
  · have hi : of.toSuzukiReeIndex.exponent i = 1 :=
      SuzukiReeIndex.exponent_of_isLongSimpleRoot of.toSuzukiReeIndex i (hlong.mpr h)
    simp [hi, h]
  · have hi : of.toSuzukiReeIndex.exponent i = 2 :=
      (SuzukiReeIndex.exponent_of_not_isLongSimpleRoot of.toSuzukiReeIndex i
        (hlong.not.mpr h)).trans (characteristic_eq_two of)
    simp [hi, h]

end TitsLieIndex

end TauCeti
