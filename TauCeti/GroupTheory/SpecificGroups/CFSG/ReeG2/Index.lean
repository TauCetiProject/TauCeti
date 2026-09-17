/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

/-!
# The index of the Ree family of type `G₂`

`TauCeti.LieTypeIndex` names the Ree family of type `G₂` by its constructor `reeG2 m`, whose
field order is `3 ^ (2m+1)`. This file selects that constructor and validates it, giving the
restricted index domain `TauCeti.ReeG2LieIndex` on which the family's carrier, Steinberg
endomorphism and candidate group are built, together with the numerical facts a consumer of that
domain needs: its diagram is `G₂`, its rank is two, and its characteristic is three.

The selector is a constructor test, not a mathematical property of a group. Nothing here asserts
that a named group is finite or simple.

## Main definitions

* `TauCeti.LieTypeIndex.IsReeG2`: the constructor selector, with
  `TauCeti.LieTypeIndex.isReeG2_iff_exists` naming the constructor and its parameter.
* `TauCeti.ReeG2LieIndex`: a validated index in the family.

## Main results

* `TauCeti.ReeG2LieIndex.exists_eq_of`: the eliminator matching the introduction form.
* `TauCeti.ReeG2LieIndex.dynkinType_eq`, `TauCeti.ReeG2LieIndex.rank_eq_two` and
  `TauCeti.ReeG2LieIndex.characteristic_eq_three`: the diagram, rank and characteristic.
## References

The family name, its parameter convention and the exclusion of `²G₂(3)` follow
Gorenstein--Lyons--Solomon, *The Classification of the Finite Simple Groups*, Number 1, §2.2, and
Conway et al., *Atlas of Finite Groups*. The diagram numbering is the Bourbaki one of
`TauCeti.DynkinType`.
-/

-- Adapted from the `SuzukiLieIndex` section of `TauCeti.GroupTheory.SpecificGroups.CFSG.Index`,
-- with the same declaration order.

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index names the Ree family of type `G₂`, `²G₂(3^(2m+1))`.

This is a constructor selector, not a mathematical property of a group. The exclusion of `²G₂(3)`
comes from the enclosing `TauCeti.ValidLieTypeIndex`; no finiteness or simplicity is asserted
here. -/
def IsReeG2 (d : LieTypeIndex) : Prop := ∃ m, d = .reeG2 m

/-- **The selector names the Ree type-`G₂` constructor**: an index satisfies it exactly when it is
`reeG2 m` for a parameter `m`, which is the form a consumer holding an abstract index needs. -/
@[simp] theorem isReeG2_iff_exists (d : LieTypeIndex) : d.IsReeG2 ↔ ∃ m, d = .reeG2 m := by
  exact Iff.rfl

instance : DecidablePred IsReeG2 := fun d => by
  rw [isReeG2_iff_exists]
  cases d <;>
    simp only [reduceCtorEq, exists_const, reeG2.injEq, exists_eq'] <;>
    infer_instance

/-- The Ree family of type `G₂` uses a half-Frobenius, so it carries no diagram automorphism. -/
theorem usesHalfFrobenius_of_isReeG2 {d : LieTypeIndex} (h : d.IsReeG2) :
    d.UsesHalfFrobenius := by
  obtain ⟨m, rfl⟩ := (isReeG2_iff_exists d).mp h
  simp [usesHalfFrobenius_iff]

end LieTypeIndex

/-- A validated index in the Ree family of type `G₂`, `²G₂(3^(2m+1))`.

The outer subtype is important: `²G₂(3)`, the parameter `m = 0`, is excluded from the
classification list; its derived subgroup has index three and is isomorphic to a group already
named in another family, so the derived-subgroup recipe does not produce a new simple group there,
and `²G₂(3)` is not a `ReeG2LieIndex`. The Suzuki--Ree relatives `²B₂`, `²F₄` and the Tits group
are excluded too; they are the other three constructors of `TauCeti.SuzukiReeIndex`. -/
abbrev ReeG2LieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsReeG2}

namespace ReeG2LieIndex

/-- Introduce a valid Ree index of type `G₂`, `²G₂(3^(2m+1))`. Validity forces `1 ≤ m`. -/
abbrev of (m : ℕ) (hvalid : (LieTypeIndex.reeG2 m).Valid) : ReeG2LieIndex :=
  ⟨⟨.reeG2 m, hvalid⟩, (LieTypeIndex.isReeG2_iff_exists _).mpr ⟨m, rfl⟩⟩

/-- Every Ree index of type `G₂` is of the introduction form. This is the eliminator matching `of`,
so a consumer never repeats the case split over the other constructors. -/
theorem exists_eq_of (d : ReeG2LieIndex) :
    ∃ (m : ℕ) (hvalid : (LieTypeIndex.reeG2 m).Valid), d = of m hvalid := by
  obtain ⟨⟨d, hvalid⟩, hs⟩ := d
  revert hvalid hs
  cases d
  case reeG2 m => exact fun hvalid _ => ⟨m, hvalid, rfl⟩
  all_goals exact fun _ hs => by simp at hs

/-- The Ree family of type `G₂` is built on the rank-two diagram `G₂`. -/
@[simp] theorem dynkinType_eq (d : ReeG2LieIndex) : d.1.dynkinType = .G2 := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.dynkinType_reeG2 m

/-- The Ree family of type `G₂` has rank two, that being the rank of `G₂`. -/
@[simp] theorem rank_eq_two (d : ReeG2LieIndex) : d.1.rank = 2 :=
  congrArg DynkinType.rank d.dynkinType_eq

/-- The Ree family of type `G₂` lives in characteristic three. -/
@[simp] theorem characteristic_eq_three (d : ReeG2LieIndex) : d.1.characteristic = 3 := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.characteristic_reeG2 m

/-- A Ree index of type `G₂` is a Suzuki--Ree index: its Steinberg map is an odd power of a
half-Frobenius. -/
abbrev toSuzukiReeIndex (d : ReeG2LieIndex) : SuzukiReeIndex :=
  ⟨d.1, LieTypeIndex.usesHalfFrobenius_of_isReeG2 d.2⟩

end ReeG2LieIndex

end TauCeti
