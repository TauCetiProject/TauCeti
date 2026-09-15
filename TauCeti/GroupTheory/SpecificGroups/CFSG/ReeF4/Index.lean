/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure

/-!
# The index of the Ree family of type `F₄` and of the Tits group

`TauCeti.LieTypeIndex` names the Ree family of type `F₄` by its constructor `reeF4 m`, whose field
order is `2 ^ (2m+1)`, and the Tits group by a separate constructor `tits`. Both are built from the
same special isogeny of the same type-`F₄` carrier in characteristic two, differing only in the
power of that isogeny they take: `2m+1` with `1 ≤ m` in the first case, and the first power in the
second. This file selects both constructors at once and validates them, giving the restricted index
domain `TauCeti.ReeF4LieIndex` on which the carrier, Steinberg endomorphism and candidate group are
built, together with the numerical facts a consumer of that domain needs: the diagram is `F₄`, the
rank is four, and the characteristic is two.

Covering both constructors in one domain is what lets a single `steinberg` definition, the
`fieldExponent`-th power of the half-Frobenius, serve the Tits group as well: the Tits index records
field exponent one, so that power is the half-Frobenius itself.

The selector is a constructor test, not a mathematical property of a group. Nothing here asserts
that a named group is finite or simple.

## Main definitions

* `TauCeti.LieTypeIndex.IsReeF4`: the constructor selector, true on `reeF4 m` and on `tits`.
* `TauCeti.ReeF4LieIndex`: a validated index in the family.

## Main results

* `TauCeti.ReeF4LieIndex.exists_eq_of`: the eliminator matching the two introduction forms.
* `TauCeti.ReeF4LieIndex.dynkinType_eq`, `TauCeti.ReeF4LieIndex.rank_eq_four` and
  `TauCeti.ReeF4LieIndex.characteristic_eq_two`: the diagram, rank and characteristic.
* `TauCeti.ReeF4LieIndex.charP_closure_two`: the algebraic closure attached to such an index has
  characteristic two.

## References

The family names, the parameter convention and the separate name for the Tits group follow
Gorenstein--Lyons--Solomon, *The Classification of the Finite Simple Groups*, Number 1, §2.2, and
Conway et al., *Atlas of Finite Groups*. The diagram numbering is the Bourbaki one of
`TauCeti.DynkinType`.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Index`, the index of the Ree family
-- of type G₂, with the two constructors of this family covered by one selector.

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index names a member of the type-`F₄` half-Frobenius family: the Ree family
`²F₄(2^(2m+1))` or the Tits index.

This is a constructor selector, not a mathematical property of a group. The exclusion of `²F₄(2)`
from the Ree constructor comes from the enclosing `TauCeti.ValidLieTypeIndex`; the group the
classification list carries at that parameter is the derived subgroup, which has its own
constructor `tits` and is selected here too. No finiteness or simplicity is asserted. -/
def IsReeF4 : LieTypeIndex → Prop
  | .reeF4 _ => True
  | .tits => True
  | _ => False

/-- Characterization of the two type-`F₄` half-Frobenius constructors. -/
@[simp] theorem isReeF4_iff (d : LieTypeIndex) : d.IsReeF4 ↔
    match d with
    | .reeF4 _ => True
    | .tits => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsReeF4 := fun d => by
  cases d <;> rw [isReeF4_iff] <;> infer_instance

/-- The type-`F₄` half-Frobenius family uses a half-Frobenius, so it carries no diagram
automorphism. -/
theorem usesHalfFrobenius_of_isReeF4 {d : LieTypeIndex} (h : d.IsReeF4) :
    d.UsesHalfFrobenius := by
  cases d <;> simp_all [usesHalfFrobenius_iff]

end LieTypeIndex

/-- A validated index in the type-`F₄` half-Frobenius family: the Ree family `²F₄(2^(2m+1))` or the
Tits index.

The two constructors share a domain because they share a construction. The outer subtype is still
important: the Ree constructor's parameter `m = 0` is excluded from the classification list, since
the group `²F₄(2)` it would name is not simple, and the simple group the list carries there is its
derived subgroup, named by the separate constructor `tits`. The derived-subgroup recipe below
produces that group from the Tits index, so nothing is lost by the exclusion. The Suzuki--Ree
relatives `²B₂` and `²G₂` are excluded; they are the other two constructors of
`TauCeti.SuzukiReeIndex`. -/
abbrev ReeF4LieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsReeF4}

namespace ReeF4LieIndex

/-- Introduce a valid Ree index of type `F₄`, `²F₄(2^(2m+1))`. Validity forces `1 ≤ m`. -/
abbrev ofReeF4 (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid) : ReeF4LieIndex :=
  ⟨⟨.reeF4 m, hvalid⟩, (LieTypeIndex.isReeF4_iff _).mpr trivial⟩

/-- The Tits index, the `m = 0` member of the type-`F₄` half-Frobenius family. -/
abbrev tits : ReeF4LieIndex :=
  ⟨⟨.tits, by simp⟩, (LieTypeIndex.isReeF4_iff _).mpr trivial⟩

/-- Every index in the type-`F₄` half-Frobenius family is of one of the two introduction forms.
This is the eliminator matching `ofReeF4` and `tits`, so a consumer never repeats the case split
over the other constructors. -/
theorem exists_eq_of (d : ReeF4LieIndex) :
    (∃ (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid), d = ofReeF4 m hvalid) ∨ d = tits := by
  obtain ⟨⟨d, hvalid⟩, hs⟩ := d
  revert hvalid hs
  cases d
  case reeF4 m => exact fun hvalid _ => Or.inl ⟨m, hvalid, rfl⟩
  case tits => exact fun _ _ => Or.inr rfl
  all_goals exact fun _ hs => ((LieTypeIndex.isReeF4_iff _).mp hs).elim

/-- The type-`F₄` half-Frobenius family is built on the rank-four diagram `F₄`. -/
@[simp] theorem dynkinType_eq (d : ReeF4LieIndex) : d.1.dynkinType = .F4 := by
  obtain (⟨m, hvalid, rfl⟩ | rfl) := d.exists_eq_of
  · exact LieTypeIndex.dynkinType_reeF4 m
  · exact LieTypeIndex.dynkinType_tits

/-- The type-`F₄` half-Frobenius family has rank four, that being the rank of `F₄`. -/
@[simp] theorem rank_eq_four (d : ReeF4LieIndex) : d.1.rank = 4 :=
  congrArg DynkinType.rank d.dynkinType_eq

/-- The type-`F₄` half-Frobenius family lives in characteristic two. -/
@[simp] theorem characteristic_eq_two (d : ReeF4LieIndex) : d.1.characteristic = 2 := by
  obtain (⟨m, hvalid, rfl⟩ | rfl) := d.exists_eq_of
  · exact LieTypeIndex.characteristic_reeF4 m
  · exact LieTypeIndex.characteristic_tits

/-- An index in the type-`F₄` half-Frobenius family is a Suzuki--Ree index: its Steinberg map is an
odd power of a half-Frobenius. -/
abbrev toSuzukiReeIndex (d : ReeF4LieIndex) : SuzukiReeIndex :=
  ⟨d.1, LieTypeIndex.usesHalfFrobenius_of_isReeF4 d.2⟩

/-- The algebraic closure attached to an index in the type-`F₄` half-Frobenius family has
characteristic two. -/
instance charP_closure_two (d : ReeF4LieIndex) : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

end ReeF4LieIndex

end TauCeti
