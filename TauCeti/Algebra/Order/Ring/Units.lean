/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.GroupTheory.IndexNormal

/-!
# The sign group of a linearly ordered ring

For a linearly ordered ring, the positive units `Units.posSubgroup R` form an index-`2` subgroup, so
it has finite index. Together with the general finite-index-preimage instance
(`Subgroup.instFiniteIndexComap`), this yields the finiteness of the totally positive units of a
number field, hence of its narrow class group.

Being of index `2`, the quotient `Rˣ ⧸ Units.posSubgroup R` is *the* two-element sign group;
`Units.signEquiv` identifies it with `ℤˣ`, which is how a sign is usually presented concretely.

## Main definitions and results

* `Units.instFiniteIndexPosSubgroup`: the positive units have finite index.
* `Units.signEquiv`: the sign isomorphism `Rˣ ⧸ Units.posSubgroup R ≃* ℤˣ`, with
  `Units.signEquiv_mk_eq_one_iff` and `Units.signEquiv_mk_eq_neg_one_iff` reading its two values
  off the sign of a unit.
-/

public section

namespace Units

/-- The positive units of a linearly ordered ring form an index-`2`, hence finite-index,
subgroup. -/
instance instFiniteIndexPosSubgroup (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R] :
    (Units.posSubgroup R).FiniteIndex :=
  ⟨by rw [Units.index_posSubgroup]; decide⟩

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

local instance : (Units.posSubgroup R).Normal :=
  Subgroup.normal_of_index_eq_two (Units.index_posSubgroup R)

variable (R) in
/-- **The sign isomorphism of a linearly ordered ring.** The units of `R` modulo the
positive ones form the two-element sign group `ℤˣ`, the class of a unit being its sign.

The class of a positive unit is sent to `1` and the class of a negative unit to `-1`; these two
values are read off by `Units.signEquiv_mk_eq_one_iff` and `Units.signEquiv_mk_eq_neg_one_iff`. -/
noncomputable def signEquiv : Rˣ ⧸ Units.posSubgroup R ≃* ℤˣ :=
  (MulEquiv.ofBijective
    ((QuotientGroup.mk' (Units.posSubgroup R)).comp (Units.map (Int.castRingHom R).toMonoidHom))
    ⟨by
      refine (injective_iff_map_eq_one _).mpr fun u hu => ?_
      rcases Int.units_eq_one_or u with h | h
      · exact h
      · subst u
        have : (1 : R) < 0 := by
          simpa [MonoidHom.comp_apply, QuotientGroup.eq_one_iff, Units.mem_posSubgroup] using hu
        exact (not_lt_of_ge zero_le_one this).elim,
      by
      refine fun q => QuotientGroup.induction_on q fun u => ?_
      have hmap : Units.map (Int.castRingHom R).toMonoidHom (-1 : ℤˣ) = (-1 : Rˣ) := by
        ext
        simp
      rcases lt_or_gt_of_ne u.ne_zero with h | h
      · refine ⟨-1, ?_⟩
        simpa [MonoidHom.comp_apply, hmap, QuotientGroup.eq, Units.mem_posSubgroup] using
          neg_pos.mpr h
      · refine ⟨1, ?_⟩
        rw [map_one, eq_comm, QuotientGroup.eq_one_iff, Units.mem_posSubgroup]
        exact h⟩).symm

-- Not a `simp` lemma: the simp set already reaches this statement through
-- `EmbeddingLike.map_eq_one_iff` and `QuotientGroup.eq_one_iff`, so tagging it fails `simpNF`.
/-- The sign of a unit is `1` exactly when the unit is positive. -/
theorem signEquiv_mk_eq_one_iff (u : Rˣ) :
    signEquiv R (QuotientGroup.mk u) = 1 ↔ (0 : R) < u := by
  rw [map_eq_one_iff _ (signEquiv R).injective, QuotientGroup.eq_one_iff, Units.mem_posSubgroup]

/-- The sign of a unit is `-1` exactly when the unit is negative. -/
@[simp] theorem signEquiv_mk_eq_neg_one_iff (u : Rˣ) :
    signEquiv R (QuotientGroup.mk u) = -1 ↔ (u : R) < 0 := by
  constructor
  · intro h
    rcases lt_or_gt_of_ne u.ne_zero with h' | h'
    · exact h'
    · rw [(signEquiv_mk_eq_one_iff u).mpr h'] at h
      exact absurd h (by decide)
  · intro h
    rcases Int.units_eq_one_or (signEquiv R (QuotientGroup.mk u)) with h1 | h1
    · exact absurd ((signEquiv_mk_eq_one_iff u).mp h1) (asymm h)
    · exact h1

end Units
