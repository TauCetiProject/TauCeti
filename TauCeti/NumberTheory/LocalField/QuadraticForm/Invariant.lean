/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Brauer
public import TauCeti.NumberTheory.LocalField.Quaternion.Invariant

/-!
# The local invariant of the Hasse class

The sign on the quaternion subgroup agrees with the normalized local invariant: sign `1`
means invariant zero and sign `-1` means invariant `1/2`. Applied to the Brauer-valued Hasse
invariant, this expresses its local invariant directly in terms of the classical local Hasse
invariant of the form. The normalization is the invariant map supplied by class field theory.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.
* J.-P. Serre, *Local Fields*, Chapter XIII, §3.
-/

public section

noncomputable section

namespace TauCeti

open ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- The canonical sign on quaternion classes is the local invariant, with values zero and
one half. This equality applies to every element of the quaternion subgroup. -/
theorem BrauerGroup.invMap_quaternionSubgroup (x : quaternionSubgroup K) :
    invMap K (brauerGroupEquivBr K (Additive.ofMul (x : BrauerGroup K))) =
      if quaternionSubgroupSignEquiv x = 1 then 0 else ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  by_cases hx : x = 1
  · subst x
    simp
  · have hs : quaternionSubgroupSignEquiv x ≠ 1 := by
      intro hs
      exact hx (quaternionSubgroupSignEquiv.injective (hs.trans (map_one _).symm))
    rw [ite_eq_right hs]
    exact (invMap_brauerGroupEquivBr_eq_half_iff K
      ((quaternionSubgroup_eq_twoTorsion K) ▸ x.property)).mpr
      (fun h => hx (Subtype.ext h))

/-- The Brauer-valued Hasse invariant has local invariant zero or one half according as
its classical local Hasse invariant is `1` or `-1`. -/
theorem RegularFormClass.invMap_hasseInvariant (q : RegularFormClass K) :
    invMap K (brauerGroupEquivBr K (Additive.ofMul (hasseInvariant q))) =
      if localHasse q = 1 then 0 else ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  simpa only [quaternionSubgroupSignEquiv_apply_hasseInvariant] using
    BrauerGroup.invMap_quaternionSubgroup
      (⟨hasseInvariant q, hasseInvariant_mem_quaternionSubgroup q⟩ :
        BrauerGroup.quaternionSubgroup K)

end TauCeti
