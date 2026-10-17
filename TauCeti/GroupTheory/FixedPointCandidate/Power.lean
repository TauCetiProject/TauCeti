/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.FixedSubgroup.Power

/-!
# The fixed-point candidate inside the fixed subgroup of a power

An endomorphism `F` restricts to an automorphism of the subgroup fixed by `F ^ n`, for positive
`n`. Forming the fixed-point candidate there gives the same group as forming it in the ambient
group: the fixed subgroups are first identified, then their derived central quotients are
transported. This does not assert that taking fixed points commutes with taking derived subgroups
or central quotients.
-/

public section

namespace TauCeti.FixedPointCandidate

variable {G : Type*} [Group G]

/-- The fixed/derived/own-centre recipe can be computed inside the fixed subgroup of any positive
power of its endomorphism. -/
noncomputable def powRestrictionEquiv (F : Monoid.End G) {n : ℕ} (hn : 0 < n) :
    FixedPointCandidate (G := ↥(fixedSubgroup (F ^ n))) ↑(fixedSubgroupPowAut F hn) ≃*
      FixedPointCandidate F :=
  DerivedCentralQuotient.congr (fixedSubgroupPowFixedEquiv F hn)

@[simp]
theorem powRestrictionEquiv_mk (F : Monoid.End G) {n : ℕ} (hn : 0 < n)
    (x : ↥(commutator ↥(fixedSubgroup (G := ↥(fixedSubgroup (F ^ n)))
      ↑(fixedSubgroupPowAut F hn)))) :
    powRestrictionEquiv F hn
        (x : FixedPointCandidate (G := ↥(fixedSubgroup (F ^ n))) ↑(fixedSubgroupPowAut F hn)) =
      (MulEquiv.commutatorCongr (fixedSubgroupPowFixedEquiv F hn) x : FixedPointCandidate F) := by
  exact DerivedCentralQuotient.congr_mk (fixedSubgroupPowFixedEquiv F hn) x

end TauCeti.FixedPointCandidate
