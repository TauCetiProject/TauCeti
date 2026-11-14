/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# The defining Hopf ideal of an exterior-line stabilizer

A subspace and its top exterior line have the same scheme-theoretic stabilizer. The
comparison uses their stabilizer functors over all commutative value algebras, so it also
detects nonreduced subgroup schemes.

## Main declarations

* `Submodule.stabilizerHopfIdeal_range_exteriorPowerMap_finrank`: equality of the
  defining Hopf ideals of the two stabilizers.

## References

* J. S. Milne, *Algebraic Groups* (2017), Lemma 4.28.
-/

public section

namespace Submodule

open TauCeti

attribute [local instance] Comodule.exteriorPower

variable {k H V : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup V] [Module k V] [Module.Finite k V] [Comodule k H V]

/-- A subspace and the image of its top exterior power have the same defining stabilizer
Hopf ideal, including their scheme-theoretic structure. -/
theorem stabilizerHopfIdeal_range_exteriorPowerMap_finrank (W : Submodule k V) :
    (LinearMap.range (_root_.exteriorPower.map (Module.finrank k W) W.subtype)).stabilizerHopfIdeal
        H = W.stabilizerHopfIdeal H := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
    (H := _root_.CommHopfAlgCat.of k H)
  intro A
  ext g
  rw [mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint,
    mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff_endOfPoint,
    Comodule.map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff]

end Submodule
