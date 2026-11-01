/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Closed two-sided ideals

The closure of a two-sided ideal in a topological ring is again two-sided. We
also supply the quotient topology for quotients of noncommutative rings by
native ideals; Mathlib's named topology instance currently requires commutativity.
These quotients present categories of discrete modules with central relations.

The quotient-ring construction generalizes Patrick Massot's
`QuotientRing.topologicalRing_quotient` in Mathlib from commutative rings, using
the same native additive quotient and open quotient-map argument.
-/

public section

open Topology

namespace Ideal

variable {A : Type*} [Ring A] [TopologicalSpace A]

/-- The quotient topology on a quotient of a possibly noncommutative ring.
The higher-priority Mathlib instance handles commutative rings. -/
instance (priority := 100) topologicalSpaceQuotient (I : Ideal A) :
    TopologicalSpace (A ⧸ I) :=
  TopologicalSpace.coinduced (Submodule.Quotient.mk (p := I)) inferInstance

/-- The projection to an ideal quotient is a quotient map. -/
theorem isQuotientMap_quotient_mk (I : Ideal A) [I.IsTwoSided] :
    IsQuotientMap (Ideal.Quotient.mk I) :=
  ⟨⟨rfl⟩, Ideal.Quotient.mk_surjective⟩

/-- Quotient projections of topological rings are open quotient maps. -/
theorem isOpenQuotientMap_quotient_mk [IsTopologicalRing A] (I : Ideal A) [I.IsTwoSided] :
    IsOpenQuotientMap (Ideal.Quotient.mk I) :=
  QuotientAddGroup.isOpenQuotientMap_mk

/-- A quotient of a possibly noncommutative topological ring is a topological ring. -/
instance (priority := 100) isTopologicalRingQuotient [IsTopologicalRing A]
    (I : Ideal A) [I.IsTwoSided] : IsTopologicalRing (A ⧸ I) where
  __ := QuotientAddGroup.instIsTopologicalAddGroup _
  continuous_mul := by
    have hq := I.isOpenQuotientMap_quotient_mk.prodMap I.isOpenQuotientMap_quotient_mk
    exact hq.isQuotientMap.continuous_iff.mpr
      (I.isQuotientMap_quotient_mk.continuous.comp continuous_mul)

/-- The closure of a two-sided ideal is two-sided. -/
instance isTwoSided_closure [IsTopologicalRing A] (I : Ideal A) [I.IsTwoSided] :
    I.closure.IsTwoSided where
  mul_mem_of_left {_} b ha :=
    map_mem_closure (f := fun x : A => x * b)
      (s := (I : Set A)) (t := (I : Set A))
      (continuous_mul_const b) ha fun _ hx => I.mul_mem_right b hx

end Ideal

namespace TwoSidedIdeal

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The topological closure of a two-sided ideal, as a native two-sided ideal. -/
def topologicalClosure (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  I.asIdeal.closure.toTwoSided

@[simp]
theorem coe_topologicalClosure (I : TwoSidedIdeal A) :
    (I.topologicalClosure : Set A) = closure (I : Set A) := by
  simp [topologicalClosure]

/-- A two-sided ideal is contained in its topological closure. -/
theorem le_topologicalClosure (I : TwoSidedIdeal A) : I ≤ I.topologicalClosure := by
  intro a ha
  rw [← SetLike.mem_coe, coe_topologicalClosure]
  exact subset_closure ha

/-- The topological closure is closed. -/
theorem isClosed_topologicalClosure (I : TwoSidedIdeal A) :
    IsClosed (I.topologicalClosure : Set A) := by
  rw [coe_topologicalClosure]
  exact isClosed_closure

/-- The closure is the least closed two-sided ideal containing the original ideal. -/
theorem topologicalClosure_le_iff (I J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    I.topologicalClosure ≤ J ↔ I ≤ J :=
  ⟨fun h => I.le_topologicalClosure.trans h,
    fun h => by
      rw [← SetLike.coe_subset_coe, coe_topologicalClosure]
      exact closure_minimal h hJ⟩

end TwoSidedIdeal
