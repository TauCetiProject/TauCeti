/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Closed two-sided ideals

The closure of a two-sided ideal in a topological ring is again two-sided. We
also supply the topological-ring structure on Mathlib's existing quotient topology
for quotients of noncommutative rings by native ideals. The closed ideal generated
by an ideal of the center presents discrete modules with central relations.

The quotient-ring construction generalizes Patrick Massot's
`QuotientRing.topologicalRing_quotient` in Mathlib from commutative rings, using
the same native additive quotient and open quotient-map argument.
-/

public section

open Topology

namespace Ideal

variable {A : Type*} [Ring A] [TopologicalSpace A]

/-- A quotient of a possibly noncommutative topological ring is a topological ring. -/
instance (priority := 100) isTopologicalRingQuotient [IsTopologicalRing A]
    (I : Ideal A) [I.IsTwoSided] : IsTopologicalRing (A ⧸ I) where
  __ := Submodule.isTopologicalAddGroup_quotient I
  continuous_mul := by
    have hq := I.isOpenQuotientMap_mkQ.prodMap I.isOpenQuotientMap_mkQ
    exact hq.isQuotientMap.continuous_iff.mpr
      (I.isQuotientMap_mkQ.continuous.comp continuous_mul)

/-- The closure of a two-sided ideal is two-sided. -/
instance isTwoSided_closure [IsTopologicalRing A] (I : Ideal A) [I.IsTwoSided] :
    I.closure.IsTwoSided where
  mul_mem_of_left {_} b ha :=
    map_mem_closure (f := fun x : A => x * b)
      (s := (I : Set A)) (t := (I : Set A))
      (continuous_mul_const b) ha fun _ hx => I.mul_mem_right b hx

end Ideal

namespace TwoSidedIdeal

section TopologicalClosure

variable {A : Type*} [NonUnitalRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The topological closure of a two-sided ideal in a possibly nonunital topological ring, as a
native two-sided ideal. -/
def topologicalClosure (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (closure (I : Set A))
    (subset_closure I.zero_mem)
    (fun hx hy => map_mem_closure₂ continuous_add hx hy fun _ ha _ hb => I.add_mem ha hb)
    (fun hx => map_mem_closure continuous_neg hx fun _ ha => I.neg_mem ha)
    (fun {x _} hy => map_mem_closure (continuous_const_mul x) hy fun _ hb => I.mul_mem_left x _ hb)
    (fun {_ y} hx => map_mem_closure (f := fun x : A => x * y) (s := (I : Set A))
      (t := (I : Set A)) (continuous_mul_const y) hx fun _ ha => I.mul_mem_right _ y ha)

@[simp]
theorem coe_topologicalClosure (I : TwoSidedIdeal A) :
    (I.topologicalClosure : Set A) = closure (I : Set A) := by
  simp [topologicalClosure]

@[simp]
theorem mem_topologicalClosure {I : TwoSidedIdeal A} {a : A} :
    a ∈ I.topologicalClosure ↔ a ∈ closure (I : Set A) := by
  rw [← SetLike.mem_coe, coe_topologicalClosure]

/-- A two-sided ideal is contained in its topological closure. -/
theorem le_topologicalClosure (I : TwoSidedIdeal A) : I ≤ I.topologicalClosure := by
  intro a ha
  rw [mem_topologicalClosure]
  exact subset_closure ha

/-- The topological closure is closed. -/
theorem isClosed_topologicalClosure (I : TwoSidedIdeal A) :
    IsClosed (I.topologicalClosure : Set A) := by
  rw [coe_topologicalClosure]
  exact isClosed_closure

/-- A closed two-sided ideal equals its topological closure. -/
@[simp]
theorem topologicalClosure_eq_self (I : TwoSidedIdeal A) [hI : IsClosed (I : Set A)] :
    I.topologicalClosure = I := by
  ext a
  rw [mem_topologicalClosure, hI.closure_eq, SetLike.mem_coe]

/-- Taking topological closure of a two-sided ideal is idempotent. -/
theorem topologicalClosure_idem (I : TwoSidedIdeal A) :
    I.topologicalClosure.topologicalClosure = I.topologicalClosure := by
  have : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  exact I.topologicalClosure.topologicalClosure_eq_self

/-- Taking topological closure of two-sided ideals is monotone. -/
theorem topologicalClosure_mono {I J : TwoSidedIdeal A} (h : I ≤ J) :
    I.topologicalClosure ≤ J.topologicalClosure := by
  rw [← SetLike.coe_subset_coe, coe_topologicalClosure, coe_topologicalClosure]
  exact closure_mono h

/-- The closure is the least closed two-sided ideal containing the original ideal. -/
theorem topologicalClosure_le_iff (I J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    I.topologicalClosure ≤ J ↔ I ≤ J :=
  ⟨fun h => I.le_topologicalClosure.trans h,
    fun h => by
      rw [← SetLike.coe_subset_coe, coe_topologicalClosure]
      exact closure_minimal h hJ⟩

end TopologicalClosure

section ClosedKer

variable {A B F : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A]
  [NonUnitalNonAssocSemiring B] [TopologicalSpace B] [T1Space B]
  [FunLike F A B] [NonUnitalRingHomClass F A B]

/-- The kernel two-sided ideal of a continuous nonunital ring homomorphism into a `T₁` space is
closed. -/
theorem isClosed_ker {f : F} (hf : Continuous f) : IsClosed (TwoSidedIdeal.ker f : Set A) := by
  have hset : (TwoSidedIdeal.ker f : Set A) = f ⁻¹' {0} := by
    ext x
    exact TwoSidedIdeal.mem_ker f
  rw [hset]
  exact isClosed_singleton.preimage hf

end ClosedKer

end TwoSidedIdeal

namespace Ideal

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]
  [TopologicalSpace A] [IsTopologicalRing A]

/-- The closed two-sided ideal generated by an ideal of the center. -/
def closedCentralIdeal (L : Ideal (Subalgebra.center R A)) : TwoSidedIdeal A :=
  (TwoSidedIdeal.span ((↑) '' (L : Set (Subalgebra.center R A)))).topologicalClosure

/-- The generated central ideal is closed. -/
theorem isClosed_closedCentralIdeal (L : Ideal (Subalgebra.center R A)) :
    IsClosed (closedCentralIdeal L : Set A) :=
  TwoSidedIdeal.isClosed_topologicalClosure _

/-- Every central relation belongs to the closed generated ideal. -/
theorem mem_closedCentralIdeal (L : Ideal (Subalgebra.center R A))
    {z : Subalgebra.center R A} (hz : z ∈ L) : (z : A) ∈ closedCentralIdeal L :=
  TwoSidedIdeal.le_topologicalClosure _ (TwoSidedIdeal.subset_span ⟨z, hz, rfl⟩)

/-- The closed central ideal is the least closed two-sided ideal containing the relations. -/
theorem closedCentralIdeal_le_iff (L : Ideal (Subalgebra.center R A))
    (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    closedCentralIdeal L ≤ J ↔ ∀ z ∈ L, (z : A) ∈ J := by
  rw [closedCentralIdeal, TwoSidedIdeal.topologicalClosure_le_iff _ _ hJ,
    TwoSidedIdeal.span_le]
  exact ⟨fun h z hz => h ⟨z, hz, rfl⟩, fun h _ ⟨z, hz, he⟩ => he ▸ h z hz⟩

end Ideal
