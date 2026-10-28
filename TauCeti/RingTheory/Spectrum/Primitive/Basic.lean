/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.Primitive
public import Mathlib.Topology.Order.HullKernel

/-!
# The primitive spectrum and its hull–kernel topology

The primitive spectrum of a unital ring consists of the annihilators of simple left modules.
Its closed sets are the hulls of two-sided ideals. The kernel of a set of primitive ideals is
their intersection, and taking its hull gives exactly the topological closure. In particular,
the intersection of the entire primitive spectrum is the Jacobson radical.

This topology is useful for organizing simple-module representations of Banach algebras.
The construction itself is algebraic: no norm, completeness or commutativity is needed.
Primitive ideals need not be maximal two-sided ideals, so the topology is T₀ rather than
necessarily T₁.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* Mathlib's `Topology.Order.HullKernel` supplies the lattice hull, kernel, Galois
  connection and relative lower topology, specialized to primitive two-sided ideals.
-/

public section

namespace TauCeti

/-- The primitive spectrum of a unital ring: two-sided ideals that are annihilators of
simple left modules. -/
structure PrimitiveSpectrum (R : Type*) [Ring R] where
  /-- The underlying two-sided ideal. -/
  asTwoSidedIdeal : TwoSidedIdeal R
  /-- The underlying left ideal is primitive. -/
  isPrimitive : asTwoSidedIdeal.asIdeal.IsPrimitive

namespace PrimitiveSpectrum

variable {R : Type*} [Ring R]

@[ext]
theorem ext {p q : PrimitiveSpectrum R} (h : p.asTwoSidedIdeal = q.asTwoSidedIdeal) :
    p = q := by
  cases p
  cases q
  cases h
  rfl

private def equivSubtype : PrimitiveSpectrum R ≃
    {I : TwoSidedIdeal R | I.asIdeal.IsPrimitive} where
  toFun p := ⟨p.asTwoSidedIdeal, p.isPrimitive⟩
  invFun I := ⟨I.1, I.2⟩

private theorem infPrime (I : TwoSidedIdeal R) (hI : I.asIdeal.IsPrimitive) :
    InfPrime I := by
  refine ⟨?_, fun J K h ↦ (hI.inf_le_iff J K).mp h⟩
  intro h
  apply hI.ne_top
  have htop : I = ⊤ := isMax_iff_eq_top.mp h
  simp [htop]

/-- The hull of a two-sided ideal is the set of primitive ideals containing it. -/
def hull (I : TwoSidedIdeal R) : Set (PrimitiveSpectrum R) :=
  equivSubtype ⁻¹' _root_.PrimitiveSpectrum.hull {J : TwoSidedIdeal R |
    J.asIdeal.IsPrimitive} I

@[simp]
theorem mem_hull {I : TwoSidedIdeal R} {p : PrimitiveSpectrum R} :
    p ∈ hull I ↔ I ≤ p.asTwoSidedIdeal := Iff.rfl

/-- The kernel of a set of primitive ideals is their intersection. -/
def kernel (s : Set (PrimitiveSpectrum R)) : TwoSidedIdeal R :=
  _root_.PrimitiveSpectrum.kernel (equivSubtype '' s)

@[simp]
theorem mem_kernel {s : Set (PrimitiveSpectrum R)} {a : R} :
    a ∈ kernel s ↔ ∀ p ∈ s, a ∈ p.asTwoSidedIdeal := by
  simp [kernel, _root_.PrimitiveSpectrum.kernel, TwoSidedIdeal.mem_sInf,
    equivSubtype]

/-- Hull and kernel reverse inclusion and form a Galois connection. -/
theorem subset_hull_iff_le_kernel {s : Set (PrimitiveSpectrum R)} {I : TwoSidedIdeal R} :
    s ⊆ hull I ↔ I ≤ kernel s := by
  simpa only [hull, kernel, Set.image_subset_iff, OrderDual.toDual_le_toDual,
    OrderDual.ofDual_toDual] using
    (_root_.PrimitiveSpectrum.gc (equivSubtype '' s) (OrderDual.toDual I)).symm

/-- The order-reversing hull–kernel Galois connection. -/
theorem gc : GaloisConnection (fun I : TwoSidedIdeal R ↦ OrderDual.toDual (hull I))
    (fun s ↦ kernel (OrderDual.ofDual s)) := by
  intro I s
  exact subset_hull_iff_le_kernel

theorem hull_anti_mono {I J : TwoSidedIdeal R} (h : I ≤ J) : hull J ⊆ hull I :=
  fun _ hp ↦ h.trans hp

theorem kernel_anti_mono {s t : Set (PrimitiveSpectrum R)} (h : s ⊆ t) :
    kernel t ≤ kernel s := by
  intro a ha
  exact mem_kernel.mpr fun p hp ↦ mem_kernel.mp ha p (h hp)

@[simp]
theorem hull_bot : hull (⊥ : TwoSidedIdeal R) = Set.univ := by
  ext p
  simp

@[simp]
theorem hull_top : hull (⊤ : TwoSidedIdeal R) = ∅ := by
  ext p
  simp only [mem_hull, Set.mem_empty_iff_false, iff_false]
  intro h
  exact p.isPrimitive.ne_top (p.asTwoSidedIdeal.asIdeal.eq_top_of_isUnit_mem
    (h (by simp)) isUnit_one)

@[simp]
theorem kernel_empty : kernel (∅ : Set (PrimitiveSpectrum R)) = ⊤ := by
  ext a
  simp

@[simp]
theorem kernel_singleton (p : PrimitiveSpectrum R) : kernel {p} = p.asTwoSidedIdeal := by
  ext a
  simp

/-- A supremum of ideals corresponds to an intersection of hulls. -/
theorem hull_iSup {ι : Sort*} (I : ι → TwoSidedIdeal R) :
    hull (⨆ i, I i) = ⋂ i, hull (I i) := by
  simpa only [hull, Set.preimage_iInter] using
    congrArg (fun s ↦ equivSubtype ⁻¹' s) (_root_.PrimitiveSpectrum.hull_iSup I)

/-- The finite-union property of hulls uses two-sided ideals, even in a noncommutative ring. -/
theorem hull_inf (I J : TwoSidedIdeal R) : hull (I ⊓ J) = hull I ∪ hull J := by
  exact congrArg (fun s ↦ equivSubtype ⁻¹' s)
    (_root_.PrimitiveSpectrum.hull_inf infPrime I J)

/-- Every set lies in the hull of its kernel. -/
theorem subset_hull_kernel (s : Set (PrimitiveSpectrum R)) : s ⊆ hull (kernel s) :=
  subset_hull_iff_le_kernel.mpr le_rfl

/-- Taking hull, kernel and hull again does not change a hull. -/
@[simp]
theorem hull_kernel_hull (I : TwoSidedIdeal R) : hull (kernel (hull I)) = hull I :=
  gc.l_u_l_eq_l I

private local instance : TopologicalSpace (TwoSidedIdeal R) := Topology.lower _

private local instance : Topology.IsLower (TwoSidedIdeal R) := ⟨rfl⟩

/-- The hull–kernel topology is the relative lower topology on primitive two-sided ideals. -/
instance : TopologicalSpace (PrimitiveSpectrum R) :=
  TopologicalSpace.induced (fun p : PrimitiveSpectrum R ↦
    (⟨p.asTwoSidedIdeal, p.isPrimitive⟩ : {I : TwoSidedIdeal R | I.asIdeal.IsPrimitive}))
    (@TopologicalSpace.induced _ _ Subtype.val (Topology.lower _))

private def homeomorphSubtype : PrimitiveSpectrum R ≃ₜ
    {I : TwoSidedIdeal R | I.asIdeal.IsPrimitive} :=
  equivSubtype.toHomeomorphOfIsInducing ⟨rfl⟩

/-- Closed subsets of the primitive spectrum are precisely hulls of two-sided ideals. -/
theorem isClosed_iff (s : Set (PrimitiveSpectrum R)) : IsClosed s ↔ ∃ I, hull I = s := by
  rw [← homeomorphSubtype.isClosed_image, _root_.PrimitiveSpectrum.isClosed_iff infPrime]
  constructor
  · rintro ⟨I, hI⟩
    refine ⟨I, ?_⟩
    simpa only [hull, ← hI, homeomorphSubtype, Equiv.toHomeomorphOfIsInducing_apply] using
      equivSubtype.injective.preimage_image s
  · rintro ⟨I, rfl⟩
    exact ⟨I, by
      simpa only [homeomorphSubtype, Equiv.toHomeomorphOfIsInducing_apply, hull] using
        equivSubtype.surjective.image_preimage (_root_.PrimitiveSpectrum.hull _ I)⟩

theorem isClosed_hull (I : TwoSidedIdeal R) : IsClosed (hull I) :=
  (isClosed_iff _).mpr ⟨I, rfl⟩

/-- Closure in the primitive spectrum is obtained by taking kernel and then hull. -/
theorem closure_eq_hull_kernel (s : Set (PrimitiveSpectrum R)) :
    closure s = hull (kernel s) := by
  refine Set.Subset.antisymm
    (closure_minimal (subset_hull_kernel s) (isClosed_hull _)) ?_
  obtain ⟨I, hI⟩ := (isClosed_iff (closure s)).mp isClosed_closure
  rw [← hI]
  exact hull_anti_mono (subset_hull_iff_le_kernel.mp (hI ▸ subset_closure))

/-- Closedness is the fixed-point property of hull after kernel. -/
theorem isClosed_iff_hull_kernel (s : Set (PrimitiveSpectrum R)) :
    IsClosed s ↔ hull (kernel s) = s := by
  rw [← closure_eq_hull_kernel, closure_eq_iff_isClosed]

/-- Passing to the closure leaves the kernel unchanged. -/
@[simp]
theorem kernel_closure (s : Set (PrimitiveSpectrum R)) : kernel (closure s) = kernel s := by
  apply le_antisymm (kernel_anti_mono subset_closure)
  rw [closure_eq_hull_kernel]
  exact subset_hull_iff_le_kernel.mp (Set.Subset.refl _)

/-- A primitive ideal specializes to exactly the primitive ideals containing it. -/
theorem closure_singleton (p : PrimitiveSpectrum R) :
    closure ({p} : Set (PrimitiveSpectrum R)) = hull p.asTwoSidedIdeal := by
  rw [closure_eq_hull_kernel, kernel_singleton]

instance : T0Space (PrimitiveSpectrum R) := by
  rw [t0Space_iff_inseparable]
  intro p q h
  obtain ⟨hpq, hqp⟩ := inseparable_iff_mem_closure.mp h
  apply ext
  apply le_antisymm
  · rwa [closure_singleton, mem_hull] at hqp
  · rwa [closure_singleton, mem_hull] at hpq

/-- The kernel of the entire primitive spectrum is the Jacobson radical. -/
theorem kernel_univ :
    kernel (Set.univ : Set (PrimitiveSpectrum R)) = (Ring.jacobson R).toTwoSided := by
  ext a
  rw [mem_kernel, Ideal.mem_toTwoSided, Ring.mem_jacobson_iff_forall_mem_isPrimitive]
  constructor
  · intro h I hI
    let := hI.isTwoSided
    simpa only [Ideal.mem_toTwoSided] using
      h ⟨I.toTwoSided, by simpa using hI⟩ (Set.mem_univ _)
  · intro h p _
    exact h p.asTwoSidedIdeal.asIdeal p.isPrimitive

end PrimitiveSpectrum

end TauCeti
