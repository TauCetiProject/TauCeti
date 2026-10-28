/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.Primitive
public import Mathlib.Topology.Separation.Basic

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
* The closed-set construction follows Mathlib's `PrimeSpectrum.zariskiTopology`, with
  two-sided ideals in place of commutative ideals and the primitive-ideal intersection
  property in place of elementwise primality. No prime-spectrum results are assumed.
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

/-- The hull of a two-sided ideal is the set of primitive ideals containing it. -/
def hull (I : TwoSidedIdeal R) : Set (PrimitiveSpectrum R) :=
  {p | I ≤ p.asTwoSidedIdeal}

@[simp]
theorem mem_hull {I : TwoSidedIdeal R} {p : PrimitiveSpectrum R} :
    p ∈ hull I ↔ I ≤ p.asTwoSidedIdeal := Iff.rfl

/-- The kernel of a set of primitive ideals is their intersection. -/
def kernel (s : Set (PrimitiveSpectrum R)) : TwoSidedIdeal R :=
  ⨅ p : s, p.1.asTwoSidedIdeal

@[simp]
theorem mem_kernel {s : Set (PrimitiveSpectrum R)} {a : R} :
    a ∈ kernel s ↔ ∀ p ∈ s, a ∈ p.asTwoSidedIdeal := by
  simp [kernel, TwoSidedIdeal.mem_iInf]

/-- Hull and kernel reverse inclusion and form a Galois connection. -/
theorem subset_hull_iff_le_kernel {s : Set (PrimitiveSpectrum R)} {I : TwoSidedIdeal R} :
    s ⊆ hull I ↔ I ≤ kernel s := by
  simp only [Set.subset_def, mem_hull, le_iInf_iff, kernel, Subtype.forall]

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
  ext p
  simp

/-- The finite-union property of hulls uses two-sided ideals, even in a noncommutative ring. -/
theorem hull_inf (I J : TwoSidedIdeal R) : hull (I ⊓ J) = hull I ∪ hull J := by
  ext p
  exact p.isPrimitive.inf_le_iff I J

/-- Every set lies in the hull of its kernel. -/
theorem subset_hull_kernel (s : Set (PrimitiveSpectrum R)) : s ⊆ hull (kernel s) :=
  subset_hull_iff_le_kernel.mpr le_rfl

/-- Taking hull, kernel and hull again does not change a hull. -/
@[simp]
theorem hull_kernel_hull (I : TwoSidedIdeal R) : hull (kernel (hull I)) = hull I :=
  gc.l_u_l_eq_l I

/-- The hull–kernel topology has exactly the hulls of two-sided ideals as its closed sets. -/
instance : TopologicalSpace (PrimitiveSpectrum R) :=
  TopologicalSpace.ofClosed (Set.range hull) ⟨⊤, hull_top⟩
    (by
      intro Zs hZs
      classical
      choose I hI using fun s : Zs ↦ hZs s.property
      refine ⟨⨆ s, I s, ?_⟩
      rw [hull_iSup, Set.sInter_eq_iInter]
      simp only [hI])
    (by
      rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩
      exact ⟨I ⊓ J, hull_inf I J⟩)

/-- Closed subsets of the primitive spectrum are precisely hulls of two-sided ideals. -/
theorem isClosed_iff (s : Set (PrimitiveSpectrum R)) : IsClosed s ↔ ∃ I, hull I = s := by
  rw [← isOpen_compl_iff]
  -- The open predicate in the closed-set construction tests the complement.
  change sᶜᶜ ∈ Set.range hull ↔ _
  simp

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
