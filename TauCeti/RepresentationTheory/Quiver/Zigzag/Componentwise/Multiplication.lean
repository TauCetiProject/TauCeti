/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Multiplication
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Decomposition

/-!
# Multiplication in the componentwise zigzag algebra

The vertex, dart and volume basis of the public zigzag algebra has the same
path-product table on every nontrivial component. On a singleton component,
the vertex vector is the unit and the volume vector is the square-zero
generator of the dual numbers. This file gives a single table valid for
both kinds of component, and for disconnected graphs.

In Tau Ceti's later-factor-first convention, the product of a dart with
its reverse is the volume at the head of the first dart.

The table follows Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties
of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

universe u w

variable {V : Type u} (G : SimpleGraph V)

variable (k : Type w) [CommRing k] [Finite V]

/-- The multiplication table in a connected component with an edge is the
path-quotient table, transported along the component presentation. -/
private theorem componentBasis_mul_nontrivial (C : G.ConnectedComponent) [Nontrivial C]
    (b c : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentBasis k G C b * zigzagComponentBasis k G C c =
      (zigzagBasisMul C.toSimpleGraph b c).elim 0 (zigzagComponentBasis k G C) := by
  let hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i =>
    SimpleGraph.exists_adj_iff_not_isIsolated.mpr
      (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
  apply (zigzagComponentAlgebraEquivNonisolated k G C).injective
  rw [map_mul]
  simp only [zigzagComponentAlgebraEquivNonisolated_zigzagComponentBasis k G C hns,
    zigzagBasis_mul]
  cases zigzagBasisMul C.toSimpleGraph b c <;>
    simp [zigzagComponentAlgebraEquivNonisolated_zigzagComponentBasis k G C hns]

/-- The multiplication table on a singleton component is the dual-number
table, with the volume vector identified with the infinitesimal generator. -/
private theorem componentBasis_mul_subsingleton (C : G.ConnectedComponent) [Subsingleton C]
    (b c : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentBasis k G C b * zigzagComponentBasis k G C c =
      (zigzagBasisMul C.toSimpleGraph b c).elim 0 (zigzagComponentBasis k G C) := by
  have noDart (d : C.toSimpleGraph.Dart) : False :=
    C.toSimpleGraph.ne_of_adj d.adj (Subsingleton.elim _ _)
  rcases b with i | d | i
  · rcases c with j | e | j
    · have hij : i = j := Subsingleton.elim _ _
      subst j
      apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
      simp
    · exact (noDart e).elim
    · have hij : i = j := Subsingleton.elim _ _
      subst j
      apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
      simp
  · exact (noDart d).elim
  · rcases c with j | e | j
    · have hij : i = j := Subsingleton.elim _ _
      subst j
      apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
      simp
    · exact (noDart e).elim
    · apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
      simp only [zigzagBasisMul_volume_volume, Option.elim_none, map_mul, map_zero,
        zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inr_inr]
      apply ULift.ext
      exact DualNumber.eps_mul_eps

/-- Multiplication of basis vectors in any connected-component factor, including
the singleton dual-number factors. -/
@[simp]
theorem zigzagComponentBasis_mul (C : G.ConnectedComponent)
    (b c : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentBasis k G C b * zigzagComponentBasis k G C c =
      (zigzagBasisMul C.toSimpleGraph b c).elim 0 (zigzagComponentBasis k G C) := by
  rcases subsingleton_or_nontrivial C with hC | hC
  · exact componentBasis_mul_subsingleton G k C b c
  · exact componentBasis_mul_nontrivial G k C b c

omit [Finite V] in
/-- The product index respects the basis-index equivalence on one component. -/
@[simp]
theorem zigzagBasisMul_component (C : G.ConnectedComponent)
    (b c : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagBasisMul G (zigzagComponentBasisIndexEquiv G ⟨C, b⟩)
        (zigzagComponentBasisIndexEquiv G ⟨C, c⟩) =
      (zigzagBasisMul C.toSimpleGraph b c).map
        (fun d => zigzagComponentBasisIndexEquiv G ⟨C, d⟩) := by
  classical
  rcases b with i | d | i <;> rcases c with j | e | j
  all_goals simp [SimpleGraph.Dart.ext_iff, Prod.ext_iff]

omit [Finite V] in
/-- Basis indices from distinct components have zero product. -/
@[simp]
theorem zigzagBasisMul_eq_none_of_ne_component {C D : G.ConnectedComponent} (h : C ≠ D)
    (b : ZigzagBasisIndex C.toSimpleGraph) (c : ZigzagBasisIndex D.toSimpleGraph) :
    zigzagBasisMul G (zigzagComponentBasisIndexEquiv G ⟨C, b⟩)
      (zigzagComponentBasisIndexEquiv G ⟨D, c⟩) = none := by
  classical
  have hne (i : C) (j : D) : (i : V) ≠ j := by
    intro hij
    have hi : (i : V) ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C i.val).2 i.property
    have hj : (j : V) ∈ D.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff D j.val).2 j.property
    rw [hij] at hi
    exact (Set.disjoint_left.mp
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent G h)) hi hj
  rcases b with i | d | i <;> rcases c with j | e | j
  all_goals simp [SimpleGraph.Dart.ext_iff, Prod.ext_iff,
    hne, Ne.symm (hne _ _)]

/-- The complete multiplication table of the public zigzag algebra. Every
product of vertex, dart and volume basis vectors is either another basis
vector, with index prescribed by `zigzagBasisMul`, or zero. This includes
the square-zero volume at each isolated vertex. -/
@[simp]
theorem zigzagAlgebraBasis_mul (b c : ZigzagBasisIndex G) :
    zigzagAlgebraBasis k G b * zigzagAlgebraBasis k G c =
      (zigzagBasisMul G b c).elim 0 (zigzagAlgebraBasis k G) := by
  obtain ⟨⟨C, b'⟩, rfl⟩ := (zigzagComponentBasisIndexEquiv G).surjective b
  obtain ⟨⟨D, c'⟩, rfl⟩ := (zigzagComponentBasisIndexEquiv G).surjective c
  by_cases hCD : C = D
  · subst D
    rw [zigzagBasisMul_component]
    apply zigzagAlgebra.ext k G
    intro E
    rw [map_mul]
    by_cases hEC : E = C
    · subst E
      simp only [zigzagComponentProjection_zigzagAlgebraBasis]
      rw [zigzagComponentBasis_mul]
      cases hp : zigzagBasisMul C.toSimpleGraph b' c' with
      | none => simp
      | some d => simp
    · rw [zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k C E hEC b',
        zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k C E hEC c', zero_mul]
      cases hp : zigzagBasisMul C.toSimpleGraph b' c' with
      | none => simp
      | some d => simp [zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k C E hEC]
  · rw [zigzagBasisMul_eq_none_of_ne_component G hCD]
    apply zigzagAlgebra.ext k G
    intro E
    rw [map_mul]
    by_cases hEC : E = C
    · subst E
      rw [zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k D C hCD c',
        mul_zero]
      simp
    · rw [zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k C E hEC b', zero_mul]
      simp

end TauCeti
