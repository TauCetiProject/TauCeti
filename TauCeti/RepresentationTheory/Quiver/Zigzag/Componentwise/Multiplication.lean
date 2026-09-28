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

open Classical in
/-- The index of a product of two vertex--dart--volume basis elements, or
`none` when the table gives zero. The left factor is traversed second. -/
noncomputable def zigzagBasisProduct : ZigzagBasisIndex G → ZigzagBasisIndex G →
    Option (ZigzagBasisIndex G)
  | .inl i, .inl j => if i = j then some (.inl i) else none
  | .inl i, .inr (.inl d) => if i = d.snd then some (.inr (.inl d)) else none
  | .inl i, .inr (.inr j) => if i = j then some (.inr (.inr j)) else none
  | .inr (.inl d), .inl i => if i = d.fst then some (.inr (.inl d)) else none
  | .inr (.inl d), .inr (.inl e) =>
      if e = d.symm then some (.inr (.inr d.snd)) else none
  | .inr (.inl _), .inr (.inr _) => none
  | .inr (.inr i), .inl j => if i = j then some (.inr (.inr i)) else none
  | .inr (.inr _), .inr (.inl _) => none
  | .inr (.inr _), .inr (.inr _) => none

variable (k : Type w) [CommRing k] [Finite V]

/-- The multiplication table in a connected component with an edge is the
path-quotient table, transported along the component presentation. -/
private theorem componentBasis_mul_nontrivial (C : G.ConnectedComponent) [Nontrivial C]
    (b c : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentBasis k G C b * zigzagComponentBasis k G C c =
      (zigzagBasisProduct C.toSimpleGraph b c).elim 0 (zigzagComponentBasis k G C) := by
  let hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i =>
    SimpleGraph.exists_adj_iff_not_isIsolated.mpr
      (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
  apply (zigzagComponentAlgebraEquivNonisolated k G C).injective
  rw [map_mul]
  simp only [zigzagComponentAlgebraEquivNonisolated_zigzagComponentBasis k G C hns]
  rcases b with i | d | i <;> rcases c with j | e | j
  all_goals simp only [zigzagBasisProduct]
  all_goals try split_ifs
  all_goals simp only [Option.elim_some, Option.elim_none, map_zero,
    zigzagComponentAlgebraEquivNonisolated_zigzagComponentBasis k G C hns,
    zigzagBasis_apply, zigzagBasisFun_inl, zigzagBasisFun_inr_inl,
    zigzagBasisFun_inr_inr]
  all_goals try subst_vars
  all_goals first
    | exact zigzagMk_vertexIdempotent_mul_self k C.toSimpleGraph _
    | exact zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k C.toSimpleGraph
        (by assumption)
    | exact zigzagMk_vertexIdempotent_mul_ofArrow k C.toSimpleGraph _
    | exact zigzagMk_vertexIdempotent_mul_ofArrow_of_ne k C.toSimpleGraph _
        (by assumption)
    | exact zigzagMk_ofArrow_mul_vertexIdempotent k C.toSimpleGraph _
    | exact zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k C.toSimpleGraph _
        (by assumption)
    | exact zigzagMk_vertexIdempotent_mul_zigzagVolume k C.toSimpleGraph _
    | exact zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k C.toSimpleGraph
        (by assumption)
    | exact zigzagVolume_mul_zigzagMk_vertexIdempotent k C.toSimpleGraph _
    | exact zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k C.toSimpleGraph
        (by assumption)
    | exact zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k C.toSimpleGraph
        (Ne.symm (by assumption))
    | exact zigzagMk_ofArrow_mul_ofArrow_symm k C.toSimpleGraph _
    | exact zigzagMk_ofArrow_mul_ofArrow_of_ne k C.toSimpleGraph (by assumption)
    | exact zigzagMk_ofArrow_mul_zigzagVolume k C.toSimpleGraph _ _
    | exact zigzagVolume_mul_zigzagMk_ofArrow k C.toSimpleGraph _ _
    | exact zigzagVolume_mul_zigzagVolume k C.toSimpleGraph _ _

/-- The multiplication table on a singleton component is the dual-number
table, with the volume vector identified with the infinitesimal generator. -/
private theorem componentBasis_mul_subsingleton (C : G.ConnectedComponent) [Subsingleton C]
    (b c : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentBasis k G C b * zigzagComponentBasis k G C c =
      (zigzagBasisProduct C.toSimpleGraph b c).elim 0 (zigzagComponentBasis k G C) := by
  have noDart (d : C.toSimpleGraph.Dart) : False :=
    C.toSimpleGraph.ne_of_adj d.adj (Subsingleton.elim _ _)
  rcases b with i | d | i
  · rcases c with j | e | j
    · have hij : i = j := Subsingleton.elim _ _
      subst j
      apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
      simp [zigzagBasisProduct]
    · exact (noDart e).elim
    · have hij : i = j := Subsingleton.elim _ _
      subst j
      apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
      simp [zigzagBasisProduct]
  · exact (noDart d).elim
  · rcases c with j | e | j
    · have hij : i = j := Subsingleton.elim _ _
      subst j
      apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
      simp [zigzagBasisProduct]
    · exact (noDart e).elim
    · apply (zigzagComponentAlgebraEquivULiftDualNumber k G C).injective
      simp only [zigzagBasisProduct, Option.elim_none, map_mul, map_zero,
        zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inr_inr]
      apply ULift.ext
      exact DualNumber.eps_mul_eps

/-- Multiplication of basis vectors in any connected-component factor, including
the singleton dual-number factors. -/
@[simp]
theorem zigzagComponentBasis_mul (C : G.ConnectedComponent)
    (b c : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagComponentBasis k G C b * zigzagComponentBasis k G C c =
      (zigzagBasisProduct C.toSimpleGraph b c).elim 0 (zigzagComponentBasis k G C) := by
  rcases subsingleton_or_nontrivial C with hC | hC
  · exact componentBasis_mul_subsingleton G k C b c
  · exact componentBasis_mul_nontrivial G k C b c

omit [Finite V] in
private theorem zigzagBasisProduct_component (C : G.ConnectedComponent)
    (b c : ZigzagBasisIndex C.toSimpleGraph) :
    zigzagBasisProduct G (zigzagComponentBasisIndexEquiv G ⟨C, b⟩)
        (zigzagComponentBasisIndexEquiv G ⟨C, c⟩) =
      (zigzagBasisProduct C.toSimpleGraph b c).map
        (fun d => zigzagComponentBasisIndexEquiv G ⟨C, d⟩) := by
  classical
  rcases b with i | d | i <;> rcases c with j | e | j
  all_goals simp [zigzagBasisProduct, SimpleGraph.Dart.ext_iff, Prod.ext_iff]

omit [Finite V] in
private theorem component_vertices_ne {C D : G.ConnectedComponent} (h : C ≠ D)
    (i : C) (j : D) : (i : V) ≠ j := by
  intro hij
  apply h
  calc
    C = G.connectedComponentMk i.val := i.property.symm
    _ = G.connectedComponentMk j.val := congrArg (G.connectedComponentMk) hij
    _ = D := j.property

omit [Finite V] in
private theorem zigzagBasisProduct_ne_component {C D : G.ConnectedComponent} (h : C ≠ D)
    (b : ZigzagBasisIndex C.toSimpleGraph) (c : ZigzagBasisIndex D.toSimpleGraph) :
    zigzagBasisProduct G (zigzagComponentBasisIndexEquiv G ⟨C, b⟩)
      (zigzagComponentBasisIndexEquiv G ⟨D, c⟩) = none := by
  classical
  rcases b with i | d | i <;> rcases c with j | e | j
  all_goals simp [zigzagBasisProduct, SimpleGraph.Dart.ext_iff, Prod.ext_iff,
    component_vertices_ne G h, Ne.symm (component_vertices_ne G h _ _)]

/-- The complete multiplication table of the public zigzag algebra. Every
product of vertex, dart and volume basis vectors is either another basis
vector, with index prescribed by `zigzagBasisProduct`, or zero. This includes
the square-zero volume at each isolated vertex. -/
@[simp]
theorem zigzagAlgebraBasis_mul (b c : ZigzagBasisIndex G) :
    zigzagAlgebraBasis k G b * zigzagAlgebraBasis k G c =
      (zigzagBasisProduct G b c).elim 0 (zigzagAlgebraBasis k G) := by
  obtain ⟨⟨C, b'⟩, rfl⟩ := (zigzagComponentBasisIndexEquiv G).surjective b
  obtain ⟨⟨D, c'⟩, rfl⟩ := (zigzagComponentBasisIndexEquiv G).surjective c
  by_cases hCD : C = D
  · subst D
    rw [zigzagBasisProduct_component]
    apply zigzagAlgebra.ext k G
    intro E
    rw [map_mul]
    by_cases hEC : E = C
    · subst E
      simp only [zigzagComponentProjection_zigzagAlgebraBasis]
      rw [zigzagComponentBasis_mul]
      cases hp : zigzagBasisProduct C.toSimpleGraph b' c' with
      | none => simp
      | some d => simp
    · rw [zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k C E hEC b',
        zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k C E hEC c', zero_mul]
      cases hp : zigzagBasisProduct C.toSimpleGraph b' c' with
      | none => simp
      | some d => simp [zigzagComponentProjection_zigzagAlgebraBasis_of_ne G k C E hEC]
  · rw [zigzagBasisProduct_ne_component G hCD]
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
