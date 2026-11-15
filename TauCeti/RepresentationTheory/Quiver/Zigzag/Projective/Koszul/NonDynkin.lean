/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.NonDynkin
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Koszul.Bipartite
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.NonKoszul

/-!
# Koszul resolutions of zigzag simples for non-Dynkin graphs and the Koszulity dichotomy

Let `G` be a finite connected simple graph which is not a finite Dynkin diagram. The
Etingof--Eu theorem gives injective left Koszul differentials for the preprojective algebra of
every orientation of `G`, including when `G` is an affine or wild tree. Transport across the
signed--signless comparison for bipartite graphs, together with the direct construction for
graphs containing a cycle, then gives a linear graded projective resolution of every vertex
simple of the zigzag algebra of `G`.

Combined with the finite-ADE linear-resolution obstruction of
`TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.NonKoszul` and the finite/infinite
dichotomy of `TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.FiniteDimensional`, this
establishes the complete resolution-theoretic Koszulity classification for connected finite
simple graphs on at least two vertices: every graded vertex simple of `ZigzagAlgebra k G` admits
a linear graded projective resolution if and only if `G` is not isomorphic to the diagram of any
valid finite Dynkin type, and if and only if the preprojective (or signless preprojective)
algebra of `G` is infinite-dimensional.

## Main results

* `exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_not_exists_dynkinType_iso`:
  every graded vertex simple of a connected non-Dynkin zigzag algebra has a linear graded
  projective resolution.
* `forall_exists_isLinear_zigzagGradedSimple_iff`: **the Koszulity dichotomy for zigzag
  algebras**: for a connected finite simple graph on at least two vertices, every graded vertex
  simple is linearly resolved if and only if the graph is not a Dynkin diagram.
* `forall_exists_isLinear_zigzagGradedSimple_iff_forall_preprojectiveKoszulLeft_injective`,
  `forall_exists_isLinear_zigzagGradedSimple_iff_not_finiteDimensional_preprojective`, and
  `forall_exists_isLinear_zigzagGradedSimple_iff_not_finiteDimensional_signlessPreprojective`:
  equivalence of zigzag Koszulity with exactness of the preprojective Koszul complex and with
  infinite-dimensionality of the preprojective and signless preprojective algebras.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  J. Amer. Math. Soc. 9 (1996), Section 2.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246
  (2001), Section 3.
-/

public section

namespace TauCeti

open DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V} [Finite V]

/-- **Every vertex simple of a connected non-Dynkin zigzag algebra has a linear resolution.**
If `G` is not isomorphic to the diagram of any valid finite Dynkin type, then the graded simple
at every vertex has a linear graded projective resolution. This includes all connected
non-Dynkin trees as well as connected graphs containing a cycle. -/
theorem
exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_not_exists_dynkinType_iso
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) (v : V) :
    ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w}
      (zigzagIntegerGrade k G) (zigzagGradedSimple k G v).grading, r.IsLinear := by
  classical
  let _ : LinearOrder V := (Finite.equivFin V).linearOrder
  let o := Orientation.ofLinearOrder G
  exact
  exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_preprojectiveKoszulLeft_injective
    k hG.preconnected o
      (preprojectiveKoszulLeft_injective_of_not_exists_dynkinType_iso k hG hD o) v

/-- **The Koszulity dichotomy for zigzag algebras**: for a connected finite simple graph `G` on at
least two vertices, every graded vertex simple of `ZigzagAlgebra k G` admits a linear graded
projective resolution if and only if `G` is not isomorphic to the diagram of any valid Dynkin
type. -/
theorem forall_exists_isLinear_zigzagGradedSimple_iff [Nontrivial V] (hG : G.Connected) :
    (∀ v : V, ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w}
      (zigzagIntegerGrade k G) (zigzagGradedSimple k G v).grading, r.IsLinear) ↔
      ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) :=
  ⟨fun h ⟨_, ht, ⟨e⟩⟩ =>
    let ⟨v, hv⟩ := exists_not_exists_isLinear_zigzagGradedSimple_of_iso k ht e
    hv (h v),
   fun hD v =>
    exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_not_exists_dynkinType_iso
      k hG hD v⟩

/-- For a connected finite simple graph `G` on at least two vertices and any orientation `o` of `G`,
every graded vertex simple of `ZigzagAlgebra k G` admits a linear graded projective resolution if
and only if the left Koszul differential of `Π_k(OrientedQuiver G o)` is injective at every
vertex. -/
theorem forall_exists_isLinear_zigzagGradedSimple_iff_forall_preprojectiveKoszulLeft_injective
    [Nontrivial V] (hG : G.Connected) (o : Orientation G) :
    (∀ v : V, ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w}
      (zigzagIntegerGrade k G) (zigzagGradedSimple k G v).grading, r.IsLinear) ↔
      ∀ v : OrientedQuiver G o, Function.Injective (preprojectiveKoszulLeft k v) := by
  rw [forall_exists_isLinear_zigzagGradedSimple_iff k hG,
    forall_preprojectiveKoszulLeft_injective_iff k hG o]

/-- For a connected finite simple graph `G` on at least two vertices and any orientation `o` of `G`,
every graded vertex simple of `ZigzagAlgebra k G` admits a linear graded projective resolution if
and only if the preprojective algebra `Π_k(OrientedQuiver G o)` is infinite-dimensional. -/
theorem forall_exists_isLinear_zigzagGradedSimple_iff_not_finiteDimensional_preprojective
    [Nontrivial V] (hG : G.Connected) (o : Orientation G) :
    (∀ v : V, ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w}
      (zigzagIntegerGrade k G) (zigzagGradedSimple k G v).grading, r.IsLinear) ↔
      ¬ FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  rw [forall_exists_isLinear_zigzagGradedSimple_iff k hG,
    finiteDimensional_preprojectiveAlgebra_orientedQuiver_iff k hG o]

/-- For a connected finite simple graph `G` on at least two vertices, every graded vertex simple of
`ZigzagAlgebra k G` admits a linear graded projective resolution if and only if the signless
preprojective algebra of `DoubledQuiver G` is infinite-dimensional. -/
theorem forall_exists_isLinear_zigzagGradedSimple_iff_not_finiteDimensional_signlessPreprojective
    [Nontrivial V] [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    (∀ v : V, ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w}
      (zigzagIntegerGrade k G) (zigzagGradedSimple k G v).grading, r.IsLinear) ↔
      ¬ FiniteDimensional k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  rw [forall_exists_isLinear_zigzagGradedSimple_iff k hG,
    finiteDimensional_signlessPreprojectiveAlgebra_iff k hG]

end TauCeti
