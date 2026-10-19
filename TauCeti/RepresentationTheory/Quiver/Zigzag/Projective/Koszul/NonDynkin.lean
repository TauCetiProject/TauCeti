/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.NonDynkin
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Koszul.Bipartite

/-!
# Koszul resolutions of zigzag simples for non-Dynkin graphs

Let `G` be a finite connected simple graph which is not a finite Dynkin diagram. The
Etingof--Eu theorem gives injective left Koszul differentials for the preprojective algebra of
every orientation of `G`, including when `G` is an affine or wild tree. Transport across the
signed--signless comparison for bipartite graphs, together with the direct construction for
graphs containing a cycle, then gives a linear graded projective resolution of every vertex
simple of the zigzag algebra of `G`.

This completes the positive half of the classical Koszulity classification of finite connected
zigzag algebras in its resolution-theoretic form. The finite ADE obstruction is
`TauCeti.exists_not_exists_isLinear_zigzagGradedSimple_of_isSimplyLaced`.

## Main result

* The main theorem below gives every graded vertex simple of a connected non-Dynkin zigzag
  algebra a linear projective resolution.

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

end TauCeti
