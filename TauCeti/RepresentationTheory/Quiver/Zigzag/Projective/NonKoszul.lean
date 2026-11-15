/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.LinearResolution

/-!
# The linear-resolution obstruction for finite ADE zigzag algebras

For a finite simple graph without isolated vertices, finite-dimensionality of the preprojective
algebra of an orientation forces a negative coefficient in the inverse graded Cartan matrix of
the zigzag algebra. A linear projective resolution of every graded vertex simple would make all
these coefficients nonnegative. Hence at least one vertex simple has no linear graded projective
resolution.

Applied to any finite graph on at least two vertices isomorphic to a valid Dynkin diagram, this
proves the non-Koszul half of the finite-ADE classification in the resolution-theoretic form: not
every graded vertex simple is linearly resolved. The rank-one zigzag convention is deliberately
excluded because its generator has degree two and it is not the quadratic presentation used here.

## Main results

* `TauCeti.exists_not_exists_isLinear_zigzagGradedSimple_of_finiteDimensional_preprojective`: a
  finite-dimensional preprojective algebra obstructs linear resolutions of zigzag vertex simples.
* `TauCeti.exists_not_exists_isLinear_zigzagGradedSimple_of_iso`: every finite graph on at least
  two vertices isomorphic to a valid Dynkin diagram has a vertex simple without a linear graded
  projective resolution.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  J. Amer. Math. Soc. 9 (1996), Sections 1.2 and 2.11.
* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), Sections 3 and 4.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*,
  Math. Res. Lett. 14 (2007), Sections 2 and 3.
-/

public section

namespace TauCeti

open DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V}
  [Finite V] [Nonempty V]

/-- **A finite-dimensional preprojective algebra obstructs linear resolutions of zigzag
simples.** If some orientation of a nonempty finite graph without isolated vertices has a
finite-dimensional preprojective algebra, then at least one graded vertex simple of the zigzag
algebra has no linear graded projective resolution. -/
theorem exists_not_exists_isLinear_zigzagGradedSimple_of_finiteDimensional_preprojective
    (hns : ∀ i : V, ∃ j, G.Adj i j) (o : Orientation G)
    [FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver G o))] :
    ∃ v : V, ¬ ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w}
      (zigzagIntegerGrade k G) (zigzagGradedSimple k G v).grading, r.IsLinear := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨n, u, v, hneg⟩ :=
    exists_coeff_inv_zigzagGradedCartanMatrix_map_aeval_neg_X_lt_zero k hns o
  refine ⟨v, fun hlinear => ?_⟩
  have hnonneg :=
    coeff_inv_zigzagGradedCartanMatrix_map_aeval_neg_X_nonneg hns v hlinear n u
  omega

/-- **Every finite graph on at least two vertices isomorphic to a valid Dynkin diagram has a
zigzag vertex simple without a linear resolution.** -/
theorem exists_not_exists_isLinear_zigzagGradedSimple_of_iso {V : Type u} {G : SimpleGraph V}
    [Finite V] [Nontrivial V] {t : DynkinType} (ht : t.Valid)
    (e : G ≃g diagramGraph t.cartanMatrix) :
    ∃ v : V, ¬ ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w}
      (zigzagIntegerGrade k G) (zigzagGradedSimple k G v).grading, r.IsLinear := by
  classical
  have hconn : G.Connected :=
    e.connected_iff.mpr (DynkinType.connected_diagramGraph_cartanMatrix ht)
  have hns (i : V) : ∃ j, G.Adj i j := hconn.preconnected.exists_adj_of_nontrivial i
  let _ : LinearOrder V := (Finite.equivFin V).linearOrder
  let o := Orientation.ofLinearOrder G
  have _ := finiteDimensional_preprojectiveAlgebra_of_iso k e o
  exact exists_not_exists_isLinear_zigzagGradedSimple_of_finiteDimensional_preprojective k hns o

end TauCeti
