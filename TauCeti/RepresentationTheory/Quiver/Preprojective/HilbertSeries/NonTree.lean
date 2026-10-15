/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.ZigzagCartan
public import TauCeti.RepresentationTheory.Quiver.Preprojective.NonTree

/-!
# Hilbert series for every orientation of a graph containing a cycle

For a finite preconnected simple graph containing a cycle, every orientation has exact
vertex Koszul complexes and linear graded projective resolutions. Consequently its
preprojective matrix Hilbert series is the inverse of `(1 + X²) I - X A`, where `A` is
the adjacency matrix. The chosen orientation can have sinks: these statements use
orientation-independent injectivity from
`TauCeti.RepresentationTheory.Quiver.Preprojective.NonTree`.

The homogeneous corner dimensions satisfy the resulting second-order recursion.
Reindexing by the vertices of the graph identifies the denominator with the zigzag
graded Cartan matrix at `q = -X`. This is an identity of formal power series, with no
claim about a finite Ext-Euler pairing. Non-Dynkin trees are not covered.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*,
  Math. Res. Lett. 14 (2007), Sections 2 and 3.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*,
  J. Algebra 246 (2001), for the zigzag graded Cartan matrix.
-/

public section

namespace TauCeti

open _root_.Quiver PowerSeries DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V}
  (hG : G.Preconnected) (hc : ¬G.IsAcyclic) (o : Orientation G)

include hG hc

section Finite

variable [Finite V]

/-- The homogeneous corner dimensions of every orientation of a finite preconnected graph
containing a cycle obey the preprojective Hilbert-series recursion. The middle sum counts
arrows of the doubled quiver, independently of the direction of the original arrows. -/
theorem sum_card_mul_finrank_preprojectiveCorner_eq_of_not_isAcyclic
    (m : ℕ) (i : Symmetrify (OrientedQuiver G o)) (v : OrientedQuiver G o) :
    ∑ w : Symmetrify (OrientedQuiver G o),
        Fintype.card (w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (preprojectiveCorner k (OrientedQuiver G o) (m + 1) i w) =
      Module.finrank k
          (preprojectiveCorner k (OrientedQuiver G o) (m + 2) i (Symmetrify.of.obj v)) +
        Module.finrank k
          (preprojectiveCorner k (OrientedQuiver G o) m i (Symmetrify.of.obj v)) :=
  (sum_card_mul_finrank_preprojectiveCorner_eq_iff k (OrientedQuiver G o) m i v).2
    fun _ hy =>
      (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_not_isAcyclic k hG hc o v
        (by
          rw [doubledVertexIdempotent_def]
          exact preprojectiveMk_vertexIdempotent_mul_of_mem_preprojectiveCorner hy)).1

variable [DecidableEq (OrientedQuiver G o)]

/-- For every orientation of a finite preconnected graph containing a cycle,
`((1 + X²) I - X A) H = I`, where `A` counts doubled arrows and `H` is the matrix
Hilbert series of the preprojective algebra. -/
theorem mul_preprojectiveHilbertSeries_eq_one_of_not_isAcyclic :
    (((1 : ℤ⟦X⟧) + X ^ 2) •
        (1 : Matrix (OrientedQuiver G o) (OrientedQuiver G o) ℤ⟦X⟧) -
      (X : ℤ⟦X⟧) • Matrix.of fun v w : OrientedQuiver G o =>
        (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧)) *
      preprojectiveHilbertSeries k (OrientedQuiver G o) = 1 :=
  (mul_preprojectiveHilbertSeries_eq_one_iff k (OrientedQuiver G o)).2 fun v _ hy =>
    (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_not_isAcyclic k hG hc o v hy).1

/-- The preprojective matrix Hilbert series of every orientation of a finite preconnected
graph containing a cycle is `((1 + X²) I - X A)⁻¹`. This formula holds over every field,
including characteristic two. -/
theorem preprojectiveHilbertSeries_eq_inv_of_not_isAcyclic :
    preprojectiveHilbertSeries k (OrientedQuiver G o) =
      (((1 : ℤ⟦X⟧) + X ^ 2) •
          (1 : Matrix (OrientedQuiver G o) (OrientedQuiver G o) ℤ⟦X⟧) -
        (X : ℤ⟦X⟧) • Matrix.of fun v w : OrientedQuiver G o =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧))⁻¹ :=
  (Matrix.inv_eq_right_inv
    (mul_preprojectiveHilbertSeries_eq_one_of_not_isAcyclic k hG hc o)).symm

end Finite

/-- For every orientation of a finite preconnected graph containing a cycle, the matrix
Hilbert series of its preprojective algebra, indexed by graph vertices, is the inverse
zigzag graded Cartan matrix at `q = -X`. The orientation may have sinks. -/
theorem preprojectiveHilbertSeries_eq_inv_zigzagGradedCartanMatrix_map_aeval_neg_X_of_not_isAcyclic
    [Fintype V] [DecidableEq V] :
    (preprojectiveHilbertSeries k (OrientedQuiver G o)).submatrix
        (OrientedQuiver.vertex G o) (OrientedQuiver.vertex G o) =
      ((zigzagGradedCartanMatrix k G).map (Polynomial.aeval (-X : ℤ⟦X⟧)))⁻¹ := by
  obtain ⟨f, hf⟩ := hG.exists_forall_adj_and_apply_apply_ne_of_not_isAcyclic hc
  apply (Matrix.inv_eq_right_inv ?_).symm
  exact (zigzagGradedCartanMatrix_map_aeval_neg_X_mul_preprojectiveHilbertSeries_eq_one_iff
    k o (fun i => ⟨f i, (hf i).1⟩)).2 fun v _ hy =>
      (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_not_isAcyclic k hG hc o v hy).1

end TauCeti
