/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Sinkless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# Preprojective Hilbert series as inverse zigzag Cartan matrices

Let `Π = Π_k(Q)` be the preprojective algebra of a finite quiver `Q` over a field `k`, with matrix
Hilbert series `H(t)` (`TauCeti.preprojectiveHilbertSeries`), and let `A` be the arrow-count matrix
of the doubled quiver. By `TauCeti.mul_preprojectiveHilbertSeries_eq_one_iff`, the identity
`((1 + t²) I - t A) H(t) = I` holds exactly when the Koszul complexes of the vertex modules are
projective resolutions. When `Q` has no sinks, they are
(`TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff`), so

```text
H(t) = ((1 + t²) I - t A)⁻¹
```

in the ring of matrices of formal power series, and the dimensions of the graded corners obey the
recursion `dim e_v Π_{m+2} e_i + dim e_v Π_m e_i = ∑_w #(w ⟶ v) dim e_w Π_{m+1} e_i`.

When `Q` is an orientation of a finite simple graph `G` without isolated vertices, `A` is the
adjacency matrix of `G`, so `(1 + t²) I - t A` is the graded Cartan matrix
`C_G(q) = (1 + q²) I + q A_G` of the zigzag algebra of `G` (`TauCeti.zigzagGradedCartanMatrix`)
evaluated at `q = -t`. This compares the inverse quantum Cartan matrix of the zigzag algebra, in the
power-series completion, with the graded dimensions of the preprojective algebra, which is its
quadratic dual for bipartite `G`:

```text
H_{Π(Q)}(t) = C_G(-t)⁻¹.
```

It holds for every orientation of `G` at which every Koszul complex is a resolution, and this file
proves it unconditionally for every orientation without sinks. A connected graph has an orientation
without sinks exactly when it is not a tree, so the non-Dynkin trees, such as `D~ₙ` and `E₆~`,
`E₇~`, `E₈~`, are covered only through the conditional form.

## Main results

* `TauCeti.sum_card_mul_finrank_preprojectiveCorner_eq`: for a quiver without sinks, the dimension
  recursion of the graded corners holds in every degree.
* `TauCeti.mul_preprojectiveHilbertSeries_eq_one` and
  `TauCeti.preprojectiveHilbertSeries_eq_inv`: for a quiver without sinks,
  `H(t) = ((1 + t²) I - t A)⁻¹`.
* `TauCeti.zigzagGradedCartanMatrix_map_aeval_neg_X_mul_preprojectiveHilbertSeries_eq_one_iff`:
  for an orientation of a graph without isolated vertices, `C_G(-t) H(t) = I` exactly when every
  Koszul complex of the preprojective algebra is a resolution.
* `TauCeti.preprojectiveHilbertSeries_eq_inv_zigzagGradedCartanMatrix_map_aeval_neg_X`: **for an
  orientation without sinks, `H_{Π(Q)}(t) = C_G(-t)⁻¹`.**

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the Hilbert series `H(t) = ((1 + t²) I - t A)⁻¹` of
  the preprojective algebra of a non-Dynkin quiver.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246
  (2001), for the graded Cartan matrix of the zigzag algebra and its quadratic dual.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra PowerSeries

universe u v w

section Quiver

variable (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)] (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w))
include hQ

/-- **The dimension recursion for a quiver without sinks.** If every vertex of `Q` is the tail of an
arrow, then for all vertices `i` and `v` and every degree `m`,

```text
∑_w #(w ⟶ v) dim e_w Π_{m+1} e_i = dim e_v Π_{m+2} e_i + dim e_v Π_m e_i,
```

the sum running over the vertices `w` of the doubled quiver. -/
theorem sum_card_mul_finrank_preprojectiveCorner_eq (m : ℕ) (i : Symmetrify Q) (v : Q) :
    ∑ w : Symmetrify Q, Fintype.card (w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (preprojectiveCorner k Q (m + 1) i w) =
        Module.finrank k (preprojectiveCorner k Q (m + 2) i (Symmetrify.of.obj v)) +
          Module.finrank k (preprojectiveCorner k Q m i (Symmetrify.of.obj v)) :=
  (sum_card_mul_finrank_preprojectiveCorner_eq_iff k Q m i v).2 fun _ hy =>
    (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff k hQ v (by
      rw [doubledVertexIdempotent_def]
      exact preprojectiveMk_vertexIdempotent_mul_of_mem_preprojectiveCorner hy)).1

variable [DecidableEq Q]

/-- **The Hilbert series identity for a quiver without sinks.** If every vertex of `Q` is the tail
of an arrow and `A_{v,w} = #(w ⟶ v)` is the arrow-count matrix of the doubled quiver, then
`((1 + X²) I - X A) H = I` for the matrix Hilbert series `H` of `Π`. -/
theorem mul_preprojectiveHilbertSeries_eq_one :
    (((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix Q Q ℤ⟦X⟧) -
        (X : ℤ⟦X⟧) • Matrix.of fun v w : Q =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧)) *
        preprojectiveHilbertSeries k Q = 1 :=
  (mul_preprojectiveHilbertSeries_eq_one_iff k Q).2 fun v _ hy =>
    (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff k hQ v hy).1

/-- **The Hilbert series of the preprojective algebra of a quiver without sinks** is the inverse
matrix `H = ((1 + X²) I - X A)⁻¹`, for `A_{v,w} = #(w ⟶ v)` the arrow-count matrix of the doubled
quiver. -/
theorem preprojectiveHilbertSeries_eq_inv :
    preprojectiveHilbertSeries k Q =
      (((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix Q Q ℤ⟦X⟧) -
        (X : ℤ⟦X⟧) • Matrix.of fun v w : Q =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧))⁻¹ :=
  (Matrix.inv_eq_right_inv (mul_preprojectiveHilbertSeries_eq_one k hQ)).symm

end Quiver

section Graph

open DoubledQuiver

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V} (o : Orientation G)

/-- **Over a graph without isolated vertices, the zigzag graded Cartan matrix at `q = -X` is the
denominator of the preprojective Hilbert series** of any orientation, read through the
identification of the vertices of the oriented quiver with those of `G`. -/
private theorem zigzagGradedCartanMatrix_map_aeval_neg_X_eq_submatrix [Finite V]
    [DecidableEq (OrientedQuiver G o)] (hns : ∀ i : V, ∃ j, G.Adj i j) :
    (zigzagGradedCartanMatrix k G).map (Polynomial.aeval (-X : ℤ⟦X⟧)) =
      (((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix (OrientedQuiver G o) (OrientedQuiver G o) ℤ⟦X⟧) -
        (X : ℤ⟦X⟧) • Matrix.of fun v w : OrientedQuiver G o =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧)).submatrix
        (OrientedQuiver.vertexEquiv G o) (OrientedQuiver.vertexEquiv G o) := by
  classical
  refine Matrix.ext fun v w => ?_
  rw [Matrix.map_apply, zigzagGradedCartanMatrix_apply k G hns, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.of_apply]
  simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [OrientedQuiver.vertexEquiv_apply, OrientedQuiver.vertexEquiv_apply,
    OrientedQuiver.card_symmetrify_hom, G.adj_comm w v]
  split_ifs <;> simp [sub_eq_add_neg]

/-- **The inverse quantum Cartan comparison, conditionally.** Let `G` be a finite simple graph
without isolated vertices, `o` an orientation of `G`, and `H` the matrix Hilbert series of the
preprojective algebra of the oriented quiver, indexed by the vertices of `G`. Then the zigzag graded
Cartan matrix `C_G(q) = (1 + q²) I + q A_G` evaluated at `q = -X` satisfies `C_G(-X) H = I` exactly
when at every vertex `v` the only `y ∈ e_v Π` killed by the reverse `b*` of every arrow `b` of the
doubled quiver into `v` is `0`, that is, exactly when every Koszul complex of `Π` is a projective
resolution. -/
theorem zigzagGradedCartanMatrix_map_aeval_neg_X_mul_preprojectiveHilbertSeries_eq_one_iff
    [Fintype V] [DecidableEq V] (hns : ∀ i : V, ∃ j, G.Adj i j) :
    (zigzagGradedCartanMatrix k G).map (Polynomial.aeval (-X : ℤ⟦X⟧)) *
        (preprojectiveHilbertSeries k (OrientedQuiver G o)).submatrix
          (OrientedQuiver.vertex G o) (OrientedQuiver.vertex G o) = 1 ↔
      ∀ (v : OrientedQuiver G o) (y : preprojectiveAlgebra k (OrientedQuiver G o)),
        preprojectiveMk k (OrientedQuiver G o) (doubledVertexIdempotent k v) * y = y →
          (∀ (w : Symmetrify (OrientedQuiver G o)) (b : w ⟶ Symmetrify.of.obj v),
            preprojectiveMk k (OrientedQuiver G o) (ofArrow (Quiver.reverse b)) * y = 0) →
              y = 0 := by
  classical
  have he : OrientedQuiver.vertex G o = ⇑(OrientedQuiver.vertexEquiv G o) :=
    funext fun v => (OrientedQuiver.vertexEquiv_apply G o v).symm
  rw [← mul_preprojectiveHilbertSeries_eq_one_iff,
    zigzagGradedCartanMatrix_map_aeval_neg_X_eq_submatrix k o hns, he, Matrix.submatrix_mul_equiv,
    ← Matrix.submatrix_one_equiv (OrientedQuiver.vertexEquiv G o)]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  -- Reindexing back along the inverse equivalence recovers the matrices over the oriented quiver.
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] using
    congrArg (fun M => M.submatrix (OrientedQuiver.vertexEquiv G o).symm
      (OrientedQuiver.vertexEquiv G o).symm) h

variable (hQ : ∀ u : OrientedQuiver G o, ∃ w, Nonempty (u ⟶ w))
include hQ

/-- **The inverse quantum Cartan comparison for an orientation without sinks.** If `o` orients
the finite simple graph `G` so that every vertex is the tail of an arrow, then the zigzag graded
Cartan matrix of `G` evaluated at `q = -X` is a left inverse of the matrix Hilbert series of the
preprojective algebra of the oriented quiver: `C_G(-X) H = I`. -/
theorem zigzagGradedCartanMatrix_map_aeval_neg_X_mul_preprojectiveHilbertSeries_eq_one
    [Fintype V] [DecidableEq V] :
    (zigzagGradedCartanMatrix k G).map (Polynomial.aeval (-X : ℤ⟦X⟧)) *
        (preprojectiveHilbertSeries k (OrientedQuiver G o)).submatrix
          (OrientedQuiver.vertex G o) (OrientedQuiver.vertex G o) = 1 := by
  -- The outgoing arrow at each vertex crosses an edge, so no vertex of `G` is isolated.
  have hns (i : V) : ∃ j, G.Adj i j := by
    obtain ⟨j, ⟨a⟩⟩ := hQ (OrientedQuiver.vertex G o i)
    obtain ⟨j, rfl⟩ := (OrientedQuiver.vertexEquiv G o).surjective j
    rw [OrientedQuiver.vertexEquiv_apply] at a
    obtain ⟨h, -, -⟩ := OrientedQuiver.exists_eq_arrow G o a
    exact ⟨j, h⟩
  exact (zigzagGradedCartanMatrix_map_aeval_neg_X_mul_preprojectiveHilbertSeries_eq_one_iff k o
    hns).2 fun v _ hy => (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff k hQ v hy).1

/-- **The Hilbert series of a preprojective algebra is the inverse zigzag Cartan matrix at
`q = -X`.** If `o` orients the finite simple graph `G` so that every vertex is the tail of an
arrow, then the matrix Hilbert series of the preprojective algebra of the oriented quiver,
indexed by the vertices of `G`, is `H(X) = C_G(-X)⁻¹`, where `C_G(q) = (1 + q²) I + q A_G` is the
graded Cartan matrix of the zigzag algebra of `G`. -/
theorem preprojectiveHilbertSeries_eq_inv_zigzagGradedCartanMatrix_map_aeval_neg_X
    [Fintype V] [DecidableEq V] :
    (preprojectiveHilbertSeries k (OrientedQuiver G o)).submatrix
        (OrientedQuiver.vertex G o) (OrientedQuiver.vertex G o) =
      ((zigzagGradedCartanMatrix k G).map (Polynomial.aeval (-X : ℤ⟦X⟧)))⁻¹ :=
  (Matrix.inv_eq_right_inv
    (zigzagGradedCartanMatrix_map_aeval_neg_X_mul_preprojectiveHilbertSeries_eq_one k o hQ)).symm

end Graph

end TauCeti
