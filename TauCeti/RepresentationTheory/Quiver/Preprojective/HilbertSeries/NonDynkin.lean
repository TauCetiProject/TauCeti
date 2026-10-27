/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.ZigzagCartan
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.NonDynkin

/-!
# Preprojective Hilbert series of non-Dynkin graphs as inverse zigzag Cartan matrices

Let `G` be a connected finite simple graph which is not a Dynkin diagram, `o` any orientation of
`G` and `H(t)` the matrix Hilbert series of the preprojective algebra `Π_k(Q)` of the oriented
quiver over a field `k`, indexed by the vertices of `G`. The oriented quiver carries a positive
weight which is superadditive on its underlying multigraph
(`TauCeti.exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso`, in
`Koszul/NonDynkin.lean`), so by the theorem of Etingof and Eu the weighted inverse quantum Cartan
comparison of `HilbertSeries/ZigzagCartan.lean` holds unconditionally:

```text
H_{Π(Q)}(t) = C_G(-t)⁻¹,
```

where `C_G(q) = (1 + q²) I + q A_G` is the graded Cartan matrix of the zigzag algebra of `G`. This
is an identity in the ring of matrices of formal power series over `ℤ`. It covers the non-Dynkin
trees, such as `D~ₙ`, `E₆~`, `E₇~` and `E₈~`, which have no orientation without sinks, together
with every connected graph containing a cycle. For a finite simply-laced Dynkin diagram with at
least two vertices the comparison fails: the preprojective algebra is finite-dimensional and
`C_G(-t)⁻¹` has a negative coefficient
(`TauCeti.exists_coeff_inv_zigzagGradedCartanMatrix_map_aeval_neg_X_lt_zero`).

## Main results

* `C_G(-t) H(t) = I` for every orientation of a connected non-Dynkin graph:
  `zigzagGradedCartanMatrix_mul_preprojectiveHilbertSeries_eq_one_of_not_exists_dynkinType_iso`.
* **`H_{Π(Q)}(t) = C_G(-t)⁻¹` for every orientation of a connected non-Dynkin graph:**
  `preprojectiveHilbertSeries_eq_inv_zigzagGradedCartanMatrix_of_not_exists_dynkinType_iso`.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the Hilbert series of the preprojective algebra of
  a non-Dynkin quiver.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246
  (2001), for the graded Cartan matrix of the zigzag algebra.
-/

public section

namespace TauCeti

open _root_.Quiver PowerSeries DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  (hG : G.Connected)
  (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
  (o : Orientation G)

include hG hD

/-- **The inverse quantum Cartan comparison for a connected non-Dynkin graph.** For every
orientation `o` of a connected finite simple graph `G` which is not a Dynkin diagram, the zigzag
graded Cartan matrix `C_G(q) = (1 + q²) I + q A_G` evaluated at `q = -X` is a left inverse of the
matrix Hilbert series of the preprojective algebra of the oriented quiver, indexed by the vertices
of `G`. -/
theorem
zigzagGradedCartanMatrix_mul_preprojectiveHilbertSeries_eq_one_of_not_exists_dynkinType_iso :
    (zigzagGradedCartanMatrix k G).map (Polynomial.aeval (-X : ℤ⟦X⟧)) *
        (preprojectiveHilbertSeries k (OrientedQuiver G o)).submatrix
          (OrientedQuiver.vertex G o) (OrientedQuiver.vertex G o) = 1 := by
  obtain ⟨δ, hδ, hδle⟩ :=
    exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso hG hD o
  exact
    zigzagGradedCartanMatrix_map_aeval_neg_X_mul_preprojectiveHilbertSeries_eq_one_of_two_mul_le_sum
      k o hδ hδle

/-- **The Hilbert series of the preprojective algebra of a connected non-Dynkin graph is the
inverse zigzag Cartan matrix at `q = -X`.** For every orientation `o` of a connected finite simple
graph `G` which is not a Dynkin diagram, the matrix Hilbert series of the preprojective algebra of
the oriented quiver over any field, indexed by the vertices of `G`, is `H(X) = C_G(-X)⁻¹`, where
`C_G(q) = (1 + q²) I + q A_G` is the graded Cartan matrix of the zigzag algebra of `G`. This
includes the non-Dynkin trees, whose orientations all have sinks. -/
theorem
preprojectiveHilbertSeries_eq_inv_zigzagGradedCartanMatrix_of_not_exists_dynkinType_iso :
    (preprojectiveHilbertSeries k (OrientedQuiver G o)).submatrix
        (OrientedQuiver.vertex G o) (OrientedQuiver.vertex G o) =
      ((zigzagGradedCartanMatrix k G).map (Polynomial.aeval (-X : ℤ⟦X⟧)))⁻¹ := by
  obtain ⟨δ, hδ, hδle⟩ :=
    exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso hG hD o
  exact
    preprojectiveHilbertSeries_eq_inv_zigzagGradedCartanMatrix_map_aeval_neg_X_of_two_mul_le_sum
      k o hδ hδle

end TauCeti
