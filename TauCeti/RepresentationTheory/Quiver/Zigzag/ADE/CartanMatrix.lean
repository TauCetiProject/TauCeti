/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix

/-!
# Graded Cartan matrices of the named ADE zigzag algebras

This file specializes the graded Cartan formula for zigzag algebras to the Bourbaki-labelled
`D₄` and `E₈` graphs and to the arm-labelled affine `E₈ = T_{2,3,6}` graph.  In each case the
matrix is

```text
(1 + q²) I + q A,
```

and the entrywise formulas below record the labels of every edge.  The specialization at `q = -1`
of the affine matrix is its generalized Cartan matrix.  This specialized integer matrix is
singular, with the affine marks as a null vector, although the determinant of the polynomial
matrix is nonzero (its value at `q = 0` is `1`).

## Main results

* `TauCeti.zigzagGradedCartanMatrix_D4_eq`,
  `TauCeti.zigzagGradedCartanMatrix_E8_eq`, and
  `TauCeti.zigzagGradedCartanMatrix_affineE8_eq`: the three named matrix formulas.
* `TauCeti.zigzagGradedCartanMatrix_D4_apply`,
  `TauCeti.zigzagGradedCartanMatrix_E8_apply`, and
  `TauCeti.zigzagGradedCartanMatrix_affineE8_apply`: their entries in the established node
  labellings.
* `TauCeti.zigzagGradedCartanMatrix_map_eval_neg_one_affineE8`: specialization to the graph
  Cartan matrix, which `TauCeti.AffineDynkinType.cartanMatrix_eq_graphCartanMatrix` identifies
  with the affine generalized Cartan matrix.
* `TauCeti.eval_neg_one_det_zigzagGradedCartanMatrix_affineE8` and
  `TauCeti.det_zigzagGradedCartanMatrix_affineE8_ne_zero`: the singular specialization and the
  nonzero polynomial determinant.

## References

The formula follows Huerfano--Khovanov, *A category for the adjoint representation*, Section 3,
and Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.  The affine
`E₈ = T_{2,3,6}` labelling and marks follow Kac, *Infinite dimensional Lie algebras*, Chapter 4.
-/

public section

namespace TauCeti

open Polynomial

private theorem exists_adj_zigzagD4Graph (i : Fin 4) :
    ∃ j, zigzagD4Graph.Adj i j :=
  SimpleGraph.exists_adj_iff_not_isIsolated.mpr
    (connected_zigzagD4Graph.preconnected.not_isIsolated i)

private theorem exists_adj_zigzagE8Graph (i : Fin 8) :
    ∃ j, zigzagE8Graph.Adj i j :=
  SimpleGraph.exists_adj_iff_not_isIsolated.mpr
    (connected_zigzagE8Graph.preconnected.not_isIsolated i)

private theorem exists_adj_zigzagAffineE8Graph (i : Fin 9) :
    ∃ j, zigzagAffineE8Graph.Adj i j :=
  SimpleGraph.exists_adj_iff_not_isIsolated.mpr
    (connected_zigzagAffineE8Graph.preconnected.not_isIsolated i)

/-! ### Matrix and entrywise formulas -/

/-- **The graded Cartan matrix of the `D₄` zigzag algebra** is `(1 + q²)I + qA`. -/
theorem zigzagGradedCartanMatrix_D4_eq (k : Type*) [Field k] :
    zigzagGradedCartanMatrix k zigzagD4Graph =
      (1 + X ^ 2 : ℤ[X]) • (1 : Matrix (Fin 4) (Fin 4) ℤ[X]) +
        (X : ℤ[X]) • zigzagD4Graph.adjMatrix ℤ[X] :=
  zigzagGradedCartanMatrix_eq k zigzagD4Graph exists_adj_zigzagD4Graph

/-- **The graded Cartan matrix of the `E₈` zigzag algebra** is `(1 + q²)I + qA`. -/
theorem zigzagGradedCartanMatrix_E8_eq (k : Type*) [Field k] :
    zigzagGradedCartanMatrix k zigzagE8Graph =
      (1 + X ^ 2 : ℤ[X]) • (1 : Matrix (Fin 8) (Fin 8) ℤ[X]) +
        (X : ℤ[X]) • zigzagE8Graph.adjMatrix ℤ[X] :=
  zigzagGradedCartanMatrix_eq k zigzagE8Graph exists_adj_zigzagE8Graph

/-- **The graded Cartan matrix of the affine `E₈` zigzag algebra** is `(1 + q²)I + qA`. -/
theorem zigzagGradedCartanMatrix_affineE8_eq (k : Type*) [Field k] :
    zigzagGradedCartanMatrix k zigzagAffineE8Graph =
      (1 + X ^ 2 : ℤ[X]) • (1 : Matrix (Fin 9) (Fin 9) ℤ[X]) +
        (X : ℤ[X]) • zigzagAffineE8Graph.adjMatrix ℤ[X] :=
  zigzagGradedCartanMatrix_eq k zigzagAffineE8Graph exists_adj_zigzagAffineE8Graph

/-- **The entries of the Bourbaki-labelled `D₄` graded Cartan matrix.** The three listed pairs
are precisely its off-diagonal entries equal to `q`; its diagonal entries are `1 + q²`. -/
theorem zigzagGradedCartanMatrix_D4_apply (k : Type*) [Field k] (i j : Fin 4) :
    zigzagGradedCartanMatrix k zigzagD4Graph i j =
      (if i = j then 1 + X ^ 2 else 0) +
        if (min (i : ℕ) (j : ℕ), max (i : ℕ) (j : ℕ)) ∈
          [((0 : ℕ), (1 : ℕ)), (1, 2), (1, 3)] then X else 0 := by
  rw [zigzagGradedCartanMatrix_apply k zigzagD4Graph exists_adj_zigzagD4Graph]
  simp only [zigzagD4Graph_adj]

/-- **The entries of the Bourbaki-labelled `E₈` graded Cartan matrix.** The seven listed pairs
are precisely its off-diagonal entries equal to `q`; its diagonal entries are `1 + q²`. -/
theorem zigzagGradedCartanMatrix_E8_apply (k : Type*) [Field k] (i j : Fin 8) :
    zigzagGradedCartanMatrix k zigzagE8Graph i j =
      (if i = j then 1 + X ^ 2 else 0) +
        if (min (i : ℕ) (j : ℕ), max (i : ℕ) (j : ℕ)) ∈
            [((0 : ℕ), (2 : ℕ)), (1, 3), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)]
          then X else 0 := by
  rw [zigzagGradedCartanMatrix_apply k zigzagE8Graph exists_adj_zigzagE8Graph]
  simp only [zigzagE8Graph_adj]

/-- **The entries of the arm-labelled affine `E₈ = T_{2,3,6}` graded Cartan matrix.** The
eight listed pairs are precisely its off-diagonal entries equal to `q`; its diagonal entries are
`1 + q²`. -/
theorem zigzagGradedCartanMatrix_affineE8_apply (k : Type*) [Field k] (i j : Fin 9) :
    zigzagGradedCartanMatrix k zigzagAffineE8Graph i j =
      (if i = j then 1 + X ^ 2 else 0) +
        if (min (i : ℕ) (j : ℕ), max (i : ℕ) (j : ℕ)) ∈
            [((0 : ℕ), (1 : ℕ)), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7),
              (7, 8)] then X else 0 := by
  rw [zigzagGradedCartanMatrix_apply k zigzagAffineE8Graph
    exists_adj_zigzagAffineE8Graph]
  simp only [zigzagAffineE8Graph_adj]

/-! ### Symmetry and the affine specialization -/

/-- The `D₄` graded Cartan matrix is symmetric. -/
theorem isSymm_zigzagGradedCartanMatrix_D4 (k : Type*) [Field k] :
    (zigzagGradedCartanMatrix k zigzagD4Graph).IsSymm :=
  isSymm_zigzagGradedCartanMatrix k zigzagD4Graph

/-- The `E₈` graded Cartan matrix is symmetric. -/
theorem isSymm_zigzagGradedCartanMatrix_E8 (k : Type*) [Field k] :
    (zigzagGradedCartanMatrix k zigzagE8Graph).IsSymm :=
  isSymm_zigzagGradedCartanMatrix k zigzagE8Graph

/-- The affine `E₈` graded Cartan matrix is symmetric. -/
theorem isSymm_zigzagGradedCartanMatrix_affineE8 (k : Type*) [Field k] :
    (zigzagGradedCartanMatrix k zigzagAffineE8Graph).IsSymm :=
  isSymm_zigzagGradedCartanMatrix k zigzagAffineE8Graph

/-- **At `q = -1`, the affine `E₈` graded Cartan matrix is the affine generalized Cartan
matrix** `2I - A`. This graph Cartan matrix is identified with
`TauCeti.AffineDynkinType.E8.cartanMatrix` by
`TauCeti.AffineDynkinType.cartanMatrix_eq_graphCartanMatrix`. -/
theorem zigzagGradedCartanMatrix_map_eval_neg_one_affineE8 (k : Type*) [Field k] :
    (zigzagGradedCartanMatrix k zigzagAffineE8Graph).map (eval (-1)) =
      graphCartanMatrix zigzagAffineE8Graph ℤ := by
  rw [zigzagGradedCartanMatrix_map_eval_neg_one k zigzagAffineE8Graph
    exists_adj_zigzagAffineE8Graph]
  exact (graphCartanMatrix_eq_two_smul_one_sub_adjMatrix zigzagAffineE8Graph).symm

/-- **The affine `E₈` specialization at `q = -1` is singular.** Its determinant vanishes
because the explicit affine mark vector `(6,3,4,2,5,4,3,2,1)` is a null vector with final
coordinate `1`. -/
theorem eval_neg_one_det_zigzagGradedCartanMatrix_affineE8 (k : Type*) [Field k] :
    eval (-1) (zigzagGradedCartanMatrix k zigzagAffineE8Graph).det = 0 := by
  -- `RingHom.map_det` uses the bundled evaluation homomorphism; this only replaces its
  -- underlying function `eval (-1)` by that bundle.
  change evalRingHom (-1) (zigzagGradedCartanMatrix k zigzagAffineE8Graph).det = 0
  rw [RingHom.map_det]
  -- `RingHom.mapMatrix` and `Matrix.map` have the same entries but expose different wrappers.
  change ((zigzagGradedCartanMatrix k zigzagAffineE8Graph).map (eval (-1))).det = 0
  rw [zigzagGradedCartanMatrix_map_eval_neg_one_affineE8]
  let δ : Fin 9 → ℤ := ![6, 3, 4, 2, 5, 4, 3, 2, 1]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := δ) (i := 8)
  · funext i
    fin_cases i <;>
      norm_num [graphCartanMatrix_mulVec_apply, SimpleGraph.neighborFinset_eq_filter,
        zigzagAffineE8Graph_adj, δ] <;> decide
  · change (1 : ℤ) ∈ nonZeroDivisors ℤ
    exact one_mem _

/-- **The affine `E₈` graded Cartan determinant is a nonzero polynomial**, despite vanishing
at `q = -1`. At `q = 0` the graded Cartan matrix is the identity. -/
theorem det_zigzagGradedCartanMatrix_affineE8_ne_zero (k : Type*) [Field k] :
    (zigzagGradedCartanMatrix k zigzagAffineE8Graph).det ≠ 0 :=
  det_zigzagGradedCartanMatrix_ne_zero k zigzagAffineE8Graph

end TauCeti
