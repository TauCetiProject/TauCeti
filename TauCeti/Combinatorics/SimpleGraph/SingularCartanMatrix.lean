/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.CoefficientGame
public import TauCeti.Combinatorics.SimpleGraph.IntegralNullVector
public import TauCeti.LinearAlgebra.Matrix.ZMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Order.Star.Int
import TauCeti.Data.Matrix.DotProduct

/-!
# Singular positive semidefinite graph Cartan matrices

For a finite preconnected simple graph `G`, the matrix `2I - A` over a linearly ordered field is
positive semidefinite and singular exactly when `G` carries a nonzero natural-valued additive
function, that is a nonzero `a : V → ℕ` with `∑_{j ∼ i} a j = 2 * a i` at every vertex. In the
language of the coefficient game this says that a nonzero stuck position without precarious
vertices exists exactly when `2I - A` is positive semidefinite and singular.

One direction is the positive-additive-function theory: such an `a` is positive, so
`2I - A` is positive semidefinite (`SimpleGraph.posSemidef_graphCartanMatrix`), and `a` is a
nonzero null vector. For the converse, the off-diagonal entries of `2I - A` are nonpositive, so
for a positive semidefinite `2I - A` the coordinatewise absolute value of a null vector is again a
null vector (`Matrix.PosSemidef.mulVec_abs_eq_zero`). Singularity of `2I - A` over the field
gives an integer null vector, since the determinant is computed over `ℤ`, and its absolute value
is the required natural-valued additive function. It is strictly positive by zero propagation
(`SimpleGraph.Preconnected.pos_of_sum_eq_two_mul`).

## Main results

* `SimpleGraph.Preconnected.exists_sum_eq_two_mul_iff_posSemidef_and_det_eq_zero`: a nonzero
  natural-valued additive function exists exactly when `2I - A` is positive semidefinite and
  singular.
* `Preconnected.exists_isStuck_and_forall_not_isPrecarious_iff_posSemidef_and_det_eq_zero`:
  the same criterion for nonzero stuck positions without precarious vertices.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Theorem 4.3.
* P. Etingof et al., *Introduction to representation theory*, Problem 5.3, for the semidefinite
  description of the affine diagrams.
-/

public section

namespace SimpleGraph

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R]
  [TrivialStar R]

variable (R) in
/-- **Singular positive semidefinite graph Cartan matrices.** On a finite preconnected simple
graph, a nonzero weight `a : V → ℕ` with `∑_{j ∼ i} a j = 2 * a i` at every vertex exists exactly
when `2I - A`, over any linearly ordered field, is positive semidefinite and singular. Such a
weight is then strictly positive (`SimpleGraph.Preconnected.pos_of_sum_eq_two_mul`). -/
theorem Preconnected.exists_sum_eq_two_mul_iff_posSemidef_and_det_eq_zero (hG : G.Preconnected) :
    (∃ a : V → ℕ, a ≠ 0 ∧ ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) ↔
      (G.graphCartanMatrix R).PosSemidef ∧ (G.graphCartanMatrix R).det = 0 := by
  constructor
  · rintro ⟨a, ha, hsum⟩
    have hδ (i : V) : ∑ j ∈ G.neighborFinset i, (a j : R) = 2 * (a i : R) := by
      exact_mod_cast hsum i
    have hpos (i : V) : 0 < (a i : R) := by exact_mod_cast hG.pos_of_sum_eq_two_mul hsum ha i
    refine ⟨posSemidef_graphCartanMatrix G hpos hδ, exists_mulVec_eq_zero_iff.mp
      ⟨_, fun h ↦ ha (funext fun i ↦ ?_), graphCartanMatrix_mulVec_eq_zero G hδ⟩⟩
    simpa using congrFun h i
  · rintro ⟨hC, hdet⟩
    -- The determinant is computed over `ℤ`, so there is a nonzero integer null vector `v`.
    have hdetℤ : (G.graphCartanMatrix ℤ).det = 0 := by
      have h := (Int.castRingHom R).map_det (G.graphCartanMatrix ℤ)
      rw [RingHom.mapMatrix_apply, graphCartanMatrix_map, hdet, eq_intCast] at h
      exact_mod_cast h
    obtain ⟨v, hv, hCv⟩ := exists_mulVec_eq_zero_iff.mpr hdetℤ
    -- Positive semidefiniteness descends to `ℤ`, along the order embedding `ℤ → R`.
    have hCℤ : (G.graphCartanMatrix ℤ).PosSemidef := by
      refine .of_dotProduct_mulVec_nonneg ?_ fun y ↦ ?_
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
          isSymm_graphCartanMatrix]
      · have h := hC.dotProduct_mulVec_nonneg (Int.castRingHom R ∘ y)
        rw [star_trivial, ← graphCartanMatrix_map G (Int.castRingHom R),
          ← RingHom.map_dotProduct_mulVec, eq_intCast] at h
        rw [star_trivial]
        exact_mod_cast h
    -- The absolute value of `v` is a natural-valued null vector.
    have habs := hCℤ.mulVec_abs_eq_zero (fun i j hij ↦ by
      simp only [graphCartanMatrix_apply, hij, ↓reduceIte]
      split_ifs <;> norm_num) hCv
    refine ⟨fun i ↦ (v i).natAbs, fun h ↦ hv (funext fun i ↦ ?_), fun i ↦ ?_⟩
    · exact Int.natAbs_eq_zero.mp (congrFun h i)
    · have hi := congrFun habs i
      rw [graphCartanMatrix_mulVec_apply, Pi.zero_apply, sub_eq_zero] at hi
      zify
      simpa only [Int.natCast_natAbs] using hi.symm

variable (R) in
/-- **The coefficient-game form of the semidefinite criterion.** On a finite preconnected simple
graph, a nonzero position `a : V → ℕ`, read in `ℤ`, which is stuck and has no precarious vertex
exists exactly when `2I - A`, over any linearly ordered field, is positive semidefinite and
singular. -/
theorem Preconnected.exists_isStuck_and_forall_not_isPrecarious_iff_posSemidef_and_det_eq_zero
    (hG : G.Preconnected) :
    (∃ a : V → ℕ, a ≠ 0 ∧ G.IsStuck (fun i ↦ (a i : ℤ)) ∧
        ∀ i, ¬ G.IsPrecarious (fun i ↦ (a i : ℤ)) i) ↔
      (G.graphCartanMatrix R).PosSemidef ∧ (G.graphCartanMatrix R).det = 0 := by
  rw [← hG.exists_sum_eq_two_mul_iff_posSemidef_and_det_eq_zero R]
  refine exists_congr fun a ↦ and_congr_right fun _ ↦ ?_
  rw [isStuck_and_forall_not_isPrecarious_iff_graphCartanMatrix_mulVec_eq_zero, funext_iff]
  refine forall_congr' fun i ↦ ?_
  rw [graphCartanMatrix_mulVec_apply, Pi.zero_apply, sub_eq_zero, eq_comm]
  norm_cast

end SimpleGraph
