/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.NegativeDefinite

/-!
# A diagonal-dominance criterion for negative-definite plumbings

Némethi's lattice homology takes as its standing hypothesis a **negative-definite** plumbing
graph: the intersection form of the plumbed four-manifold must be negative definite on the whole
lattice. Checking this directly means diagonalizing (or completing the square on) the intersection
matrix, which is what `NegativeDefinite.lean` does by hand for the `A₂` plumbing. This file
supplies a general, purely combinatorial sufficient condition that avoids that work.

The condition is **strict diagonal dominance** of the negated intersection matrix `-A`: for every
sphere `i`, the framing is more negative than the number of neighbours,

`degree i < - weight i`.

Since the off-diagonal entries of `-A` are minus the adjacency indicators, the row sum of their
absolute values off the diagonal is exactly `degree i`, so the displayed inequality says that the
diagonal entry `- weight i` strictly dominates that row sum. The standard arithmetic-geometric
bound `2 (x i)(x j) ≤ (x i)² + (x j)²` on each edge then gives, for every lattice vector `x`,

`x · x ≤ ∑ i, (weight i + degree i) · (x i)²`,

whose right-hand side is a sum of nonpositive terms that is strictly negative once `x ≠ 0`. Hence
the intersection form is strictly negative away from the origin, which is the self-pairing form of
negative-definiteness. This recovers `a2Plumbing_isNegativeDefinite` (each vertex of the `A₂`
plumbing has degree `1` and framing `-2`) as a one-line instance, and, more usefully, certifies
negative-definiteness of every plumbing whose framings are sufficiently negative — the generic
Seifert-fibred examples — without any per-graph square completion.

## Main results

* `TauCeti.PlumbingGraph.isNegativeDefinite_of_forall_intersectionForm_self_neg`: a plumbing whose
  intersection form is strictly negative on every nonzero lattice vector is negative definite (the
  converse of `IsNegativeDefinite.intersectionForm_self_neg`).
* `TauCeti.PlumbingGraph.intersectionForm_self_le_weight_add_degree`: the diagonal-dominance upper
  bound `x · x ≤ ∑ i, (weight i + degree i) · (x i)²`.
* `TauCeti.PlumbingGraph.isNegativeDefinite_of_degree_lt_neg_weight`: strict diagonal dominance
  `degree i < - weight i` for all `i` implies the plumbing is negative definite.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose standing hypothesis is a negative-definite plumbing. The
diagonal-dominance sufficient condition is the elementary certificate used throughout Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

open scoped Matrix

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- A plumbing whose intersection form is strictly negative on every nonzero lattice vector is
negative definite: the negated intersection matrix is symmetric, and its self-pairing
`star x ⬝ᵥ (-A *ᵥ x)` equals `- (x · x)`, which the hypothesis makes positive. This is the
converse of `IsNegativeDefinite.intersectionForm_self_neg`, packaging the square-completion step
of `a2Plumbing_isNegativeDefinite` once and for all. -/
theorem isNegativeDefinite_of_forall_intersectionForm_self_neg
    (h : ∀ x : V → ℤ, x ≠ 0 → P.intersectionForm x x < 0) : P.IsNegativeDefinite := by
  rw [isNegativeDefinite_iff, Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(Matrix.isHermitian_iff_isSymm.mpr P.intersectionMatrix_isSymm).neg, fun x hx => ?_⟩
  have hconv : star x ⬝ᵥ ((-P.intersectionMatrix) *ᵥ x) = -P.intersectionForm x x := by
    rw [Matrix.neg_mulVec, dotProduct_neg, star_trivial, P.intersectionForm_apply,
      ← Matrix.toBilin'_apply P.intersectionMatrix x x, Matrix.toBilin'_apply']
  rw [hconv]
  linarith [h x hx]

omit [DecidableEq V] in
/-- The `i`-th row of the adjacency indicator sums, over all columns, to the degree of `i`: the
number of `j` with `Adj i j` is `degree i`. -/
private theorem sum_ite_adj_one (i : V) :
    (∑ j, if P.toSimpleGraph.Adj i j then (1 : ℤ) else 0) = P.toSimpleGraph.degree i := by
  rw [Finset.sum_boole]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

omit [DecidableEq V] in
/-- The adjacency cross-term sum of the intersection form is bounded above by the degree-weighted
sum of squares: applying `2 (x i)(x j) ≤ (x i)² + (x j)²` on each edge and summing over the two
endpoints turns each edge into a diagonal contribution to both of its endpoints. -/
theorem sum_adj_mul_le_degree_mul_sq (x : V → ℤ) :
    (∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x i * x j else 0) ≤
      ∑ i, (P.toSimpleGraph.degree i : ℤ) * x i ^ 2 := by
  -- Double the edge sum and bound each edge term by the sum of the two endpoint squares.
  have hdouble :
      2 * (∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x i * x j else 0) ≤
        ∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x i ^ 2 + x j ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_ite, mul_zero]
    split_ifs with hadj
    · have := two_mul_le_add_sq (x i) (x j)
      linarith
    · rfl
  -- The endpoint-square sum splits into two equal halves, each the degree-weighted sum of squares.
  have hsplit :
      (∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x i ^ 2 + x j ^ 2 else 0) =
        2 * ∑ i, (P.toSimpleGraph.degree i : ℤ) * x i ^ 2 := by
    have hterm : ∀ i j, (if P.toSimpleGraph.Adj i j then x i ^ 2 + x j ^ 2 else 0) =
        (if P.toSimpleGraph.Adj i j then x i ^ 2 else 0) +
          (if P.toSimpleGraph.Adj i j then x j ^ 2 else 0) := by
      intro i j; split_ifs <;> ring
    simp_rw [hterm, Finset.sum_add_distrib]
    have hfirst :
        (∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x i ^ 2 else 0) =
          ∑ i, (P.toSimpleGraph.degree i : ℤ) * x i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hrow :
          (∑ j, if P.toSimpleGraph.Adj i j then x i ^ 2 else 0) =
            (∑ j, if P.toSimpleGraph.Adj i j then (1 : ℤ) else 0) * x i ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      rw [hrow, P.sum_ite_adj_one i]
    have hsecond :
        (∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x j ^ 2 else 0) =
          ∑ i, (P.toSimpleGraph.degree i : ℤ) * x i ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hrow :
          (∑ i, if P.toSimpleGraph.Adj i j then x j ^ 2 else 0) =
            (∑ i, if P.toSimpleGraph.Adj j i then (1 : ℤ) else 0) * x j ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : P.toSimpleGraph.Adj i j
        · rw [if_pos h, if_pos ((P.toSimpleGraph.adj_comm i j).mp h)]; ring
        · rw [if_neg h, if_neg (fun hji => h ((P.toSimpleGraph.adj_comm i j).mpr hji))]; ring
      rw [hrow, P.sum_ite_adj_one j]
    rw [hfirst, hsecond]
    ring
  rw [hsplit] at hdouble
  linarith

/-- The diagonal-dominance upper bound on the intersection form: the self-pairing is at most the
sum, over spheres, of `(weight i + degree i)` times `(x i)²`. This is the quadratic-form estimate
underlying the negative-definiteness criterion. -/
theorem intersectionForm_self_le_weight_add_degree (x : V → ℤ) :
    P.intersectionForm x x ≤
      ∑ i, (P.weight i + P.toSimpleGraph.degree i) * x i ^ 2 := by
  rw [P.intersectionForm_self]
  have hle := P.sum_adj_mul_le_degree_mul_sq x
  have hcombine :
      (∑ i, P.weight i * x i ^ 2) + ∑ i, (P.toSimpleGraph.degree i : ℤ) * x i ^ 2 =
        ∑ i, (P.weight i + P.toSimpleGraph.degree i) * x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  linarith [hcombine]

/-- **Strict diagonal dominance implies negative-definiteness.** If every sphere's framing is more
negative than its number of neighbours, `degree i < - weight i`, then the plumbing is negative
definite.

The row-sum condition makes each coefficient `weight i + degree i` strictly negative, so the
diagonal-dominance bound `intersectionForm_self_le_weight_add_degree` expresses `x · x` as at most
a sum of nonpositive terms; picking a coordinate where `x` is nonzero makes that sum strictly
negative. -/
theorem isNegativeDefinite_of_degree_lt_neg_weight
    (h : ∀ i, (P.toSimpleGraph.degree i : ℤ) < -P.weight i) : P.IsNegativeDefinite := by
  refine P.isNegativeDefinite_of_forall_intersectionForm_self_neg fun x hx => ?_
  refine lt_of_le_of_lt (P.intersectionForm_self_le_weight_add_degree x) ?_
  -- Every coefficient is strictly negative, so every summand is nonpositive.
  have hcoeff : ∀ i, P.weight i + (P.toSimpleGraph.degree i : ℤ) < 0 := fun i => by
    have := h i; linarith
  have hnonpos : ∀ i ∈ Finset.univ,
      (P.weight i + (P.toSimpleGraph.degree i : ℤ)) * x i ^ 2 ≤ 0 := fun i _ =>
    mul_nonpos_of_nonpos_of_nonneg (hcoeff i).le (sq_nonneg _)
  -- Some coordinate is nonzero, and there its summand is strictly negative.
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hsq : (1 : ℤ) ≤ x i₀ ^ 2 := by
    have : x i₀ ^ 2 ≠ 0 := pow_ne_zero 2 hi₀
    have : (0 : ℤ) < x i₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm this)
    omega
  have hstrict : (P.weight i₀ + (P.toSimpleGraph.degree i₀ : ℤ)) * x i₀ ^ 2 < 0 := by
    have hc := hcoeff i₀
    nlinarith [hc, hsq]
  have hsplit :
      ∑ i, (P.weight i + (P.toSimpleGraph.degree i : ℤ)) * x i ^ 2 =
        (P.weight i₀ + (P.toSimpleGraph.degree i₀ : ℤ)) * x i₀ ^ 2 +
          ∑ i ∈ Finset.univ.erase i₀,
            (P.weight i + (P.toSimpleGraph.degree i : ℤ)) * x i ^ 2 :=
    (Finset.add_sum_erase Finset.univ
      (fun i => (P.weight i + (P.toSimpleGraph.degree i : ℤ)) * x i ^ 2)
      (Finset.mem_univ i₀)).symm
  have hrest : ∑ i ∈ Finset.univ.erase i₀,
      (P.weight i + (P.toSimpleGraph.degree i : ℤ)) * x i ^ 2 ≤ 0 :=
    Finset.sum_nonpos fun i _ => hnonpos i (Finset.mem_univ i)
  rw [hsplit]
  linarith

end PlumbingGraph

/-- The triangle plumbing on three spheres, each with framing `-3`: its underlying graph is the
complete graph `K₃`, so every vertex has degree `2`, and `2 < 3`. A self-validating instance of
the diagonal-dominance criterion whose graph carries edges (so the adjacency bound is genuinely
used), where hand square-completion would be more laborious than for `A₂`. -/
def triangleMinusThree : PlumbingGraph (Fin 3) where
  toSimpleGraph := ⊤
  decidableAdj := inferInstance
  weight := fun _ => -3

example : triangleMinusThree.IsNegativeDefinite := by
  refine triangleMinusThree.isNegativeDefinite_of_degree_lt_neg_weight fun i => ?_
  have hdeg : triangleMinusThree.toSimpleGraph.degree i = 2 := by
    change (⊤ : SimpleGraph (Fin 3)).degree i = 2
    rw [SimpleGraph.IsRegularOfDegree.top i]
    simp
  have hw : triangleMinusThree.weight i = -3 := rfl
  rw [hdeg, hw]
  norm_num

end TauCeti
