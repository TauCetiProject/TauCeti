/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Derivative and Lagrange residue sums of nodal polynomials

For a finite family of distinct nodes `x : ι → K` in a field `K`, the nodal polynomial
`Lagrange.nodal Finset.univ x = ∏ j, (X - C (x j))` is the monic polynomial with simple roots
`x j`. Its derivative at a node `x i` evaluates to `∏ j ∈ univ.erase i, (x i - x j)`.

This file records the derivative evaluation at a node, two classical residue-sum identities for
rational functions `F / p` and `F / ((X - C c) * p)` with `deg F < deg p`, and the alternating
signs of `p'(x i)` when the nodes are strictly monotone or antitone in a linearly ordered field.

## Main results

* `Lagrange.eval_derivative_nodal`: `(derivative (nodal univ x)).eval (x i) =
  ∏ j ∈ univ.erase i, (x i - x j)`.
* `Lagrange.sum_eval_div_eval_derivative_nodal`: for monic `F` of degree `< card ι`,
  `∑ i, F.eval (x i) / (derivative (nodal univ x)).eval (x i)` equals `1` if
  `F.natDegree + 1 = card ι` and `0` otherwise.
* `Lagrange.sum_eval_div_sub_mul_eval_derivative_nodal`: for `deg F < card ι` and `c` not a node,
  `∑ i, F.eval (x i) / ((x i - c) * (derivative (nodal univ x)).eval (x i)) =
  -(F.eval c / (nodal univ x).eval c)`.
* `Lagrange.derivative_nodal_sign_of_strictAnti` and
  `Lagrange.derivative_nodal_sign_of_strictMono`: sign of `(derivative (nodal univ x)).eval (x i)`
  for strictly decreasing or increasing nodes `x : Fin M → K`.

## References

* J.-L. Lagrange, *Leçons élémentaires sur les mathématiques* (1795), Lecture V (Lagrange
  interpolation and residue identities).
* L. Alpöge, `New.DiscreteSeries.sum_eval_div_eval_derivative_nodal` and
  `New.DiscreteSeries.sum_eval_div_sub_mul_eval_derivative_nodal` in
  `src/Lib/General/Algebra/ResidueSums.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

noncomputable section

open Finset Polynomial

namespace Lagrange

section Residues

variable {ι K : Type*} [Fintype ι] [Field K] {x : ι → K} {F : K[X]}

/-- The derivative of `nodal univ x` at a node `x i` is the product of `x i - x j` over `j ≠ i`. -/
theorem eval_derivative_nodal [DecidableEq ι] (x : ι → K) (i : ι) :
    (derivative (nodal univ x)).eval (x i) = ∏ j ∈ univ.erase i, (x i - x j) := by
  rw [eval_nodal_derivative_eval_node_eq (mem_univ i), eval_nodal]

/-- For distinct nodes `x : ι → K` and a monic polynomial `F` with `F.natDegree < card ι`,
the sum of residues `F(x i) / p'(x i)` equals `1` if `F.natDegree + 1 = card ι` and `0`
otherwise. -/
theorem sum_eval_div_eval_derivative_nodal (hx : Function.Injective x) (hF : F.Monic)
    (hdeg : F.natDegree < Fintype.card ι) :
    ∑ i : ι, F.eval (x i) / (derivative (nodal univ x)).eval (x i) =
      if F.natDegree + 1 = Fintype.card ι then 1 else 0 := by
  classical
  simp_rw [eval_derivative_nodal]
  rw [← coeff_eq_sum hx.injOn (degree_le_natDegree.trans_lt (Nat.cast_lt.2 hdeg)), card_univ]
  split_ifs with htop
  · rw [← htop, Nat.add_sub_cancel, hF.coeff_natDegree]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- For distinct nodes `x : ι → K`, `F` with `F.natDegree < card ι`, and `c` not a node, the sum
of residues `F(x i) / ((x i - c) * p'(x i))` equals `-F(c) / p(c)`. -/
theorem sum_eval_div_sub_mul_eval_derivative_nodal (hx : Function.Injective x) {c : K}
    (hc : ∀ i : ι, c ≠ x i) (hdeg : F.natDegree < Fintype.card ι) :
    ∑ i : ι, F.eval (x i) / ((x i - c) * (derivative (nodal univ x)).eval (x i)) =
      -(F.eval c / (nodal univ x).eval c) := by
  classical
  have hval : F.eval c = (nodal univ x).eval c *
      ∑ i : ι, nodalWeight univ x i * (c - x i)⁻¹ * F.eval (x i) := by
    rw [← eval_interpolate_not_at_node _ fun i _ ↦ hc i,
      ← eq_interpolate hx.injOn (degree_le_natDegree.trans_lt (Nat.cast_lt.2 hdeg))]
  rw [hval, mul_div_cancel_left₀ _ (eval_nodal_not_at_node fun i _ ↦ hc i), ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [nodalWeight_eq_eval_derivative_nodal (mem_univ i), div_eq_mul_inv, ← neg_sub c (x i),
    neg_mul, inv_neg, mul_inv]
  ring

end Residues

section Signs

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {M : ℕ} {x : Fin M → K}

/-- For strictly decreasing nodes `x 0 > x 1 > ...`, `(derivative (nodal univ x)).eval (x i)` has
sign `(-1) ^ i`. -/
theorem derivative_nodal_sign_of_strictAnti (hx : StrictAnti x) (i : Fin M) :
    0 < (-1 : K) ^ (i : ℕ) * (derivative (nodal univ x)).eval (x i) := by
  have hsplit : (-1 : K) ^ (i : ℕ) * ∏ j ∈ univ.erase i, (x i - x j) =
      (∏ j ∈ Ioi i, (x i - x j)) * ∏ j ∈ Iio i, (x j - x i) := by
    have herase : ∏ j ∈ univ.erase i, (x i - x j) =
        (∏ j ∈ Ioi i, (x i - x j)) * ∏ j ∈ Iio i, (x i - x j) := by
      rw [← prod_disjUnion (disjoint_Ioi_Iio i), Ioi_disjUnion_Iio, compl_singleton]
    rw [herase, ← Fin.card_Iio, mul_left_comm, ← prod_neg]
    simp_rw [neg_sub]
  rw [eval_derivative_nodal, hsplit]
  exact mul_pos (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Ioi.1 hj)))
    (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Iio.1 hj)))

/-- For strictly increasing nodes `x 0 < ... < x (M - 1)`,
`(derivative (nodal univ x)).eval (x i)` has sign `(-1) ^ (M - 1 - i)`. -/
theorem derivative_nodal_sign_of_strictMono (hx : StrictMono x) (i : Fin M) :
    0 < (-1 : K) ^ (M - 1 - (i : ℕ)) * (derivative (nodal univ x)).eval (x i) := by
  have hsplit : (-1 : K) ^ (M - 1 - (i : ℕ)) * ∏ j ∈ univ.erase i, (x i - x j) =
      (∏ j ∈ Ioi i, (x j - x i)) * ∏ j ∈ Iio i, (x i - x j) := by
    have herase : ∏ j ∈ univ.erase i, (x i - x j) =
        (∏ j ∈ Ioi i, (x i - x j)) * ∏ j ∈ Iio i, (x i - x j) := by
      rw [← prod_disjUnion (disjoint_Ioi_Iio i), Ioi_disjUnion_Iio, compl_singleton]
    rw [herase, ← Fin.card_Ioi, ← mul_assoc, ← prod_neg]
    simp_rw [neg_sub]
  rw [eval_derivative_nodal, hsplit]
  exact mul_pos (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Ioi.1 hj)))
    (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Iio.1 hj)))

end Signs

end Lagrange
