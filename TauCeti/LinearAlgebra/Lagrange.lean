/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# Lagrange residue sums and derivative signs of nodal polynomials

For a finite family of distinct nodes `x : ι → K`, the nodal polynomial
`Lagrange.nodal Finset.univ x = ∏ j, (X - C (x j))` is the monic polynomial with simple roots
`x j`. Its derivative at a node `x i` evaluates to `∏ j ∈ univ.erase i, (x i - x j)`.

This file records the classical residue-sum identity over a field for rational functions
`F / ((X - C c) * p)` with `deg F < deg p`, and the alternating signs of `p'(x i)` when the
nodes are strictly monotone or antitone in a linearly ordered commutative ring.

## Main results

* `Lagrange.sum_eval_div_sub_mul_eval_derivative_nodal`: for `x` injective on `s`, `deg F < #s`,
  and `c ∉ x '' s`,
  `∑ i ∈ s, F.eval (x i) / ((x i - c) * (derivative (nodal s x)).eval (x i)) =
  -(F.eval c / (nodal s x).eval c)`.
* `Lagrange.neg_one_pow_mul_eval_derivative_nodal_pos_of_strictAnti` and
  `Lagrange.neg_one_pow_mul_eval_derivative_nodal_pos_of_strictMono`: positivity of
  `(-1) ^ i * (derivative (nodal univ x)).eval (x i)` and
  `(-1) ^ (M - 1 - i) * (derivative (nodal univ x)).eval (x i)` for strictly decreasing or
  increasing nodes `x : Fin M → K`.

## References

* J.-L. Lagrange, *Leçons élémentaires sur les mathématiques* (1795), Lecture V (Lagrange
  interpolation and residue identities).
* L. Alpöge, `New.DiscreteSeries.sum_eval_div_sub_mul_eval_derivative_nodal` in
  `src/Lib/General/Algebra/ResidueSums.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

noncomputable section

open Finset Polynomial

namespace Lagrange

section Residues

variable {ι K : Type*} [Field K] {s : Finset ι} {x : ι → K} {F : K[X]}

/-- For nodes `x : ι → K` injective on `s : Finset ι`, `F` with `F.degree < #s`, and `c` not a
node in `s`, the sum of residues `F(x i) / ((x i - c) * p'(x i))` over `i ∈ s` equals
`-F(c) / p(c)`. -/
theorem sum_eval_div_sub_mul_eval_derivative_nodal (hx : Set.InjOn x s) {c : K}
    (hc : ∀ i ∈ s, c ≠ x i) (hdeg : F.degree < #s) :
    ∑ i ∈ s, F.eval (x i) / ((x i - c) * (derivative (nodal s x)).eval (x i)) =
      -(F.eval c / (nodal s x).eval c) := by
  classical
  have hval : F.eval c = (nodal s x).eval c *
      ∑ i ∈ s, nodalWeight s x i * (c - x i)⁻¹ * F.eval (x i) := by
    rw [← eval_interpolate_not_at_node _ hc, ← eq_interpolate hx hdeg]
  rw [hval, mul_div_cancel_left₀ _ (eval_nodal_not_at_node hc), ← sum_neg_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [nodalWeight_eq_eval_derivative_nodal hi, div_eq_mul_inv, ← neg_sub c (x i),
    neg_mul, inv_neg, mul_inv]
  ring

end Residues

section Signs

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] {M : ℕ} {x : Fin M → K}

/-- For strictly decreasing nodes `x 0 > x 1 > ...`,
`(-1) ^ i * (derivative (nodal univ x)).eval (x i)` is positive. -/
theorem neg_one_pow_mul_eval_derivative_nodal_pos_of_strictAnti (hx : StrictAnti x) (i : Fin M) :
    0 < (-1 : K) ^ (i : ℕ) * (derivative (nodal univ x)).eval (x i) := by
  have hsplit : (-1 : K) ^ (i : ℕ) * ∏ j ∈ univ.erase i, (x i - x j) =
      (∏ j ∈ Ioi i, (x i - x j)) * ∏ j ∈ Iio i, (x j - x i) := by
    rw [Finset.prod_erase_univ_eq_prod_Ioi_mul_prod_Iio i (fun j ↦ x i - x j), ← Fin.card_Iio,
      mul_left_comm, ← prod_neg]
    simp_rw [neg_sub]
  rw [eval_nodal_derivative_eval_node_eq (mem_univ i), eval_nodal, hsplit]
  exact mul_pos (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Ioi.1 hj)))
    (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Iio.1 hj)))

/-- For strictly increasing nodes `x 0 < ... < x (M - 1)`,
`(-1) ^ (M - 1 - i) * (derivative (nodal univ x)).eval (x i)` is positive. -/
theorem neg_one_pow_mul_eval_derivative_nodal_pos_of_strictMono (hx : StrictMono x) (i : Fin M) :
    0 < (-1 : K) ^ (M - 1 - (i : ℕ)) * (derivative (nodal univ x)).eval (x i) := by
  have hsplit : (-1 : K) ^ (M - 1 - (i : ℕ)) * ∏ j ∈ univ.erase i, (x i - x j) =
      (∏ j ∈ Ioi i, (x j - x i)) * ∏ j ∈ Iio i, (x i - x j) := by
    rw [Finset.prod_erase_univ_eq_prod_Ioi_mul_prod_Iio i (fun j ↦ x i - x j), ← Fin.card_Ioi,
      ← mul_assoc, ← prod_neg]
    simp_rw [neg_sub]
  rw [eval_nodal_derivative_eval_node_eq (mem_univ i), eval_nodal, hsplit]
  exact mul_pos (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Ioi.1 hj)))
    (prod_pos fun j hj ↦ sub_pos.2 (hx (mem_Iio.1 hj)))

end Signs

end Lagrange
