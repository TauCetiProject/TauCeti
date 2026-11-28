/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.Polynomial.GaussianBinomial
import TauCeti.LinearAlgebra.LinearMap.RankCount
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Counting matrices of fixed rank over finite fields

`TauCeti.natCard_matrix_rank_eq_gaussianBinomial_mul_prod` counts rectangular matrices of a given
rank using a Gaussian binomial coefficient. `TauCeti.natCast_card_matrix_rank_eq_prod_div` gives
the same count as a product of rational quotients. Dividing by `q^(m*n)` gives the rank distribution
for uniform `m × n` matrices over a field of order `q`. Rank–nullity then gives the rectangular
kernel law by taking rank `n - j` for right kernels of dimension `j` with `j ≤ n`.

The formulas specialize `TauCeti.natCard_linearMap_finrank_range_eq_gaussianBinomial_mul_prod`
and `TauCeti.natCast_card_linearMap_finrank_range_eq_prod_div` via
`TauCeti.natCard_matrix_rank_eq_natCard_linearMap_finrank_range`.

See Koymans and Pagano, *Higher Rédei reciprocity and integral points on conics*,
arXiv:2005.14157v2, equation (6.10), for the corresponding count over the field of two elements.
-/

public section

open Matrix Module

namespace TauCeti

/-- The number of matrices of rank `r` with `m` rows and `n` columns over a field of order
`q` is `[m r]_q ∏_{i<r} (q^n - q^i)`, including zero when `r > min m n`. -/
theorem natCard_matrix_rank_eq_gaussianBinomial_mul_prod
    (K m n : Type*) [DivisionRing K] [Finite K] [Finite m] [Finite n] (r : ℕ) :
    Nat.card {A : Matrix m n K // A.rank = r} =
      gaussianBinomial (Nat.card K) (Nat.card m) r *
        ∏ i : Fin r, (Nat.card K ^ Nat.card n - Nat.card K ^ i.val) := by
  classical
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
  rw [natCard_matrix_rank_eq_natCard_linearMap_finrank_range,
    natCard_linearMap_finrank_range_eq_gaussianBinomial_mul_prod]
  simp only [finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- The rank count over a field of order `q`, expressed as a product of rational quotients
`∏_{i<r} (q^m - q^i) (q^n - q^i) / (q^r - q^i)`. If `r > min m n`, a numerator
factor is zero. -/
theorem natCast_card_matrix_rank_eq_prod_div
    (K m n : Type*) [DivisionRing K] [Finite K] [Finite m] [Finite n] (r : ℕ) :
    (Nat.card {A : Matrix m n K // A.rank = r} : ℚ) =
      ∏ i : Fin r, (((Nat.card K : ℚ) ^ Nat.card m - (Nat.card K : ℚ) ^ i.val) *
        ((Nat.card K : ℚ) ^ Nat.card n - (Nat.card K : ℚ) ^ i.val) /
        ((Nat.card K : ℚ) ^ r - (Nat.card K : ℚ) ^ i.val)) := by
  classical
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
  rw [natCard_matrix_rank_eq_natCard_linearMap_finrank_range,
    natCast_card_linearMap_finrank_range_eq_prod_div]
  simp only [finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end TauCeti
