/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.Polynomial.GaussianBinomial
import TauCeti.Data.Nat.Cast.Basic
import TauCeti.LinearAlgebra.LinearMap.Range
import TauCeti.LinearAlgebra.LinearMap.SurjectionCount
import TauCeti.LinearAlgebra.Submodule.CardFinrank

/-!
# Counting matrices of fixed rank over finite fields

`TauCeti.natCard_matrix_rank_eq_gaussianBinomial_mul_prod` counts rectangular matrices of a given
rank using a Gaussian binomial coefficient. `TauCeti.natCast_card_matrix_rank_eq_prod_div` gives
the same count as a product of rational quotients. Dividing by `q^(m*n)` gives the rank distribution
for uniform `m × n` matrices over a field of order `q`. Rank–nullity then gives the rectangular
kernel law by taking rank `n - j` for right kernels of dimension `j` with `j ≤ n`.

Related results are `TauCeti.card_submodule_finrank_eq_gaussianBinomial` for subspace counts,
`TauCeti.natCard_linearMap_surjective` for prescribed images, and
`TauCeti.gaussianBinomial_mul_prod_pow_sub_pow` for the Gaussian product identity.

See Koymans and Pagano, *Higher Rédei reciprocity and integral points on conics*,
arXiv:2005.14157v2, equation (6.10), for the corresponding count over the field of two elements.
-/

public section

open Finset Function LinearMap Matrix Module

namespace TauCeti

/-- The number of matrices of rank `r` with `m` rows and `n` columns over a field of order
`q` is `[m r]_q ∏_{i<r} (q^n - q^i)`, including zero when `r > min m n`. -/
theorem natCard_matrix_rank_eq_gaussianBinomial_mul_prod
    (K m n : Type*) [Field K] [Finite K] [Finite m] [Finite n] (r : ℕ) :
    Nat.card {A : Matrix m n K // A.rank = r} =
      gaussianBinomial (Nat.card K) (Nat.card m) r *
        ∏ i : Fin r, (Nat.card K ^ Nat.card n - Nat.card K ^ i.val) := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
  let columnSpace := fun A : Matrix m n K ↦ A.mulVecLin.range
  have rank_iff (A : Matrix m n K) : A.rank = r ↔ finrank K (columnSpace A) = r := by
    have h : finrank K (columnSpace A) = A.rank := A.finrank_range_mulVecLin
    rw [h]
  have countFiber (W : {W : Submodule K (m → K) // finrank K W = r}) :
      Nat.card {A // columnSpace A = W.val} =
        ∏ i : Fin r, (Nat.card K ^ Nat.card n - Nat.card K ^ i.val) := by
    let e := (toLin' (R := K) (m := m) (n := n)).toEquiv.subtypeEquiv
      (p := fun A ↦ A.mulVecLin.range = W.val) (q := fun f ↦ f.range = W.val) (fun A ↦ by
        simp only [LinearEquiv.coe_toEquiv, toLin'_apply'])
    rw [Nat.card_congr (e.trans (W.val.rangeEqEquivSurjective (M := n → K))),
      natCard_linearMap_surjective, W.property, finrank_fintype_fun_eq_card,
      Nat.card_eq_fintype_card (α := n)]
  have countColumnSpaces : Nat.card {W : Submodule K (m → K) // finrank K W = r} =
      gaussianBinomial (Nat.card K) (Nat.card m) r := by
    rw [card_submodule_finrank_eq_gaussianBinomial, finrank_fintype_fun_eq_card,
      Nat.card_eq_fintype_card (α := m), Nat.card_eq_fintype_card (α := K)]
  -- Sum the common fibre size over all column spaces of dimension `r`.
  let e := Equiv.sigmaSubtypeFiberEquivSubtype columnSpace (q := fun W ↦ finrank K W = r) rank_iff
  rw [Nat.card_congr e.symm, Nat.card_sigma, sum_const_nat (fun W _ ↦ countFiber W)]
  rw [card_univ, ← Nat.card_eq_fintype_card, countColumnSpaces]

/-- The rank count over a field of order `q`, expressed as a product of rational quotients
`∏_{i<r} (q^m - q^i) (q^n - q^i) / (q^r - q^i)`. If `r > min m n`, a numerator
factor is zero. -/
theorem natCast_card_matrix_rank_eq_prod_div
    (K m n : Type*) [Field K] [Finite K] [Finite m] [Finite n] (r : ℕ) :
    (Nat.card {A : Matrix m n K // A.rank = r} : ℚ) =
      ∏ i : Fin r, (((Nat.card K : ℚ) ^ Nat.card m - (Nat.card K : ℚ) ^ i.val) *
        ((Nat.card K : ℚ) ^ Nat.card n - (Nat.card K : ℚ) ^ i.val) /
        ((Nat.card K : ℚ) ^ r - (Nat.card K : ℚ) ^ i.val)) := by
  let q := Nat.card K
  have hq : 1 < q := Finite.one_lt_card
  have hqRat : 1 < (q : ℚ) := Nat.one_lt_cast.mpr hq
  have hden : (∏ i : Fin r, ((q : ℚ) ^ r - (q : ℚ) ^ i.val)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ ↦ sub_ne_zero.mpr (pow_lt_pow_right₀ hqRat i.isLt).ne'
  have hGaussian := gaussianBinomial_mul_prod_pow_sub_pow (q : ℚ) (Nat.card m) r
  simp only [← Fin.prod_univ_eq_prod_range] at hGaussian
  have hcast : ((gaussianBinomial q (Nat.card m) r : ℕ) : ℚ) =
      gaussianBinomial (q : ℚ) (Nat.card m) r :=
    map_gaussianBinomial (Nat.castRingHom ℚ) q _ r
  rw [natCard_matrix_rank_eq_gaussianBinomial_mul_prod, Nat.cast_mul, hcast,
    Nat.cast_prod_pow_sub_pow hq.le]
  rw [prod_div_distrib, prod_mul_distrib]
  apply (eq_div_iff hden).mpr
  rw [mul_right_comm, hGaussian]

end TauCeti
