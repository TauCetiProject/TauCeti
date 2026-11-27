/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.Polynomial.GaussianBinomial
import TauCeti.LinearAlgebra.LinearMap.SurjectionCount
import TauCeti.LinearAlgebra.Submodule.CardFinrank

/-!
# Counting matrices of fixed rank over finite fields

`Matrix.natCard_rank_eq` counts matrices of rank `r` by their column spaces.
`TauCeti.card_submodule_finrank_eq_gaussianBinomial` counts the possible column spaces
and `LinearMap.natCard_surjective` counts the surjections onto each one.
`Matrix.natCast_card_rank_eq_prod_div` expresses the same count as a rational product using
`TauCeti.gaussianBinomial_mul_prod_pow_sub_pow`.

See Koymans and Pagano, *Higher Rédei reciprocity and integral points on conics*,
arXiv:2005.14157v2, equation (6.10), for the corresponding count over the field of two elements.
-/

public section

open Finset Function LinearMap Module TauCeti

namespace Matrix

/-- The number of matrices of rank `r` with `m` rows and `n` columns over a field of order
`q` is `[m r]_q ∏_{i<r} (q^n - q^i)`, including zero when `r > min m n`. -/
theorem natCard_rank_eq (K m n : Type*) [Field K] [Fintype K] [Fintype m] [Fintype n] (r : ℕ) :
    Nat.card {A : Matrix m n K // A.rank = r} =
      TauCeti.gaussianBinomial (Fintype.card K) (Fintype.card m) r *
        ∏ i : Fin r, (Fintype.card K ^ Fintype.card n - Fintype.card K ^ i.val) := by
  classical
  let columnSpace (A : {A : Matrix m n K // A.rank = r}) :
      {W : Submodule K (m → K) // finrank K W = r} :=
    ⟨A.val.mulVecLin.range, A.val.finrank_range_mulVecLin.trans A.property⟩
  have countFiber (W : {W : Submodule K (m → K) // finrank K W = r}) :
      Nat.card {A // columnSpace A = W} =
        ∏ i : Fin r, (Fintype.card K ^ Fintype.card n - Fintype.card K ^ i.val) := by
    let e : {A // columnSpace A = W} ≃ {f : (n → K) →ₗ[K] W.val // Surjective f} :=
      { toFun := fun A ↦ by
          have hA : A.val.val.mulVecLin.range = W.val := congrArg Subtype.val A.property
          refine ⟨A.val.val.mulVecLin.codRestrict W.val (fun x ↦ hA ▸ mem_range_self _ x), ?_⟩
          rw [← range_eq_top, range_codRestrict, hA, Submodule.comap_subtype_self]
        invFun := fun f ↦ by
          let A : Matrix m n K := (W.val.subtype.comp f.val).toMatrix'
          have hA : A.mulVecLin = W.val.subtype.comp f.val := by
            rw [← toLin'_apply', toLin'_toMatrix']
          have hW : A.mulVecLin.range = W.val := by
            rw [hA, range_comp_of_range_eq_top _ (range_eq_top.mpr f.property),
              Submodule.range_subtype]
          have hr : A.rank = r := by
            rw [← A.finrank_range_mulVecLin, hW, W.property]
          exact ⟨⟨A, hr⟩, Subtype.ext hW⟩
        left_inv := by
          intro A
          apply Subtype.ext
          apply Subtype.ext
          exact (congrArg toMatrix' (subtype_comp_codRestrict ..)).trans
            (toMatrix'_toLin' _)
        right_inv := by
          intro f
          apply Subtype.ext
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          exact LinearMap.congr_fun (toLin'_toMatrix' (W.val.subtype.comp f.val)) x }
    rw [Nat.card_congr e, LinearMap.natCard_surjective, W.property,
      finrank_fintype_fun_eq_card]
  have countColumnSpaces : Nat.card {W : Submodule K (m → K) // finrank K W = r} =
      gaussianBinomial (Fintype.card K) (Fintype.card m) r := by
    rw [card_submodule_finrank_eq_gaussianBinomial, finrank_fintype_fun_eq_card]
  -- Sum the common fibre size over all column spaces of dimension `r`.
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv columnSpace).symm, Nat.card_sigma,
    sum_const_nat (fun W _ ↦ countFiber W), card_univ, ← Nat.card_eq_fintype_card,
    countColumnSpaces]

/-- The rank count over a field of order `q`, expressed as a product of rational quotients
`∏_{i<r} (q^m - q^i) (q^n - q^i) / (q^r - q^i)`. If `r > min m n`, a numerator
factor is zero. -/
theorem natCast_card_rank_eq_prod_div
    (K m n : Type*) [Field K] [Fintype K] [Fintype m] [Fintype n] (r : ℕ) :
    (Nat.card {A : Matrix m n K // A.rank = r} : ℚ) =
      ∏ i : Fin r, (((Fintype.card K : ℚ) ^ Fintype.card m - (Fintype.card K : ℚ) ^ i.val) *
        ((Fintype.card K : ℚ) ^ Fintype.card n - (Fintype.card K : ℚ) ^ i.val) /
        ((Fintype.card K : ℚ) ^ r - (Fintype.card K : ℚ) ^ i.val)) := by
  let q := Fintype.card K
  have hq : 1 < q := Fintype.one_lt_card
  have hqRat : 1 < (q : ℚ) := by exact_mod_cast hq
  have castProduct (d : ℕ) :
      ((∏ i : Fin r, (q ^ d - q ^ i.val) : ℕ) : ℚ) =
        ∏ i : Fin r, ((q : ℚ) ^ d - (q : ℚ) ^ i.val) := by
    by_cases h : d < r
    · let i : Fin r := ⟨d, h⟩
      have hNat : ∏ j : Fin r, (q ^ d - q ^ j.val) = 0 :=
        prod_eq_zero (mem_univ i) (Nat.sub_self _)
      have hRat : ∏ j : Fin r, ((q : ℚ) ^ d - (q : ℚ) ^ j.val) = 0 :=
        prod_eq_zero (mem_univ i) (sub_self _)
      rw [hNat, hRat, Nat.cast_zero]
    · rw [Nat.cast_prod]
      refine prod_congr rfl fun i _ ↦ ?_
      rw [Nat.cast_sub (Nat.pow_le_pow_right hq.le (i.isLt.le.trans (Nat.le_of_not_gt h))),
        Nat.cast_pow, Nat.cast_pow]
  have hden : (∏ i : Fin r, ((q : ℚ) ^ r - (q : ℚ) ^ i.val)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ ↦ sub_ne_zero.mpr (pow_lt_pow_right₀ hqRat i.isLt).ne'
  have hGaussian := gaussianBinomial_mul_prod_pow_sub_pow (q : ℚ) (Fintype.card m) r
  simp only [← Fin.prod_univ_eq_prod_range] at hGaussian
  have hcast : ((gaussianBinomial q (Fintype.card m) r : ℕ) : ℚ) =
      gaussianBinomial (q : ℚ) (Fintype.card m) r :=
    map_gaussianBinomial (Nat.castRingHom ℚ) q _ r
  rw [natCard_rank_eq, Nat.cast_mul, hcast, castProduct, prod_div_distrib, prod_mul_distrib]
  apply (eq_div_iff hden).mpr
  rw [mul_right_comm, hGaussian]

end Matrix
