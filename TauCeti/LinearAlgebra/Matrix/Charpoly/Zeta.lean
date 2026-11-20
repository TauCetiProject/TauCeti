/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Newton
public import TauCeti.RingTheory.PowerSeries.Log

/-!
# The trace–determinant formula and Lefschetz zeta functions

For a square matrix `A` over a commutative ring, the generating series of the traces of its powers
is the logarithmic derivative of `det (1 - X A) = Matrix.charpolyRev A`:

`(∑ₖ tr (A ^ (k + 1)) Xᵏ) det (1 - X A) = -d/dX det (1 - X A)`.

This is the generating-function form of Newton's identities
(`Matrix.mul_coeff_charpolyRev_eq_neg_sum`), and it holds over every commutative ring. Over a
`ℚ`-algebra it integrates to the **trace–determinant formula**

`log det (1 - X A) = -∑ₖ tr (A ^ k) Xᵏ / k`,  `exp (∑ₖ tr (A ^ k) Xᵏ / k) = det (1 - X A)⁻¹`.

The same holds for an endomorphism `f` of a finite free module, with `det (1 - X f)` the reverse
of its characteristic polynomial.

The formula computes the zeta function of a map from its action on homology. If `φ` acts on the
homology groups `Hᵢ` by `fᵢ`, its Lefschetz numbers are `L (φ ^ k) = ∑ᵢ (-1) ^ i tr (fᵢ ^ k)`, and
its homological zeta function `exp (∑ₖ L (φ ^ k) Xᵏ / k)` is the alternating product

`exp (∑ₖ L (φ ^ k) Xᵏ / k) = ∏ᵢ det (1 - X fᵢ) ^ (-1) ^ (i + 1)`

(`LinearMap.subst_exp_mul_prod_even_eq_prod_odd`, stated without inverses). The left side is
defined for every map, whether or not its fixed points are isolated; when they are, and all the
iterates are nondegenerate, the Lefschetz fixed point theorem identifies `L (φ ^ k)` with the
signed count of the fixed points of `φ ^ k`, and the left side becomes the dynamical zeta
function. For instance, Arnold's cat map acts on `H₀`, `H₁` and `H₂` of the torus by `1`, `P` and
`det P = 1`, so its homological zeta function is `det (1 - X P) / (1 - X) ^ 2`.

## Main results

* `Matrix.mk_trace_pow_succ_mul_charpolyRev`: Newton's identities as the power series identity
  `(∑ₖ tr (A ^ (k + 1)) Xᵏ) det (1 - X A) = -d/dX det (1 - X A)`.
* `Matrix.logOf_charpolyRev`: `log det (1 - X A) = -∑ₖ tr (A ^ k) Xᵏ / k`.
* `Matrix.subst_exp_mul_charpolyRev`, `Matrix.subst_exp_eq_inv_charpolyRev`: the trace–determinant
  formula `exp (∑ₖ tr (A ^ k) Xᵏ / k) = det (1 - X A)⁻¹`.
* `LinearMap.logOf_reverse_charpoly`, `LinearMap.subst_exp_mul_reverse_charpoly`,
  `LinearMap.subst_exp_eq_inv_reverse_charpoly`: the same for an endomorphism of a finite free
  module.
* `LinearMap.subst_exp_mul_prod_even_eq_prod_odd`, `LinearMap.subst_exp_eq_prod_odd_mul_inv`: the
  homological zeta function of a graded endomorphism is the alternating product of the
  `det (1 - X fᵢ)`.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Ch. I,
  §2, (2.10′).
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  209–244, Example 1.9 (the mapping-torus zeta function and its determinant formula).
-/

public section

open PowerSeries Finset

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The power series `det (1 - X A)` has constant coefficient one. -/
theorem constantCoeff_coe_charpolyRev (A : Matrix n n R) :
    constantCoeff (A.charpolyRev : R⟦X⟧) = 1 := by
  rw [Polynomial.constantCoeff_coe, coeff_charpolyRev_zero]

/-- **Newton's identities as a power series identity.** The generating series of the traces of
the positive powers of `A` is minus the logarithmic derivative of `det (1 - X A)`:
`(∑ₖ tr (A ^ (k + 1)) Xᵏ) det (1 - X A) = -d/dX det (1 - X A)`. -/
theorem mk_trace_pow_succ_mul_charpolyRev (A : Matrix n n R) :
    (mk fun k ↦ (A ^ (k + 1)).trace) * (A.charpolyRev : R⟦X⟧) =
      -d⁄dX (A.charpolyRev : R⟦X⟧) := by
  ext r
  have h := A.mul_coeff_charpolyRev_eq_neg_sum (r + 1)
  push_cast at h
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_neg, coeff_derivative,
    Polynomial.coeff_coe, mul_comm _ ((r : R) + 1), h, neg_neg]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [coeff_mk, Polynomial.coeff_coe, mul_comm]

variable [Algebra ℚ R]

/-- **The logarithm of `det (1 - X A)`** is `-∑ₖ tr (A ^ k) Xᵏ / k`. -/
theorem logOf_charpolyRev (A : Matrix n n R) :
    logOf (A.charpolyRev : R⟦X⟧) = mk fun k ↦ (k : ℚ)⁻¹ • -(A ^ k).trace := by
  have hneg : (mk fun k ↦ -(A ^ (k + 1)).trace : R⟦X⟧) = -mk fun k ↦ (A ^ (k + 1)).trace := by
    ext k
    simp
  rw [logOf_eq_mk_iff (constantCoeff_coe_charpolyRev A), hneg, neg_mul,
    mk_trace_pow_succ_mul_charpolyRev, neg_neg]

/-- **The trace–determinant formula** `exp (∑ₖ tr (A ^ k) Xᵏ / k) = det (1 - X A)⁻¹`, stated
without inverses. -/
theorem subst_exp_mul_charpolyRev (A : Matrix n n R) :
    (exp R).subst (mk fun k ↦ (k : ℚ)⁻¹ • (A ^ k).trace) * (A.charpolyRev : R⟦X⟧) = 1 := by
  have hL : constantCoeff (mk fun k ↦ (k : ℚ)⁻¹ • (A ^ k).trace : R⟦X⟧) = 0 := by simp
  rw [← logOf_inj (by rw [map_mul, constantCoeff_subst_exp hL, constantCoeff_coe_charpolyRev,
      one_mul]) constantCoeff_one,
    logOf_mul (constantCoeff_subst_exp hL) (constantCoeff_coe_charpolyRev A), logOf_subst_exp hL,
    logOf_charpolyRev, logOf_one]
  ext k
  simp

/-- **The trace–determinant formula** over a field of characteristic zero:
`exp (∑ₖ tr (A ^ k) Xᵏ / k) = det (1 - X A)⁻¹`. -/
theorem subst_exp_eq_inv_charpolyRev {K : Type*} [Field K] [Algebra ℚ K] (A : Matrix n n K) :
    (exp K).subst (mk fun k ↦ (k : ℚ)⁻¹ • (A ^ k).trace) = (A.charpolyRev : K⟦X⟧)⁻¹ :=
  (PowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_coe_charpolyRev]; exact one_ne_zero)).2
    A.subst_exp_mul_charpolyRev

end Matrix

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- The power series `det (1 - X f)` has constant coefficient one. -/
theorem constantCoeff_coe_reverse_charpoly (f : Module.End R M) :
    constantCoeff (f.charpoly.reverse : R⟦X⟧) = 1 := by
  rw [charpoly_def, Matrix.reverse_charpoly, Matrix.constantCoeff_coe_charpolyRev]

variable [Algebra ℚ R]

/-- **The logarithm of `det (1 - X f)`** for an endomorphism `f` of a finite free module is
`-∑ₖ tr (f ^ k) Xᵏ / k`. -/
theorem logOf_reverse_charpoly (f : Module.End R M) :
    logOf (f.charpoly.reverse : R⟦X⟧) =
      PowerSeries.mk fun k ↦ (k : ℚ)⁻¹ • -trace R M (f ^ k) := by
  rw [charpoly_def, Matrix.reverse_charpoly]
  simp only [trace_eq_matrix_trace R (Module.Free.chooseBasis R M), ← LinearMap.toMatrix_pow]
  exact Matrix.logOf_charpolyRev _

/-- **The trace–determinant formula** `exp (∑ₖ tr (f ^ k) Xᵏ / k) = det (1 - X f)⁻¹` for an
endomorphism `f` of a finite free module, stated without inverses. -/
theorem subst_exp_mul_reverse_charpoly (f : Module.End R M) :
    (exp R).subst (PowerSeries.mk fun k ↦ (k : ℚ)⁻¹ • trace R M (f ^ k)) *
      (f.charpoly.reverse : R⟦X⟧) = 1 := by
  rw [charpoly_def, Matrix.reverse_charpoly]
  simp only [trace_eq_matrix_trace R (Module.Free.chooseBasis R M), ← LinearMap.toMatrix_pow]
  exact Matrix.subst_exp_mul_charpolyRev _

/-- **The trace–determinant formula** `exp (∑ₖ tr (f ^ k) Xᵏ / k) = det (1 - X f)⁻¹` for an
endomorphism `f` of a finite-dimensional vector space over a field of characteristic zero. -/
theorem subst_exp_eq_inv_reverse_charpoly {K V : Type*} [Field K] [Algebra ℚ K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) :
    (exp K).subst (PowerSeries.mk fun k ↦ (k : ℚ)⁻¹ • trace K V (f ^ k)) =
      (f.charpoly.reverse : K⟦X⟧)⁻¹ :=
  (PowerSeries.eq_inv_iff_mul_eq_one
    (by rw [constantCoeff_coe_reverse_charpoly]; exact one_ne_zero)).2
    f.subst_exp_mul_reverse_charpoly

/-- **The homological zeta function of a graded endomorphism.** Let `fᵢ` be endomorphisms of finite
free modules `Vᵢ`, for `i` in a finite set `s` of degrees, with Lefschetz numbers
`L k = ∑ᵢ (-1) ^ i tr (fᵢ ^ k)`. Then `exp (∑ₖ L k Xᵏ / k)` is the alternating product
`∏ᵢ det (1 - X fᵢ) ^ (-1) ^ (i + 1)`, stated without inverses: multiplied by the factors of even
degree it is the product of the factors of odd degree. -/
theorem subst_exp_mul_prod_even_eq_prod_odd (s : Finset ℕ) {V : ℕ → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, Module.Free R (V i)]
    [∀ i, Module.Finite R (V i)] (f : ∀ i, Module.End R (V i)) :
    (exp R).subst
        (PowerSeries.mk fun k ↦ (k : ℚ)⁻¹ • ∑ i ∈ s, (-1) ^ i * trace R (V i) (f i ^ k)) *
        ∏ i ∈ s with Even i, ((f i).charpoly.reverse : R⟦X⟧) =
      ∏ i ∈ s with Odd i, ((f i).charpoly.reverse : R⟦X⟧) := by
  set L : R⟦X⟧ :=
    PowerSeries.mk fun k ↦ (k : ℚ)⁻¹ • ∑ i ∈ s, (-1) ^ i * trace R (V i) (f i ^ k)
  have hL : constantCoeff L = 0 := by
    simp [L]
  have hc (t : Finset ℕ) : constantCoeff (∏ i ∈ t, ((f i).charpoly.reverse : R⟦X⟧)) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun i _ ↦ constantCoeff_coe_reverse_charpoly (f i)
  rw [← logOf_inj (by rw [map_mul, constantCoeff_subst_exp hL, hc, one_mul]) (hc _),
    logOf_mul (constantCoeff_subst_exp hL) (hc _), logOf_subst_exp hL,
    logOf_prod fun i _ ↦ constantCoeff_coe_reverse_charpoly (f i),
    logOf_prod fun i _ ↦ constantCoeff_coe_reverse_charpoly (f i)]
  simp only [logOf_reverse_charpoly]
  -- Compare coefficients: the terms of even degree cancel, those of odd degree remain.
  ext k
  have he : ∑ i ∈ s with Even i, (-1 : R) ^ i * trace R (V i) (f i ^ k) =
      ∑ i ∈ s with Even i, trace R (V i) (f i ^ k) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2.neg_one_pow, one_mul]
  have ho : ∑ i ∈ s with ¬Even i, (-1 : R) ^ i * trace R (V i) (f i ^ k) =
      -∑ i ∈ s with Odd i, trace R (V i) (f i ^ k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr (by simp only [Nat.not_even_iff_odd]) fun i hi ↦ ?_
    rw [(Finset.mem_filter.1 hi).2.neg_one_pow, neg_one_mul]
  simp only [L, map_add, map_sum, coeff_mk]
  rw [← Finset.sum_filter_add_sum_filter_not s Even, he, ho]
  simp only [smul_add, smul_neg, Finset.smul_sum, Finset.sum_neg_distrib]
  abel

/-- **The homological zeta function of a graded endomorphism** over a field of characteristic
zero: `exp (∑ₖ L k Xᵏ / k)` is the product of the `det (1 - X fᵢ)` of odd degree divided by the
product of those of even degree. -/
theorem subst_exp_eq_prod_odd_mul_inv {K : Type*} [Field K] [Algebra ℚ K] (s : Finset ℕ)
    {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (f : ∀ i, Module.End K (V i)) :
    (exp K).subst
        (PowerSeries.mk fun k ↦ (k : ℚ)⁻¹ • ∑ i ∈ s, (-1) ^ i * trace K (V i) (f i ^ k)) =
      (∏ i ∈ s with Odd i, ((f i).charpoly.reverse : K⟦X⟧)) *
        (∏ i ∈ s with Even i, ((f i).charpoly.reverse : K⟦X⟧))⁻¹ := by
  have hc : constantCoeff (∏ i ∈ s with Even i, ((f i).charpoly.reverse : K⟦X⟧)) ≠ 0 := by
    rw [map_prod, Finset.prod_eq_one fun i _ ↦ constantCoeff_coe_reverse_charpoly (f i)]
    exact one_ne_zero
  rw [← subst_exp_mul_prod_even_eq_prod_odd, mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]

end LinearMap
