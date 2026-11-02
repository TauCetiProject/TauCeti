/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.Basic.Real.Basic
import TauCeti.Analysis.Polynomial.RealRoots.Product
import TauCeti.Data.Multiset.Filter
import TauCeti.Data.SignType.Basic
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots

/-!
# Signs of `det (1 - A ^ k)` from the real eigenvalues of `A`

For a real square matrix `A` and a real polynomial `f`, the determinant of `f(A)` is a nonnegative
multiple of the product of `f(x)` over the real characteristic roots `x` of `A`, counted with
algebraic multiplicity: each conjugate pair `λ, conj λ` of nonreal eigenvalues contributes
`|f(λ)|² ≥ 0`. So whenever `det (f(A)) ≠ 0`, its sign is the product of the signs of `f(x)` over
the real eigenvalues.

For `f = 1 - X ^ k` this computes the Lefschetz sign `ε(A ^ k) = sgn det (1 - A ^ k)` of the
`k`-th iterate of a linearized return map `A`. Write `i₊` and `i₋` for the numbers of real
eigenvalues of `A` in `(1, ∞)` and in `(-∞, -1)`, and `i₀` for the number in `(-1, 1)`, all with
algebraic multiplicity. If `1 - A ^ k` is invertible then

`ε(A ^ k) = (-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`.

In particular `ε(A) = (-1) ^ i₊`. If `1 - A ^ k` is invertible for every positive `k`, then the
signs `ε(A ^ k)` alternate in `k` exactly when `i₋` is odd, and are constant otherwise. If no
eigenvalue is `± 1`, the number of nonreal eigenvalues is even, so
`(-1) ^ (i₊ + i₋) = (-1) ^ (n + i₀)` for an `n × n` matrix. For a closed orbit all of whose
iterates are nondegenerate, these identities make the exponential of the logarithmic series
`∑_k ε(A ^ k) t ^ k / k` equal to the factor `(1 - (-1) ^ i₋ t) ^ (-(-1) ^ (i₊ + i₋))` of a
dynamical zeta function; that series identity is not proved here.

## Main results

* `Matrix.exists_det_aeval_eq_mul_prod_roots`: `det (f(A)) = c ∏ f(x)` over the real
  characteristic roots `x` of `A`, for some real `c ≥ 0`.
* `Matrix.sign_det_aeval`: if `det (f(A)) ≠ 0`, its sign is `∏ sgn f(x)` over the real roots.
* `Matrix.sign_det_one_sub_pow`, `LinearMap.sign_det_one_sub_pow`: the iterate sign formula
  `sgn det (1 - A ^ k) = (-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`.
* `Matrix.neg_one_pow_card_roots_charpoly`: the number of real characteristic roots has the parity
  of the size of the matrix.
* `Matrix.neg_one_pow_card_filter_one_lt_add_card_filter_lt_neg_one`: if `1 - A ^ 2` is
  invertible, `(-1) ^ (i₊ + i₋) = (-1) ^ (n + i₀)`.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), 369–396 (the signs of closed orbits and their iterates in the product
  formula for the zeta function).
* D. Fried, *Lefschetz formulas for flows*, Contemp. Math. 58, Part III (1987), 19–69.
-/

public section

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a real square matrix `A` and a real polynomial `f`, `det (f(A))` is a nonnegative multiple
of the product of `f(x)` over the real characteristic roots `x` of `A`, counted with algebraic
multiplicity. -/
theorem exists_det_aeval_eq_mul_prod_roots (A : Matrix n n ℝ) (f : ℝ[X]) :
    ∃ c : ℝ, 0 ≤ c ∧ (aeval A f).det = c * (A.charpoly.roots.map f.eval).prod := by
  obtain ⟨c, hc, h⟩ := A.charpoly.exists_prod_aroots_eq_mul_prod_roots f
  refine ⟨c, hc, Complex.ofReal_injective ?_⟩
  -- Over `ℂ`, `det (f(A))` is the product of `f` over all characteristic roots of `A`.
  have hmap : (algebraMap ℝ ℂ).mapMatrix (aeval A f) = aeval (A.map (algebraMap ℝ ℂ)) f := by
    simpa using (aeval_algHom_apply (Complex.ofRealAm.mapMatrix (m := n)) A f).symm
  -- The complex characteristic roots of `A` are the complex roots of its real charpoly.
  have hroots : (A.map (algebraMap ℝ ℂ)).charpoly.roots = A.charpoly.aroots ℂ := by
    rw [charpoly_map, aroots_def]
  have hdet : ((aeval A f).det : ℂ) =
      (A.charpoly.aroots ℂ |>.map fun z ↦ aeval z f).prod := by
    rw [← Complex.coe_algebraMap, RingHom.map_det, hmap, ← aeval_map_algebraMap ℂ,
      det_aeval_eq_prod_roots_charpoly, hroots]
    simp [eval_map_algebraMap]
  exact hdet.trans h

/-- If `det (f(A)) ≠ 0` for a real square matrix `A` and a real polynomial `f`, its sign is the
product of the signs of `f(x)` over the real characteristic roots `x` of `A`, counted with
algebraic multiplicity. -/
theorem sign_det_aeval (A : Matrix n n ℝ) (f : ℝ[X]) (h : (aeval A f).det ≠ 0) :
    SignType.sign (aeval A f).det =
      (A.charpoly.roots.map fun x ↦ SignType.sign (f.eval x)).prod := by
  obtain ⟨c, hc, hdet⟩ := A.exists_det_aeval_eq_mul_prod_roots f
  have hc : 0 < c := hc.lt_of_ne (by rintro rfl; simp_all)
  rw [hdet, sign_mul, sign_pos hc, one_mul, ← signHom_apply, map_multiset_prod, Multiset.map_map]
  simp

/-- **The sign of an iterate.** If `1 - A ^ k` is invertible for a real square matrix `A`, then
`sgn det (1 - A ^ k) = (-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`, where `i₊` and `i₋` count the real
characteristic roots of `A` in `(1, ∞)` and in `(-∞, -1)`, with algebraic multiplicity. -/
theorem sign_det_one_sub_pow (A : Matrix n n ℝ) (k : ℕ) (h : (1 - A ^ k).det ≠ 0) :
    SignType.sign (1 - A ^ k).det =
      (-1) ^ (A.charpoly.roots.filter (1 < ·)).card *
        (-1) ^ ((k + 1) * (A.charpoly.roots.filter (· < -1)).card) := by
  have haeval : aeval A (1 - X ^ k : ℝ[X]) = 1 - A ^ k := by simp
  rw [← haeval] at h ⊢
  rw [sign_det_aeval A _ h, Multiset.map_congr rfl fun x hx ↦ by
    rw [eval_sub, eval_one, eval_pow, eval_X,
      TauCeti.sign_one_sub_pow (by simpa using eval_ne_zero_of_det_aeval_ne_zero A _ h hx)]]
  rw [Multiset.prod_map_mul, Multiset.prod_map_ite_one, Multiset.prod_map_ite_one, pow_mul]

/-- The number of real characteristic roots of a real square matrix, counted with algebraic
multiplicity, has the parity of its size: the nonreal roots come in conjugate pairs. -/
theorem neg_one_pow_card_roots_charpoly (A : Matrix n n ℝ) :
    (-1 : SignType) ^ A.charpoly.roots.card = (-1) ^ Fintype.card n := by
  have h : (aeval A (C (-1 : ℝ))).det = (-1) ^ Fintype.card n := by simp [det_neg]
  have h0 : (aeval A (C (-1 : ℝ))).det ≠ 0 := by rw [h]; simp
  have := sign_det_aeval A _ h0
  rw [h, sign_pow] at this
  simpa using this.symm

/-- If `1 - A ^ 2` is invertible for a real `n × n` matrix `A`, so that no eigenvalue is `± 1`,
then `(-1) ^ (i₊ + i₋) = (-1) ^ (n + i₀)`, where `i₊`, `i₋` and `i₀` count the real characteristic
roots of `A` in `(1, ∞)`, in `(-∞, -1)` and in `(-1, 1)`, with algebraic multiplicity. -/
theorem neg_one_pow_card_filter_one_lt_add_card_filter_lt_neg_one (A : Matrix n n ℝ)
    (h : (1 - A ^ 2).det ≠ 0) :
    (-1 : SignType) ^ ((A.charpoly.roots.filter (1 < ·)).card +
        (A.charpoly.roots.filter (· < -1)).card) =
      (-1) ^ (Fintype.card n + (A.charpoly.roots.filter (|·| < 1)).card) := by
  have haeval : aeval A (1 - X ^ 2 : ℝ[X]) = 1 - A ^ 2 := by simp
  rw [← haeval] at h
  -- No characteristic root is `± 1`, so each lies in exactly one of the three ranges.
  have hroots : (-1 : SignType) ^ A.charpoly.roots.card =
      (-1) ^ (A.charpoly.roots.filter (1 < ·)).card *
        (-1) ^ (A.charpoly.roots.filter (· < -1)).card *
          (-1) ^ (A.charpoly.roots.filter (|·| < 1)).card := by
    rw [← Multiset.prod_map_ite_one, ← Multiset.prod_map_ite_one, ← Multiset.prod_map_ite_one,
      ← Multiset.prod_map_mul, ← Multiset.prod_map_mul, ← Multiset.prod_replicate,
      ← Multiset.map_const']
    refine congrArg _ (Multiset.map_congr rfl fun x hx ↦ ?_)
    have hx := eval_ne_zero_of_det_aeval_ne_zero A _ h hx
    simp only [eval_sub, eval_one, eval_pow, eval_X] at hx
    have h1 : x ≠ 1 := by rintro rfl; simp at hx
    have h2 : x ≠ -1 := by rintro rfl; simp at hx
    rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · rcases lt_trichotomy x (-1) with hx2 | rfl | hx2
      · simp [hx2, (by linarith : ¬ 1 < x), abs_lt, (by linarith : ¬ -1 < x)]
      · exact absurd rfl h2
      · simp [hx1.not_gt, hx2.not_gt, abs_lt, hx1, hx2]
    · exact absurd rfl h1
    · simp [hx1, (by linarith : ¬ x < -1), abs_lt, hx1.not_gt]
  have hsq (m : ℕ) : (-1 : SignType) ^ m * (-1) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [pow_add, pow_add (-1 : SignType), ← neg_one_pow_card_roots_charpoly A, hroots, mul_assoc,
    hsq, mul_one]

end Matrix

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **The sign of an iterate**, for an endomorphism `f` of a finite-dimensional real vector space:
if `1 - f ^ k` is invertible, then `sgn det (1 - f ^ k) = (-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`, where
`i₊` and `i₋` count the real roots of the characteristic polynomial of `f` in `(1, ∞)` and in
`(-∞, -1)`, with multiplicity. -/
theorem sign_det_one_sub_pow (f : Module.End ℝ V) (k : ℕ) (h : (1 - f ^ k).det ≠ 0) :
    SignType.sign (1 - f ^ k).det =
      (-1) ^ (f.charpoly.roots.filter (1 < ·)).card *
        (-1) ^ ((k + 1) * (f.charpoly.roots.filter (· < -1)).card) := by
  let b := Module.finBasis ℝ V
  have hmat : toMatrix b b (1 - f ^ k) = 1 - toMatrix b b f ^ k := by
    rw [map_sub, toMatrix_one, toMatrix_pow]
  rw [← det_toMatrix b, hmat] at h ⊢
  rw [← charpoly_toMatrix f b]
  exact (toMatrix b b f).sign_det_one_sub_pow k h

end LinearMap
