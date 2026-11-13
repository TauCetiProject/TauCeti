/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Eval.SMul
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.Polynomial.Taylor

/-!
# The confluent Vandermonde determinant

For nodes `a : Fin r → R` in a commutative ring and multiplicities `m : Fin r → ℕ`, the confluent
Vandermonde matrix `Matrix.confluentVandermonde a m` is the square matrix of size
`M = ∑ i, m i` whose row `ρ`, with `⟨i, k⟩ = finSigmaFinEquiv.symm ρ`, lists the Hasse jets
`D^[k] (X ^ j) (a i) = choose j k * a i ^ (j - k)` of the monomials `X ^ j`, `j < M`, in increasing
degree. Rows are in the lexicographic order of the jets `(i, k)`, `k < m i`, so the row of
`⟨i, k⟩` is `∑_{i' < i} m i' + k`. This is the matrix of the Hermite jet map on polynomials of
degree below `M` in the monomial basis.

The determinant is `∏_{i < j} (a j - a i) ^ (m i * m j)` over every commutative ring, with no
injectivity hypothesis on the nodes. The proof changes basis from the monomials to the
Newton–Hermite polynomials `(X - a i) ^ k * ∏_{i' < i} (X - a i') ^ m i'`: the change of basis is
upper unitriangular, and the jet matrix of the new basis is lower triangular with diagonal entry
`∏_{i' < i} (a i - a i') ^ m i'` at the jet `⟨i, k⟩`.

## Main definitions

* `Matrix.confluentVandermonde a m`: the Hasse confluent Vandermonde matrix.
* `Matrix.confluentNodePerm m σ`: the permutation of the jet positions induced by reordering the
  nodes along `σ`.

## Main results

* `Matrix.det_confluentVandermonde`: `det (confluentVandermonde a m) = ∏_{i < j} (a j - a i) ^
  (m i * m j)`; for `a = (1, 0)` and `m = (1, 1)` it is `-1`, which pins the sign.
* `Matrix.confluentVandermonde_mul`: the jet matrix of a family of polynomials of degree below
  `M` is the confluent Vandermonde matrix times their coefficient matrix.
* `Matrix.det_iterate_derivative_eq_prod_factorial_mul_det_confluentVandermonde`: with ordinary
  derivatives `D^k` in place of Hasse derivatives the determinant gains the factor
  `∏ i, ∏_{k < m i} k !`.
* `Matrix.confluentVandermonde_one`, `Matrix.det_confluentVandermonde_one`: for simple nodes the
  matrix is `Matrix.vandermonde a` and the formula is `Matrix.det_vandermonde`.
* `Matrix.confluentNodePerm_cast_finSigmaFinEquiv`: `confluentNodePerm m σ` sends the jet
  `⟨i, k⟩` for `m ∘ σ` to the jet `⟨σ i, k⟩` for `m`.
* `Matrix.det_confluentVandermonde_comp`: reordering the nodes multiplies the determinant by the
  sign of the induced permutation of the rows.
* `Matrix.det_confluentVandermonde_add`, `Matrix.det_confluentVandermonde_smul`:
  translation invariance and homogeneity of degree `∑_{i < j} m i * m j`.
* `Matrix.det_confluentVandermonde_ne_zero_iff`: over a domain the determinant is nonzero iff
  `a i ≠ a j` whenever `i ≠ j` and `m i`, `m j` are both nonzero; a repeated node of
  multiplicity `0` is allowed.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (Grundlehren 326, 2000),
  proof of Lemma 3.24, p. 100, and Exercise 3.11, p. 111 (the transposed matrix, determinant up to
  sign).
-/

public section

open Polynomial Finset
open scoped Nat

namespace Matrix

variable {R : Type*} [CommRing R] {r : ℕ}

/-- The Hasse confluent Vandermonde matrix: rows indexed by `Fin (∑ i, m i)` in the lexicographic
order `finSigmaFinEquiv ⟨i, k⟩` of the jets `(i, k)`, `k < m i`, columns by the monomials `X ^ j`
in increasing degree, entry `(hasseDeriv k (X ^ j)).eval (a i)`. -/
noncomputable def confluentVandermonde (a : Fin r → R) (m : Fin r → ℕ) :
    Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) R :=
  of fun ρ j =>
    (hasseDeriv ((finSigmaFinEquiv.symm ρ).2 : ℕ) (X ^ (j : ℕ) : R[X])).eval
      (a (finSigmaFinEquiv.symm ρ).1)

/-- Unfolding the entries of `confluentVandermonde`. -/
theorem confluentVandermonde_apply (a : Fin r → R) (m : Fin r → ℕ) (ρ j : Fin (∑ i, m i)) :
    confluentVandermonde a m ρ j =
      (hasseDeriv ((finSigmaFinEquiv.symm ρ).2 : ℕ) (X ^ (j : ℕ) : R[X])).eval
        (a (finSigmaFinEquiv.symm ρ).1) := (rfl)

/-- The entry in the row of the jet `⟨i, k⟩` and the column of `X ^ j` is
`choose j k * a i ^ (j - k)`, which is `0` for `k > j` (Mathlib's `hasseDeriv_monomial`). -/
@[simp]
theorem confluentVandermonde_finSigmaFinEquiv (a : Fin r → R) (m : Fin r → ℕ)
    (x : (i : Fin r) × Fin (m i)) (j : Fin (∑ i, m i)) :
    confluentVandermonde a m (finSigmaFinEquiv x) j =
      ((j : ℕ).choose x.2 : R) * a x.1 ^ ((j : ℕ) - x.2) := by
  rw [confluentVandermonde_apply, Equiv.symm_apply_apply]
  simp [← monomial_one_right_eq_X_pow, hasseDeriv_monomial]

/-- The matrix of jets of a family of polynomials of degree below `∑ i, m i` is the confluent
Vandermonde matrix times the matrix of their coefficients. -/
theorem confluentVandermonde_mul (a : Fin r → R) (m : Fin r → ℕ) {n : Type*}
    (p : n → R[X]) (hp : ∀ c, (p c).natDegree < ∑ i, m i) :
    confluentVandermonde a m * of (fun (j : Fin (∑ i, m i)) c => (p c).coeff j) =
      of fun ρ c => (hasseDeriv ((finSigmaFinEquiv.symm ρ).2 : ℕ) (p c)).eval
        (a (finSigmaFinEquiv.symm ρ).1) := by
  ext ρ c
  rw [Matrix.mul_apply, of_apply, as_sum_range' (p c) _ (hp c), ← Fin.sum_univ_eq_sum_range]
  simp only [confluentVandermonde_apply, of_apply, map_sum, eval_finsetSum,
    ← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, eval_smul, smul_eq_mul]
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- The Newton–Hermite polynomial `(X - a i) ^ k * ∏_{i' < i} (X - a i') ^ m i'` attached to the
jet `⟨i, k⟩`. -/
private noncomputable def newtonHermite (a : Fin r → R) (m : Fin r → ℕ)
    (x : (i : Fin r) × Fin (m i)) : R[X] :=
  (X - C (a x.1)) ^ (x.2 : ℕ) * ∏ i ∈ univ.filter (· < x.1), (X - C (a i)) ^ m i

private theorem monic_newtonHermite (a : Fin r → R) (m : Fin r → ℕ)
    (x : (i : Fin r) × Fin (m i)) : (newtonHermite a m x).Monic :=
  ((monic_X_sub_C _).pow _).mul (monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _)

private theorem natDegree_newtonHermite [Nontrivial R] (a : Fin r → R) (m : Fin r → ℕ)
    (x : (i : Fin r) × Fin (m i)) :
    (newtonHermite a m x).natDegree = finSigmaFinEquiv x := by
  rw [newtonHermite, ((monic_X_sub_C _).pow _).natDegree_mul
    (monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _),
    natDegree_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _,
    val_finSigmaFinEquiv_eq_sum_filter]
  simp [(monic_X_sub_C _).natDegree_pow, add_comm]

/-- Jets of `newtonHermite` at later jets vanish. -/
private theorem eval_hasseDeriv_newtonHermite_of_lt (a : Fin r → R) (m : Fin r → ℕ)
    {x y : (i : Fin r) × Fin (m i)} (h : finSigmaFinEquiv x < finSigmaFinEquiv y) :
    (hasseDeriv x.2 (newtonHermite a m y)).eval (a x.1) = 0 := by
  rcases lt_trichotomy x.1 y.1 with hxy | hxy | hxy
  · refine X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.mp ?_ _ x.2.2
    exact (dvd_prod_of_mem _ (by simpa using hxy)).mul_left _
  · obtain ⟨i, k⟩ := x
    obtain ⟨i', k'⟩ := y
    obtain rfl : i = i' := hxy
    rw [Fin.lt_def, val_finSigmaFinEquiv_eq_sum_filter, val_finSigmaFinEquiv_eq_sum_filter] at h
    refine X_sub_C_pow_dvd_iff_forall_eval_hasseDeriv_eq_zero.mp (dvd_mul_right _ _) _ ?_
    simpa using h
  · exact absurd h (finSigmaFinEquiv_lt_of_fst_lt hxy).not_gt

private theorem eval_hasseDeriv_newtonHermite_self (a : Fin r → R) (m : Fin r → ℕ)
    (x : (i : Fin r) × Fin (m i)) :
    (hasseDeriv x.2 (newtonHermite a m x)).eval (a x.1) =
      ∏ i ∈ univ.filter (· < x.1), (a x.1 - a i) ^ m i := by
  rw [← taylor_coeff, newtonHermite, taylor_mul, taylor_pow]
  simp [coeff_X_pow_mul', taylor_coeff_zero, eval_prod]

/-- **The confluent Vandermonde determinant**: over every commutative ring,
`det (confluentVandermonde a m) = ∏_{i < j} (a j - a i) ^ (m i * m j)`, with the sign fixed by
the lexicographic row order and no injectivity hypothesis on `a`. -/
theorem det_confluentVandermonde (a : Fin r → R) (m : Fin r → ℕ) :
    (confluentVandermonde a m).det =
      ∏ i : Fin r, ∏ j : Fin r, if i < j then (a j - a i) ^ (m i * m j) else 1 := by
  nontriviality R
  set N : Fin (∑ i, m i) → R[X] := fun c => newtonHermite a m (finSigmaFinEquiv.symm c)
  have hdeg (c : Fin (∑ i, m i)) : (N c).natDegree = c := by
    simp [N, natDegree_newtonHermite]
  have hC := det_matrixOfPolynomials N hdeg fun c => monic_newtonHermite a m _
  have hL : (of fun (ρ : Fin (∑ i, m i)) c => (hasseDeriv ((finSigmaFinEquiv.symm ρ).2 : ℕ)
      (N c)).eval (a (finSigmaFinEquiv.symm ρ).1)).IsLowerTriangular := by
    intro ρ c hρc
    exact eval_hasseDeriv_newtonHermite_of_lt a m (x := finSigmaFinEquiv.symm ρ)
      (y := finSigmaFinEquiv.symm c) (by simpa using hρc)
  have hJ := congrArg det (confluentVandermonde_mul a m N fun c => (hdeg c).trans_lt c.2)
  rw [det_mul, hC, mul_one, det_of_isLowerTriangular _ hL] at hJ
  rw [hJ]
  simp only [of_apply, N, eval_hasseDeriv_newtonHermite_self]
  rw [finSigmaFinEquiv.symm.prod_comp
    (fun x => ∏ i ∈ univ.filter (· < x.1), (a x.1 - a i) ^ m i), Fintype.prod_sigma]
  simp only [prod_const, card_univ, Fintype.card_fin, ← prod_pow, ← pow_mul]
  rw [prod_comm]
  refine prod_congr rfl fun j _ => ?_
  rw [prod_filter]

/-- The confluent Vandermonde matrix with ordinary derivatives `D^k (X ^ j) (a i)` in place of
Hasse derivatives: row `⟨i, k⟩` is `k !` times that of `confluentVandermonde a m`. -/
theorem det_iterate_derivative_eq_prod_factorial_mul_det_confluentVandermonde (a : Fin r → R)
    (m : Fin r → ℕ) :
    (of fun ρ (j : Fin (∑ i, m i)) => (derivative^[(finSigmaFinEquiv.symm ρ).2] (X ^ (j : ℕ) :
      R[X])).eval (a (finSigmaFinEquiv.symm ρ).1)).det =
      (∏ i, ∏ k ∈ range (m i), (k ! : R)) * (confluentVandermonde a m).det := by
  have h : (of fun ρ (j : Fin (∑ i, m i)) => (derivative^[(finSigmaFinEquiv.symm ρ).2]
      (X ^ (j : ℕ) : R[X])).eval (a (finSigmaFinEquiv.symm ρ).1)) =
      diagonal (fun ρ => (((finSigmaFinEquiv.symm ρ).2 : ℕ) ! : R)) *
        confluentVandermonde a m := by
    ext ρ j
    rw [diagonal_mul, of_apply, confluentVandermonde_apply, ← factorial_smul_hasseDeriv]
    simp
  rw [h, det_mul, det_diagonal]
  congr 1
  rw [finSigmaFinEquiv.symm.prod_comp (fun x => ((x.2 : ℕ) ! : R)), Fintype.prod_sigma]
  exact prod_congr rfl fun i _ => Fin.prod_univ_eq_prod_range (fun k => (k ! : R)) (m i)

/-- With every multiplicity `1`, the confluent Vandermonde matrix is Mathlib's Vandermonde
matrix, reindexed along `∑ i, 1 = r`. -/
theorem confluentVandermonde_one (a : Fin r → R) :
    confluentVandermonde a (fun _ => 1) =
      (vandermonde a).submatrix (finCongr (by simp)) (finCongr (by simp)) := by
  ext ρ j
  have hρ : finSigmaFinEquiv.symm ρ = ⟨finCongr (by simp) ρ, 0⟩ := by
    rw [Equiv.symm_apply_eq]
    ext
    simp
  rw [confluentVandermonde_apply, hρ]
  simp

/-- For simple nodes the confluent Vandermonde determinant is Mathlib's `det_vandermonde`. -/
theorem det_confluentVandermonde_one (a : Fin r → R) :
    (confluentVandermonde a (fun _ => 1)).det = ∏ i : Fin r, ∏ j ∈ Ioi i, (a j - a i) := by
  rw [confluentVandermonde_one, det_submatrix_equiv_self, det_vandermonde]

/-- The permutation of the jet positions induced by reordering the nodes along `σ`: the position
of `⟨i, k⟩` for the multiplicities `m ∘ σ`, read in `Fin (∑ i, m i)` through
`∑ i, m (σ i) = ∑ i, m i`, goes to the position of `⟨σ i, k⟩` for `m`. -/
def confluentNodePerm (m : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (∑ i, m i)) :=
  (finCongr (Equiv.sum_comp σ m)).symm.trans
    (finSigmaFinEquiv.symm.trans
      ((Equiv.sigmaCongrLeft (β := fun i => Fin (m i)) σ).trans finSigmaFinEquiv))

/-- `confluentNodePerm m σ` sends the jet `⟨i, k⟩` for the multiplicities `m ∘ σ` to the jet
`⟨σ i, k⟩` for `m`. -/
@[simp]
theorem confluentNodePerm_cast_finSigmaFinEquiv (m : Fin r → ℕ) (σ : Equiv.Perm (Fin r))
    (x : (i : Fin r) × Fin (m (σ i))) :
    confluentNodePerm m σ (Fin.cast (Equiv.sum_comp σ m) (finSigmaFinEquiv x)) =
      finSigmaFinEquiv (⟨σ x.1, x.2⟩ : (i : Fin r) × Fin (m i)) := by
  simp [confluentNodePerm]

/-- Reordering the nodes and multiplicities along `σ` permutes the rows of the confluent
Vandermonde matrix by `confluentNodePerm m σ`. -/
theorem confluentVandermonde_comp (a : Fin r → R) (m : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    confluentVandermonde (a ∘ σ) (m ∘ σ) =
      ((confluentVandermonde a m).submatrix (confluentNodePerm m σ) id).submatrix
        (finCongr (Equiv.sum_comp σ m)) (finCongr (Equiv.sum_comp σ m)) := by
  ext ρ j
  obtain ⟨x, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [submatrix_apply, submatrix_apply, finCongr_apply,
    confluentNodePerm_cast_finSigmaFinEquiv, confluentVandermonde_finSigmaFinEquiv,
    confluentVandermonde_finSigmaFinEquiv]
  simp

/-- Reordering the nodes and multiplicities along `σ` multiplies the determinant by the sign of
the induced permutation of the jet positions. -/
theorem det_confluentVandermonde_comp (a : Fin r → R) (m : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    (confluentVandermonde (a ∘ σ) (m ∘ σ)).det =
      Equiv.Perm.sign (confluentNodePerm m σ) * (confluentVandermonde a m).det := by
  rw [confluentVandermonde_comp, det_submatrix_equiv_self, det_permute]

/-- Translating the nodes leaves the determinant unchanged. -/
theorem det_confluentVandermonde_add (a : Fin r → R) (m : Fin r → ℕ) (c : R) :
    (confluentVandermonde (fun i => a i + c) m).det = (confluentVandermonde a m).det := by
  simp only [det_confluentVandermonde, add_sub_add_right_eq_sub]

/-- Scaling the nodes by `u` multiplies the determinant by `u ^ (∑_{i < j} m i * m j)`. -/
theorem det_confluentVandermonde_smul (a : Fin r → R) (m : Fin r → ℕ) (u : R) :
    (confluentVandermonde (u • a) m).det =
      u ^ (∑ i : Fin r, ∑ j : Fin r, if i < j then m i * m j else 0) *
        (confluentVandermonde a m).det := by
  simp only [det_confluentVandermonde, Pi.smul_apply, smul_eq_mul, ← mul_sub, ← prod_pow_eq_pow_sum,
    ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_pow]

/-- Over a domain the confluent Vandermonde determinant vanishes exactly when two distinct nodes
of nonzero multiplicity coincide. -/
theorem det_confluentVandermonde_ne_zero_iff [IsDomain R] (a : Fin r → R) (m : Fin r → ℕ) :
    (confluentVandermonde a m).det ≠ 0 ↔
      ∀ i j, i ≠ j → m i ≠ 0 → m j ≠ 0 → a i ≠ a j := by
  simp only [det_confluentVandermonde, prod_ne_zero_iff, mem_univ, forall_const]
  constructor
  · intro h i j hij hi hj
    rcases hij.lt_or_gt with hij | hij
    · have := h i j
      rw [ite_eq_left hij, pow_ne_zero_iff (mul_ne_zero hi hj), sub_ne_zero] at this
      exact this.symm
    · have := h j i
      rw [ite_eq_left hij, pow_ne_zero_iff (mul_ne_zero hj hi), sub_ne_zero] at this
      exact this
  · intro h i j
    split_ifs with hij
    · by_cases hm : m i * m j = 0
      · simp [hm]
      · rw [← Ne, mul_ne_zero_iff] at hm
        exact pow_ne_zero _ (sub_ne_zero.2 (h j i hij.ne' hm.2 hm.1))
    · exact one_ne_zero

/-- Over a domain, injective nodes give a nonzero confluent Vandermonde determinant. -/
theorem det_confluentVandermonde_ne_zero [IsDomain R] {a : Fin r → R} (ha : Function.Injective a)
    (m : Fin r → ℕ) : (confluentVandermonde a m).det ≠ 0 :=
  (det_confluentVandermonde_ne_zero_iff a m).2 fun _ _ hij _ _ => ha.ne hij

/-! ### Checks -/

section Checks

/-- Rows `(0,0)`, `(0,1)`, `(1,0)` for the double node `0` and the simple node `1`. -/
example : confluentVandermonde ![(0 : ℤ), 1] ![2, 1] = !![1, 0, 0; 0, 1, 0; 1, 1, 1] := by
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [confluentVandermonde_finSigmaFinEquiv]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

example : (confluentVandermonde ![(0 : ℤ), 1] ![2, 1]).det = 1 := by
  simp [det_confluentVandermonde, Fin.prod_univ_two]

/-- The sign check: the lexicographic row order gives `(a 1 - a 0) ^ 1 = -1`. -/
example : confluentVandermonde ![(1 : ℤ), 0] ![1, 1] = !![1, 1; 1, 0] := by
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [confluentVandermonde_finSigmaFinEquiv]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

example : (confluentVandermonde ![(1 : ℤ), 0] ![1, 1]).det = -1 := by
  simp [det_confluentVandermonde, Fin.prod_univ_two]

/-- The formula with `a i - a j` in place of `a j - a i` has the wrong sign. -/
example : (∏ i : Fin 2, ∏ j : Fin 2,
    if i < j then (![(1 : ℤ), 0] i - ![(1 : ℤ), 0] j) ^ (![1, 1] i * ![1, 1] j) else 1) = 1 := by
  simp [Fin.prod_univ_two]

example : confluentVandermonde ![(1 : ℤ), 0] ![2, 1] = !![1, 1, 1; 0, 1, 2; 1, 0, 0] := by
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [confluentVandermonde_finSigmaFinEquiv]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

example : (confluentVandermonde ![(1 : ℤ), 0] ![2, 1]).det = 1 := by
  simp [det_confluentVandermonde, Fin.prod_univ_two]

example : (confluentVandermonde ![(0 : ℤ), 1, 2] ![2, 1, 1]).det = 4 := by
  simp [det_confluentVandermonde, Fin.prod_univ_three]

/-- The ordinary-derivative matrix for the same nodes: every `k < 2` has `k ! = 1`. -/
example : (of fun ρ (j : Fin (∑ i, ![2, 1, 1] i)) =>
    (derivative^[(finSigmaFinEquiv.symm ρ).2] (X ^ (j : ℕ) : ℤ[X])).eval
      (![(0 : ℤ), 1, 2] (finSigmaFinEquiv.symm ρ).1)).det = 4 := by
  rw [det_iterate_derivative_eq_prod_factorial_mul_det_confluentVandermonde,
    det_confluentVandermonde]
  simp [Fin.prod_univ_three, Finset.prod_range_succ]

example : (confluentVandermonde ![(2 : ℤ), 5, 7] (fun _ => 1)).det = 30 := by
  rw [det_confluentVandermonde_one]
  simp [Fin.prod_univ_succ, Fin.prod_Ioi_succ]

/-- One triple node: the matrix is upper unitriangular. -/
example : confluentVandermonde ![(5 : ℤ)] ![3] = !![1, 5, 25; 0, 1, 10; 0, 0, 1] := by
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [confluentVandermonde_finSigmaFinEquiv]
  fin_cases i
  fin_cases k <;> fin_cases j <;> decide

example : (confluentVandermonde ![(5 : ℤ)] ![3]).det = 1 := by
  simp [det_confluentVandermonde]

/-- The ordinary-derivative matrix at the triple node `0` is `diag (0!, 1!, 2!)`. -/
example : (of fun ρ (j : Fin (∑ i, ![3] i)) =>
    (derivative^[(finSigmaFinEquiv.symm ρ).2] (X ^ (j : ℕ) : ℤ[X])).eval
      (![(0 : ℤ)] (finSigmaFinEquiv.symm ρ).1)).det = 2 := by
  rw [det_iterate_derivative_eq_prod_factorial_mul_det_confluentVandermonde,
    det_confluentVandermonde]
  simp [Finset.prod_range_succ]

/-- No nodes, or all multiplicities zero: the `0 × 0` determinant is `1`. -/
example (a : Fin 0 → ℤ) (m : Fin 0 → ℕ) : (confluentVandermonde a m).det = 1 := by
  simp [det_confluentVandermonde]

example (a : Fin 2 → ℤ) : (confluentVandermonde a 0).det = 1 := by
  simp [det_confluentVandermonde]

/-- A repeated simple node: the determinant is `0 ^ 1`; the formula needs no injectivity. -/
example : (confluentVandermonde ![(0 : ℤ), 0] ![1, 1]).det = 0 := by
  simp [det_confluentVandermonde, Fin.prod_univ_two]

/-- A repeated node of multiplicity zero does not matter: `a` is not injective, yet the matrix is
`[[1, 0], [1, 1]]` with determinant `1`. -/
example : confluentVandermonde ![(0 : ℤ), 0, 1] ![1, 0, 1] = !![1, 0; 1, 1] := by
  ext ρ j
  obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective ρ
  rw [confluentVandermonde_finSigmaFinEquiv]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

example : (confluentVandermonde ![(0 : ℤ), 0, 1] ![1, 0, 1]).det = 1 := by
  simp [det_confluentVandermonde, Fin.prod_univ_three]

example : ¬ Function.Injective ![(0 : ℤ), 0, 1] ∧
    (confluentVandermonde ![(0 : ℤ), 0, 1] ![1, 0, 1]).det ≠ 0 := by
  refine ⟨fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide), ?_⟩
  rw [det_confluentVandermonde_ne_zero_iff]
  decide

end Checks

end Matrix
