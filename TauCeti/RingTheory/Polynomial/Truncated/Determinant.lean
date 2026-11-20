/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.PowerBasis
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.Algebra.Polynomial.Taylor

/-!
# Determinants of polynomial power expansions on a thickening `R[X] / ((X - c) ^ n)`

Let `R` be a commutative ring, `c : R` and `f : R[X]`. Expanding the powers
`1, f, f ^ 2, …, f ^ (n - 1)` modulo `(X - C c) ^ n` in the monomial basis `1, X, …, X ^ (n - 1)`
produces an `n × n` matrix `A` over `R` satisfying

`(X - C c) ^ n ∣ f ^ i - ∑ j : Fin n, C (A j i) * X ^ j`

for every `i : Fin n`. This is the matrix of the `R`-linear composition map `g ↦ g.comp f` from the
degree-bounded polynomials `R[X]_n` to the thickened point `R[X] / ((X - C c) ^ n)`.

This file computes its determinant:

`det A = (f.derivative.eval c) ^ (n * (n - 1) / 2)`.

Following Schröer's (2009) unitriangular Taylor-shift proof, changing basis on the target via
`X ↦ X + C c` (`Polynomial.taylor c`) and on the source from `X ^ i` to `(X - C (f.eval c)) ^ i`
multiplies `A` on both sides by upper-triangular monic polynomial coefficient matrices of
determinant `1` (`Matrix.det_matrixOfPolynomials`), turning `A` into the lower-triangular matrix of
coefficients of `(taylor c f - C (f.eval c)) ^ i` below degree `n`, whose `i`-th diagonal entry is
`(f.derivative.eval c) ^ i`.

In exponential characteristic `p`, `(X - C c) ^ p ^ e = X ^ p ^ e - C (c ^ p ^ e)`, so for any
power basis `pb` of `S` over `R` of dimension `pb.dim = p ^ e` with `pb.gen ^ pb.dim ∈ R`, the
transition matrix from `pb.basis` to the powers of `aeval pb.gen f` has determinant
`aeval pb.gen f.derivative ^ (pb.dim * (pb.dim - 1) / 2)` in `S`
(`PowerBasis.det_toMatrix_aeval_pow`). This is the local determinant step in Schröer's (2009) proof
of Tate's (1952) genus-change theorem.

## Main results

* `Matrix.det_of_X_sub_C_pow_dvd_pow_sub_sum`: any `n × n` matrix whose `i`-th column gives the
  expansion of `f ^ i` modulo `(X - C c) ^ n` has determinant
  `f.derivative.eval c ^ (n * (n - 1) / 2)`.
* `Polynomial.det_coeff_pow_modByMonic_X_sub_C_pow`: the closed form for the remainder matrix
  `((f ^ i) %ₘ ((X - C c) ^ n)).coeff j`.
* `PowerBasis.det_toMatrix_aeval_pow`: for a power basis `pb` of dimension `p ^ e` in exponential
  characteristic `p` with `pb.gen ^ pb.dim ∈ R`, the determinant of the transition matrix from
  `pb.basis` to the powers of `aeval pb.gen f` equals
  `aeval pb.gen f.derivative ^ (pb.dim * (pb.dim - 1) / 2)` in `S`.

## References

* S. Schröer, *On genus change in algebraic curves over imperfect fields*, Proc. Amer. Math. Soc.
  137 (2009), 1239–1243.
* J. Tate, *Genus change in inseparable extensions of function fields*, Proc. Amer. Math. Soc. 3
  (1952), 400–406.
-/

public section

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Shifting `f ^ i ≡ ∑_j A_{j,i} X^j (mod (X - c)^n)` by `taylor c` expresses the low-degree
coefficients of `(taylor c f) ^ i` by multiplying `A` on the left by the monic shift matrix of
`X + C c`. -/
private theorem shift_mul_apply_of_X_sub_C_pow_dvd {f : R[X]} {c : R} {A : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i : Fin n, (X - C c) ^ n ∣ f ^ (i : ℕ) - ∑ j : Fin n, C (A j i) * X ^ (j : ℕ))
    (k i : Fin n) :
    ((of fun k j : Fin n ↦ ((X + C c) ^ (j : ℕ)).coeff k) * A) k i =
      ((taylor c f) ^ (i : ℕ)).coeff k := by
  have hdvd : X ^ n ∣ (taylor c f) ^ (i : ℕ) - ∑ j : Fin n, C (A j i) * (X + C c) ^ (j : ℕ) := by
    simpa [taylor_apply] using X_sub_C_pow_dvd_iff.mp (hA i)
  have hzero : ((taylor c f) ^ (i : ℕ)).coeff k =
      (∑ j : Fin n, C (A j i) * (X + C c) ^ (j : ℕ)).coeff k := by
    rw [← sub_eq_zero, ← coeff_sub]
    exact (X_pow_dvd_iff.mp hdvd) k k.isLt
  rw [hzero, finsetSum_coeff, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [of_apply, coeff_C_mul, mul_comm]

/-- Multiplying on the right by the monic shift matrix of `X - C (f.eval c)` turns the columns from
`(taylor c f) ^ m` into `(taylor c f - C (f.eval c)) ^ i`. -/
private theorem shift_mul_shift_apply {f : R[X]} {c : R} {A : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i : Fin n, (X - C c) ^ n ∣ f ^ (i : ℕ) - ∑ j : Fin n, C (A j i) * X ^ (j : ℕ))
    (k i : Fin n) :
    ((of fun k j : Fin n ↦ ((X + C c) ^ (j : ℕ)).coeff k) * A *
        of fun m i : Fin n ↦ ((X + C (-f.eval c)) ^ (i : ℕ)).coeff m) k i =
      ((taylor c f - C (f.eval c)) ^ (i : ℕ)).coeff k := by
  nontriviality R
  rw [Matrix.mul_apply]
  simp_rw [shift_mul_apply_of_X_sub_C_pow_dvd hA, of_apply]
  have hdeg : ((X + C (-f.eval c)) ^ (i : ℕ)).natDegree < n :=
    natDegree_pow_le.trans_lt (by rw [natDegree_X_add_C, mul_one]; exact i.isLt)
  have hsum : ((X + C (-f.eval c)) ^ (i : ℕ)).comp (taylor c f) =
      ∑ m ∈ Finset.range n,
        C (((X + C (-f.eval c)) ^ (i : ℕ)).coeff m) * (taylor c f) ^ m := by
    rw [comp_eq_sum_left, sum_over_range' _ _ n hdeg]
    simp
  have hcomp : ((X + C (-f.eval c)) ^ (i : ℕ)).comp (taylor c f) =
      (taylor c f - C (f.eval c)) ^ (i : ℕ) := by
    simp [sub_eq_add_neg]
  rw [← hcomp, hsum, finsetSum_coeff, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [coeff_C_mul, mul_comm]

/-- **Determinant of a polynomial power-expansion matrix modulo `(X - C c) ^ n`**: if each column
`i` of `A : Matrix (Fin n) (Fin n) R` gives the coefficients of `f ^ i` modulo `(X - C c) ^ n`, then
`det A = (f.derivative.eval c) ^ (n * (n - 1) / 2)`. -/
theorem det_of_X_sub_C_pow_dvd_pow_sub_sum {f : R[X]} {c : R} {A : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i : Fin n, (X - C c) ^ n ∣ f ^ (i : ℕ) - ∑ j : Fin n, C (A j i) * X ^ (j : ℕ)) :
    A.det = f.derivative.eval c ^ (n * (n - 1) / 2) := by
  nontriviality R
  let P : Matrix (Fin n) (Fin n) R := of fun k j ↦ ((X + C c) ^ (j : ℕ)).coeff k
  let Q : Matrix (Fin n) (Fin n) R := of fun m i ↦ ((X + C (-f.eval c)) ^ (i : ℕ)).coeff m
  have hP : P.det = 1 := det_matrixOfPolynomials (fun j : Fin n ↦ (X + C c) ^ (j : ℕ))
    (fun j ↦ by rw [(monic_X_add_C c).natDegree_pow, natDegree_X_add_C, mul_one])
    (fun j ↦ (monic_X_add_C c).pow _)
  have hQ : Q.det = 1 := det_matrixOfPolynomials (fun i : Fin n ↦ (X + C (-f.eval c)) ^ (i : ℕ))
    (fun i ↦ by rw [(monic_X_add_C _).natDegree_pow, natDegree_X_add_C, mul_one])
    (fun i ↦ (monic_X_add_C _).pow _)
  have hlow : (P * A * Q).IsLowerTriangular := fun k i hki ↦ by
    dsimp only [P, Q]
    rw [shift_mul_shift_apply hA]
    exact coeff_taylor_sub_C_eval_pow_of_lt f c hki
  have hdet : (P * A * Q).det = A.det := by rw [det_mul, det_mul, hP, hQ, one_mul, mul_one]
  rw [← hdet, det_of_isLowerTriangular _ hlow]
  have hdiag (i : Fin n) : (P * A * Q) i i = f.derivative.eval c ^ (i : ℕ) := by
    dsimp only [P, Q]
    rw [shift_mul_shift_apply hA, coeff_taylor_sub_C_eval_pow_self]
  simp_rw [hdiag]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i ↦ i) n, Finset.sum_range_id]

end Matrix

namespace Polynomial

/-- **Determinant of the `modByMonic` power-expansion matrix modulo `(X - C c) ^ n`**: the `n × n`
matrix whose `(j, i)`-entry is the `X ^ j`-coefficient of `(f ^ i) %ₘ ((X - C c) ^ n)` has
determinant `(f.derivative.eval c) ^ (n * (n - 1) / 2)`. -/
theorem det_coeff_pow_modByMonic_X_sub_C_pow {R : Type*} [CommRing R] (n : ℕ) (f : R[X])
    (c : R) :
    (Matrix.of fun j i : Fin n ↦ ((f ^ (i : ℕ)) %ₘ ((X - C c) ^ n)).coeff j).det =
      f.derivative.eval c ^ (n * (n - 1) / 2) := by
  nontriviality R
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine Matrix.det_of_X_sub_C_pow_dvd_pow_sub_sum fun i ↦ ?_
  have hm : ((X - C c) ^ n).Monic := (monic_X_sub_C c).pow n
  have hnd : ((X - C c) ^ n).natDegree = n := by
    rw [(monic_X_sub_C c).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hne1 : (X - C c) ^ n ≠ 1 := fun h1 ↦ by
    have := congrArg natDegree h1
    rw [hnd, natDegree_one] at this
    omega
  have hdeg : ((f ^ (i : ℕ)) %ₘ ((X - C c) ^ n)).natDegree < n :=
    (natDegree_modByMonic_lt _ hm hne1).trans_eq hnd
  have hsum : ∑ j : Fin n, C (((f ^ (i : ℕ)) %ₘ ((X - C c) ^ n)).coeff j) * X ^ (j : ℕ) =
      (f ^ (i : ℕ)) %ₘ ((X - C c) ^ n) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun m ↦ C (((f ^ (i : ℕ)) %ₘ ((X - C c) ^ n)).coeff m) * X ^ m) n]
    exact (((f ^ (i : ℕ)) %ₘ ((X - C c) ^ n)).as_sum_range_C_mul_X_pow' hdeg).symm
  simp only [Matrix.of_apply]
  rw [hsum]
  exact ⟨(f ^ (i : ℕ)) /ₘ ((X - C c) ^ n),
    sub_eq_of_eq_add' (modByMonic_add_div (f ^ (i : ℕ)) ((X - C c) ^ n)).symm⟩

end Polynomial

namespace PowerBasis

/-- **Determinant of the power-expansion matrix in a purely inseparable power basis**: if `pb` is a
power basis of `S` over `R` of dimension `pb.dim = p ^ e` in exponential characteristic `p` with
`pb.gen ^ pb.dim = algebraMap R S b`, then the transition matrix from `pb.basis` to the powers
`1, f(pb.gen), …, f(pb.gen) ^ (pb.dim - 1)` has determinant
`f'(pb.gen) ^ (pb.dim * (pb.dim - 1) / 2)` in `S`. -/
theorem det_toMatrix_aeval_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p e : ℕ} [ExpChar S p] (pb : PowerBasis R S) (hdim : pb.dim = p ^ e)
    {b : R} (hb : algebraMap R S b = pb.gen ^ pb.dim) (f : R[X]) :
    algebraMap R S
        (LinearMap.toMatrix pb.basis pb.basis
          (pb.basis.constr R fun i : Fin pb.dim ↦ aeval pb.gen f ^ (i : ℕ))).det =
      aeval pb.gen f.derivative ^ (pb.dim * (pb.dim - 1) / 2) := by
  classical
  nontriviality S
  have : Nontrivial R := (algebraMap R S).domain_nontrivial
  set ψ : S →ₗ[R] S := pb.basis.constr R fun i : Fin pb.dim ↦ aeval pb.gen f ^ (i : ℕ)
  set A : Matrix (Fin pb.dim) (Fin pb.dim) R := LinearMap.toMatrix pb.basis pb.basis ψ
  have hcol (i : Fin pb.dim) :
      aeval pb.gen f ^ (i : ℕ) = ∑ j : Fin pb.dim, algebraMap R S (A j i) * pb.gen ^ (j : ℕ) := by
    rw [← pb.basis.constr_basis R (fun m : Fin pb.dim ↦ aeval pb.gen f ^ (m : ℕ)) i,
      ← pb.basis.sum_repr (ψ (pb.basis i))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← LinearMap.toMatrix_apply pb.basis pb.basis ψ j i, Algebra.smul_def, pb.basis_eq_pow]
  have hdvd_R (i : Fin pb.dim) :
      (X ^ pb.dim - C b) ∣ f ^ (i : ℕ) - ∑ j : Fin pb.dim, C (A j i) * X ^ (j : ℕ) := by
    set q : R[X] := f ^ (i : ℕ) - ∑ j : Fin pb.dim, C (A j i) * X ^ (j : ℕ)
    have hm : (X ^ pb.dim - C b).Monic := monic_X_pow_sub_C b pb.dim_pos.ne'
    have hne1 : (X ^ pb.dim - C b : R[X]) ≠ 1 := fun h1 ↦
      pb.dim_pos.ne' (by simpa [natDegree_X_pow_sub_C] using congrArg natDegree h1)
    rw [← modByMonic_eq_zero_iff_dvd hm]
    have hdeg : (q %ₘ (X ^ pb.dim - C b)).natDegree < pb.dim :=
      (natDegree_modByMonic_lt q hm hne1).trans_eq (by rw [natDegree_X_pow_sub_C])
    have haeval_mod : aeval pb.gen (q %ₘ (X ^ pb.dim - C b)) = 0 := by
      have hq0 : aeval pb.gen q = 0 := by
        simpa [q, map_sum] using sub_eq_zero.2 (hcol i)
      have hmod0 : aeval pb.gen (X ^ pb.dim - C b) = 0 := by
        rw [map_sub, map_pow, aeval_X, aeval_C, hb, sub_self]
      rw [aeval_modByMonic_eq_self_of_root hmod0, hq0]
    by_contra hne
    exact (pb.dim_le_natDegree_of_root hne haeval_mod).not_gt hdeg
  have hdvd_S (i : Fin pb.dim) : (X - C pb.gen) ^ pb.dim ∣
      (f.map (algebraMap R S)) ^ (i : ℕ) -
        ∑ j : Fin pb.dim, C (((algebraMap R S).mapMatrix A) j i) * X ^ (j : ℕ) := by
    have hmap := Polynomial.map_dvd (algebraMap R S) (hdvd_R i)
    have hfac : (X ^ pb.dim - C b).map (algebraMap R S) = (X - C pb.gen) ^ pb.dim := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hb, C_pow,
        hdim, sub_pow_expChar_pow]
    simpa [hfac, Polynomial.map_sum] using hmap
  rw [RingHom.map_det (algebraMap R S), Matrix.det_of_X_sub_C_pow_dvd_pow_sub_sum hdvd_S,
    Polynomial.derivative_map, Polynomial.eval_map, aeval_def]

end PowerBasis
