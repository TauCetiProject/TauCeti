/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Complete
import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# The Jacobi--Trudi identity

The Schur polynomial `s_μ`, defined in `TauCeti.diagramSchurPoly` as the generating function of
the semistandard tableaux of shape `μ`, is a determinant of complete homogeneous symmetric
polynomials:

`s_μ = det (h_{μᵢ - i + j})_{0 ≤ i, j < r}`

for every `r` at least the number of rows of `μ`, in any number of variables and over any
commutative ring.  The indices `μᵢ - i + j` are integers, and `h_m` is `0` for `m < 0`; this is
`TauCeti.hsymmInt`.  The statement is `TauCeti.diagramSchurPoly_eq_det_hsymmInt` for Young
diagrams in the alphabet `Fin N`, and `TauCeti.schurPoly_eq_det_hsymmInt` for partitions in an
arbitrary finite alphabet.

## The proof

The route is Macdonald's (I.3.4), through Jacobi's bialternant formula
`TauCeti.diagramSchurPoly_mul_alternant`, `s_μ · a_δ = a_{μ+δ}`, with `δ_j = N - 1 - j`.

* For a variable `x_k`, the generating functions `∑ₙ hₙ tⁿ = ∏ᵢ (1 - xᵢ t)⁻¹`
  (`TauCeti.mk_hsymm_eq_prod_mk_pow`) and `E⁽ᵏ⁾(t) = ∏_{i ≠ k} (1 - xᵢ t)` multiply to
  `(1 - x_k t)⁻¹`.  Comparing coefficients of `tᵐ` gives `x_kᵐ = ∑_{r < N} e⁽ᵏ⁾_r h_{m - r}`,
  where `e⁽ᵏ⁾_r` is the coefficient of `tʳ` in `E⁽ᵏ⁾`, which vanishes for `r ≥ N`.
* For every exponent vector `α`, this factors the alternant matrix `(x_k^{α_j})` as the product
  of the matrix `(e⁽ᵏ⁾_{N-1-l})_{k,l}` and the matrix `(h_{α_j - (N - 1 - l)})_{l,j}`.  For
  `α = δ` the second factor is unitriangular, so the first has determinant `a_δ`, and for
  `α = μ + δ` the second factor is the transpose of the Jacobi--Trudi matrix.  Hence
  `a_{μ+δ} = a_δ · det (h_{μᵢ - i + j})`.
* Over `ℤ` the polynomial ring is a domain and `a_δ ≠ 0`, so `a_δ` cancels against the
  bialternant formula.  Both sides commute with changing the coefficients, which carries the
  identity to every commutative ring.

This proves the identity with an `N × N` matrix when `μ` has at most `N` rows.  A row of `μ` of
length `0` contributes a last row `(0, …, 0, 1)` to the matrix, so the determinant does not depend
on the size `r` once `r` is at least the number of rows.  Finally, for `μ` with more than `N`
rows both sides vanish compatibly: setting a variable to `0` preserves Schur polynomials
(`TauCeti.aeval_snoc_zero_diagramSchurPoly`) and complete homogeneous symmetric polynomials
(`TauCeti.aeval_snoc_zero_hsymmInt`), so the identity descends from `N + 1` variables to `N`.

## Main results

* `TauCeti.diagramSchurPoly_eq_det_hsymmInt`: **the Jacobi--Trudi identity** for the Schur
  polynomial of a Young diagram.
* `TauCeti.schurPoly_eq_det_hsymmInt`: the Jacobi--Trudi identity for the Schur polynomial of a
  partition.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, formula (3.4) and its proof.
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.16.1.
-/

public section

namespace TauCeti

open MvPolynomial Finset

variable {R : Type*} [CommRing R]

/-! ### Expanding a power of a variable in complete homogeneous symmetric polynomials -/

section Expansion

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The polynomial `E⁽ᵏ⁾(t) = ∏_{i ≠ k} (1 - xᵢ t)`, whose coefficient of `tʳ` is `(-1)ʳ` times
the `r`-th elementary symmetric polynomial in the variables other than `x_k`. -/
private noncomputable def dropFactor (k : σ) : Polynomial (MvPolynomial σ R) :=
  ∏ i ∈ univ.erase k, (1 - Polynomial.C (X i) * Polynomial.X)

/-- `E⁽ᵏ⁾` is a product of `N - 1` linear factors, so it has no coefficient in degree `N` or
above. -/
private theorem coeff_dropFactor_eq_zero (k : σ) {r : ℕ} (hr : Fintype.card σ ≤ r) :
    (dropFactor (R := R) k).coeff r = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
  have hk : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨k⟩
  have : (dropFactor (R := R) k).natDegree ≤ ∑ _i ∈ univ.erase k, 1 := by
    refine (Polynomial.natDegree_prod_le _ _).trans (sum_le_sum fun i _ => ?_)
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simpa using (Polynomial.natDegree_C_mul_le (X i : MvPolynomial σ R) Polynomial.X).trans
      Polynomial.natDegree_X_le
  rw [sum_const, smul_eq_mul, mul_one, card_erase_of_mem (mem_univ k), card_univ] at this
  omega

/-- `E⁽ᵏ⁾(t) · ∑ₙ hₙ tⁿ = (1 - x_k t)⁻¹`: every factor `1 - xᵢ t` with `i ≠ k` cancels against
the geometric series in `xᵢ t`. -/
private theorem coe_dropFactor_mul_mk_hsymm (k : σ) :
    (dropFactor (R := R) k : PowerSeries (MvPolynomial σ R)) *
        PowerSeries.mk (fun n => hsymm σ R n) =
      PowerSeries.mk fun n => (X k : MvPolynomial σ R) ^ n := by
  rw [mk_hsymm_eq_prod_mk_pow, ← mul_prod_erase univ _ (mem_univ k), dropFactor,
    ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, mul_left_comm, ← prod_mul_distrib,
    prod_eq_one fun i _ => ?_, mul_one]
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, mul_comm,
    powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one]

/-- `x_kᵐ = ∑_{r < N} e⁽ᵏ⁾_r h_{m - r}`, the coefficient of `tᵐ` in
`E⁽ᵏ⁾(t) · ∑ₙ hₙ tⁿ = (1 - x_k t)⁻¹`. -/
private theorem X_pow_eq_sum_coeff_dropFactor_mul_hsymmInt (k : σ) (m : ℕ) :
    (X k : MvPolynomial σ R) ^ m =
      ∑ r ∈ range (Fintype.card σ), (dropFactor (R := R) k).coeff r * hsymmInt σ R (m - r) := by
  have h := congrArg (PowerSeries.coeff m) (coe_dropFactor_mul_mk_hsymm (R := R) k)
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_mk]
    at h
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk] at h
  rw [← h]
  -- Both sums agree with the sum over `r < m + 1 + N`: the extra terms vanish because
  -- `h_{m - r} = 0` for `r > m`, respectively because `e⁽ᵏ⁾_r = 0` for `r ≥ N`.
  have h1 : ∑ r ∈ range (m + 1), (dropFactor (R := R) k).coeff r * hsymm σ R (m - r) =
      ∑ r ∈ range (m + 1 + Fintype.card σ),
        (dropFactor (R := R) k).coeff r * hsymmInt σ R (m - r) := by
    rw [← sum_subset (range_subset_range.mpr (Nat.le_add_right (m + 1) _)) fun r _ hr => ?_]
    · refine sum_congr rfl fun r hr => ?_
      rw [mem_range] at hr
      rw [← hsymmInt_natCast, Nat.cast_sub (by omega)]
    · rw [hsymmInt_of_neg (by simp at hr; omega), mul_zero]
  rw [h1]
  refine (sum_subset (range_subset_range.mpr (Nat.le_add_left _ _)) fun r _ hr => ?_).symm
  rw [coeff_dropFactor_eq_zero k (by simpa using hr), zero_mul]

end Expansion

/-! ### Factoring the alternant matrix -/

section Factorization

variable {N : ℕ}

/-- The alternant matrix `(x_k^{α_j})` is the product of `(e⁽ᵏ⁾_{N-1-l})_{k,l}` and
`(h_{α_j - (N - 1 - l)})_{l,j}`, so the alternant is the product of their determinants. -/
private theorem alternant_eq_det_mul_det (α : Fin N → ℕ) :
    alternant (Fin N) R α =
      (Matrix.of fun k l : Fin N => (dropFactor (R := R) k).coeff (N - 1 - l)).det *
        (Matrix.of fun l j : Fin N => hsymmInt (Fin N) R ((α j : ℤ) - (N - 1 - l : ℕ))).det := by
  rw [alternant_def, ← Matrix.det_mul]
  congr 1
  ext k j : 1
  rw [Matrix.of_apply, Matrix.mul_apply, X_pow_eq_sum_coeff_dropFactor_mul_hsymmInt k (α j),
    Fintype.card_fin, ← sum_range_reflect, ← Fin.sum_univ_eq_sum_range]
  simp only [Matrix.of_apply]

/-- At the staircase `δ_j = N - 1 - j`, the matrix `(h_{δ_j - (N - 1 - l)})_{l,j} = (h_{l - j})`
is lower unitriangular. -/
private theorem det_hsymmInt_staircase :
    (Matrix.of fun l j : Fin N =>
      hsymmInt (Fin N) R (((N - 1 - j : ℕ) : ℤ) - (N - 1 - l : ℕ))).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ fun l j (h : l < j) => ?_]
  · exact prod_eq_one fun l _ => by simp
  · rw [Matrix.of_apply, hsymmInt_of_neg]
    have : (l : ℕ) < j := h
    omega

/-- The staircase alternant `a_δ` is the determinant of `(e⁽ᵏ⁾_{N-1-l})_{k,l}`. -/
private theorem alternant_staircase_eq_det :
    alternant (Fin N) R (fun j => N - 1 - j) =
      (Matrix.of fun k l : Fin N => (dropFactor (R := R) k).coeff (N - 1 - l)).det := by
  rw [alternant_eq_det_mul_det, det_hsymmInt_staircase, mul_one]

/-- `a_{μ+δ} = a_δ · det (h_{μᵢ - i + j})`. -/
private theorem alternant_betaNumber_eq (μ : YoungDiagram) :
    alternant (Fin N) R (fun j => μ.betaNumber N j) =
      alternant (Fin N) R (fun j => N - 1 - j) *
        (Matrix.of fun i j : Fin N =>
          hsymmInt (Fin N) R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  rw [alternant_eq_det_mul_det, alternant_staircase_eq_det]
  congr 1
  rw [← Matrix.det_transpose]
  congr 1
  ext l j : 1
  simp only [Matrix.transpose_apply, Matrix.of_apply, YoungDiagram.betaNumber_def]
  congr 1
  have hl := l.isLt
  have hj := j.isLt
  omega

/-- The Jacobi--Trudi identity over `ℤ`, with an `N × N` matrix, for a shape with at most `N`
rows: the staircase alternant cancels from the bialternant formula. -/
private theorem diagramSchurPoly_int_eq_det (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ N) :
    diagramSchurPoly N ℤ μ =
      (Matrix.of fun i j : Fin N =>
        hsymmInt (Fin N) ℤ ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  have h := diagramSchurPoly_mul_alternant (R := ℤ) N μ hμ
  rw [alternant_betaNumber_eq, mul_comm (alternant _ _ _)] at h
  refine mul_right_cancel₀ (alternant_ne_zero_of_injective fun i j hij => ?_) h
  have hi := i.isLt
  have hj := j.isLt
  exact Fin.ext (by omega)

end Factorization

/-! ### The Jacobi--Trudi identity -/

section JacobiTrudi

/-- Appending a row of length `0` to the Jacobi--Trudi matrix appends the row `(0, …, 0, 1)`,
which does not change the determinant. -/
private theorem det_hsymmInt_succ {N : ℕ} (μ : YoungDiagram) {r : ℕ} (hr : μ.rowLen r = 0) :
    (Matrix.of fun i j : Fin (r + 1) =>
        hsymmInt (Fin N) R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det =
      (Matrix.of fun i j : Fin r =>
        hsymmInt (Fin N) R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc, sum_eq_zero fun j _ => ?_,
    zero_add]
  · rw [Fin.succAbove_last, Matrix.of_apply, Fin.val_last, hr, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_mul]
    simp only [Nat.cast_zero, zero_sub, neg_add_cancel, hsymmInt_zero, one_mul]
    exact congrArg Matrix.det (Matrix.ext fun i j => by simp)
  · rw [Matrix.of_apply, hsymmInt_of_neg, mul_zero, zero_mul]
    simp [hr]

/-- The Jacobi--Trudi determinant does not depend on the size of the matrix, once it is at least
the number of rows of the shape. -/
private theorem det_hsymmInt_eq_of_colLen_le {N : ℕ} (μ : YoungDiagram) {r : ℕ}
    (hr : μ.colLen 0 ≤ r) :
    (Matrix.of fun i j : Fin r =>
        hsymmInt (Fin N) R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det =
      (Matrix.of fun i j : Fin (μ.colLen 0) =>
        hsymmInt (Fin N) R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    rw [det_hsymmInt_succ μ (YoungDiagram.rowLen_eq_zero_of_colLen_le hr), ih]

/-- The Jacobi--Trudi identity for a shape with at most `N` rows, transported from `ℤ`. -/
private theorem diagramSchurPoly_eq_det_of_colLen_le {N : ℕ} (μ : YoungDiagram)
    (hN : μ.colLen 0 ≤ N) :
    diagramSchurPoly N R μ =
      (Matrix.of fun i j : Fin (μ.colLen 0) =>
        hsymmInt (Fin N) R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  rw [← det_hsymmInt_eq_of_colLen_le μ hN, ← map_diagramSchurPoly (Int.castRingHom R),
    diagramSchurPoly_int_eq_det μ hN, RingHom.map_det]
  congr 1
  ext i j : 1
  simp

/-- **The Jacobi--Trudi identity.**  The Schur polynomial of a Young diagram `μ` in the alphabet
`Fin N` is the determinant `det (h_{μᵢ - i + j})_{0 ≤ i, j < r}` of complete homogeneous symmetric
polynomials, for every `r` at least the number of rows of `μ`.  The index `μᵢ - i + j` is an
integer, and `h_m = 0` for `m < 0` (`TauCeti.hsymmInt`).

There is no condition relating `N` to `μ`: when `μ` has more than `N` rows, both sides vanish. -/
theorem diagramSchurPoly_eq_det_hsymmInt (N : ℕ) (μ : YoungDiagram) {r : ℕ}
    (hr : μ.colLen 0 ≤ r) :
    diagramSchurPoly N R μ =
      (Matrix.of fun i j : Fin r =>
        hsymmInt (Fin N) R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  rw [det_hsymmInt_eq_of_colLen_le μ hr]
  -- Descend from `N + d ≥ ℓ(μ)` variables, where the identity holds, to `N` variables, by
  -- setting the last variable to `0` one at a time.
  obtain ⟨d, hd⟩ : ∃ d, μ.colLen 0 ≤ N + d := ⟨μ.colLen 0, Nat.le_add_left _ _⟩
  induction d generalizing N with
  | zero => exact diagramSchurPoly_eq_det_of_colLen_le μ hd
  | succ d ih =>
    rcases le_or_gt (μ.colLen 0) N with hN | _
    · exact diagramSchurPoly_eq_det_of_colLen_le μ hN
    · rw [← aeval_snoc_zero_diagramSchurPoly, ih (N := N + 1) (by omega), AlgHom.map_det]
      congr 1
      ext i j : 1
      simp [aeval_snoc_zero_hsymmInt]

/-- **The Jacobi--Trudi identity for partitions.**  In a finite alphabet `σ`, the Schur polynomial
of a partition `μ` is `det (h_{μᵢ - i + j})_{0 ≤ i, j < r}` for every `r` at least the number of
parts of `μ`, where `μᵢ` is the `i`-th largest part (`0` past the last part) and `h_m = 0` for
`m < 0`. -/
theorem schurPoly_eq_det_hsymmInt {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
    (μ : n.Partition) {r : ℕ} (hr : μ.parts.card ≤ r) :
    schurPoly σ R μ =
      (Matrix.of fun i j : Fin r =>
        hsymmInt σ R (((diagramOf μ).rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  rw [schurPoly_eq_rename,
    diagramSchurPoly_eq_det_hsymmInt _ _ ((colLen_zero_diagramOf μ).trans_le hr), AlgHom.map_det]
  congr 1
  ext i j : 1
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact rename_hsymmInt _ _

end JacobiTrudi

end TauCeti
