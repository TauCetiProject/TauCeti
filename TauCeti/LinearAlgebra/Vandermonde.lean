/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Pi.Interval
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Int.SuccPred
import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Vandermonde determinants in the falling-factorial basis

The falling factorials `descPochhammer R j` are monic of degree `j`, so Mathlib's
`Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` rewrites `det (vandermonde y)` as the
determinant of the matrix `(descPochhammer R j).eval (yᵢ)`.  Unlike the powers, the falling
factorials have a closed-form discrete antiderivative and a closed-form left shift, and this file
proves the two identities for the Vandermonde determinant that those two facts supply.

## The box-sum identity

Let `x₀ ≤ x₁ ≤ ⋯ ≤ xₙ` be integers and let `y` range over the box of integer vectors with
`xᵢ ≤ yᵢ ≤ xᵢ₊₁ - 1`, one interval for each consecutive pair.  Then

`n ! · ∑ y, det (vandermonde y) = det (vandermonde x)`,

which is `TauCeti.factorial_mul_sum_det_vandermonde`.  Unwinding the determinants, the product
`∏_{i < j} (yⱼ - yᵢ)` of the differences of an `n`-tuple, summed over the box, is `1 / n !` times
the corresponding product for the `(n + 1)`-tuple that bounds it.

The identity drives the branching recursion for the Weyl dimension formula of `GL n`: the
interlacing condition indexing the constituents of an irreducible restricted to `GL (n - 1)` is
exactly such a box, and the two Vandermonde products are the two Weyl dimension numerators.

Three moves prove it; only the last uses the ordering hypothesis.  *The falling-factorial basis*
replaces the powers, because they have the closed-form discrete antiderivative
`TauCeti.sum_Ico_descPochhammer_eval`.  *Multilinearity*: a determinant is multilinear in its rows
and the box constrains the rows independently, so the sum of the determinants over the box is the
determinant of the matrix of row sums (`MultilinearMap.map_sum_finset`); evaluating those row
sums, and clearing the denominators `1, 2, …, n` by a column scaling, produces the matrix of
differences `(descPochhammer ℤ (j+1)).eval (xᵢ₊₁) - (descPochhammer ℤ (j+1)).eval (xᵢ)`, whose
determinant is `n !` times the sum.  *A row reduction*: that matrix of differences is what remains
of the `(n+1) × (n+1)` matrix `(descPochhammer ℤ j).eval (xᵢ)` after subtracting each row from its
successor and deleting the column `j = 0`, which is constant equal to `1`.  Multiplying on the
left by the bidiagonal matrix performing the subtraction contributes a factor `(-1)^{n+1}` to the
determinant, and expanding the product along its first column — where only the last entry
survives — contributes the same sign, so the two determinants agree.

## The lowering identity

Over an arbitrary commutative ring, lower a single node `yᵢ` by one and weight the resulting
Vandermonde determinant by `yᵢ`.  Summing over the nodes gives back the original determinant,
scaled by `∑ yᵢ - (0 + 1 + ⋯ + (m - 1))`:

`∑ i, yᵢ · det (vandermonde (update y i (yᵢ - 1))) = (∑ i, yᵢ - ∑ i, i) · det (vandermonde y)`,

which is `TauCeti.sum_mul_det_vandermonde_update_sub_one`, with
`TauCeti.sum_mul_prod_sub_update_sub_one` its unwound form as a product of differences over the
ordered pairs of an initial segment of `ℕ`.  It is the Vandermonde identity behind the Frobenius
determinant formula for the number of standard Young tableaux of a given shape, where the nodes
are the beta-numbers of a Young diagram and lowering one of them is erasing a corner.

Two moves prove it.  *The left shift*: `x · (x - 1)^{underline j} = x^{underline (j+1)}`, so
multiplying the lowered row by `yᵢ` turns the falling-factorial matrix of the lowered node vector
into the same matrix with its `i`-th row shifted up one degree, and
`x^{underline (j+1)} = x^{underline j} · (x - j)` expands that row as `yᵢ` times the original minus
`j` times the original, entry by entry.  *Jacobi's row formula*
`Matrix.sum_det_updateRow_mul_row`: summing over the rows the determinant of a matrix with one row
scaled entry by entry multiplies the determinant by the total of the scaling factors, which turns
the `j`-weighted correction into `(0 + 1 + ⋯ + (m - 1)) · det`.

Mathlib's `monic_descPochhammer` and `descPochhammer_natDegree` assume the coefficient ring is a
nontrivial ring without zero divisors, which the lowering identity does not; it uses
`TauCeti.monic_descPochhammer`, which holds over any ring, and `TauCeti.descPochhammer_natDegree`,
which holds over any nontrivial ring.  The trivial ring is handled separately, where the identity is
vacuous.

## Integrality of weighted Vandermonde products

Weight the rows of a Vandermonde determinant by `wᵢ`.  If `p j` is monic of degree `j`, the column
of `u^j` may be replaced by the column of the values of `p j` without changing the determinant, so
if `d j` divides every weighted value `wᵢ · (p j).eval (uᵢ)` then `∏ⱼ d j` divides
`∏ᵢ wᵢ · det (vandermonde u)` (`TauCeti.prod_dvd_prod_mul_det_vandermonde`).  With `p j` the falling
factorial and `w = 1` this is the argument of Mathlib's `Matrix.superFactorial_dvd_vandermonde_det`.
Three products arise as numerators of Weyl dimension formulas.  The first two are divisible by
`1! · 3! ⋯ (2n - 1)!`:

* the odd Vandermonde product `∏ᵢ xᵢ · ∏_{i < j} (xᵢ² - xⱼ²)`, the numerator for the symplectic
  groups, with the monic odd polynomials `x (x² - 1²) ⋯ (x² - k²)`, each of which is the falling
  factorial of degree `2k + 1` at `x + k` (`TauCeti.mul_prod_sq_sub_sq_eq_descPochhammer_eval`);
* the product `∏ᵢ (2xᵢ + 1) · ∏_{i < j} (xᵢ - xⱼ)(xᵢ + xⱼ + 1)` of the differences of the values
  `x (x + 1)`, the numerator for the odd orthogonal groups, with the polynomials
  `∏_{c < k} (x - c)(x + c + 1)`, whose weighted values are sums of two falling factorials of
  degree `2k + 1` (`TauCeti.two_mul_add_one_mul_prod_sub_mul_add_add_one_eq`).

The third, the unweighted product `∏_{i < j} (xᵢ² - xⱼ²)`, the numerator for the even orthogonal
groups, is divisible by `2!/2 · 4!/2 ⋯ (2n - 2)!/2`, with the monic even polynomials
`(x² - 0²) ⋯ (x² - k²)`, twice each of which is a sum of two falling factorials of degree `2k + 2`
(`TauCeti.two_mul_prod_sq_sub_sq_eq`).

## Main results

* `TauCeti.factorial_mul_sum_det_vandermonde`: **the box-sum identity for Vandermonde
  determinants.**
* `TauCeti.sum_mul_det_vandermonde_update_sub_one` and `TauCeti.sum_mul_prod_sub_update_sub_one`:
  **the lowering identity for Vandermonde determinants.**
* `TauCeti.prod_dvd_prod_mul_det_vandermonde` and `TauCeti.prod_dvd_prod_mul_prod_sub`:
  **integrality for weighted Vandermonde products.**
* `TauCeti.prod_factorial_dvd_prod_mul_det_vandermonde_sq` and
  `TauCeti.prod_factorial_dvd_prod_mul_prod_sq_sub_sq`: **integrality for the odd Vandermonde
  product** `∏ᵢ xᵢ · ∏_{i < j} (xⱼ² - xᵢ²)`, which is divisible by `1! · 3! ⋯ (2n - 1)!`, a
  positive integer (`TauCeti.prod_factorial_two_mul_add_one_pos`).
* `TauCeti.prod_factorial_dvd_prod_two_mul_add_one_mul_prod_sub_mul_add_add_one`: **integrality
  for the Vandermonde product of the values `x (x + 1)`** weighted by `2x + 1`, which is divisible
  by `1! · 3! ⋯ (2n - 1)!` too.
* `TauCeti.prod_add_one_mul_factorial_dvd_prod_prod_sq_sub_sq`: **integrality for the even
  Vandermonde product** `∏_{i < j} (xᵢ² - xⱼ²)`, which is divisible by
  `2!/2 · 4!/2 ⋯ (2n - 2)!/2`, a positive integer
  (`TauCeti.prod_add_one_mul_factorial_two_mul_add_one_pos`), the value of the product at the
  nodes `n - 1, …, 1, 0` (`TauCeti.prod_prod_sq_sub_sq_eq_prod_add_one_mul_factorial`).
-/

public section

namespace TauCeti

open Finset Matrix Polynomial

/-! ### The box-sum identity -/

/-- The Vandermonde determinant of a node vector, computed in the falling-factorial basis: the
falling factorials are monic of degree `j`, so they give the same determinant as the powers. -/
private theorem det_vandermonde_eq_det_descPochhammer {R : Type*} [CommRing R] [Nontrivial R]
    (m : ℕ) (y : Fin m → R) :
    (Matrix.vandermonde y).det
      = (Matrix.of fun i j : Fin m => (descPochhammer R (j : ℕ)).eval (y i)).det :=
  Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde y
    (fun j => descPochhammer R (j : ℕ)) (fun j => descPochhammer_natDegree (j : ℕ))
    (fun j => monic_descPochhammer (j : ℕ))

/-- **The row reduction.**  The `n × n` matrix of differences of falling factorials at the
consecutive nodes `xᵢ`, `xᵢ₊₁` has the same determinant as the `(n+1) × (n+1)` Vandermonde matrix
of the nodes themselves: it is obtained from the falling-factorial form of the latter by
subtracting each row from its successor and deleting the constant column `j = 0`. -/
private theorem det_descPochhammer_sub_eq_det_vandermonde {n : ℕ} (x : Fin (n + 1) → ℤ) :
    (Matrix.of fun i j : Fin n =>
        (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.succ)
          - (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.castSucc)).det
      = (Matrix.vandermonde x).det := by
  classical
  -- `N` is the Vandermonde matrix of `x` in the falling-factorial basis, and `E` is the bidiagonal
  -- matrix subtracting each row of `N` from its predecessor.
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of fun i j => (descPochhammer ℤ (j : ℕ)).eval (x i)
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i k =>
    (if (k : ℕ) = (i : ℕ) + 1 then (1 : ℤ) else 0) - (if k = i then 1 else 0)
  have hN : ∀ i j, N i j = (descPochhammer ℤ (j : ℕ)).eval (x i) := fun _ _ => rfl
  have hE : ∀ i k, E i k
      = (if (k : ℕ) = (i : ℕ) + 1 then (1 : ℤ) else 0) - (if k = i then 1 else 0) :=
    fun _ _ => rfl
  have hEN : ∀ i j : Fin (n + 1),
      (E * N) i j
        = (∑ k : Fin (n + 1), if (k : ℕ) = (i : ℕ) + 1 then N k j else 0) - N i j := by
    intro i j
    rw [Matrix.mul_apply]
    have hterm : ∀ k : Fin (n + 1), E i k * N k j
        = (if (k : ℕ) = (i : ℕ) + 1 then N k j else 0) - (if k = i then N k j else 0) := by
      intro k
      rw [hE]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib]
    congr 1
    simp
  have hEupper : E.IsUpperTriangular := by
    intro i k hki
    have hk : (k : ℕ) < (i : ℕ) := hki
    have h1 : ¬ ((k : ℕ) = (i : ℕ) + 1) := by omega
    have h2 : ¬ (k = i) := by rintro rfl; omega
    rw [hE]
    simp [h1, h2]
  have hEdet : E.det = (-1 : ℤ) ^ (n + 1) := by
    rw [Matrix.det_of_isUpperTriangular hEupper]
    have hdiag : ∀ i : Fin (n + 1), E i i = -1 := by
      intro i
      rw [hE]
      simp
    rw [Finset.prod_congr rfl fun i _ => hdiag i]
    simp
  -- The column `j = 0` of `N` is constant equal to `1`, so `E * N` has a single nonzero entry
  -- there, in its last row.
  have hcol : ∀ i : Fin (n + 1), N i 0 = 1 := by
    intro i
    rw [hN]
    simp
  have hcastSucc : ∀ (i : Fin n) (j : Fin (n + 1)),
      (E * N) i.castSucc j = N i.succ j - N i.castSucc j := by
    intro i j
    rw [hEN]
    simp only [Fin.val_castSucc, ← Fin.val_succ, Fin.val_inj, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  have hlast : (E * N) (Fin.last n) 0 = -1 := by
    rw [hEN, hcol]
    have hne : ∀ k : Fin (n + 1), ¬ ((k : ℕ) = n + 1) := fun k => by omega
    simp [hne]
  have hsubmat : (E * N).submatrix (Fin.last n).succAbove Fin.succ
      = Matrix.of fun i j : Fin n =>
          (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.succ)
            - (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.castSucc) := by
    ext i j
    rw [Matrix.submatrix_apply, Fin.succAbove_last, hcastSucc, hN, hN]
    simp
  have hdetEN : (E * N).det = (-1 : ℤ) ^ (n + 1) *
      (Matrix.of fun i j : Fin n =>
        (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.succ)
          - (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.castSucc)).det := by
    rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (Fin.last n)]
    · rw [hlast, hsubmat, Fin.val_last]
      ring
    · intro i _ hi
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      rw [hcastSucc]
      simp only [hcol]
      ring
    · simp
  -- Both readings of `det (E * N)` carry the same sign, which therefore cancels.
  have hdetN : N.det = (Matrix.vandermonde x).det :=
    (det_vandermonde_eq_det_descPochhammer (n + 1) x).symm
  rw [Matrix.det_mul, hEdet, hdetN] at hdetEN
  exact (((isUnit_neg_one (α := ℤ)).pow (n + 1)).mul_right_inj.mp hdetEN).symm

/-- **Summing Vandermonde determinants over a box of nested intervals.**  For integers
`x₀ ≤ x₁ ≤ ⋯ ≤ xₙ`, the Vandermonde determinant of `y`, summed over all integer vectors with
`xᵢ ≤ yᵢ ≤ xᵢ₊₁ - 1`, is the Vandermonde determinant of `x` divided by `n !`; the statement clears
that denominator, so it is an identity over `ℤ`.

The hypothesis is exactly what makes each interval a range of summation; the nodes are otherwise
arbitrary integers, of either sign. -/
theorem factorial_mul_sum_det_vandermonde {n : ℕ} (x : Fin (n + 1) → ℤ)
    (hx : ∀ i : Fin n, x i.castSucc ≤ x i.succ) :
    (Nat.factorial n : ℤ) *
        ∑ y ∈ Finset.Icc (fun i : Fin n => x i.castSucc) (fun i : Fin n => x i.succ - 1),
          (Matrix.vandermonde y).det
      = (Matrix.vandermonde x).det := by
  classical
  -- Multilinearity of the determinant in the rows, used in every row at once: a term of the
  -- expansion is a choice of one summand in each row, so the terms are indexed by the box.
  have hbox : (Matrix.of fun i j : Fin n =>
        ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1), (descPochhammer ℤ (j : ℕ)).eval t).det
      = ∑ y ∈ Fintype.piFinset fun i : Fin n => Finset.Icc (x i.castSucc) (x i.succ - 1),
          (Matrix.of fun i j : Fin n => (descPochhammer ℤ (j : ℕ)).eval (y i)).det := by
    have key := (Matrix.detRowAlternating (R := ℤ) (n := Fin n)).toMultilinearMap.map_sum_finset
      (A := fun i : Fin n => Finset.Icc (x i.castSucc) (x i.succ - 1))
      (g := fun (_ : Fin n) (t : ℤ) (j : Fin n) => (descPochhammer ℤ (j : ℕ)).eval t)
    have hrow : (fun i : Fin n => ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1),
          fun j : Fin n => (descPochhammer ℤ (j : ℕ)).eval t)
        = fun i j : Fin n =>
          ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1), (descPochhammer ℤ (j : ℕ)).eval t := by
      funext i j
      exact Finset.sum_apply j _ _
    rw [hrow] at key
    exact key
  have hsum : (∑ y ∈ Finset.Icc (fun i : Fin n => x i.castSucc) (fun i : Fin n => x i.succ - 1),
      (Matrix.vandermonde y).det)
      = (Matrix.of fun i j : Fin n =>
          ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1),
            (descPochhammer ℤ (j : ℕ)).eval t).det := by
    rw [hbox]
    exact Finset.sum_congr rfl fun y _ => det_vandermonde_eq_det_descPochhammer n y
  have hscale : (Matrix.of fun i j : Fin n =>
        (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.succ)
          - (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.castSucc))
      = (Matrix.of fun i j : Fin n =>
          ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1),
            (descPochhammer ℤ (j : ℕ)).eval t)
        * Matrix.diagonal fun j : Fin n => ((j : ℕ) : ℤ) + 1 := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.of_apply, Matrix.of_apply, mul_comm]
    rw [Finset.Icc_sub_one_right_eq_Ico]
    exact (sum_Ico_descPochhammer_eval (j : ℕ) (hx i)).symm
  have hdet := det_descPochhammer_sub_eq_det_vandermonde x
  rw [hscale, Matrix.det_mul, Matrix.det_diagonal] at hdet
  simp only [← Nat.cast_add_one, ← Nat.cast_prod] at hdet
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => k + 1) n,
    Finset.prod_range_add_one_eq_factorial] at hdet
  rw [hsum, mul_comm, hdet]

/-! ### The lowering identity -/

/-- Lowering one node of a Vandermonde matrix by one, read in the falling-factorial basis: only
the corresponding row of the matrix changes. -/
private theorem det_vandermonde_update_sub_one {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ}
    (y : Fin m → R) (i : Fin m) :
    (Matrix.vandermonde (Function.update y i (y i - 1))).det
      = ((Matrix.of fun k j : Fin m => (descPochhammer R (j : ℕ)).eval (y k)).updateRow i
          fun j : Fin m => (descPochhammer R (j : ℕ)).eval (y i - 1)).det := by
  classical
  rw [det_vandermonde_eq_det_descPochhammer]
  congr 1
  ext k j
  rcases eq_or_ne k i with rfl | h
  · simp
  · simp [Matrix.updateRow_ne h, Function.update_of_ne h]

/-- **The lowering identity for Vandermonde determinants.**  Lowering a single node by one and
weighting by that node, then summing over the nodes, multiplies the Vandermonde determinant by the
total of the nodes less `0 + 1 + ⋯ + (m - 1)`. -/
theorem sum_mul_det_vandermonde_update_sub_one {R : Type*} [CommRing R] {m : ℕ} (y : Fin m → R) :
    (∑ i, y i * (Matrix.vandermonde (Function.update y i (y i - 1))).det)
      = ((∑ i, y i) - ∑ i : Fin m, ((i : ℕ) : R)) * (Matrix.vandermonde y).det := by
  classical
  -- over the trivial ring there is nothing to prove, and the falling factorials have no degree
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  set N : Matrix (Fin m) (Fin m) R :=
    Matrix.of fun k j : Fin m => (descPochhammer R (j : ℕ)).eval (y k) with hNdef
  have hdet : (Matrix.vandermonde y).det = N.det := det_vandermonde_eq_det_descPochhammer m y
  have key : ∀ i : Fin m, y i * (Matrix.vandermonde (Function.update y i (y i - 1))).det
      = y i * N.det - (N.updateRow i fun j : Fin m => ((j : ℕ) : R) * N i j).det := by
    intro i
    have hrow : (y i • fun j : Fin m => (descPochhammer R (j : ℕ)).eval (y i - 1))
        = (y i • N i) - fun j : Fin m => ((j : ℕ) : R) * N i j := by
      funext j
      -- the left shift `x · (x - 1)^{underline j} = x^{underline (j+1)}` …
      have hleft : (descPochhammer R ((j : ℕ) + 1)).eval (y i)
          = y i * (descPochhammer R (j : ℕ)).eval (y i - 1) := by
        simpa using descPochhammer_succ_eval_add_one (j : ℕ) (y i - 1)
      -- … against the trailing factor `x^{underline (j+1)} = x^{underline j} · (x - j)`
      have hright := descPochhammer_succ_eval (S := R) (j : ℕ) (y i)
      simp only [hNdef, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      rw [← hleft, hright]
      ring
    -- the determinant is alternating in the rows, so the difference of rows splits it in two
    have hsplit : (N.updateRow i ((y i • N i) - fun j : Fin m => ((j : ℕ) : R) * N i j)).det
        = (N.updateRow i (y i • N i)).det
          - (N.updateRow i fun j : Fin m => ((j : ℕ) : R) * N i j).det :=
      Matrix.detRowAlternating.map_update_sub N i _ _
    rw [det_vandermonde_update_sub_one, ← Matrix.det_updateRow_smul, hrow, hsplit,
      Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Matrix.sum_det_updateRow_mul_row, hdet]
  ring

/-- The Vandermonde determinant of the first `m` values of a sequence, as a product of the
differences over the ordered pairs of `Finset.range m`.  The sign is left as an unevaluated power
of `-1`: the lowering identity multiplies it into both of its sides, where it cancels. -/
private theorem det_vandermonde_eq_prod_range {R : Type*} [CommRing R] (m : ℕ) (b : ℕ → R) :
    (Matrix.vandermonde fun i : Fin m => b i).det
      = (-1) ^ (∑ i : Fin m, (Finset.Ioi i).card)
        * ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m, (b k - b l) := by
  classical
  have hIoi : ∀ i : Fin m, ∏ j ∈ Finset.Ioi i, (b j - b i)
      = (-1) ^ (Finset.Ioi i).card * ∏ l ∈ Finset.Ico ((i : ℕ) + 1) m, (b i - b l) := by
    intro i
    have hprod := Finset.prod_map (Finset.Ioi i) Fin.valEmbedding (fun l => b i - b l)
    rw [Fin.map_valEmbedding_Ioi, ← Finset.Ico_add_one_left_eq_Ioo] at hprod
    rw [hprod, ← Finset.prod_neg]
    exact Finset.prod_congr rfl fun j _ => by simp
  rw [Matrix.det_vandermonde, Finset.prod_congr rfl fun i _ => hIoi i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum,
    Fin.prod_univ_eq_prod_range (fun k : ℕ => ∏ l ∈ Finset.Ico (k + 1) m, (b k - b l)) m]

/-- **The lowering identity, unwound.**  For a sequence in a commutative ring, the product of the
differences over the ordered pairs below a bound, with one term of the sequence lowered by one and
the result weighted by that term, summed over the terms below the bound, is the total of the terms
below the bound less `0 + 1 + ⋯ + (m - 1)`, times the product of the differences of the original
sequence. -/
theorem sum_mul_prod_sub_update_sub_one {R : Type*} [CommRing R] (m : ℕ) (b : ℕ → R) :
    (∑ i ∈ Finset.range m, b i *
        ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m,
          (Function.update b i (b i - 1) k - Function.update b i (b i - 1) l))
      = ((∑ i ∈ Finset.range m, b i) - ∑ i ∈ Finset.range m, (i : R))
        * ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m, (b k - b l) := by
  classical
  have hupd : ∀ i : Fin m, Function.update (fun k : Fin m => b k) i (b (i : ℕ) - 1)
      = fun k : Fin m => Function.update b (i : ℕ) (b (i : ℕ) - 1) (k : ℕ) := by
    intro i
    funext k
    rcases eq_or_ne k i with rfl | h
    · simp
    · rw [Function.update_of_ne h, Function.update_of_ne fun hc => h (Fin.val_injective hc)]
  have hterm : ∀ i : Fin m,
      (Matrix.vandermonde (Function.update (fun k : Fin m => b k) i (b (i : ℕ) - 1))).det
        = (-1) ^ (∑ i : Fin m, (Finset.Ioi i).card)
          * ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m,
              (Function.update b (i : ℕ) (b (i : ℕ) - 1) k
                - Function.update b (i : ℕ) (b (i : ℕ) - 1) l) := by
    intro i
    rw [hupd i, det_vandermonde_eq_prod_range m (Function.update b (i : ℕ) (b (i : ℕ) - 1))]
  have key := sum_mul_det_vandermonde_update_sub_one fun i : Fin m => b i
  rw [Finset.sum_congr rfl fun i _ => by rw [hterm i], det_vandermonde_eq_prod_range m b] at key
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => b i * ∏ k ∈ Finset.range m,
      ∏ l ∈ Finset.Ico (k + 1) m,
        (Function.update b i (b i - 1) k - Function.update b i (b i - 1) l)) m,
    ← Fin.sum_univ_eq_sum_range b m,
    ← Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : R)) m]
  -- A power of `-1` is a unit even when the coefficient ring has zero divisors.
  apply ((isUnit_neg_one (α := R)).pow (∑ i : Fin m, (Finset.Ioi i).card)).mul_right_inj.mp
  simpa only [Finset.mul_sum, mul_left_comm] using key

/-! ### Integrality of weighted Vandermonde determinants -/

/-- **Integrality for a weighted Vandermonde determinant.**  Let `p j` be monic of degree `j` and
suppose that `d j` divides the weighted value `w i * (p j).eval (u i)` at every node.  Then
`∏ j, d j` divides `∏ i, w i * det (vandermonde u)`: replacing the column of `u^j` by that of the
values of `p j` does not change the determinant, after which column `j` of the weighted matrix is a
multiple of `d j`.  With `p j` the falling factorial and `w = 1` this is the argument of Mathlib's
`Matrix.superFactorial_dvd_vandermonde_det`. -/
theorem prod_dvd_prod_mul_det_vandermonde {R : Type*} [CommRing R] {n : ℕ} (u w d : Fin n → R)
    (p : Fin n → R[X]) (hdeg : ∀ j, (p j).natDegree = j) (hmonic : ∀ j, (p j).Monic)
    (hdvd : ∀ i j, d j ∣ w i * (p j).eval (u i)) :
    (∏ j, d j) ∣ (∏ i, w i) * (Matrix.vandermonde u).det := by
  choose c hc using hdvd
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde _ p hdeg hmonic,
    ← Matrix.det_mul_column]
  have hmat : (Matrix.of fun i j : Fin n =>
        w i * Matrix.of (fun i j : Fin n => (p j).eval (u i)) i j)
      = Matrix.of fun i j : Fin n => d j * c i j := by
    ext i j
    simp only [Matrix.of_apply, hc]
  have hrow := Matrix.det_mul_row d (Matrix.of c)
  simp only [Matrix.of_apply] at hrow
  rw [hmat, hrow]
  exact dvd_mul_right _ _

/-- **Integrality for a weighted Vandermonde product.**  For sequences of nodes `uₖ` and weights
`wₖ`, if `p j` is monic of degree `j` for `j < m` and `d j` divides `wᵢ * (p j).eval (uᵢ)` for
`i, j < m`, then
`∏_{k < m} d k` divides `∏_{k < m} wₖ · ∏_{k < l < m} (uₖ - uₗ)`.  This is
`TauCeti.prod_dvd_prod_mul_det_vandermonde` with the determinant expanded; the sign relating the two
orders of the differences does not affect divisibility. -/
theorem prod_dvd_prod_mul_prod_sub {R : Type*} [CommRing R] (m : ℕ) (u w d : ℕ → R)
    (p : ℕ → R[X]) (hdeg : ∀ j < m, (p j).natDegree = j) (hmonic : ∀ j < m, (p j).Monic)
    (hdvd : ∀ i < m, ∀ j < m, d j ∣ w i * (p j).eval (u i)) :
    (∏ k ∈ Finset.range m, d k)
      ∣ ∏ k ∈ Finset.range m, w k * ∏ l ∈ Finset.Ico (k + 1) m, (u k - u l) := by
  have h := prod_dvd_prod_mul_det_vandermonde (fun i : Fin m => u i) (fun i => w i)
    (fun j => d j) (fun j => p j) (fun j => hdeg j j.2) (fun j => hmonic j j.2)
    fun i j => hdvd i i.2 j j.2
  rw [det_vandermonde_eq_prod_range m u, mul_left_comm] at h
  have hunit := (isUnit_neg_one (α := R)).pow (∑ i : Fin m, (Finset.Ioi i).card)
  simpa only [Fin.prod_univ_eq_prod_range, Finset.prod_mul_distrib] using hunit.dvd_mul_left.mp h

/-! ### Products of squared differences, weighted by the nodes -/

/-- The divisor `1! · 3! ⋯ (2n - 1)!` of the odd Vandermonde product is positive, so it may be
cancelled. -/
theorem prod_factorial_two_mul_add_one_pos (n : ℕ) :
    0 < ∏ k ∈ Finset.range n, ((2 * k + 1).factorial : ℤ) := by
  exact_mod_cast Nat.prod_factorial_pos (Finset.range n) fun k => 2 * k + 1

/-- **Integrality for the odd Vandermonde product.**  For integer nodes `xᵢ`, the product
`∏ᵢ xᵢ · det (vandermonde (xᵢ²)) = ∏ᵢ xᵢ · ∏_{i < j} (xⱼ² - xᵢ²)` is divisible by
`1! · 3! ⋯ (2n - 1)!`.  This is the analogue, for the odd powers `x, x³, …, x^{2n-1}`, of
Mathlib's `Matrix.superFactorial_dvd_vandermonde_det` for the powers `1, x, …, x^{n-1}`. -/
theorem prod_factorial_dvd_prod_mul_det_vandermonde_sq {n : ℕ} (x : Fin n → ℤ) :
    (∏ k ∈ Finset.range n, ((2 * k + 1).factorial : ℤ))
      ∣ (∏ i, x i) * (Matrix.vandermonde fun i => x i ^ 2).det := by
  -- Replace the column of `x^{2k+1}` by the column of the monic odd polynomial
  -- `x (x² - 1²) ⋯ (x² - k²)`, whose values are multiples of `(2k + 1)!`.
  rw [← Fin.prod_univ_eq_prod_range (fun k => ((2 * k + 1).factorial : ℤ)) n]
  exact prod_dvd_prod_mul_det_vandermonde _ x _
    (fun j => ∏ m ∈ Finset.range j, (X - C (((m : ℤ) + 1) ^ 2)))
    (fun j => by rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range])
    (fun j => monic_prod_X_sub_C _ _)
    fun i j => by simpa [eval_prod] using factorial_dvd_mul_prod_sq_sub_sq j (x i)

/-- **Integrality for the odd Vandermonde product, unwound.**  For a sequence of integers, the
product `∏_{k < m} bₖ · ∏_{k < l < m} (bₖ² - bₗ²)` is divisible by `1! · 3! ⋯ (2m - 1)!`.  This is
`TauCeti.prod_factorial_dvd_prod_mul_det_vandermonde_sq` with the determinant expanded. -/
theorem prod_factorial_dvd_prod_mul_prod_sq_sub_sq (m : ℕ) (b : ℕ → ℤ) :
    (∏ k ∈ Finset.range m, ((2 * k + 1).factorial : ℤ))
      ∣ ∏ k ∈ Finset.range m, b k * ∏ l ∈ Finset.Ico (k + 1) m, (b k ^ 2 - b l ^ 2) :=
  prod_dvd_prod_mul_prod_sub m (fun k => b k ^ 2) b _
    (fun j => ∏ m ∈ Finset.range j, (X - C (((m : ℤ) + 1) ^ 2)))
    (fun j _ => by rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range])
    (fun j _ => monic_prod_X_sub_C _ _)
    fun i _ j _ => by simpa [eval_prod] using factorial_dvd_mul_prod_sq_sub_sq j (b i)

/-- The divisor `2!/2 · 4!/2 ⋯ (2m)!/2` of the even Vandermonde product is positive, so it may
be cancelled. -/
theorem prod_add_one_mul_factorial_two_mul_add_one_pos (m : ℕ) :
    0 < ∏ k ∈ Finset.range m, ((k + 1) * (2 * k + 1).factorial : ℤ) :=
  Finset.prod_pos fun k _ => by positivity

/-- The products `∏_{c < j} (j² - c²)` for `j < m`, the rows of the even Vandermonde product at the
nodes `m - 1, …, 1, 0`, multiply to `2!/2 · 4!/2 ⋯ (2m - 2)!/2`: the row `j = k + 1` is
`(k + 1) (2k + 1)!` (`TauCeti.prod_sq_sub_sq_eq_mul_factorial`) and the row `j = 0` is empty. -/
theorem prod_prod_sq_sub_sq_eq_prod_add_one_mul_factorial {R : Type*} [CommRing R] (m : ℕ) :
    ∏ j ∈ Finset.range m, ∏ c ∈ Finset.range j, ((j : R) ^ 2 - (c : R) ^ 2)
      = ∏ k ∈ Finset.range (m - 1), ((k + 1) * (2 * k + 1).factorial : R) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [Finset.prod_range_succ', Finset.prod_range_zero, mul_one, Nat.add_sub_cancel]
    exact Finset.prod_congr rfl fun k _ => by
      exact_mod_cast prod_sq_sub_sq_eq_mul_factorial (R := R) k

/-- **Integrality for the even Vandermonde product.**  For a sequence of integers, the product
`∏_{k < l < m} (bₖ² - bₗ²)` is divisible by `∏_{k < m - 1} (k + 1) (2k + 1)!`, that is, by
`2!/2 · 4!/2 ⋯ (2m - 2)!/2`.  In the Vandermonde determinant of the squares, the column of
`(x²)^j` may be replaced by the column of `∏_{c < j} (x² - c²)`, whose values at the integers are
multiples of its value `∏_{c < j} (j² - c²)` at `x = j`
(`TauCeti.mul_factorial_dvd_prod_sq_sub_sq`). -/
theorem prod_add_one_mul_factorial_dvd_prod_prod_sq_sub_sq (m : ℕ) (b : ℕ → ℤ) :
    (∏ k ∈ Finset.range (m - 1), ((k + 1) * (2 * k + 1).factorial : ℤ))
      ∣ ∏ k ∈ Finset.range m, ∏ l ∈ Finset.Ico (k + 1) m, (b k ^ 2 - b l ^ 2) := by
  have h := prod_dvd_prod_mul_prod_sub m (fun k => b k ^ 2) (fun _ => 1)
    (fun j => ∏ c ∈ Finset.range j, ((j : ℤ) ^ 2 - (c : ℤ) ^ 2))
    (fun j => ∏ c ∈ Finset.range j, (X - C ((c : ℤ) ^ 2)))
    (fun j _ => by rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range])
    (fun j _ => monic_prod_X_sub_C _ _)
    fun i _ j _ => by
      rw [one_mul, eval_prod]
      simp only [eval_sub, eval_X, eval_C]
      cases j with
      | zero => simp
      | succ k =>
        rw [prod_sq_sub_sq_eq_mul_factorial (R := ℤ) k]
        push_cast
        exact mul_factorial_dvd_prod_sq_sub_sq k (b i)
  simpa only [prod_prod_sq_sub_sq_eq_prod_add_one_mul_factorial, one_mul] using h

/-! ### The Vandermonde product of `x (x + 1)`, weighted by `2x + 1` -/

/-- **Integrality for the Vandermonde product of the values `x (x + 1)`.**  For a sequence of
integers, the product `∏_{k < m} (2bₖ + 1) · ∏_{k < l < m} (bₖ - bₗ) (bₖ + bₗ + 1)` is divisible by
`1! · 3! ⋯ (2m - 1)!`.  The factors are the differences `bₖ (bₖ + 1) - bₗ (bₗ + 1)`, so in the
Vandermonde determinant of the nodes `x (x + 1)`, weighted by `2x + 1`, the column of
`(x (x + 1))^j` may be replaced by the column of `∏_{c < j} (x - c) (x + c + 1)`, whose weighted
values are multiples of `(2j + 1)!`
(`TauCeti.factorial_dvd_two_mul_add_one_mul_prod_sub_mul_add_add_one`). -/
theorem prod_factorial_dvd_prod_two_mul_add_one_mul_prod_sub_mul_add_add_one (m : ℕ)
    (b : ℕ → ℤ) :
    (∏ k ∈ Finset.range m, ((2 * k + 1).factorial : ℤ))
      ∣ ∏ k ∈ Finset.range m,
          (2 * b k + 1) * ∏ l ∈ Finset.Ico (k + 1) m, (b k - b l) * (b k + b l + 1) := by
  have h := prod_dvd_prod_mul_prod_sub m (fun k => b k * (b k + 1)) (fun k => 2 * b k + 1) _
    (fun j => ∏ c ∈ Finset.range j, (X - C ((c : ℤ) * (c + 1))))
    (fun j _ => by rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range])
    (fun j _ => monic_prod_X_sub_C _ _)
    fun i _ j _ => by
      have hrow : ∏ c ∈ Finset.range j, (b i * (b i + 1) - c * (c + 1))
          = ∏ c ∈ Finset.range j, (b i - c) * (b i + c + 1) :=
        Finset.prod_congr rfl fun c _ => by ring
      simpa [eval_prod, hrow] using
        factorial_dvd_two_mul_add_one_mul_prod_sub_mul_add_add_one j (b i)
  convert h using 3 with k _
  exact Finset.prod_congr rfl fun l _ => by ring

end TauCeti
