/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Subresultant.Signed
import TauCeti.Algebra.Polynomial.Coeff.Basic
import TauCeti.GroupTheory.Perm.Inversion

/-!
# The Sylvester–Habicht matrix

Basu, Pollack and Roy define the signed subresultant coefficients of `p` and `q`, of degrees `m`
and `n`, as determinants of the Sylvester–Habicht matrix. Its rows are the coefficient vectors of

```
X^(n-j-1)*p, …, X*p, p, q, X*q, …, X^(m-j-1)*q
```

read in the decreasing degrees `m+n-j-1, …, j`. The principal subresultant coefficient
`Polynomial.psc` instead uses columns `q, …, X^(m-j-1)*q, p, …, X^(n-j-1)*p` and increasing
degrees. This file defines `Polynomial.sylvesterHabichtMatrix` at fixed formal bounds and
proves that the two determinants differ by the sign of reversing the degrees, of swapping the two
polynomial blocks, and of reversing the order of the `p` block. Hence the determinant of the
Sylvester–Habicht matrix is the signed coefficient `Polynomial.signedPsc` throughout the
subresultant range.

Both determinants are taken at the same formal bounds, so the conversion holds without change
when the actual degrees are smaller, and the degree-drop formulas for `Polynomial.signedPsc`
apply to the Sylvester–Habicht determinant. At the terminal index `n` with `n ≤ m`, it is
`(-1) ^ (m - n).choose 2 * q.coeff n ^ (m - n)`
(`Polynomial.det_sylvesterHabichtMatrix_min`).

## Main results

* `Polynomial.det_sylvesterHabichtMatrix`: the determinant of the Sylvester–Habicht matrix is
  `(-1) ^ (((m - j) + (n - j)).choose 2 + (n - j).choose 2 + (m - j) * (n - j))` times the
  principal subresultant coefficient, at every index `j`.
* `Polynomial.det_sylvesterHabichtMatrix_eq_signedPsc`: in the subresultant range it is the signed
  principal subresultant coefficient.
* `Polynomial.det_sylvesterHabichtMatrix_min`: the terminal determinant.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4 (signed subresultants and the Sylvester–Habicht matrix).
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3 (`subresultantE`).
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The Sylvester–Habicht matrix of `p` and `q` at index `j` and formal degree bounds `m` and `n`.

Its first `n - j` rows read `X^(n-j-1)*p, …, X*p, p` and its last `m - j` rows read
`q, X*q, …, X^(m-j-1)*q`, with `p` and `q` truncated to their formal bounds `m` and `n`; when
`p.natDegree ≤ m` and `q.natDegree ≤ n` the entries are exactly those coefficients
(`Polynomial.sylvesterHabichtMatrix_apply_eq_coeff`). Column `c` reads the coefficient of degree
`c.rev + j`, so the columns run through the degrees `m+n-j-1, …, j` in decreasing order when
`j ≤ min m n`. -/
def _root_.Polynomial.sylvesterHabichtMatrix [Semiring R] (p q : R[X]) (m n j : ℕ) :
    Matrix (Fin ((n - j) + (m - j))) (Fin ((n - j) + (m - j))) R :=
  Matrix.of fun r c =>
    r.addCases
      (fun l => if (l.rev : ℕ) ≤ c.rev.val + j ∧ c.rev.val + j ≤ l.rev.val + m then
        p.coeff (c.rev.val + j - l.rev.val) else 0)
      (fun l => if (l : ℕ) ≤ c.rev.val + j ∧ c.rev.val + j ≤ l.val + n then
        q.coeff (c.rev.val + j - l.val) else 0)

/-- An entry of a Sylvester–Habicht matrix in the first, `p`-row block. -/
@[simp]
theorem _root_.Polynomial.sylvesterHabichtMatrix_castAdd [Semiring R]
    (p q : R[X]) (m n j : ℕ) (l : Fin (n - j)) (c : Fin ((n - j) + (m - j))) :
    sylvesterHabichtMatrix p q m n j (Fin.castAdd (m - j) l) c =
      if (l.rev : ℕ) ≤ c.rev.val + j ∧ c.rev.val + j ≤ l.rev.val + m then
        p.coeff (c.rev.val + j - l.rev.val) else 0 := by
  simp [sylvesterHabichtMatrix]

/-- An entry of a Sylvester–Habicht matrix in the second, `q`-row block. -/
@[simp]
theorem _root_.Polynomial.sylvesterHabichtMatrix_natAdd [Semiring R]
    (p q : R[X]) (m n j : ℕ) (l : Fin (m - j)) (c : Fin ((n - j) + (m - j))) :
    sylvesterHabichtMatrix p q m n j (Fin.natAdd (n - j) l) c =
      if (l : ℕ) ≤ c.rev.val + j ∧ c.rev.val + j ≤ l.val + n then
        q.coeff (c.rev.val + j - l.val) else 0 := by
  simp [sylvesterHabichtMatrix]

/-- When the formal bounds dominate the degrees, the entries of the Sylvester–Habicht matrix are
coefficients of the shifted input polynomials. -/
theorem _root_.Polynomial.sylvesterHabichtMatrix_apply_eq_coeff [Semiring R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (j : ℕ)
    (r c : Fin ((n - j) + (m - j))) :
    sylvesterHabichtMatrix p q m n j r c =
      r.addCases (fun l => (X ^ l.rev.val * p).coeff (c.rev.val + j))
        (fun l => (X ^ l.val * q).coeff (c.rev.val + j)) := by
  induction r using Fin.addCases <;>
    simp [sylvesterHabichtMatrix, coeff_X_pow_mul_of_natDegree_le hm,
      coeff_X_pow_mul_of_natDegree_le hn]

/-- Mapping coefficients maps every entry of the fixed-bound Sylvester–Habicht matrix. -/
@[simp]
theorem _root_.Polynomial.sylvesterHabichtMatrix_map_map [Semiring R] [Semiring S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    sylvesterHabichtMatrix (p.map f) (q.map f) m n j =
      f.mapMatrix (sylvesterHabichtMatrix p q m n j) := by
  ext r c
  induction r using Fin.addCases <;> simp [sylvesterHabichtMatrix, apply_ite f]

/-- The permutation of `Fin (a + b)` reversing the order of the last `b` indices and fixing the
first `a`. -/
private def reverseRightBlock (a b : ℕ) : Equiv.Perm (Fin (a + b)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl _) Fin.revPerm)

private theorem reverseRightBlock_natAdd (a b : ℕ) (l : Fin b) :
    reverseRightBlock a b (Fin.natAdd a l) = Fin.natAdd a l.rev := by
  simp [reverseRightBlock, Equiv.permCongr_apply]

private theorem sign_reverseRightBlock (a b : ℕ) :
    Equiv.Perm.sign (reverseRightBlock a b) = (-1) ^ b.choose 2 := by
  simp [reverseRightBlock, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Fin.sign_revPerm]

/-- The permutation relating the column orders of the principal subresultant and
Sylvester–Habicht matrices has the sign of reversing all `a + b` indices, of reversing the last `b`
of them, and of swapping the blocks. -/
private theorem sign_reindexPerm (a b : ℕ) :
    Equiv.Perm.sign ((finAddFlip.symm.trans (reverseRightBlock a b)).symm.trans
      ((finCongr (add_comm b a)).trans Fin.revPerm)) =
      (-1) ^ ((a + b).choose 2 + b.choose 2 + a * b) := by
  have h : (finAddFlip.symm.trans (reverseRightBlock a b)).symm.trans
      ((finCongr (add_comm b a)).trans Fin.revPerm) =
      (reverseRightBlock a b).symm.trans
        ((finAddFlip.trans (finCongr (add_comm b a))).trans Fin.revPerm) :=
    Equiv.ext fun _ => rfl
  rw [h, Equiv.Perm.sign_trans, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm,
    sign_reverseRightBlock, sign_finAddFlip_trans_finCongr, Fin.sign_revPerm, ← pow_add,
    ← pow_add]
  congr 1
  ring

/-- The Sylvester–Habicht matrix is the transpose of the principal subresultant matrix, with the
degrees reversed, the two polynomial blocks swapped, and the order of the `p` block reversed. -/
private theorem sylvesterHabichtMatrix_eq_transpose_reindex [Semiring R]
    (p q : R[X]) (m n j : ℕ) :
    sylvesterHabichtMatrix p q m n j =
      ((subresultantMatrix p q m n j).reindex
        ((finCongr (add_comm (n - j) (m - j))).trans Fin.revPerm).symm
        ((finAddFlip.symm.trans (reverseRightBlock (m - j) (n - j))).symm)).transpose := by
  ext r c
  have hrev : ((Fin.revPerm (finCongr (add_comm (n - j) (m - j)) c)) : ℕ) = c.rev := by
    simp only [Fin.revPerm_apply, Fin.val_rev, finCongr_apply, Fin.val_cast]
    omega
  induction r using Fin.addCases with
  | left l =>
      have hrow : reverseRightBlock (m - j) (n - j)
          (finAddFlip.symm (Fin.castAdd (m - j) l)) = Fin.natAdd (m - j) l.rev := by
        rw [show finAddFlip.symm (Fin.castAdd (m - j) l) = Fin.natAdd (m - j) l from
          finAddFlip.symm_apply_eq.mpr (finAddFlip_apply_natAdd l (m - j)).symm,
          reverseRightBlock_natAdd]
      simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Equiv.trans_apply, hrow, subresultantMatrix_natAdd,
        sylvesterHabichtMatrix_castAdd, hrev]
  | right l =>
      have hrow : reverseRightBlock (m - j) (n - j)
          (finAddFlip.symm (Fin.natAdd (n - j) l)) = Fin.castAdd (n - j) l := by
        rw [show finAddFlip.symm (Fin.natAdd (n - j) l) = Fin.castAdd (n - j) l from
          finAddFlip.symm_apply_eq.mpr (finAddFlip_apply_castAdd l (n - j)).symm]
        simp [reverseRightBlock, Equiv.permCongr_apply]
      simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Equiv.trans_apply, hrow, subresultantMatrix_castAdd,
        sylvesterHabichtMatrix_natAdd, hrev]

/-- The determinant of the Sylvester–Habicht matrix is the principal subresultant coefficient
times the sign of reversing the `(m - j) + (n - j)` degrees, of reversing the `n - j` rows of the
`p` block, and of swapping the two blocks. The formal bounds are retained on both sides. -/
theorem _root_.Polynomial.det_sylvesterHabichtMatrix [CommRing R] (p q : R[X]) (m n j : ℕ) :
    (sylvesterHabichtMatrix p q m n j).det =
      (-1) ^ (((m - j) + (n - j)).choose 2 + (n - j).choose 2 + (m - j) * (n - j)) *
        psc p q m n j := by
  rw [sylvesterHabichtMatrix_eq_transpose_reindex, Matrix.det_transpose, Matrix.det_reindex,
    psc_def, Equiv.symm_symm, sign_reindexPerm]
  simp

/-- In the subresultant range, the determinant of the Sylvester–Habicht matrix is the signed
principal subresultant coefficient. This includes the terminal index `min m n`, and both sides
keep the formal bounds when the actual degrees are smaller. -/
theorem _root_.Polynomial.det_sylvesterHabichtMatrix_eq_signedPsc [CommRing R]
    (p q : R[X]) {m n j : ℕ} (hj : j ≤ min m n) :
    (sylvesterHabichtMatrix p q m n j).det = signedPsc p q m n j := by
  rw [det_sylvesterHabichtMatrix, signedPsc_def, show m + n - 2 * j = (m - j) + (n - j) by omega]
  simp [hj]

/-- At the terminal index the Sylvester–Habicht determinant is a power of the coefficient at the
smaller formal bound. When the right bound is smaller the matrix is antitriangular, and the
determinant carries the sign `(-1) ^ (m - n).choose 2` of its antidiagonal, Basu–Pollack–Roy's
`ε (m - n)`. -/
theorem _root_.Polynomial.det_sylvesterHabichtMatrix_min [CommRing R] (p q : R[X]) (m n : ℕ) :
    (sylvesterHabichtMatrix p q m n (min m n)).det =
      if m ≤ n then p.coeff m ^ (n - m)
      else (-1) ^ (m - n).choose 2 * q.coeff n ^ (m - n) := by
  rw [det_sylvesterHabichtMatrix_eq_signedPsc p q le_rfl]
  by_cases hmn : m ≤ n
  · simp [hmn]
  · have hnm : n ≤ m := by omega
    simp [hmn, hnm]

end TauCeti
