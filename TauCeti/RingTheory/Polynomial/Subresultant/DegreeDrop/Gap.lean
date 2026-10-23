/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Subresultant.Polynomial
import TauCeti.LinearAlgebra.Matrix.Determinant.Proportional

/-!
# Subresultants above the actual degree of an input

Let `q` have formal bound `n` but actual degree `e < n`, as happens when a leading coefficient
vanishes under specialization. For indices `j < e` the subresultants of `p` and `q` are the
ones computed at the bound `e`, up to a power of `p.coeff m`
(`Polynomial.subresultant_eq_C_coeff_pow_mul_of_right_degree_drop`), and at `j = e` they are a
scalar multiple of `q` (`Polynomial.subresultant_right_bound_of_degree_drop`). This file treats
the remaining strict indices `e ≤ j < min m n`. The column block of shifts of `q` has `m - j`
columns, and its first two columns read only the first row of the coefficient matrix once
`e < j`. Consequently:

* if `e < j` and `j + 2 ≤ m`, every coefficient minor vanishes, so the subresultant is zero;
* at the last strict index `j = m - 1`, with `e ≤ j`, the subresultant is
  `p.coeff m ^ (n - j) • q`.

Together with the two results above, this determines the subresultants of `p` and `q` at every
strict index from the actual degree of `q`. The left versions follow by the block-swap sign.
Taking `q` constant gives the subresultants of a polynomial and a constant.

These identities hold over every commutative ring, with no hypothesis on `p` and no
nonvanishing assumption on any coefficient.

## Main results

* `Polynomial.subresultant_eq_zero_of_natDegree_right_lt`,
  `Polynomial.subresultant_eq_zero_of_natDegree_left_lt`: vanishing in the degree gap.
* `Polynomial.subresultant_eq_C_mul_of_natDegree_right_le`,
  `Polynomial.subresultant_eq_C_mul_of_natDegree_left_le`: the last strict index.
* `Polynomial.subresultant_C_right`, `Polynomial.subresultant_C_left`: subresultants with a
  constant input at positive indices.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4 (specialization of subresultants).
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [CommRing R] {p q : R[X]} {m n j k : ℕ}

/-! ### Vanishing in the degree gap -/

/-- If the right input has degree below `j` and the `q`-block has at least two columns, every
coefficient minor at index `j` vanishes: the first two `q`-columns are supported in the first
row. -/
theorem _root_.Polynomial.subresultantCoeff_eq_zero_of_natDegree_right_lt
    (hq : q.natDegree < j) (hjm : j + 2 ≤ m) (k : ℕ) :
    subresultantCoeff p q m n j k = 0 := by
  let i₀ : Fin ((m - j) + (n - j)) := ⟨0, by omega⟩
  -- The first two `q`-columns vanish outside the first row.
  have hcol (l : Fin (m - j)) (hl : l.val ≤ 1) (i : Fin ((m - j) + (n - j))) :
      subresultantCoeffMatrix p q m n j k i (Fin.castAdd (n - j) l) =
        subresultantCoeffMatrix p q m n j k i₀ (Fin.castAdd (n - j) l) *
          if i = i₀ then 1 else 0 := by
    by_cases hi : i = i₀
    · simp [hi]
    · have hi' : i.val ≠ 0 := fun h ↦ hi (Fin.ext h)
      simp only [hi, hi', ↓reduceIte, mul_zero, subresultantCoeffMatrix_castAdd]
      split_ifs
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
      · rfl
  rw [subresultantCoeff_def]
  exact Matrix.det_eq_zero_of_column_eq_smul
    (a := Fin.castAdd (n - j) ⟨0, by omega⟩) (b := Fin.castAdd (n - j) ⟨1, by omega⟩)
    (by simp [Fin.ext_iff]) (hcol _ (by simp)) (hcol _ (by simp))

/-- In the degree gap of the right input, the principal coefficient vanishes. -/
theorem _root_.Polynomial.psc_eq_zero_of_natDegree_right_lt
    (hq : q.natDegree < j) (hjm : j + 2 ≤ m) :
    psc p q m n j = 0 := by
  simpa using subresultantCoeff_eq_zero_of_natDegree_right_lt (p := p) (n := n) hq hjm j

/-- In the degree gap of the right input, the subresultant polynomial vanishes. -/
theorem _root_.Polynomial.subresultant_eq_zero_of_natDegree_right_lt
    (hq : q.natDegree < j) (hjm : j + 2 ≤ m) :
    subresultant p q m n j = 0 := by
  ext k
  simp [subresultantCoeff_eq_zero_of_natDegree_right_lt hq hjm]

/-- If the left input has degree below `j` and the `p`-block has at least two columns, every
coefficient minor at index `j` vanishes. -/
theorem _root_.Polynomial.subresultantCoeff_eq_zero_of_natDegree_left_lt
    (hp : p.natDegree < j) (hjn : j + 2 ≤ n) (k : ℕ) :
    subresultantCoeff p q m n j k = 0 := by
  rw [subresultantCoeff_comm, subresultantCoeff_eq_zero_of_natDegree_right_lt hp hjn, mul_zero]

/-- In the degree gap of the left input, the principal coefficient vanishes. -/
theorem _root_.Polynomial.psc_eq_zero_of_natDegree_left_lt
    (hp : p.natDegree < j) (hjn : j + 2 ≤ n) :
    psc p q m n j = 0 := by
  simpa using subresultantCoeff_eq_zero_of_natDegree_left_lt (q := q) (m := m) hp hjn j

/-- In the degree gap of the left input, the subresultant polynomial vanishes. -/
theorem _root_.Polynomial.subresultant_eq_zero_of_natDegree_left_lt
    (hp : p.natDegree < j) (hjn : j + 2 ≤ n) :
    subresultant p q m n j = 0 := by
  ext k
  simp [subresultantCoeff_eq_zero_of_natDegree_left_lt hp hjn]

/-! ### The last strict index -/

/-- At index `j` with left bound `j + 1`, if the right input has degree at most `j`, the
coefficient minors are the coefficients of `q` times `p.coeff (j + 1) ^ (n - j)`: the
coefficient matrix is upper triangular. -/
theorem _root_.Polynomial.subresultantCoeff_eq_coeff_pow_mul_of_natDegree_right_le
    (hq : q.natDegree ≤ j) (hjn : j ≤ n) (hk : k ≤ j) :
    subresultantCoeff p q (j + 1) n j k = p.coeff (j + 1) ^ (n - j) * q.coeff k := by
  let M := subresultantCoeffMatrix p q (j + 1) n j k
  have htri : M.IsUpperTriangular := by
    intro i c hci
    have hi : i.val ≠ 0 := by have : c.val < i.val := hci; omega
    induction c using Fin.addCases with
    | left l =>
      simp only [M, subresultantCoeffMatrix_castAdd, hi, ↓reduceIte]
      split_ifs
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
      · rfl
    | right l =>
      have : (j + 1 - j) + l.val < i.val := hci
      simp only [M, subresultantCoeffMatrix_natAdd, hi, ↓reduceIte]
      split_ifs with h
      · exact absurd h (by omega)
      · rfl
  have hdiag (i : Fin ((j + 1 - j) + (n - j))) :
      M i i = if i.val = 0 then q.coeff k else p.coeff (j + 1) := by
    induction i using Fin.addCases with
    | left l =>
      have hl : l.val = 0 := by omega
      simp [M, hl, show k ≤ n by omega]
    | right l =>
      have hne : (j + 1 - j) + l.val ≠ 0 := by omega
      simp only [M, subresultantCoeffMatrix_natAdd, Fin.val_natAdd, hne, ↓reduceIte]
      split_ifs with h
      · congr 1
        omega
      · exact absurd (by omega) h
  rw [subresultantCoeff_def, Matrix.det_of_isUpperTriangular htri, Fin.prod_univ_add]
  simp only [hdiag, Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.prod_eq_single (⟨0, by omega⟩ : Fin (j + 1 - j))
    (fun l _ hl ↦ absurd (Fin.ext (by have := l.isLt; omega)) hl)
    (by simp)]
  simp [mul_comm]

/-- At index `j` with left bound `j + 1`, if the right input has degree at most `j`, the
principal coefficient is `p.coeff (j + 1) ^ (n - j) * q.coeff j`. -/
theorem _root_.Polynomial.psc_eq_coeff_pow_mul_of_natDegree_right_le
    (hq : q.natDegree ≤ j) (hjn : j ≤ n) :
    psc p q (j + 1) n j = p.coeff (j + 1) ^ (n - j) * q.coeff j := by
  simpa using subresultantCoeff_eq_coeff_pow_mul_of_natDegree_right_le (p := p) hq hjn le_rfl

/-- **The last strict index.** At index `j` with left bound `j + 1 ≤ n`, if the right input has
degree at most `j`, the subresultant polynomial is `p.coeff (j + 1) ^ (n - j) • q`. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_of_natDegree_right_le
    (hq : q.natDegree ≤ j) (hjn : j < n) :
    subresultant p q (j + 1) n j = C (p.coeff (j + 1) ^ (n - j)) * q := by
  ext k
  rw [coeff_subresultant, coeff_C_mul]
  by_cases hk : k ≤ j
  · simp only [show j < min (j + 1) n by omega, hk, and_self, ↓reduceIte]
    exact subresultantCoeff_eq_coeff_pow_mul_of_natDegree_right_le hq hjn.le hk
  · simp only [hk, and_false, ↓reduceIte]
    rw [coeff_eq_zero_of_natDegree_lt (p := q) (by omega), mul_zero]

/-- At index `j` with right bound `j + 1`, if the left input has degree at most `j`, the
coefficient minors are the coefficients of `p` times `(-q.coeff (j + 1)) ^ (m - j)`. -/
theorem _root_.Polynomial.subresultantCoeff_eq_neg_coeff_pow_mul_of_natDegree_left_le
    (hp : p.natDegree ≤ j) (hjm : j ≤ m) (hk : k ≤ j) :
    subresultantCoeff p q m (j + 1) j k = (-q.coeff (j + 1)) ^ (m - j) * p.coeff k := by
  rw [subresultantCoeff_comm, subresultantCoeff_eq_coeff_pow_mul_of_natDegree_right_le hp hjm hk,
    show j + 1 - j = 1 by omega, mul_one, neg_pow]
  ring

/-- At index `j` with right bound `j + 1`, if the left input has degree at most `j`, the
principal coefficient is `(-q.coeff (j + 1)) ^ (m - j) * p.coeff j`. -/
theorem _root_.Polynomial.psc_eq_neg_coeff_pow_mul_of_natDegree_left_le
    (hp : p.natDegree ≤ j) (hjm : j ≤ m) :
    psc p q m (j + 1) j = (-q.coeff (j + 1)) ^ (m - j) * p.coeff j := by
  simpa using subresultantCoeff_eq_neg_coeff_pow_mul_of_natDegree_left_le (q := q) hp hjm le_rfl

/-- At index `j` with right bound `j + 1 ≤ m`, if the left input has degree at most `j`, the
subresultant polynomial is `(-q.coeff (j + 1)) ^ (m - j) • p`. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_of_natDegree_left_le
    (hp : p.natDegree ≤ j) (hjm : j < m) :
    subresultant p q m (j + 1) j = C ((-q.coeff (j + 1)) ^ (m - j)) * p := by
  rw [subresultant_comm, subresultant_eq_C_mul_of_natDegree_right_le hp hjm, ← mul_assoc, ← C_mul,
    show j + 1 - j = 1 by omega, mul_one, neg_pow (q.coeff (j + 1))]

/-! ### Constant inputs -/

/-- At a positive index, the subresultant of `p` and a constant `c` is zero, except at the last
strict index `j = m - 1 < n`, where it is the constant `c * p.coeff m ^ (n - j)`. At index zero
it is the constant resultant (`Polynomial.subresultant_zero`). -/
theorem _root_.Polynomial.subresultant_C_right (p : R[X]) (c : R) (hj : 0 < j) :
    subresultant p (C c) m n j = if j + 1 = m ∧ j < n then C (c * p.coeff m ^ (n - j)) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, hjn⟩ := h
    rw [subresultant_eq_C_mul_of_natDegree_right_le (by simp) hjn, ← C_mul, mul_comm]
  · by_cases hjm : j + 2 ≤ m
    · exact subresultant_eq_zero_of_natDegree_right_lt (by simpa using hj) hjm
    · exact subresultant_eq_zero_of_min_le _ _ _ _ _ (by omega)

/-- At a positive index, the subresultant of a constant `c` and `q` is zero, except at the last
strict index `j = n - 1 < m`, where it is the constant `(-q.coeff n) ^ (m - j) * c`. -/
theorem _root_.Polynomial.subresultant_C_left (c : R) (q : R[X]) (hj : 0 < j) :
    subresultant (C c) q m n j =
      if j + 1 = n ∧ j < m then C ((-q.coeff n) ^ (m - j) * c) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, hjm⟩ := h
    rw [subresultant_eq_C_mul_of_natDegree_left_le (by simp) hjm, ← C_mul]
  · by_cases hjn : j + 2 ≤ n
    · exact subresultant_eq_zero_of_natDegree_left_lt (by simpa using hj) hjn
    · exact subresultant_eq_zero_of_min_le _ _ _ _ _ (by omega)

end TauCeti
