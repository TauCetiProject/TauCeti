/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Reductum
public import TauCeti.RingTheory.Polynomial.Subresultant.Polynomial
import TauCeti.LinearAlgebra.Matrix.CornerMinor

/-!
# Degree drops in subresultant polynomials

Below the smaller degree bounds, lowering a bound scales the entire subresultant polynomial,
not just its principal coefficient. At a smaller terminal bound, the surviving polynomial is
instead a scalar multiple of the corresponding input. Thus terminal scalar data must not be replaced
by the zero polynomial used outside the strict subresultant range.

The coefficient-minor formulas retain formal bounds and hold over arbitrary commutative rings.
The specialization formulas use reducta taken before mapping coefficients, allowing degree
drops and zero fibers. These identities supply the specialization laws for comparisons with
polynomial remainder sequences.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4 (specialization of subresultants).
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*}

/-- When the formal bounds dominate the degrees, a coefficient matrix reads shifted input
coefficients, at degree `k` in its first row and at degree `i.val + j` elsewhere. -/
theorem _root_.Polynomial.subresultantCoeffMatrix_apply_eq_coeff [Semiring R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (j k : ℕ) (i l : Fin ((m - j) + (n - j))) :
    subresultantCoeffMatrix p q m n j k i l =
      l.addCases (fun l => (X ^ l.val * q).coeff (if i.val = 0 then k else i.val + j))
        (fun l => (X ^ l.val * p).coeff (if i.val = 0 then k else i.val + j)) := by
  generalize hd : (if i.val = 0 then k else i.val + j) = d
  induction l using Fin.addCases with
  | left l =>
    simp only [subresultantCoeffMatrix_castAdd, Fin.addCases_left, coeff_X_pow_mul', hd]
    by_cases h : l.val ≤ d
    · by_cases h' : d ≤ l.val + n
      · simp only [h, h', and_self, ↓reduceIte]
      · have hdeg : q.natDegree < d - l.val := by omega
        simp only [h, h', and_false, ↓reduceIte, coeff_eq_zero_of_natDegree_lt hdeg]
    · simp only [h, false_and, ↓reduceIte]
  | right l =>
    simp only [subresultantCoeffMatrix_natAdd, Fin.addCases_right, coeff_X_pow_mul', hd]
    by_cases h : l.val ≤ d
    · by_cases h' : d ≤ l.val + m
      · simp only [h, h', and_self, ↓reduceIte]
      · have hdeg : p.natDegree < d - l.val := by omega
        simp only [h, h', and_false, ↓reduceIte, coeff_eq_zero_of_natDegree_lt hdeg]
    · simp only [h, false_and, ↓reduceIte]

private theorem lastRow_of_degree_drop [Semiring R] {p q : R[X]} {m n j k : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j < m) (hjn : j ≤ n)
    (i l : Fin ((m - j) + (n + 1 - j))) (hi : i.val = (m - j) + (n - j)) :
    subresultantCoeffMatrix p q m (n + 1) j k i l =
      if l.val = (m - j) + (n - j) then p.coeff m else 0 := by
  have hi0 : i.val ≠ 0 := by omega
  rw [subresultantCoeffMatrix_apply_eq_coeff hm (hn.trans (Nat.le_succ n))]
  simp only [hi0, ↓reduceIte]
  induction l using Fin.addCases with
  | left l =>
    have hdeg : q.natDegree < i.val + j - l.val := by omega
    have hle : l.val ≤ i.val + j := by omega
    have hne : l.val ≠ (m - j) + (n - j) := by omega
    simp [coeff_X_pow_mul', hle, coeff_eq_zero_of_natDegree_lt hdeg, hne]
  | right l =>
    by_cases h : (m - j) + l.val = (m - j) + (n - j)
    · have hcoeff : i.val + j - l.val = m := by omega
      have hle : l.val ≤ i.val + j := by omega
      simp [coeff_X_pow_mul', h, hcoeff, hle]
    · have hdeg : p.natDegree < i.val + j - l.val := by omega
      have hle : l.val ≤ i.val + j := by omega
      have hne : l.val ≠ n - j := by omega
      simp [coeff_X_pow_mul', hle, hne, coeff_eq_zero_of_natDegree_lt hdeg]

variable [CommRing R]

/-- Lowering an oversized right bound by one scales every coefficient minor by the coefficient
at the left bound. The smaller right terminal index is included, but `j < m` is essential. -/
theorem _root_.Polynomial.subresultantCoeff_succ_right {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j < m) (hjn : j ≤ n)
    (k : ℕ) :
    subresultantCoeff p q m (n + 1) j k =
      p.coeff m * subresultantCoeff p q m n j k := by
  classical
  let d := (m - j) + (n - j)
  have hd : (m - j) + (n + 1 - j) = d + 1 := by dsimp [d]; omega
  let e := finCongr hd
  let M := (subresultantCoeffMatrix p q m (n + 1) j k).reindex e e
  have hlast (l : Fin (d + 1)) :
      M (Fin.last d) l = if l = Fin.last d then p.coeff m else 0 := by
    simpa only [M, Matrix.reindex_apply, Matrix.submatrix_apply, e, finCongr_apply,
      finCongr_symm, Fin.val_cast, Fin.val_last, Fin.ext_iff] using
      lastRow_of_degree_drop hm hn hjm hjn (e.symm (Fin.last d)) (e.symm l) rfl
  -- Removing the last row and column preserves the replaced first row.
  have hminor : M.submatrix Fin.castSucc Fin.castSucc =
      subresultantCoeffMatrix p q m n j k := by
    ext i l
    simp only [Matrix.submatrix_apply, M, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [subresultantCoeffMatrix_apply_eq_coeff hm (hn.trans (Nat.le_succ n)),
      subresultantCoeffMatrix_apply_eq_coeff hm hn]
    induction l using Fin.addCases with
    | left l =>
      have hl : e.symm (Fin.castSucc (Fin.castAdd (n - j) l)) =
          Fin.castAdd (n + 1 - j) l := by ext; rfl
      rw [hl]
      simp [e]
    | right l =>
      have hle : n - j ≤ n + 1 - j := by omega
      have hl : e.symm (Fin.castSucc (Fin.natAdd (m - j) l)) =
          Fin.natAdd (m - j) (Fin.castLE hle l) := by ext; rfl
      rw [hl]
      simp [e]
  have hdet : subresultantCoeff p q m (n + 1) j k = M.det := by
    simp only [M, Matrix.det_reindex_self, subresultantCoeff_def]
  rw [hdet, Matrix.det_eq_mul_det_submatrix_castSucc_of_row M (by
    intro l hl
    simp [hlast, hl]), hlast, hminor]
  simp [subresultantCoeff_def]

/-- Lowering an oversized right bound scales every coefficient minor by the corresponding
power of the coefficient at the left bound, including the smaller right terminal index. -/
theorem _root_.Polynomial.subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop
    {p q : R[X]} {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hjm : j < m) (hjn : j ≤ n) (k : ℕ) :
    subresultantCoeff p q m N j k =
      p.coeff m ^ (N - n) * subresultantCoeff p q m n j k := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [subresultantCoeff_succ_right hm (hn.trans hN) hjm (hjn.trans hN), ih]
    have hgap : N + 1 - n = (N - n) + 1 := by omega
    rw [hgap, pow_succ]
    ring

/-- Lowering an oversized left bound scales coefficient minors by the right coefficient
power and the column-block sign. The smaller left terminal index is included. -/
theorem _root_.Polynomial.subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop
    {p q : R[X]} {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j < n) (k : ℕ) :
    subresultantCoeff p q M n j k = (-1) ^ ((M - m) * (n - j)) *
      q.coeff n ^ (M - m) * subresultantCoeff p q m n j k := by
  have hgap : M - j = (M - m) + (m - j) := by omega
  calc
    subresultantCoeff p q M n j k = (-1) ^ ((M - j) * (n - j)) *
        (q.coeff n ^ (M - m) * subresultantCoeff q p n m j k) := by
      rw [subresultantCoeff_comm p q M n j k,
        subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hn hm hM hjn hjm]
    _ = _ := by
      rw [subresultantCoeff_comm p q m n j k, hgap, add_mul, pow_add]
      ring

/-- Below both smaller bounds, an arbitrary right-bound drop scales the whole subresultant
polynomial. The formula does not replace a terminal scalar minor by a polynomial. -/
theorem _root_.Polynomial.subresultant_eq_C_coeff_pow_mul_of_right_degree_drop
    {p q : R[X]} {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hj : j < min m n) :
    subresultant p q m N j = C (p.coeff m ^ (N - n)) * subresultant p q m n j := by
  ext k
  have hj' : j < min m N := by omega
  by_cases hk : k ≤ j
  · simp only [subresultant_coeff, hj, hj', hk, and_self, ↓reduceIte, coeff_C_mul]
    exact subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hm hn hN
      (by omega) (by omega) k
  · simp only [coeff_C_mul, subresultant_coeff, hk, and_false, ↓reduceIte, mul_zero]

/-- Below both smaller bounds, a left-bound drop scales the whole subresultant polynomial,
including the column-block sign. -/
theorem _root_.Polynomial.subresultant_eq_C_sign_mul_coeff_pow_mul_of_left_degree_drop
    {p q : R[X]} {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hj : j < min m n) :
    subresultant p q M n j = C ((-1) ^ ((M - m) * (n - j)) * q.coeff n ^ (M - m)) *
      subresultant p q m n j := by
  ext k
  have hj' : j < min M n := by omega
  by_cases hk : k ≤ j
  · simp only [subresultant_coeff, hj, hj', hk, and_self, ↓reduceIte, coeff_C_mul]
    simpa only [mul_assoc] using
      subresultantCoeff_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM
        (by omega) (by omega) k
  · simp only [coeff_C_mul, subresultant_coeff, hk, and_false, ↓reduceIte, mul_zero]

/-- At the smaller right terminal index, a coefficient minor reads a coefficient of the right
input times a power of its coefficient at the bound. The empty determinant is excluded. -/
@[simp]
theorem _root_.Polynomial.subresultantCoeff_right_bound (p q : R[X]) {m n k : ℕ}
    (hnm : n < m) (hk : k ≤ n) :
    subresultantCoeff p q m n n k = q.coeff k * q.coeff n ^ (m - n - 1) := by
  classical
  let M := subresultantCoeffMatrix p q m n n k
  let i₀ : Fin ((m - n) + (n - n)) := ⟨0, by omega⟩
  have htri : M.IsUpperTriangular := by
    intro i l hli
    have hli' : l.val < i.val := by simpa using Fin.lt_def.mp hli
    have hi0 : i.val ≠ 0 := by omega
    induction l using Fin.addCases with
    | left l =>
      have hbound : ¬ i.val + n ≤ l.val + n := by
        simp only [Fin.val_castAdd] at hli'
        omega
      simp [M, subresultantCoeffMatrix_castAdd, hi0, hbound]
    | right l => exact Fin.elim0 (Fin.cast (by simp) l)
  have hdiag (i : Fin ((m - n) + (n - n))) :
      M i i = if i = i₀ then q.coeff k else q.coeff n := by
    induction i using Fin.addCases with
    | left i =>
      simp only [M, subresultantCoeffMatrix_castAdd, Fin.val_castAdd]
      by_cases hi : i.val = 0
      · have hi₀ : Fin.castAdd (n - n) i = i₀ := by ext; exact hi
        simp [hi, hi₀, hk]
      · have hi₀ : Fin.castAdd (n - n) i ≠ i₀ := by
          intro h
          exact hi (congrArg Fin.val h)
        simp [hi, hi₀]
    | right i => exact Fin.elim0 (Fin.cast (by simp) i)
  rw [subresultantCoeff_def, Matrix.det_of_isUpperTriangular htri]
  simp_rw [hdiag]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  have hprod : (∏ x ∈ Finset.univ.erase i₀, if x = i₀ then q.coeff k else q.coeff n) =
      ∏ _x ∈ Finset.univ.erase i₀, q.coeff n :=
    Finset.prod_congr rfl fun x hx => ite_eq_right (Finset.ne_of_mem_erase hx)
  rw [hprod]
  simp

/-- When only the right bound drops, the subresultant at its smaller terminal index survives
as a scalar multiple of the right polynomial, rather than a terminal subresultant polynomial. -/
theorem _root_.Polynomial.subresultant_right_bound_of_degree_drop {p q : R[X]} {m n N : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hnm : n < m) (hnN : n < N) :
    subresultant p q m N n =
      C (p.coeff m ^ (N - n) * q.coeff n ^ (m - n - 1)) * q := by
  ext k
  have hj : n < min m N := by omega
  rw [coeff_C_mul, subresultant_coeff]
  by_cases hk : k ≤ n
  · simp only [hj, hk, and_self, ↓reduceIte]
    rw [subresultantCoeff_eq_coeff_pow_mul_of_right_degree_drop hm hn hnN.le hnm le_rfl,
      subresultantCoeff_right_bound p q hnm hk]
    ring
  · have hq : q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hk, hq]

/-- The smaller left terminal index likewise survives as a scalar multiple of the left input,
with the sign from swapping the formal column blocks. -/
theorem _root_.Polynomial.subresultant_left_bound_of_degree_drop {p q : R[X]} {m M n : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hmn : m < n) (hmM : m < M) :
    subresultant p q M n m =
      C ((-1) ^ ((M - m) * (n - m)) * q.coeff n ^ (M - m) *
        p.coeff m ^ (n - m - 1)) * p := by
  rw [subresultant_comm, subresultant_right_bound_of_degree_drop hn hm hmn hmM,
    ← mul_assoc, ← C_mul]
  congr 2
  ring

/-- Dropping both formal bounds forces every subresultant polynomial to vanish, not merely
its principal coefficient. Outside the strict range the polynomial is zero by convention. -/
theorem _root_.Polynomial.subresultant_eq_zero_of_natDegree_lt_bounds {p q : R[X]}
    {m n j : ℕ} (hm : p.natDegree < m) (hn : q.natDegree < n) :
    subresultant p q m n j = 0 := by
  by_cases hj : j < min m n
  · have hnpos : 0 < n := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    ext k
    rw [subresultant_coeff]
    by_cases hk : k ≤ j
    · simp only [hj, hk, and_self, ↓reduceIte, coeff_zero]
      rw [subresultantCoeff_succ_right hm.le (by omega) (by omega) (by omega),
        coeff_eq_zero_of_natDegree_lt hm, zero_mul]
    · simp [hk]
  · exact subresultant_eq_zero_of_min_le p q m n j (by omega)

/-- After specialization, a right-bound drop below the smaller bounds scales the mapped
subresultant. The reduced input is obtained by truncating before mapping. -/
theorem _root_.Polynomial.map_subresultant_of_right_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m n N j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hN : n ≤ N) (hj : j < min m n) :
    (subresultant p q m N j).map f = C (f (p.coeff m) ^ (N - n)) *
      subresultant (p.map f) ((q.reductum (n + 1)).map f) m n j := by
  have htrunc : (q.reductum (n + 1)).map f = q.map f := by
    rw [← reductum_map]
    exact reductum_eq_self (by omega)
  rw [htrunc, ← subresultant_map_map,
    subresultant_eq_C_coeff_pow_mul_of_right_degree_drop hm hn hN hj, coeff_map]

/-- The left-bound specialization formula retains the column-block sign and the right
coefficient power, with truncation before mapping. -/
theorem _root_.Polynomial.map_subresultant_of_left_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m M n j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hM : m ≤ M) (hj : j < min m n) :
    (subresultant p q M n j).map f =
      C ((-1) ^ ((M - m) * (n - j)) * f (q.coeff n) ^ (M - m)) *
        subresultant ((p.reductum (m + 1)).map f) (q.map f) m n j := by
  have htrunc : (p.reductum (m + 1)).map f = p.map f := by
    rw [← reductum_map]
    exact reductum_eq_self (by omega)
  rw [htrunc, ← subresultant_map_map,
    subresultant_eq_C_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hj, coeff_map]

end TauCeti
