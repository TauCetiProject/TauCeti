/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Subresultant.Basic
public import TauCeti.RingTheory.Polynomial.Reductum
import TauCeti.LinearAlgebra.Matrix.CornerMinor

/-!
# Degree drops in principal subresultants

Fixed-bound principal subresultants need not equal the principal subresultants computed at
smaller actual degrees. Lowering the right bound contributes a power of the coefficient at
the left bound; lowering the left bound also contributes a block-order sign. These identities
explain how specialization interacts with degree drops, without assuming nonvanishing of
specialized leading coefficients.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4 (specialization of subresultants).
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*}

/-- The last row has only its final entry left when the right degree bound drops. -/
private theorem lastRow_of_degree_drop [Semiring R] {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j ≤ m) (hjn : j ≤ n)
    (i k : Fin ((m - j) + (n + 1 - j))) (hi : i.val = (m - j) + (n - j)) :
    subresultantMatrix p q m (n + 1) j i k =
      if k.val = (m - j) + (n - j) then p.coeff m else 0 := by
  induction k using Fin.addCases with
  | left k =>
    have hdeg : q.natDegree < i.val + j - k.val := by omega
    have hne : k.val ≠ (m - j) + (n - j) := by omega
    simp [subresultantMatrix_castAdd, coeff_eq_zero_of_natDegree_lt hdeg, hne]
  | right k =>
    by_cases h : (m - j) + k.val = (m - j) + (n - j)
    · have hcoeff : i.val + j - k.val = m := by omega
      have hlow : k.val ≤ i.val + j := by omega
      have hupp : i.val + j ≤ k.val + m := by omega
      simp [subresultantMatrix_natAdd, h, hcoeff, hlow, hupp]
    · have hdeg : p.natDegree < i.val + j - k.val := by omega
      have hne : k.val ≠ n - j := by omega
      simp [subresultantMatrix_natAdd, coeff_eq_zero_of_natDegree_lt hdeg, hne]

variable [CommRing R]

/-- Lowering an oversized right degree bound by one multiplies the principal
subresultant by the coefficient at the left bound. The terminal smaller index is included. -/
theorem _root_.Polynomial.psc_succ_right {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q m (n + 1) j = p.coeff m * psc p q m n j := by
  classical
  let d := (m - j) + (n - j)
  have hd : (m - j) + (n + 1 - j) = d + 1 := by dsimp [d]; omega
  let e := finCongr hd
  let M := (subresultantMatrix p q m (n + 1) j).reindex e e
  -- Laplace expansion at the last row leaves precisely the smaller-bound matrix.
  have hlast (k : Fin (d + 1)) :
      M (Fin.last d) k = if k = Fin.last d then p.coeff m else 0 := by
    simpa only [M, Matrix.reindex_apply, Matrix.submatrix_apply, e, finCongr_apply,
      finCongr_symm, Fin.val_cast, Fin.val_last, Fin.ext_iff] using
      lastRow_of_degree_drop hm hn hjm hjn (e.symm (Fin.last d)) (e.symm k) rfl
  have hminor : M.submatrix Fin.castSucc Fin.castSucc =
      subresultantMatrix p q m n j := by
    ext i k
    simp only [Matrix.submatrix_apply, M, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [subresultantMatrix_apply_eq_coeff hm (hn.trans (Nat.le_succ n)),
      subresultantMatrix_apply_eq_coeff hm hn]
    induction k using Fin.addCases with
    | left k =>
      have hk : e.symm (Fin.castSucc (Fin.castAdd (n - j) k)) =
          Fin.castAdd (n + 1 - j) k := by ext; rfl
      rw [hk]
      simp [e]
    | right k =>
      have hle : n - j ≤ n + 1 - j := by omega
      have hk : e.symm (Fin.castSucc (Fin.natAdd (m - j) k)) =
          Fin.natAdd (m - j) (Fin.castLE hle k) := by ext; rfl
      rw [hk]
      simp [e]
  have hdet : psc p q m (n + 1) j = M.det := by
    simp only [M, Matrix.det_reindex_self, psc_def]
  rw [hdet, Matrix.det_eq_mul_det_submatrix_castSucc_of_row M (by
    intro k hk
    simp [hlast, hk]), hlast, hminor]
  simp [psc_def]

/-- An arbitrary drop in the right bound contributes the corresponding power of the
coefficient at the left bound. The lower right bound need only dominate the degree. -/
theorem _root_.Polynomial.psc_eq_coeff_pow_mul_of_right_degree_drop {p q : R[X]}
    {m n N j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q m N j = p.coeff m ^ (N - n) * psc p q m n j := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [psc_succ_right hm (hn.trans hN) hjm (hjn.trans hN), ih]
    have hgap : N + 1 - n = (N - n) + 1 := by omega
    rw [hgap, pow_succ]
    ring

/-- Dropping the left bound also contributes the sign of moving its removed columns
past the right block. The lower left bound need only dominate the degree. -/
theorem _root_.Polynomial.psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop {p q : R[X]}
    {m M n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    psc p q M n j =
      (-1) ^ ((M - m) * (n - j)) * q.coeff n ^ (M - m) * psc p q m n j := by
  have hgap : M - j = (M - m) + (m - j) := by omega
  calc
    psc p q M n j =
        (-1) ^ ((M - j) * (n - j)) * (q.coeff n ^ (M - m) * psc q p n m j) := by
      rw [psc_comm p q M n j,
        psc_eq_coeff_pow_mul_of_right_degree_drop hn hm hM hjn hjm]
    _ = (-1) ^ ((M - m) * (n - j)) * q.coeff n ^ (M - m) * psc p q m n j := by
      rw [psc_comm p q m n j, hgap, add_mul, pow_add]
      ring

/-- At strict subresultant indices, simultaneous drops in both degree bounds force
vanishing. Terminal indices are excluded: their empty determinant can still be `1`. -/
theorem _root_.Polynomial.psc_eq_zero_of_natDegree_lt_bounds {p q : R[X]} {m n j : ℕ}
    (hm : p.natDegree < m) (hn : q.natDegree < n) (hj : j < min m n) :
    psc p q m n j = 0 := by
  have hnpos : 0 < n := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  rw [psc_succ_right hm.le (by omega) (by omega) (by omega),
    coeff_eq_zero_of_natDegree_lt hm, zero_mul]

/-- After coefficient specialization, lowering the right bound amounts to truncating
that input and multiplying by a power of the specialized coefficient at the left bound.
In particular, the lower bound can be the actual degree of the specialized right input. -/
theorem _root_.Polynomial.map_psc_of_right_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m n N j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (psc p q m N j) = f (p.coeff m) ^ (N - n) *
      psc (p.map f) ((q.reductum (n + 1)).map f) m n j := by
  have htrunc : (q.reductum (n + 1)).map f = q.map f := by
    rw [← reductum_map]
    exact reductum_eq_self (by omega)
  rw [htrunc, ← psc_map_map,
    psc_eq_coeff_pow_mul_of_right_degree_drop hm hn hN hjm hjn, coeff_map]

/-- The left-bound specialization formula retains the column-block sign as well as the
power of the specialized coefficient at the right bound. Truncation occurs before mapping. -/
theorem _root_.Polynomial.map_psc_of_left_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m M n j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hM : m ≤ M) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (psc p q M n j) = (-1) ^ ((M - m) * (n - j)) * f (q.coeff n) ^ (M - m) *
      psc ((p.reductum (m + 1)).map f) (q.map f) m n j := by
  have htrunc : (p.reductum (m + 1)).map f = p.map f := by
    rw [← reductum_map]
    exact reductum_eq_self (by omega)
  rw [htrunc, ← psc_map_map,
    psc_eq_sign_mul_coeff_pow_mul_of_left_degree_drop hm hn hM hjm hjn, coeff_map]

end TauCeti
