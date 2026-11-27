/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Commutator
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Last-border expansion of a quantum minor

An exterior row admits a left cofactor expansion at the unchanged spectral parameter. When a
principal minor is bordered by an exterior row and column, expanding the last column and then
this row expresses the result as its corner term minus a contraction of interior cofactors.
This is the last-border identity in L. Alpöge's `Formalism.FourierDecayAlt.Q.IsBorder`.
-/

public section

namespace Matrix

open Function

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A]

private theorem quantumMinor_update_row (E : Matrix ι ι A) {n : ℕ} (u : K)
    (a b : Fin (n + 1) → ι) (i : Fin (n + 1)) (r : ι) :
    E.quantumMinor u (update a i r) b =
      (-1 : ℤ) ^ i.val • E.quantumMinor u (Fin.cons r (i.removeNth a)) b := by
  rw [← Fin.insertNth_removeNth, ← Fin.cons_comp_cycleRange, quantumMinor_comp_perm_left,
    Fin.sign_cycleRange, Units.smul_def]
  simp

private theorem lie_exteriorRow_quantumMinor (E : Matrix ι ι A) {n : ℕ} (u : K)
    (a b : Fin (n + 1) → ι) {r c : ι} (hr : r ∉ Set.range b)
    (hE : ∀ i j, ⁅E r c, E (a i) (b j)⁆ = if c = a i then E r (b j) else 0) :
    ⁅E r c, E.quantumMinor u a b⁆ = ∑ i : Fin (n + 1),
      if c = a i then (-1 : ℤ) ^ i.val • E.quantumMinor u (Fin.cons r (i.removeNth a)) b
      else 0 := by
  have hne (j : Fin (n + 1)) : r ≠ b j := fun h ↦ hr ⟨j, h.symm⟩
  rw [E.lie_quantumMinor u a b (fun i j ↦ by simpa [hne j] using hE i j)]
  simp [hne, quantumMinor_update_row]

private theorem negOnePow_border_sign {n : ℕ} (i : Fin (n + 1)) :
    (-1 : ℤ) ^ (n + 1) * (-1) ^ i.val = -((-1) ^ (n - i.val)) := by
  rw [← pow_add, (by omega : n + 1 + i.val = (n - i.val + 2 * i.val) + 1),
    pow_succ, pow_add, pow_mul]
  norm_num

-- Regroup the cofactor contractions by their last-column Laplace expansions.
private theorem sum_exteriorRow_mul_quantumMinor_removeNth_castSucc
    (E : Matrix ι ι A) {n : ℕ} (u : K) (a : Fin (n + 1) → ι) (b : Fin (n + 2) → ι) (r : ι)
    (ih : ∀ i : Fin (n + 1), E.quantumMinor u (Fin.cons r (i.removeNth a)) (Fin.init b) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
        (E r (b j.castSucc) * E.quantumMinor u (i.removeNth a) (j.removeNth (Fin.init b)))) :
    (∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
      (E r (b j.castSucc) * E.quantumMinor u a (j.castSucc.removeNth b))) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
        (E.quantumMinor u (Fin.cons r (i.removeNth a)) (Fin.init b) *
          ((if a i = b (Fin.last (n + 1)) then algebraMap K A (u - (n : K)) else 0) +
            E (a i) (b (Fin.last (n + 1))))) := by
  simp_rw [ih, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [quantumMinor_succ_column_last, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hj : Fin.init (j.castSucc.removeNth b) = j.removeNth (Fin.init b) := by
    ext k
    simp [Fin.init, Fin.removeNth, Fin.castSucc_succAbove_castSucc]
  have hlast : (j.castSucc.removeNth b) (Fin.last n) = b (Fin.last (n + 1)) := by
    rw [Fin.removeNth_apply, Fin.succAbove_ne_last_last j.castSucc_lt_last.ne]
  rw [hj, hlast, mul_smul_comm, smul_comm, mul_assoc]

private theorem quantumMinor_cons_exteriorRow_step (E : Matrix ι ι A) {n : ℕ} (u : K)
    (a : Fin (n + 1) → ι) (b : Fin (n + 2) → ι) {r : ι} (hr : r ∉ Set.range b)
    (hE : ∀ i (j : Fin (n + 1)), ⁅E r (b (Fin.last (n + 1))), E (a i) (b j.castSucc)⁆ =
      if b (Fin.last (n + 1)) = a i then E r (b j.castSucc) else 0)
    (ih : ∀ i : Fin (n + 1), E.quantumMinor u (Fin.cons r (i.removeNth a)) (Fin.init b) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
        (E r (b j.castSucc) * E.quantumMinor u (i.removeNth a) (j.removeNth (Fin.init b)))) :
    E.quantumMinor u (Fin.cons r a) b = ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      (E r (b j) * E.quantumMinor u a (j.removeNth b)) := by
  let c := b (Fin.last (n + 1))
  let L := E.quantumMinor u a (Fin.init b)
  let S (i : Fin (n + 1)) := E.quantumMinor u (Fin.cons r (i.removeNth a)) (Fin.init b)
  let t (i : Fin (n + 1)) := (if a i = c then algebraMap K A (u - (n : K)) else 0) + E (a i) c
  -- The full minor's last column is shifted one further than the cofactor's last column.
  have hmain : E.quantumMinor u (Fin.cons r a) b =
      (-1 : ℤ) ^ (n + 1) • (L * E r c) + ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
        (S i * (t i - if c = a i then 1 else 0)) := by
    rw [quantumMinor_succ_column_last, Fin.sum_univ_succ]
    have hrc : r ≠ b (Fin.last (n + 1)) := fun h ↦ hr ⟨Fin.last _, h.symm⟩
    simp only [Fin.val_zero, Nat.sub_zero, Fin.cons_zero, hrc, ite_false, zero_add,
      Fin.removeNth_zero, Fin.tail_cons, Fin.cons_succ, Fin.removeNth_succ_cons, L, S, c]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Fin.val_succ, (by omega : n + 1 - (i.val + 1) = n - i.val)]
    congr 2
    by_cases hi : a i = b (Fin.last (n + 1))
    · simp [t, c, hi, Nat.cast_succ]
      abel
    · simp [t, c, hi, eq_comm]
  -- Moving the exterior entry to the left recovers exactly these diagonal corrections.
  have hcomm : E r c * L - L * E r c = ∑ i : Fin (n + 1),
      if c = a i then (-1 : ℤ) ^ i.val • S i else 0 := by
    apply lie_exteriorRow_quantumMinor E u a (Fin.init b) _ hE
    rintro ⟨j, hj⟩
    exact hr ⟨j.castSucc, hj⟩
  have hcorr : (-1 : ℤ) ^ (n + 1) • (L * E r c - E r c * L) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) • (S i * (if c = a i then 1 else 0)) := by
    rw [← neg_sub, hcomm, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : c = a i <;>
      simp only [hi, ite_true, ite_false, neg_zero, mul_zero, smul_zero, mul_one, smul_smul,
        negOnePow_border_sign, neg_smul, neg_neg]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.removeNth_last, Fin.val_last]
  rw [sum_exteriorRow_mul_quantumMinor_removeNth_castSucc E u a b r ih, hmain]
  simp only [mul_sub, Finset.sum_sub_distrib, smul_sub, L, c, t, S] at hcorr ⊢
  rw [← hcorr]
  abel

private theorem quantumMinor_cons_exteriorRow (E : Matrix ι ι A) {n : ℕ} (u : K)
    (a : Fin n → ι) (b : Fin (n + 1) → ι) {r : ι} (hr : r ∉ Set.range b)
    (hE : ∀ i j k, k < j → ⁅E r (b j), E (a i) (b k)⁆ = if b j = a i then E r (b k) else 0) :
    E.quantumMinor u (Fin.cons r a) b = ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
      (E r (b j) * E.quantumMinor u a (j.removeNth b)) := by
  induction n with
  | zero =>
    have hne : r ≠ b 0 := fun h ↦ hr ⟨0, h.symm⟩
    simp [hne]
  | succ n ih =>
    refine quantumMinor_cons_exteriorRow_step E u a b hr
      (fun i j ↦ hE i _ _ j.castSucc_lt_last) fun i ↦ ?_
    exact ih (i.removeNth a) (Fin.init b) (fun ⟨j, hj⟩ ↦ hr ⟨j.castSucc, hj⟩)
      (fun k j l h ↦ hE (i.succAbove k) j.castSucc l.castSucc (Fin.castSucc_lt_castSucc_iff.mpr h))

/-- Expand along an inserted row whose label is absent from the columns. Its entries multiply
on the left, and the cofactors retain `u`. Only the commutators of an exterior entry with
entries in preceding columns of the other rows are required. -/
theorem quantumMinor_insertNth_exteriorRow (E : Matrix ι ι A) {n : ℕ} (u : K)
    (a : Fin n → ι) (b : Fin (n + 1) → ι) (p : Fin (n + 1)) {r : ι} (hr : r ∉ Set.range b)
    (hE : ∀ i j k, k < j → ⁅E r (b j), E (a i) (b k)⁆ = if b j = a i then E r (b k) else 0) :
    E.quantumMinor u (p.insertNth r a) b = ∑ j : Fin (n + 1), (-1 : ℤ) ^ (p.val + j.val) •
      (E r (b j) * E.quantumMinor u a (j.removeNth b)) := by
  rw [← Fin.cons_comp_cycleRange, quantumMinor_comp_perm_left,
    Fin.sign_cycleRange, Units.smul_def, Units.val_pow_eq_pow_val]
  rw [E.quantumMinor_cons_exteriorRow u a b hr hE, Finset.smul_sum]
  simp only [Units.coe_neg_one, smul_smul, ← pow_add]

/-- The last-border expansion: append an exterior index to a principal quantum minor.
The corner term has the last spectral shift, and the correction contracts interior
cofactors (at the original spectral parameter) between the two off-diagonal borders. For an
empty interior the corner term alone is the size-one formula `quantumMinor_fin_one`. -/
theorem quantumMinor_snoc_self (E : Matrix ι ι A) {n : ℕ} (u : K) (v : Fin (n + 1) → ι)
    {r : ι} (hr : r ∉ Set.range v)
    (hE : ∀ i j k, k < j → ⁅E r (v j), E (v i) (v k)⁆ = if v j = v i then E r (v k) else 0) :
    E.quantumMinor u (Fin.snoc v r) (Fin.snoc v r) =
      E.quantumMinor u v v * (algebraMap K A (u - (n + 1 : ℕ)) + E r r) -
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (-1 : ℤ) ^ (i.val + j.val) •
          (E r (v j) * E.quantumMinor u (i.removeNth v) (j.removeNth v) * E (v i) r) := by
  rw [quantumMinor_succ_column_last, Fin.sum_univ_castSucc]
  simp only [Fin.init_snoc, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, one_smul,
    Fin.removeNth_last, ite_true, Fin.snoc_castSucc, Fin.val_castSucc]
  rw [add_comm]
  simp only [sub_eq_add_neg, add_right_inj, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have htuple : i.castSucc.removeNth (Fin.snoc v r : Fin (n + 2) → ι) =
      Fin.snoc (i.removeNth v) r := by
    ext k
    refine Fin.lastCases ?_ (fun l ↦ ?_) k
    · simp [Fin.removeNth_apply, Fin.succAbove_ne_last_last i.castSucc_lt_last.ne]
    · simp [Fin.removeNth_apply, Fin.castSucc_succAbove_castSucc, Fin.snoc_castSucc]
  have hri : v i ≠ r := fun h ↦ hr ⟨i, h⟩
  simp only [htuple, hri, ite_false, zero_add]
  rw [← Fin.insertNth_last', E.quantumMinor_insertNth_exteriorRow u (i.removeNth v) v (Fin.last n)
    hr (fun k j l ↦ hE (i.succAbove k) j l), Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Fin.val_last, smul_mul_assoc, smul_smul, ← pow_add, ← neg_smul]
  have hsign : (-1 : ℤ) ^ (n + 1 - i.val + (n + j.val)) = -((-1) ^ (i.val + j.val)) := by
    rw [(by omega : n + 1 - i.val + (n + j.val) = i.val + j.val + 2 * (n - i.val) + 1),
      pow_succ, pow_add, pow_mul]
    norm_num
  rw [hsign]

end Matrix
