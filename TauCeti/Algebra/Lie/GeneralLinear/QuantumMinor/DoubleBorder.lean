/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Alternating
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.FirstBorder
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.LastBorder
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Double-border expansions of quantum minors

Expand a quantum minor with a common first and last border. Successive deletions use the
induced order on the surviving positions, so cofactor signs need no sorting of labels.
The source identity is L. Alpöge's `Formalism.FourierDecayAlt.P.border_full_expansion`.
-/

public section

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A]

private theorem exteriorRow_commutator {E : Matrix ι ι A} (hE : E.HasMatrixUnitLieRelations)
    {e b a c : ι} (hc : c ≠ e) : ⁅E e b, E a c⁆ = if b = a then E e c else 0 := by
  rw [Ring.lie_def, hasMatrixUnitLieRelations_iff.mp hE, ite_eq_right hc, sub_zero]

/-- With neither exterior row label occurring in the column tuple, expand the last row
on the left and the first row on the right. The two deletions are ordered: remove `j`
first, then remove `l` from the surviving columns. -/
theorem quantumMinor_cons_snoc_eq_sum (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    {n : ℕ} (u : K) (a : Fin n → ι) (b : Fin (n + 2) → ι) (e f : ι)
    (he : ∀ j, b j ≠ e) (hf : ∀ j, b j ≠ f) :
    E.quantumMinor u (Fin.snoc (Fin.cons e a) f) b =
      ∑ j, ∑ l : Fin (n + 1), (-1 : ℤ) ^ (n + 1 + j.val + l.val) •
        (E f (b j) * E.quantumMinor (u - 1) a (l.removeNth (j.removeNth b)) *
          E e (j.removeNth b l)) := by
  rw [← Fin.insertNth_last', E.quantumMinor_insertNth_left_of_notMem_range u (Fin.cons e a) b
    (Fin.last (n + 1)) (fun ⟨j, hj⟩ ↦ hf j hj)
    (fun _ _ k _ ↦ exteriorRow_commutator hE (hf k))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [E.quantumMinor_cons_left_eq_sum_minor_mul u a (j.removeNth b) e
    (fun l ↦ he (j.succAbove l)) (fun _ _ l _ ↦ exteriorRow_commutator hE (he (j.succAbove l))),
    Finset.mul_sum, Finset.smul_sum]
  simp only [Fin.val_last, mul_smul_comm, smul_smul, ← pow_add, mul_assoc]

private theorem quantumMinor_exterior_corner (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) {n : ℕ} (u : K)
    (a : Fin (n + 1) → ι) (b : Fin (n + 2) → ι) {e f : ι}
    (hef : e ≠ f) (ha : ∀ k, a k ≠ f) (hbe : ∀ j, b j ≠ e) (hbf : ∀ j, b j ≠ f) :
    E.quantumMinor u (Fin.cons e (Fin.snoc a f)) (Fin.snoc b f) =
      (∑ j, (-1 : ℤ) ^ j.val • (E.quantumMinor (u - 1) a (j.removeNth b) * E e (b j))) *
        (algebraMap K A (u - (n + 2 : ℕ)) + E f f) +
      (-1 : ℤ) ^ (n + 2) • (E.quantumMinor u (Fin.snoc a f) b * E e f) +
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (n + 1 - k.val) •
        ((∑ j, ∑ l : Fin (n + 1), (-1 : ℤ) ^ (n + 1 + j.val + l.val) •
          (E f (b j) * E.quantumMinor (u - 1) (k.removeNth a) (l.removeNth (j.removeNth b)) *
            E e (j.removeNth b l))) * E (a k) f) := by
  have hlast : Fin.cons (α := fun _ : Fin (n + 3) ↦ ι) e (Fin.snoc a f)
      ((Fin.last (n + 1)).succ) = f := by
    rw [Fin.succ_last, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_last]
  have hremove : Fin.removeNth (α := fun _ : Fin (n + 3) ↦ ι) (Fin.last (n + 1)).succ
      (Fin.cons e (Fin.snoc a f)) = Fin.cons e a := by
    rw [Fin.removeNth_succ_cons, Fin.removeNth_last, Fin.init_snoc]
  rw [E.quantumMinor_succ_column_last, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, Fin.snoc_last, Fin.init_snoc, Fin.val_zero, Nat.sub_zero, hef,
    ite_false, zero_add, Fin.removeNth_zero, Fin.tail_cons, hlast, hremove, Fin.cons_succ,
    Fin.snoc_castSucc, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.removeNth_succ_cons,
    Fin.removeNth_castSucc_snoc, ha, ite_true]
  have hzero : n + 2 - (n + 1 + 1) = 0 := by omega
  simp only [hzero, pow_zero, one_smul]
  rw [E.quantumMinor_cons_left_eq_sum_minor_mul u a b e hbe
    (fun _ _ l _ ↦ exteriorRow_commutator hE (hbe l))]
  have hs (k : Fin (n + 1)) : n + 2 - (k.val + 1) = n + 1 - k.val := by omega
  simp only [hs]
  rw [← add_assoc, add_right_comm]
  congr 1
  · exact add_comm _ _
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin.cons_snoc_eq_snoc_cons,
    E.quantumMinor_cons_snoc_eq_sum hE u (k.removeNth a) b e f hbe hbf]

/-- Expand both borders of a quantum minor with at least two interior positions.
The terms are the interior minor multiplied by both corners, the contractions against
one border at a time, the mixed corner cofactors, and the contraction with two interior
deletions on each side.
The latter is indexed by positions in successive cofactors, rather than by sorted pairs of
positions in the original tuples. -/
theorem quantumMinor_double_border (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    {n : ℕ} (u : K) (a b : Fin (n + 2) → ι) {e f : ι} (hef : e ≠ f)
    (hae : ∀ i, a i ≠ e) (hbe : ∀ j, b j ≠ e) (haf : ∀ i, a i ≠ f) (hbf : ∀ j, b j ≠ f) :
    let T := algebraMap K A u + E e e
    let S := algebraMap K A (u - (n + 2 : ℕ) - 1) + E f f
    E.quantumMinor u (Fin.cons e (Fin.snoc a f)) (Fin.cons e (Fin.snoc b f)) =
      T * (E.quantumMinor (u - 1) a b * S -
        ∑ i, ∑ j, (-1 : ℤ) ^ (i.val + j.val) •
          (E f (b j) * E.quantumMinor (u - 1) (i.removeNth a) (j.removeNth b) * E (a i) f)) +
      (-1 : ℤ) ^ (n + 3) • (E f e * E.quantumMinor (u - 1) (Fin.cons e a) (Fin.snoc b f)) +
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i.val + 1) • (E (a i) e *
        ((∑ j, (-1 : ℤ) ^ j.val •
          (E.quantumMinor (u - 2) (i.removeNth a) (j.removeNth b) * E e (b j))) * S +
        (-1 : ℤ) ^ (n + 2) •
          (E.quantumMinor (u - 1) (Fin.snoc (i.removeNth a) f) b * E e f) +
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (n + 1 - k.val) •
          ((∑ j, ∑ l : Fin (n + 1), (-1 : ℤ) ^ (n + 1 + j.val + l.val) •
            (E f (b j) * E.quantumMinor (u - 2) (k.removeNth (i.removeNth a))
              (l.removeNth (j.removeNth b)) * E e (j.removeNth b l))) *
            E (i.removeNth a k) f))) := by
  dsimp only
  rw [E.quantumMinor_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, Fin.val_zero, pow_zero, one_smul, ite_true, Fin.removeNth_zero,
    Fin.tail_cons, Fin.val_succ, Fin.cons_succ, Fin.val_castSucc, Fin.snoc_castSucc, hae,
    ite_false, zero_add, Fin.removeNth_succ_cons, Fin.removeNth_castSucc_snoc, Fin.val_last,
    Fin.snoc_last, hef.symm, Fin.removeNth_last, Fin.init_snoc]
  have hshift : u - 1 - (↑(n + 2 : ℕ) : K) = u - ↑(n + 2 : ℕ) - 1 := by abel
  have hshift' : u - 1 - 1 = u - 2 := by ring
  rw [E.quantumMinor_snoc (u - 1) a b (fun ⟨j, hj⟩ ↦ hbf j hj) (fun ⟨i, hi⟩ ↦ haf i hi)
    (fun _ _ k _ ↦ exteriorRow_commutator hE (hbf k))]
  simp only [ite_true, hshift]
  rw [← add_assoc, add_right_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [quantumMinor_exterior_corner E hE (u - 1) (i.removeNth a) b hef
      (fun k ↦ haf (i.succAbove k)) hbe hbf, hshift, hshift']

/-- The double-border expansion with one interior position has no term with two interior
deletions. It uses only column expansion, not the matrix-unit relations. -/
theorem quantumMinor_double_border_one (E : Matrix ι ι A) (u : K) (a b e f : ι)
    (hef : e ≠ f) (hae : a ≠ e) (hbe : b ≠ e) (haf : a ≠ f) (hbf : b ≠ f) :
    let T := algebraMap K A u + E e e
    let S := algebraMap K A (u - 2) + E f f
    E.quantumMinor u ![e, a, f] ![e, b, f] =
      T * (E.quantumMinor (u - 1) ![a] ![b] * S - E f b * E a f) +
      E f e * E.quantumMinor (u - 1) ![e, a] ![b, f] -
      E a e * (E e b * S - E f b * E e f) := by
  dsimp only
  conv_lhs => rw [E.quantumMinor_succ_column_zero, Fin.sum_univ_three]
  have hs : u - 2 = u - 1 - 1 := by ring
  rw [hs]
  simp [E.quantumMinor_fin_two, Fin.removeNth_apply, Fin.succAbove,
    hef, hef.symm, hae, hbe.symm, haf, hbf.symm, sub_eq_add_neg]
  abel

end Matrix
