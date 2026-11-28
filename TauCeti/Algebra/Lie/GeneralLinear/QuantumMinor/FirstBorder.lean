/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Basic
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Commutator
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The first-border expansion of a quantum minor

Adjoining a common first row and column to a quantum minor gives a corner term and a
contraction of the two off-diagonal borders against the smaller minors. The corner
cofactor starts at `u - 1`; the cofactors in the contraction start at `u - 2` and
are multiplied by the border entries on opposite sides.

The principal-tuple identity is L. Alpöge's `Formalism.FourierDecayAlt.P.border_first_expansion`
in the formalization of the Riemann hypothesis for Dirichlet L-functions.
-/

public section

namespace Matrix

open Equiv.Perm Function

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A]

-- The commutator contribution changes the first-column shift from `u` to `u - 1`.
private theorem firstBorder_column_shift (E : Matrix ι ι A) (u : K) (i j : ι) (m : ℕ)
    (x : A) :
    (if j = i then (-1 : ℤ) ^ m • x else 0) +
      (-1 : ℤ) ^ (m + 1) • (((if i = j then algebraMap K A u else 0) + E i j) * x) =
    -((-1 : ℤ) ^ m • (((if i = j then algebraMap K A (u - 1) else 0) + E i j) * x)) := by
  by_cases hij : i = j
  · simp only [hij, ite_true, pow_succ, mul_neg, mul_one, neg_smul, map_sub, map_one,
      add_mul, sub_add_eq_add_sub, sub_mul, one_mul, smul_sub]
    abel
  · simp [hij, Ne.symm hij, pow_succ]

/-- Expand an exterior first row on the right. Moving its entries past later columns lowers
all cofactor parameters by one. -/
theorem quantumMinor_cons_left_eq_sum_minor_mul (E : Matrix ι ι A) {n : ℕ} (u : K)
    (a : Fin n → ι) (b : Fin (n + 1) → ι) (e : ι) (hb : ∀ j, b j ≠ e)
    (hE : ∀ i j (k : Fin (n + 1)), j < k →
      ⁅E e (b j), E (a i) (b k)⁆ = if b j = a i then E e (b k) else 0) :
    E.quantumMinor u (Fin.cons e a) b = ∑ j, (-1 : ℤ) ^ j.val •
      (E.quantumMinor (u - 1) a (j.removeNth b) * E e (b j)) := by
  induction n generalizing u with
  | zero => simp [Ne.symm (hb 0)]
  | succ n ih =>
    conv_lhs => rw [E.quantumMinor_succ_column_zero, Fin.sum_univ_succ]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Ne.symm (hb 0), ite_false,
      zero_add, Fin.removeNth_zero, Fin.tail_cons, Fin.cons_succ, Fin.removeNth_succ_cons]
    -- Putting the exterior entry to the right produces a row replacement for each match
    -- with the first column label. Move each replacement row to the front for induction.
    have hreplace (i : Fin (n + 1)) :
        E.quantumMinor (u - 1) (update a i e) (Fin.tail b) =
          (-1 : ℤ) ^ i.val • E.quantumMinor (u - 1) (Fin.cons e (i.removeNth a)) (Fin.tail b) := by
      simpa [Units.smul_def, Fin.sign_cycleRange, Fin.insertNth_removeNth] using
        E.quantumMinor_comp_perm_left (u - 1) (Fin.cons e (i.removeNth a)) (Fin.tail b) i.cycleRange
    have hcomm (x y : A) : x * y = y * x + ⁅x, y⁆ := by rw [Ring.lie_def]; abel
    rw [hcomm (E e (b 0)), add_assoc, add_right_inj,
      E.lie_quantumMinor (u - 1) a (Fin.tail b) (fun i j ↦ by
        simpa [Fin.tail, Ne.symm (hb j.succ)] using hE i 0 j.succ (Fin.succ_pos _))]
    have htail (j : Fin (n + 1)) : e ≠ Fin.tail b j := Ne.symm (hb j.succ)
    simp only [htail, ite_false, Finset.sum_const_zero, sub_zero, hreplace]
    rw [← Finset.sum_add_distrib]
    have hrec (i : Fin (n + 1)) := ih (u - 1) (i.removeNth a) (Fin.tail b)
      (fun j ↦ hb j.succ)
      (fun r j k hjk ↦ hE (i.succAbove r) j.succ k.succ (Fin.succ_lt_succ_iff.mpr hjk))
    simp only [Fin.val_succ, firstBorder_column_shift, hrec]
    -- Expand the cofactors on the right in their first column, then align the two sums.
    have hcols (j : Fin (n + 1)) :
        j.succ.removeNth b = Fin.cons (b 0) (j.removeNth (Fin.tail b)) := by
      conv_lhs => rw [← Fin.cons_self_tail b]
      exact Fin.removeNth_succ_cons j _ _
    simp only [hcols, E.quantumMinor_succ_column_zero (u - 1) a,
      Fin.cons_zero, Fin.tail_cons, pow_succ, mul_neg, mul_one, neg_smul,
      Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, Finset.sum_neg_distrib, neg_inj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Fin.tail, mul_smul_comm, smul_mul_assoc, mul_assoc, smul_comm ((-1 : ℤ) ^ i.val)]

/-- The expansion of a quantum minor with a common first row and column index `e` outside
both nonempty interior tuples. Only the indicated mixed commutators are needed; in particular
the interior tuples need not be injective. For empty tuples the corner term is the whole minor,
as given by `quantumMinor_fin_one`. -/
theorem quantumMinor_first_border (E : Matrix ι ι A) {n : ℕ} (u : K)
    (a b : Fin (n + 1) → ι) (e : ι) (ha : ∀ i, a i ≠ e) (hb : ∀ j, b j ≠ e)
    (hE : ∀ i j k, j < k →
      E e (b j) * E (a i) (b k) - E (a i) (b k) * E e (b j) =
        if b j = a i then E e (b k) else 0) :
    E.quantumMinor u (Fin.cons e a) (Fin.cons e b) =
      (algebraMap K A u + E e e) * E.quantumMinor (u - 1) a b -
        ∑ i, ∑ j, (-1 : ℤ) ^ (i.val + j.val) •
          (E (a i) e * E.quantumMinor (u - 2) (i.removeNth a) (j.removeNth b) * E e (b j)) := by
  rw [E.quantumMinor_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons,
    Fin.removeNth_zero, Fin.removeNth_succ_cons, ite_true, ha, ite_false, zero_add]
  have hrec (i : Fin (n + 1)) := E.quantumMinor_cons_left_eq_sum_minor_mul (u - 1)
    (i.removeNth a) b e hb
    (fun r j k hjk ↦ by
      rw [Ring.lie_def]
      exact hE (i.succAbove r) j k hjk)
  have hshift : u - 1 - 1 = u - 2 := by ring
  simp only [hrec, hshift]
  simp only [Fin.val_succ, pow_succ, mul_neg, mul_one, Finset.mul_sum, Finset.smul_sum,
    mul_smul_comm, ← mul_assoc, smul_smul, neg_mul, ← pow_add, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

end Matrix
