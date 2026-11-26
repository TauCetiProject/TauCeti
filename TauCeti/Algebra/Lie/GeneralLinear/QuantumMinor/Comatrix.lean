/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Alternating
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.GroupTheory.Perm.Fin

/-!
# The comatrix identity for quantum minors

The signed cofactors, multiplied on the right by the matrix of entries at the last spectral
shift, give the full minor on the diagonal and zero off the diagonal. The proof expands a
minor along its last column after moving the column to be replaced there. A duplicate column
accounts for the zero terms. The Capelli comatrix is the case of the full row and column tuples.

The quantum comatrix convention is that of L. Alpöge's `Formalism.REAL.QComatrix`.
-/

public section

open Equiv Equiv.Perm

namespace Matrix

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

private theorem quantumMinor_snoc_removeNth (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) (a b : Fin (n + 1) → ι) (i : Fin (n + 1)) :
    E.quantumMinor u a (Fin.snoc (i.removeNth b) (b i)) =
      (-1 : ℤ) ^ (n - i.val) • E.quantumMinor u a b := by
  -- Conjugate the permutation that moves a column to the front by reversal of the tuple.
  let e : Perm (Fin (n + 1)) := Fin.revPerm * (i.rev.cycleRange)⁻¹ * Fin.revPerm⁻¹
  have hb : Fin.snoc (i.removeNth b) (b i) = b ∘ e := by
    ext j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp [e, Fin.revPerm_symm, Fin.cycleRange_symm_zero]
    · simp [e, Fin.revPerm_symm, Fin.rev_castSucc,
        Fin.cycleRange_symm_succ, Fin.rev_succAbove, Fin.removeNth]
  have hs : sign e = (-1) ^ (n - i.val) := by
    simp [e, sign_mul, sign_inv, Fin.sign_cycleRange, Fin.val_rev, mul_comm, mul_left_comm]
  rw [hb, E.quantumMinor_comp_perm_right hE, hs, Units.smul_def]
  simp

/-- The quantum comatrix identity on any row and column tuples. The last shifted entry
multiplies its cofactor on the right. For `a = b = id` this is the Capelli comatrix identity. -/
theorem quantumMinor_comatrix (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    (u : K) (a b : Fin (n + 1) → ι) (i l : Fin (n + 1)) :
    (∑ j : Fin (n + 1), (-1 : ℤ) ^ (i.val + j.val) •
      (E.quantumMinor u (j.removeNth a) (i.removeNth b) *
        ((if a j = b l then algebraMap K A (u - (n : K)) else 0) + E (a j) (b l)))) =
      if b i = b l then E.quantumMinor u a b else 0 := by
  let b' : Fin (n + 1) → ι := Fin.snoc (i.removeNth b) (b l)
  have hsign (j : Fin (n + 1)) :
      (-1 : ℤ) ^ (i.val + j.val) = (-1) ^ (n - i.val) * (-1) ^ (n - j.val) := by
    simp only [← Int.coe_negOnePow_natCast, Nat.cast_add, ← Units.val_mul, ← Int.negOnePow_add,
      Nat.cast_sub (by omega : i.val ≤ n), Nat.cast_sub (by omega : j.val ≤ n)]
    apply congrArg ((↑) : ℤˣ → ℤ)
    rw [Int.negOnePow_eq_iff]
    exact ⟨(i.val : ℤ) + j.val - n, by omega⟩
  simp_rw [hsign, ← smul_smul]
  rw [← Finset.smul_sum]
  have hexpand := E.quantumMinor_succ_column_last u a b'
  simp only [b', Fin.init_snoc, Fin.snoc_last] at hexpand
  rw [← hexpand]
  split_ifs with h
  · rw [← h, quantumMinor_snoc_removeNth E hE, smul_smul, ← pow_add]
    simp [← two_mul, pow_mul]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (show l ≠ i from fun hli ↦ h (by rw [hli]))
    have hrepeat : ¬ Function.Injective b' := by
      intro hb'
      have hkl : k.castSucc = Fin.last n := hb' (by simp [b', Fin.removeNth, hk])
      exact k.castSucc_lt_last.ne hkl
    rw [E.quantumMinor_eq_zero_of_not_injective_right hE u a b' hrepeat, smul_zero]

end Matrix
