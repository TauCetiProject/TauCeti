/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.RTT.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# The RTT matrix of a Toda site

The local Toda Lax matrix uses an invertible coordinate `c` and its Euler operator `p`.
It has quantum determinant one, and satisfies the exchange relation when `[p, c] = c`.

See E. K. Sklyanin, *The quantum Toda chain*, for the local Lax-matrix description.
The signs and order of the entries used here are those of the transfer matrix in L. Alpöge's
formalization of the Riemann hypothesis for Dirichlet L-functions.
-/

public section

namespace TauCeti

variable {K A : Type*} [Ring A]

section Entries

variable [CommSemiring K] [Algebra K A]

/-- The local Toda Lax matrix with Euler operator `p`, invertible coordinate `c` and
spectral parameter `u`. -/
def todaSite (p : A) (c : Aˣ) (u : K) : Matrix (Fin 2) (Fin 2) A :=
  !![algebraMap K A u + p, -(c : A); (↑c⁻¹ : A), 0]

/-- The entries of the Toda site matrix. -/
theorem todaSite_def (p : A) (c : Aˣ) (u : K) :
    todaSite p c u = !![algebraMap K A u + p, -(c : A); (↑c⁻¹ : A), 0] := (rfl)

@[simp] theorem todaSite_apply_zero_zero (p : A) (c : Aˣ) (u : K) :
    todaSite p c u 0 0 = algebraMap K A u + p := (rfl)

@[simp] theorem todaSite_apply_zero_one (p : A) (c : Aˣ) (u : K) :
    todaSite p c u 0 1 = -(c : A) := (rfl)

@[simp] theorem todaSite_apply_one_zero (p : A) (c : Aˣ) (u : K) :
    todaSite p c u 1 0 = (↑c⁻¹ : A) := (rfl)

@[simp] theorem todaSite_apply_one_one (p : A) (c : Aˣ) (u : K) :
    todaSite p c u 1 1 = 0 := (rfl)

/-- The quantum determinant of a Toda site is one, independently of its Euler operator. -/
@[simp] theorem quantumDetTwo_todaSite (p : A) (c : Aˣ) (v : K) :
    quantumDetTwo (todaSite p c) v = 1 := by
  simp [quantumDetTwo_def]

end Entries

variable [CommRing K] [Algebra K A]

/-- A Toda site satisfies RTT exactly when the commutator of its Euler operator with the
coordinate is the coordinate itself. -/
@[simp] theorem isRTT_todaSite_iff (p : A) (c : Aˣ) :
    IsRTT (todaSite (K := K) p c) ↔ p * (c : A) - (c : A) * p = (c : A) := by
  constructor
  · intro h
    have h' := isRTT_iff.mp h 1 0 0 0 0 1
    simp [add_mul, mul_add] at h'
    linear_combination (norm := abel) -h'
  · intro h
    have hc : p * (c : A) = (c : A) * p + c := by
      linear_combination (norm := abel) h
    have hi : p * (↑c⁻¹ : A) = (↑c⁻¹ : A) * p - (↑c⁻¹ : A) := by
      have h' := congrArg (fun z : A ↦ (↑c⁻¹ : A) * z * (↑c⁻¹ : A)) hc
      simp only [mul_add, add_mul, ← mul_assoc, Units.inv_mul, one_mul] at h'
      have h'' : (↑c⁻¹ : A) * p = p * (↑c⁻¹ : A) + (↑c⁻¹ : A) := by
        simpa only [mul_assoc, Units.mul_inv, mul_one] using h'
      exact eq_sub_of_add_eq h''.symm
    refine isRTT_iff.mpr fun u v i j k l ↦ ?_
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, todaSite_apply_zero_zero,
        todaSite_apply_zero_one, todaSite_apply_one_zero, todaSite_apply_one_one,
        Algebra.smul_def, map_sub, add_mul, mul_add, sub_mul, mul_sub, mul_neg, neg_mul,
        mul_zero, zero_mul, sub_self, zero_add, neg_zero, neg_neg,
        Units.mul_inv, Units.inv_mul,
        Algebra.commutes u p, Algebra.commutes v p,
        Algebra.commutes u (c : A), Algebra.commutes v (c : A),
        Algebra.commutes u (↑c⁻¹ : A), Algebra.commutes v (↑c⁻¹ : A),
        Algebra.commutes u (algebraMap K A v), hc, hi] <;>
      noncomm_ring

end TauCeti
