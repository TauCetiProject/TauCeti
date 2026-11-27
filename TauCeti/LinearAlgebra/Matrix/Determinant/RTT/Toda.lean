/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.RTT.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Ring.Units

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
    simp only [todaSite_apply_zero_zero, todaSite_apply_zero_one, map_one, map_zero, sub_zero,
      one_smul, zero_add, add_mul, mul_add, mul_neg, neg_mul, one_mul, mul_one] at h'
    linear_combination (norm := abel) -h'
  · intro h
    have hc : p * (c : A) = (c : A) * p + c := by
      linear_combination (norm := abel) h
    have hi := Units.mul_inv_eq_inv_mul_sub_inv hc
    refine isRTT_iff.mpr fun u v i j k l ↦ ?_
    -- Write the scalars as `• 1`, expand, and use `[p, c] = c` and `[p, c⁻¹] = -c⁻¹` to order
    -- every product; what remains is linear over `K`.
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, hc, hi] <;>
      module

end TauCeti
