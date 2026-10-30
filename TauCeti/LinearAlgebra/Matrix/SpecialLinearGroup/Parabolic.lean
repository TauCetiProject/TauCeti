/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Algebra.Module.Torsion.Free

/-!
# Integral centralizers of parabolic matrices

A nonscalar integral matrix with a repeated eigenvalue has infinitely many determinant-one
integral matrices commuting with it. Explicitly, if `M` is parabolic, then
`1 + r (2 M - tr(M) I)`, for `r ∈ ℤ`, gives distinct such matrices. No invertibility assumption
on `M` is needed.

This is the centralizer calculation behind the zero automorphism weight of parabolic conjugacy
classes in the level-one trace formula.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1.
-/

public section

open MulAction ConjAct
open scoped MatrixGroups

namespace Matrix

/-- A parabolic integral matrix has an infinite centralizer in `SL(2, ℤ)`, viewed as its
stabilizer under conjugation. This includes singular parabolic matrices. -/
theorem infinite_stabilizer_of_isParabolic (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.IsParabolic) : Infinite (stabilizer (ConjAct SL(2, ℤ)) M) := by
  let H : Matrix (Fin 2) (Fin 2) ℤ :=
    !![M 0 0 - M 1 1, 2 * M 0 1; 2 * M 1 0, M 1 1 - M 0 0]
  have hH : H ≠ 0 := by
    intro h
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ ↦ A 0 0) h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ ↦ A 0 1) h
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ ↦ A 1 0) h
    simp [H] at h00 h01 h10
    apply hM.1
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [intCast_apply] <;> omega
  have hd : (M 0 0 + M 1 1) ^ 2 - 4 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
    simpa only [discr_fin_two, trace_fin_two, det_fin_two] using hM.2
  have hdet (r : ℤ) : (1 + r • H).det = 1 := by
    simp [det_fin_two, H]
    linear_combination -r ^ 2 * hd
  let U (r : ℤ) : SL(2, ℤ) := ⟨1 + r • H, hdet r⟩
  have hcomm (r : ℤ) : (U r : Matrix (Fin 2) (Fin 2) ℤ) * M = M * U r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, H, mul_apply, Fin.sum_univ_two] <;> ring
  have hfix (r : ℤ) : toConjAct (U r) ∈ stabilizer (ConjAct SL(2, ℤ)) M := by
    rw [mem_stabilizer_iff, specialLinearGroup_smul_def, ofConjAct_toConjAct, hcomm]
    simp [Matrix.mul_assoc, Matrix.mul_adjugate]
  let f (r : ℤ) : stabilizer (ConjAct SL(2, ℤ)) M := ⟨toConjAct (U r), hfix r⟩
  refine Infinite.of_injective f fun r s hrs ↦ ?_
  have hU : U r = U s := toConjAct.injective (congrArg Subtype.val hrs)
  have hsmul : r • H = s • H := add_left_cancel (congrArg Subtype.val hU)
  exact smul_left_injective ℤ hH hsmul

end Matrix
