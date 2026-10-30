/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct
public import TauCeti.GroupTheory.GroupAction.Stabilizer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Algebra.Group.Torsion

/-!
# Centralizers of parabolic matrices

Over an additively torsion-free commutative ring, a nonscalar matrix with discriminant zero
has infinitely many determinant-one matrices commuting with it. Explicitly, if `M` is
parabolic, then `1 + r • (2 M - tr(M) I)`, for `r ∈ ℤ`, gives distinct such matrices.
No invertibility assumption on `M` is needed.

In particular, the natural-number stabilizer cardinality of its conjugacy class in a fixed
trace-and-determinant fibre is zero by the convention for infinite types. This fact alone
does not compute a trace-formula class weight.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1 and §4.
-/

public section

open MulAction ConjAct
open scoped MatrixGroups

namespace Matrix

/-- A parabolic matrix over an additively torsion-free commutative ring has an infinite
centralizer in `SL(2, R)`, viewed as its stabilizer under conjugation. This includes singular
parabolic matrices. -/
theorem infinite_stabilizer_of_isParabolic {R : Type*} [CommRing R] [IsAddTorsionFree R]
    (M : Matrix (Fin 2) (Fin 2) R) (hM : M.IsParabolic) :
    Infinite (stabilizer (ConjAct SL(2, R)) M) := by
  let H : Matrix (Fin 2) (Fin 2) R :=
    !![M 0 0 - M 1 1, 2 * M 0 1; 2 * M 1 0, M 1 1 - M 0 0]
  have hH : H ≠ 0 := by
    intro h
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R ↦ A 0 0) h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R ↦ A 0 1) h
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R ↦ A 1 0) h
    simp [H, sub_eq_zero] at h00 h01 h10
    simp only [two_mul, ← two_nsmul, two_nsmul_eq_zero] at h01 h10
    apply hM.1
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10]
  have hd : (M 0 0 + M 1 1) ^ 2 - 4 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
    simpa only [discr_fin_two, trace_fin_two, det_fin_two] using hM.2
  have hdet (r : ℤ) : (1 + r • H).det = 1 := by
    simp [det_fin_two, H, zsmul_eq_mul]
    linear_combination -(r : R) ^ 2 * hd
  let U (r : ℤ) : SL(2, R) := ⟨1 + r • H, hdet r⟩
  have hcomm (r : ℤ) : (U r : Matrix (Fin 2) (Fin 2) R) * M = M * U r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, H, mul_apply, Fin.sum_univ_two, zsmul_eq_mul] <;> ring
  have hfix (r : ℤ) : toConjAct (U r) ∈ stabilizer (ConjAct SL(2, R)) M := by
    rw [mem_stabilizer_iff, specialLinearGroup_smul_def, ofConjAct_toConjAct, hcomm]
    simp [Matrix.mul_assoc, Matrix.mul_adjugate]
  let f (r : ℤ) : stabilizer (ConjAct SL(2, R)) M := ⟨toConjAct (U r), hfix r⟩
  refine Infinite.of_injective f fun r s hrs ↦ ?_
  have hU : U r = U s := toConjAct.injective (congrArg Subtype.val hrs)
  have hsmul : r • H = s • H := add_left_cancel (congrArg Subtype.val hU)
  obtain ⟨i, j, hij⟩ : ∃ i j, H i j ≠ 0 := by
    contrapose! hH
    ext i j
    exact hH i j
  apply IsAddTorsionFree.zsmul_left_injective hij
  simpa only [smul_apply] using congrArg (fun A ↦ A i j) hsmul

end Matrix

namespace TauCeti

/-- The conjugacy class of a parabolic matrix in a fixed trace-and-determinant fibre has
infinite stabilizer, hence stabilizer cardinality zero in `ℕ`. -/
theorem cardStabilizerOnOrbit_eq_zero_of_isParabolic {R : Type*} [CommRing R]
    [IsAddTorsionFree R] {t n : R} (M : traceDetFiber (Fin 2) t n)
    (hM : (M : Matrix (Fin 2) (Fin 2) R).IsParabolic) :
    cardStabilizerOnOrbit (Quotient.mk'' M : orbitRel.Quotient (ConjAct SL(2, R)) _) = 0 := by
  have : Infinite (stabilizer (ConjAct SL(2, R)) M) := by
    rw [SubMulAction.stabilizer_of_subMul]
    exact Matrix.infinite_stabilizer_of_isParabolic _ hM
  simpa only [cardStabilizerOnOrbit_mk] using
    (Nat.card_eq_zero_of_infinite : Nat.card (stabilizer (ConjAct SL(2, R)) M) = 0)

end TauCeti
