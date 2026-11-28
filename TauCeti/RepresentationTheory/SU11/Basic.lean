/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Matrix coordinates on `SU(1,1)`

The special unitary group of the Hermitian form with Gram matrix `diag(1, -1)` consists
of the matrices `!![a, b; conj b, conj a]` with `‖a‖ ^ 2 - ‖b‖ ^ 2 = 1`. The entries
`SU11.entryA` and `SU11.entryB` recover the pair, and `SU11.ofPair` constructs the
group element. The group inherits the subspace topology from `SL(2, ℂ)`.

The entry convention is that of Vilenkin and Klimyk, *Representation of Lie Groups and
Special Functions*, Vol. 1, §6.1.1.
-/

public section

open Matrix Topology
open scoped MatrixGroups

namespace TauCeti

/-- The subgroup of `SL(2, ℂ)` preserving the Hermitian form with Gram matrix `diag(1, -1)`. -/
def su11 : Subgroup (SL(2, ℂ)) :=
  (diagonal ![1, -1]).specialIsometryGroup (starRingEnd ℂ)

/-- The special unitary group of signature `(1, 1)`, with its matrix topology. -/
abbrev SU11 := ↥su11

/-- Membership in `su11` is the indefinite unitary equation `gᴴ J g = J`. -/
@[simp]
theorem mem_su11_iff {g : SL(2, ℂ)} :
    g ∈ su11 ↔ (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * diagonal (![1, -1] : Fin 2 → ℂ) *
      (g : Matrix (Fin 2) (Fin 2) ℂ) = diagonal ![1, -1] := by
  have hstar : (starRingEnd ℂ : ℂ → ℂ) = star := funext starRingEnd_apply
  rw [su11, mem_specialIsometryGroup_iff, conjTranspose, transpose_map, hstar]

namespace SU11

/-- The upper-left entry of an element of `SU(1,1)`. -/
def entryA (g : SU11) : ℂ := (g.val : Matrix (Fin 2) (Fin 2) ℂ) 0 0

/-- The upper-right entry of an element of `SU(1,1)`. -/
def entryB (g : SU11) : ℂ := (g.val : Matrix (Fin 2) (Fin 2) ℂ) 0 1

/-- The upper-left coefficient is the matrix entry at `(0, 0)`. -/
theorem entryA_def (g : SU11) : g.entryA = (g.val : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := (rfl)

/-- The upper-right coefficient is the matrix entry at `(0, 1)`. -/
theorem entryB_def (g : SU11) : g.entryB = (g.val : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := (rfl)

/-- In an element of `SU(1,1)`, the bottom row is the conjugate of the reversed top row. -/
theorem coe_eq_matrix (g : SU11) :
    (g.val : Matrix (Fin 2) (Fin 2) ℂ) =
      !![g.entryA, g.entryB; star g.entryB, star g.entryA] := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := g.val
  let J := diagonal (![1, -1] : Fin 2 → ℂ)
  have hg : Aᴴ * J * A = J := mem_su11_iff.mp g.property
  have hdet : A.det = 1 := g.val.det_coe
  -- The adjugate is the inverse in `SL(2, ℂ)`, so right multiplication removes `A`.
  have h := congrArg (· * A.adjugate) hg
  rw [mul_assoc (Aᴴ * J), mul_adjugate, hdet, one_smul, mul_one, adjugate_fin_two] at h
  have ha : star (A 0 0) = A 1 1 := by
    simpa [J, mul_diagonal, diagonal_mul] using congrFun (congrFun h 0) 0
  have hb : star (A 0 1) = A 1 0 := by
    simpa [J, mul_diagonal, diagonal_mul] using congrFun (congrFun h 1) 0
  calc
    A = !![A 0 0, A 0 1; A 1 0, A 1 1] := eta_fin_two A
    _ = _ := by simp only [entryA_def, entryB_def, ← ha, ← hb, A]

/-- The entries of an element of `SU(1,1)` satisfy the determinant-one relation. -/
theorem norm_entryA_sq_sub_norm_entryB_sq (g : SU11) :
    ‖g.entryA‖ ^ 2 - ‖g.entryB‖ ^ 2 = 1 := by
  have h := g.val.det_coe
  rw [coe_eq_matrix, det_fin_two] at h
  apply Complex.ofReal_injective
  simpa [Complex.mul_conj, Complex.sq_norm] using h

/-- An element of `SU(1,1)` is determined by its top row. -/
@[ext]
theorem ext {g h : SU11} (ha : g.entryA = h.entryA) (hb : g.entryB = h.entryB) : g = h :=
  Subtype.ext (Subtype.ext (by rw [coe_eq_matrix g, coe_eq_matrix h, ha, hb]))

/-- Construct an element of `SU(1,1)` from a top row satisfying the determinant-one relation. -/
noncomputable def ofPair (a b : ℂ) (h : ‖a‖ ^ 2 - ‖b‖ ^ 2 = 1) : SU11 := by
  have hdet : a * star a - b * star b = 1 := by
    simpa [Complex.mul_conj, Complex.sq_norm] using congrArg Complex.ofReal h
  refine ⟨SpecialLinearGroup.mk !![a, b; star b, star a] (by simpa [det_fin_two] using hdet),
    mem_su11_iff.mpr ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply', vec2_dotProduct]
  · simpa [Matrix.diagonal_apply, mul_comm, sub_eq_add_neg] using hdet
  · simp [mul_comm]
  · simp [mul_comm]
  · simpa [Matrix.diagonal_apply, mul_comm, neg_sub, sub_eq_add_neg]
      using congrArg Neg.neg hdet

/-- The matrix of the element with top row `(a, b)`. -/
@[simp]
theorem coe_ofPair (a b : ℂ) (h : ‖a‖ ^ 2 - ‖b‖ ^ 2 = 1) :
    ((ofPair a b h).val : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; star b, star a] := (rfl)

@[simp]
theorem entryA_ofPair (a b : ℂ) (h : ‖a‖ ^ 2 - ‖b‖ ^ 2 = 1) :
    (ofPair a b h).entryA = a := by simp [entryA_def]

@[simp]
theorem entryB_ofPair (a b : ℂ) (h : ‖a‖ ^ 2 - ‖b‖ ^ 2 = 1) :
    (ofPair a b h).entryB = b := by simp [entryB_def]

@[simp] theorem entryA_one : (1 : SU11).entryA = 1 := by simp [entryA_def]

@[simp] theorem entryB_one : (1 : SU11).entryB = 0 := by simp [entryB_def]

/-- The upper-left entry of a product in `SU(1,1)`. -/
theorem entryA_mul (g h : SU11) :
    (g * h).entryA = g.entryA * h.entryA + g.entryB * star h.entryB := by
  rw [entryA_def, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_eq_matrix g, coe_eq_matrix h, Matrix.mul_apply', vec2_dotProduct]
  simp

/-- The upper-right entry of a product in `SU(1,1)`. -/
theorem entryB_mul (g h : SU11) :
    (g * h).entryB = g.entryA * h.entryB + g.entryB * star h.entryA := by
  rw [entryB_def, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_eq_matrix g, coe_eq_matrix h, Matrix.mul_apply', vec2_dotProduct]
  simp

/-- Inversion conjugates the upper-left entry. -/
@[simp]
theorem entryA_inv (g : SU11) : (g⁻¹).entryA = star g.entryA := by
  rw [entryA_def, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, coe_eq_matrix,
    adjugate_fin_two_of]
  simp

/-- Inversion negates the upper-right entry. -/
@[simp]
theorem entryB_inv (g : SU11) : (g⁻¹).entryB = -g.entryB := by
  rw [entryB_def, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, coe_eq_matrix,
    adjugate_fin_two_of]
  simp

/-- The subspace topology on `SU(1,1)` is determined by the two top-row entries. -/
theorem continuous_iff_entryA_entryB {X : Type*} [TopologicalSpace X] {f : X → SU11} :
    Continuous f ↔ Continuous (fun x ↦ (f x).entryA) ∧ Continuous (fun x ↦ (f x).entryB) := by
  have hind : IsInducing (fun g : SU11 ↦ (g.val : Matrix (Fin 2) (Fin 2) ℂ)) :=
    SpecialLinearGroup.isClosedEmbedding_val.isInducing.comp IsInducing.subtypeVal
  rw [hind.continuous_iff]
  refine ⟨fun hf ↦ ⟨?_, ?_⟩, fun ⟨ha, hb⟩ ↦ ?_⟩
  · exact hf.matrix_elem 0 0
  · exact hf.matrix_elem 0 1
  · refine continuous_matrix fun i j ↦ ?_
    simp only [Function.comp_apply, coe_eq_matrix]
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb
    · exact hb.star
    · exact ha.star

end SU11
end TauCeti
