/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import TauCeti.Probability.RandomMatrices.Wigner

import TauCeti.MeasureTheory.MeasurableSpace.Pi

/-!
# Independence of Wigner minors and removed rows

For a Wigner matrix built from a mutually independent family of upper-triangular and diagonal
entries, the principal minor obtained by deleting the last row and column is independent of the
off-diagonal entries in that row and column.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

private noncomputable def wignerMinorCornerIndices (n : ℕ) :
    Finset (StrictUpper ⊕ ℕ) :=
  ((Finset.range n ×ˢ Finset.range n).subtype fun ij ↦ ij.1 < ij.2).disjSum (Finset.range n)

private noncomputable def wignerRemovedColumnIndices (n : ℕ) :
    Finset (StrictUpper ⊕ ℕ) :=
  ((Finset.range n ×ˢ {n}).subtype fun ij ↦ ij.1 < ij.2).disjSum ∅

private theorem inl_mem_wignerMinorCornerIndices {n : ℕ} {ij : StrictUpper}
    (h : ij.1.2 < n) :
    Sum.inl ij ∈ wignerMinorCornerIndices n := by
  simp [wignerMinorCornerIndices, h, ij.2.trans h]

private theorem inr_mem_wignerMinorCornerIndices {n i : ℕ} (h : i < n) :
    Sum.inr i ∈ wignerMinorCornerIndices n := by
  simp [wignerMinorCornerIndices, h]

private theorem disjoint_wignerMinorCornerIndices_removedColumn (n : ℕ) :
    Disjoint (wignerMinorCornerIndices n) (wignerRemovedColumnIndices n) := by
  rw [Finset.disjoint_left]
  rintro (ij | i) h₁ h₂
  · simp only [wignerMinorCornerIndices, wignerRemovedColumnIndices,
      Finset.inl_mem_disjSum, Finset.mem_subtype, Finset.mem_product,
      Finset.mem_range, Finset.mem_singleton] at h₁ h₂
    omega
  · simp [wignerRemovedColumnIndices] at h₂

private noncomputable def wignerMatrixOfArray (n : ℕ) (g : StrictUpper ⊕ ℕ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  wignerMatrix (fun ij g ↦ g (.inl ij)) (fun i g ↦ (g (.inr i)).re) n g

private theorem measurable_wignerMatrixOfArray (n : ℕ) :
    Measurable (wignerMatrixOfArray n) := by
  refine Measurable.of_eval_matrix _ fun i j ↦ ?_
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrixOfArray, wignerMatrix_apply]
    fun_prop
  · obtain rfl := Fin.ext h
    simp only [wignerMatrixOfArray, wignerMatrix_apply, lt_self_iff_false]
    fun_prop
  · have hEq :
        (fun g : StrictUpper ⊕ ℕ → ℂ ↦ wignerMatrixOfArray n g i j) =
          fun g ↦ ((Real.sqrt n)⁻¹ : ℂ) *
            star (g (Sum.inl (⟨(j.val, i.val), h⟩ : StrictUpper))) := by
      funext g
      simp [wignerMatrixOfArray, wignerMatrix_apply, h, h.not_gt]
    rw [hEq]
    exact measurable_const.mul (continuous_star.measurable.comp
      (measurable_pi_apply (Sum.inl (⟨(j.val, i.val), h⟩ : StrictUpper))))

/-- For independent Wigner entries, the principal minor obtained by deleting the last row and
column of a matrix of size `n + 1` is independent of the off-diagonal entries in the removed row
and column. -/
theorem indepFun_wignerMatrix_minor {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}
    (hξ : ∀ ij, AEMeasurable (ξ ij) μ) (hη : ∀ i, AEMeasurable (η i) μ)
    (hindep : iIndepFun
      (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) μ) (n : ℕ) :
    IndepFun
      (fun ω ↦ (wignerMatrix ξ η (n + 1) ω).submatrix Fin.castSucc Fin.castSucc)
      (fun ω (i : Fin n) ↦ ξ ⟨(i.val, n), i.isLt⟩ ω) μ := by
  let C := wignerMinorCornerIndices n
  let R := wignerRemovedColumnIndices n
  have hrow (i : Fin n) :
      (Sum.inl ⟨(i.val, n), i.isLt⟩ : StrictUpper ⊕ ℕ) ∈ R := by
    simp [R, wignerRemovedColumnIndices]
  have hZ (k : StrictUpper ⊕ ℕ) :
      AEMeasurable (Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) μ := by
    cases k with
    | inl ij => exact hξ ij
    | inr i => exact Complex.measurable_ofReal.comp_aemeasurable (hη i)
  have hminor : Measurable fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ↦
      A.submatrix Fin.castSucc Fin.castSucc := by
    refine Measurable.of_eval_matrix _ fun i j ↦ ?_
    exact Matrix.measurable_apply
  have hφ : Measurable
      ((fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ↦
          A.submatrix Fin.castSucc Fin.castSucc) ∘
        (wignerMatrixOfArray (n + 1) ∘
          fun g : C → ℂ ↦ Function.extend Subtype.val g (fun _ ↦ (0 : ℂ)))) :=
    hminor.comp ((measurable_wignerMatrixOfArray (n + 1)).comp
      (MeasureTheory.measurable_extend _ _))
  have hψ : Measurable fun (g : R → ℂ) (i : Fin n) ↦
      g ⟨Sum.inl ⟨(i.val, n), i.isLt⟩, hrow i⟩ :=
    measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  refine ((hindep.indepFun_finset₀ C R (disjoint_wignerMinorCornerIndices_removedColumn n)
    hZ).comp hφ hψ).congr (.of_forall fun ω ↦ ?_) (.of_forall fun ω ↦ rfl)
  ext i j
  simp only [Function.comp_apply, Matrix.submatrix_apply, wignerMatrixOfArray,
    wignerMatrix_apply, Fin.val_castSucc]
  by_cases hij : i.val < j.val
  · simp only [dite_eq_left hij]
    rw [Function.extend_val_apply (inl_mem_wignerMinorCornerIndices (j.isLt))]
    simp
  · by_cases hji : j.val < i.val
    · simp only [dite_eq_right hij, dite_eq_left hji]
      rw [Function.extend_val_apply (inl_mem_wignerMinorCornerIndices (i.isLt))]
      simp
    · have hEq : i = j := Fin.ext (Nat.le_antisymm (Nat.le_of_not_gt hji)
        (Nat.le_of_not_gt hij))
      subst j
      simp only [lt_self_iff_false]
      rw [Function.extend_val_apply (inr_mem_wignerMinorCornerIndices i.isLt)]
      simp

end Probability

end TauCeti
