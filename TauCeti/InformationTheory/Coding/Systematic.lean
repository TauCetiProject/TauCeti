/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.InformationSet
public import TauCeti.InformationTheory.Coding.Matrix

/-!
# Systematic matrices from an information set

A chosen information set determines a unique generator matrix whose information columns are
an identity matrix. Its rows encode the unit messages. Splitting the coordinates into the
information set and its complement puts this matrix in the form `[I | A]`; the matrix
`[-Aᵀ | I]`, returned to the original coordinate order, checks the same code.

The constructions use the restriction equivalence `IsInformationSet.equiv` and the existing
systematic block-matrix identity. They retain arbitrary coordinate types and require only the
information set to be finite for the generator theorem. The parity-check theorem assumes
finite length. No information set is chosen canonically.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.2–1.4.
-/

public section

noncomputable section

namespace TauCeti
namespace IsInformationSet

open Matrix

variable {F ι : Type*} [Field F] {C : LinearCode F ι} {s : Set ι}
variable (h : IsInformationSet C s)

open Classical in
/-- The systematic generator associated to an information set: each row encodes one unit
message, and the columns retain their original labels. -/
def generatorMatrix : Matrix s ι F :=
  fun r i ↦ (h.equiv.symm (Pi.single r 1) : ι → F) i

open Classical in
/-- A row of the systematic generator is the encoding of a unit message. -/
@[simp]
theorem generatorMatrix_apply (r : s) (i : ι) :
    h.generatorMatrix r i = (h.equiv.symm (Pi.single r 1) : ι → F) i := (rfl)

open Classical in
/-- Restricting a systematic generator to its information columns gives the identity. -/
@[simp]
theorem generatorMatrix_submatrix :
    h.generatorMatrix.submatrix id (Subtype.val : s → ι) = 1 := by
  ext r i
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

section FiniteInformationSet

variable [Fintype s]

/-- Multiplication by the systematic generator is the inverse of information restriction. -/
@[simp]
theorem vecMul_generatorMatrix (a : s → F) :
    a ᵥ* h.generatorMatrix = (h.equiv.symm a : ι → F) := by
  classical
  have hmatrix : h.generatorMatrix =
      (LinearMap.toMatrix' (C.subtype.comp h.equiv.symm.toLinearMap))ᵀ := by
    ext r i
    simp
  rw [hmatrix, vecMul_transpose, LinearMap.toMatrix'_mulVec]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.subtype_apply]

/-- The systematic generator generates the original code. -/
@[simp]
theorem generatedBy_generatorMatrix : h.generatorMatrix.generatedBy = C := by
  ext x
  rw [mem_generatedBy_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [h.vecMul_generatorMatrix]
    exact (h.equiv.symm a).property
  · intro hx
    refine ⟨h.equiv ⟨x, hx⟩, ?_⟩
    simp

open Classical in
/-- The information coordinates uniquely determine a systematic generator of a code. -/
theorem generatorMatrix_eq_of_generatedBy_eq_of_submatrix_eq_one {G : Matrix s ι F}
    (hG : G.generatedBy = C) (hI : G.submatrix id (Subtype.val : s → ι) = 1) :
    h.generatorMatrix = G := by
  ext r i
  have hr : G.row r ∈ C := hG ▸ G.row_mem_generatedBy r
  have he : h.equiv ⟨G.row r, hr⟩ = Pi.single r 1 := by
    funext j
    simpa [Matrix.submatrix_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using
      congrFun (congrFun hI r) j
  have hx := congrArg (fun x : C ↦ (x : ι → F) i) (h.equiv.symm_apply_eq.mpr he.symm)
  exact hx

end FiniteInformationSet

/-- The rows of the systematic generator are linearly independent. -/
theorem linearIndependent_generatorMatrix : LinearIndependent F h.generatorMatrix.row := by
  classical
  exact .of_comp (LinearMap.funLeft F F (Subtype.val : s → ι)) <| by
    convert Pi.linearIndependent_single_one s F using 1
    ext r i
    simp

/-- Relabelling coordinates relabels the information rows and the columns of the systematic
generator by the corresponding equivalences. -/
theorem generatorMatrix_reindex {κ : Type*} (e : κ ≃ ι) :
    (h.reindex e).generatorMatrix =
      h.generatorMatrix.submatrix (e.subtypeEquiv fun _ ↦ Iff.rfl) e := by
  classical
  let es : (e ⁻¹' s) ≃ s := e.subtypeEquiv fun _ ↦ Iff.rfl
  ext r i
  let x := h.equiv.symm (Pi.single (es r) 1)
  let y : TauCeti.reindex C e := ⟨fun j ↦ (x : ι → F) (e j),
    mem_reindex.mpr ⟨x, x.property, fun _ ↦ rfl⟩⟩
  have hy : (h.reindex e).equiv.symm (Pi.single r 1) = y := by
    apply (h.reindex e).ext
    intro j
    have hx := h.equiv_symm_apply
      (Pi.single (es r) 1)
      (es j)
    rw [equiv_symm_apply]
    calc
      (Pi.single r 1 : (e ⁻¹' s) → F) j =
          (Pi.single (es r) 1 : s → F) (es j) := by
        simp only [Pi.single_apply, es.injective.eq_iff]
      _ = _ := hx.symm
  exact congrArg (fun z : TauCeti.reindex C e ↦ (z : κ → F) i) hy

open Classical in
/-- Splitting off the information coordinates displays the generator as `[I | A]`. -/
theorem generatorMatrix_submatrix_sumCompl :
    h.generatorMatrix.submatrix id (Equiv.Set.sumCompl s) =
      fromCols (1 : Matrix s s F)
        (h.generatorMatrix.submatrix id (Subtype.val : ↥(sᶜ) → ι)) := by
  ext r (i | i)
  · simpa using congrFun (congrFun h.generatorMatrix_submatrix r) i
  · rfl

open Classical in
/-- The systematic parity-check matrix `[-Aᵀ | I]`, in the original coordinate order. -/
def parityCheckMatrix : Matrix ↥(sᶜ) ι F :=
  (fromCols (-(h.generatorMatrix.submatrix id (Subtype.val : ↥(sᶜ) → ι))ᵀ)
    (1 : Matrix ↥(sᶜ) ↥(sᶜ) F)).submatrix id (Equiv.Set.sumCompl s).symm

open Classical in
/-- The systematic check matrix is the usual block check matrix with columns relabelled. -/
theorem parityCheckMatrix_def : h.parityCheckMatrix =
    (fromCols (-(h.generatorMatrix.submatrix id (Subtype.val : ↥(sᶜ) → ι))ᵀ)
      (1 : Matrix ↥(sᶜ) ↥(sᶜ) F)).submatrix id (Equiv.Set.sumCompl s).symm := (rfl)

/-- On the information coordinates, the check matrix is the negative transpose of the
redundancy block. -/
@[simp]
theorem parityCheckMatrix_apply_of_mem (r : ↥(sᶜ)) (i : s) :
    h.parityCheckMatrix r i = -h.generatorMatrix i r := by
  simp [parityCheckMatrix_def]

open Classical in
/-- On the complementary coordinates, the check matrix is the identity. -/
@[simp]
theorem parityCheckMatrix_apply_of_notMem (r i : ↥(sᶜ)) :
    h.parityCheckMatrix r i = (1 : Matrix ↥(sᶜ) ↥(sᶜ) F) r i := by
  simp [parityCheckMatrix_def]

/-- The systematic check matrix has linearly independent rows. -/
theorem linearIndependent_parityCheckMatrix : LinearIndependent F h.parityCheckMatrix.row := by
  classical
  exact .of_comp (LinearMap.funLeft F F (Subtype.val : ↥(sᶜ) → ι)) <| by
    convert Pi.linearIndependent_single_one ↥(sᶜ) F using 1
    ext r i
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]

/-- Relabelling coordinates also relabels the complementary rows and columns of the
systematic check matrix. -/
theorem parityCheckMatrix_reindex {κ : Type*} (e : κ ≃ ι) :
    (h.reindex e).parityCheckMatrix =
      h.parityCheckMatrix.submatrix
        (e.subtypeEquiv (p := (· ∈ (e ⁻¹' s)ᶜ)) (q := (· ∈ sᶜ)) fun _ ↦ Iff.rfl) e := by
  classical
  ext r i
  by_cases hi : e i ∈ s
  · have hi' : i ∈ e ⁻¹' s := hi
    have hn := (h.reindex e).parityCheckMatrix_apply_of_mem r ⟨i, hi'⟩
    have ho := h.parityCheckMatrix_apply_of_mem
      ((e.subtypeEquiv (p := (· ∈ (e ⁻¹' s)ᶜ)) (q := (· ∈ sᶜ)) fun _ ↦ Iff.rfl) r)
      ⟨e i, hi⟩
    rw [h.generatorMatrix_reindex e] at hn
    exact hn.trans ho.symm
  · have hi' : i ∈ (e ⁻¹' s)ᶜ := hi
    have hn := (h.reindex e).parityCheckMatrix_apply_of_notMem r ⟨i, hi'⟩
    have ho := h.parityCheckMatrix_apply_of_notMem
      ((e.subtypeEquiv (p := (· ∈ (e ⁻¹' s)ᶜ)) (q := (· ∈ sᶜ)) fun _ ↦ Iff.rfl) r)
      ⟨e i, hi⟩
    refine hn.trans (Eq.trans ?_ ho.symm)
    simp only [Matrix.one_apply]
    congr 1
    exact propext ((e.subtypeEquiv (p := (· ∈ (e ⁻¹' s)ᶜ))
      (q := (· ∈ sᶜ)) fun _ ↦ Iff.rfl).injective.eq_iff).symm

variable [Fintype ι]

/-- The systematic check matrix cuts out exactly the original code. -/
@[simp↓]
theorem checkedBy_parityCheckMatrix : h.parityCheckMatrix.checkedBy = C := by
  classical
  rw [parityCheckMatrix_def,
    ← Matrix.generatedBy_one_fromCols_eq_checkedBy_fromCols_neg_transpose_one_submatrix,
    ← h.generatorMatrix_submatrix_sumCompl]
  simp [Matrix.submatrix_submatrix]

end IsInformationSet
end TauCeti
