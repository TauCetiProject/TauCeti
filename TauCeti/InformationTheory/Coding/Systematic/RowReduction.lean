/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.InformationTheory.Coding.Systematic.Basic
public import TauCeti.InformationTheory.Coding.RowOperations

/-!
# Systematic row reduction of a given generator

Given a generator matrix with as many rows as retained information coordinates, those
coordinates form an information set exactly when the corresponding square block is invertible.
Multiplying the generator by the inverse of this block gives the unique systematic generator.
Its complementary block supplies an explicit parity-check matrix in the original coordinate
order. Thus a supplied generator can be converted to a check matrix using only a chosen
information set and a matrix inverse.

Row labels need not be coordinate labels: an equivalence identifies the row type with the
information set before taking the inverse. The information-set criterion and generator
normalization need only finitely many rows, whereas the check matrix requires finite length.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*,
Sections 1.2–1.4 (systematic generators and parity checks).
-/

public section

noncomputable section

namespace TauCeti

open Matrix

variable {F ι ρ : Type*} [Field F] {s : Set ι} [Fintype s] [DecidableEq s]

open Classical in
/-- For a generator with rows indexed by the retained set, that set is an information set
exactly when its square information block is invertible. -/
@[simp]
theorem _root_.Matrix.isInformationSet_generatedBy_iff_isUnit (G : Matrix s ι F) :
    IsInformationSet G.generatedBy s ↔ IsUnit (G.submatrix id (Subtype.val : s → ι)) := by
  rw [isInformationSet_def]
  have hrestrict (a : s → F) :
      a ᵥ* G.submatrix id (Subtype.val : s → ι) = fun i : s ↦ (a ᵥ* G) i := by
    simpa only [Equiv.refl_apply, Equiv.coe_refl, Equiv.refl_symm, Function.comp_id,
      Function.comp_def, id_eq] using
      submatrix_vecMul_equiv G a (Equiv.refl s) (Subtype.val : s → ι)
  constructor
  · intro h
    apply vecMul_surjective_iff_isUnit.mp
    intro y
    obtain ⟨x, hx⟩ := h.2 y
    obtain ⟨a, ha⟩ := mem_generatedBy_iff.mp x.property
    exact ⟨a, (hrestrict a).trans
      ((congrArg (fun z : ι → F ↦ fun i : s ↦ z i) ha).trans hx)⟩
  · intro h
    constructor
    · intro x y hxy
      obtain ⟨a, ha⟩ := mem_generatedBy_iff.mp x.property
      obtain ⟨b, hb⟩ := mem_generatedBy_iff.mp y.property
      have hab : a = b := vecMul_injective_of_isUnit h (by
        simpa [hrestrict, ha, hb] using hxy)
      exact Subtype.ext (ha.symm.trans (hab ▸ hb))
    · intro y
      obtain ⟨a, ha⟩ := vecMul_surjective_iff_isUnit.mpr h y
      exact ⟨⟨a ᵥ* G, mem_generatedBy_iff.mpr ⟨a, rfl⟩⟩,
        (hrestrict a).symm.trans ha⟩

namespace IsInformationSet

variable {C : LinearCode F ι} (h : IsInformationSet C s)

include h

open Classical in
/-- The information block of a generator indexed by the information set is invertible. -/
theorem isUnit_submatrix {G : Matrix s ι F} (hG : C.IsGeneratorMatrix G) :
    IsUnit (G.submatrix id (Subtype.val : s → ι)) := by
  apply (isInformationSet_generatedBy_iff_isUnit G).mp
  simpa only [(LinearCode.isGeneratorMatrix_def C G).mp hG] using h

open Classical in
/-- Multiplying a given generator by the inverse of its information block gives the
systematic generator, with the original coordinate labels. -/
theorem generatorMatrix_eq_inv_mul {G : Matrix s ι F} (hG : C.IsGeneratorMatrix G) :
    h.generatorMatrix = (G.submatrix id (Subtype.val : s → ι))⁻¹ * G := by
  have hunit := h.isUnit_submatrix hG
  have hgen : ((G.submatrix id (Subtype.val : s → ι))⁻¹ * G).generatedBy = C :=
    (generatedBy_mul_eq_of_isUnit _ G (isUnit_nonsing_inv_iff.mpr hunit)).trans
      ((LinearCode.isGeneratorMatrix_def C G).mp hG)
  apply h.generatorMatrix_eq_of_row_mem_of_submatrix_eq_one
  · intro r
    rw [← hgen]
    exact row_mem_generatedBy _ r
  · rw [submatrix_mul _ _ id id (Subtype.val : s → ι) Function.bijective_id,
      submatrix_id_id]
    exact nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hunit)

variable [Fintype ρ]

open Classical in
/-- Arbitrary generator row labels can be identified with the information set before
inverting the information block. -/
theorem isUnit_submatrix_rows {G : Matrix ρ ι F} (hG : C.IsGeneratorMatrix G)
    (e : s ≃ ρ) : IsUnit (G.submatrix e (Subtype.val : s → ι)) := by
  have hgen : C.IsGeneratorMatrix (G.submatrix e id) := by
    rw [LinearCode.isGeneratorMatrix_def,
      generatedBy_submatrix_rows_eq_of_surjective G e e.surjective]
    exact (LinearCode.isGeneratorMatrix_def C G).mp hG
  simpa only [submatrix_submatrix, Function.comp_id, Function.id_comp] using
    h.isUnit_submatrix hgen

open Classical in
/-- Systematic row reduction of a generator with arbitrary row labels. -/
theorem generatorMatrix_eq_inv_mul_submatrix {G : Matrix ρ ι F}
    (hG : C.IsGeneratorMatrix G) (e : s ≃ ρ) :
    h.generatorMatrix = (G.submatrix e (Subtype.val : s → ι))⁻¹ * G.submatrix e id := by
  have hgen : C.IsGeneratorMatrix (G.submatrix e id) := by
    rw [LinearCode.isGeneratorMatrix_def,
      generatedBy_submatrix_rows_eq_of_surjective G e e.surjective]
    exact (LinearCode.isGeneratorMatrix_def C G).mp hG
  simpa only [submatrix_submatrix, Function.comp_id, Function.id_comp] using
    h.generatorMatrix_eq_inv_mul hgen

variable [DecidableEq ↥sᶜ] [DecidablePred (· ∈ s)]

open Classical in
/-- The check matrix calculated from a given generator has redundancy block `-Aᵀ`, where
`A` is the complementary block after systematic row reduction. -/
theorem parityCheckMatrix_eq_fromCols_inv_mul {G : Matrix ρ ι F}
    (hG : C.IsGeneratorMatrix G) (e : s ≃ ρ) :
    h.parityCheckMatrix =
      (fromCols
        (-((G.submatrix e (Subtype.val : s → ι))⁻¹ *
          G.submatrix e (Subtype.val : ↥sᶜ → ι))ᵀ)
        (1 : Matrix ↥sᶜ ↥sᶜ F)).submatrix id (Equiv.Set.sumCompl s).symm := by
  rw [h.parityCheckMatrix_def, h.generatorMatrix_eq_inv_mul_submatrix hG e,
    submatrix_mul _ _ id id (Subtype.val : ↥sᶜ → ι) Function.bijective_id]
  simp only [submatrix_id_id, submatrix_submatrix, Function.comp_id, Function.id_comp]

variable [Fintype ι]

open Classical in
/-- The explicit check matrix obtained by inverting the information block recovers the
original code as its kernel. -/
theorem checkedBy_fromCols_inv_mul {G : Matrix ρ ι F}
    (hG : C.IsGeneratorMatrix G) (e : s ≃ ρ) :
    ((fromCols
      (-((G.submatrix e (Subtype.val : s → ι))⁻¹ *
        G.submatrix e (Subtype.val : ↥sᶜ → ι))ᵀ)
      (1 : Matrix ↥sᶜ ↥sᶜ F)).submatrix id (Equiv.Set.sumCompl s).symm).checkedBy = C := by
  rw [← h.parityCheckMatrix_eq_fromCols_inv_mul hG e, h.checkedBy_parityCheckMatrix]

end IsInformationSet

end TauCeti
