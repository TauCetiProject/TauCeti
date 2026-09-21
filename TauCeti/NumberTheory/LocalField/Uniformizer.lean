/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation

/-!
# Uniformizers of a nonarchimedean local field

This file records the uniformizer predicate for a nonarchimedean local field.  It is formulated
on `Kˣ`, where the normalized valuation is defined.  The characterization below connects it with
the irreducible elements of the ring of integers, the convention used by the local-fields
infrastructure.
-/

public section
noncomputable section

open scoped WithZero
open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (K) in
/-- A uniformizer is a nonzero field element whose normalized valuation is one. -/
def IsUniformizer (π : Kˣ) : Prop :=
  normalizedValuation K π = Multiplicative.ofAdd 1

@[simp]
theorem isUniformizer_def (π : Kˣ) :
    IsUniformizer (K := K) π ↔ normalizedValuation K π = Multiplicative.ofAdd 1 := by
  rfl

variable (K) in
/-- A field unit is a uniformizer iff its underlying element is the image of an irreducible
element of the ring of integers. -/
theorem isUniformizer_iff_exists_irreducible (π : Kˣ) :
    IsUniformizer (K := K) π ↔ ∃ ϖ : 𝒪[K], Irreducible ϖ ∧ (ϖ : K) = (π : K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪[K])
  have hϖval : Ring.ordFrac 𝒪[K] (ϖ : K) = WithZero.exp 1 := by
    exact Ring.ordFrac_irreducible hϖ
  constructor
  · intro hπ
    have hπval : Ring.ordFrac 𝒪[K] (π : K) = WithZero.exp 1 := by
      rw [← normalizedValuationWithZero_eq_ordFrac, normalizedValuationWithZero_coe, hπ]
      rfl
    obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := 𝒪[K]) (π : K) (ϖ : K)
      (hπval.trans hϖval.symm)
    let ϖ' : 𝒪[K] := (↑(u⁻¹) : 𝒪[K]) * ϖ
    have hϖ' : Irreducible ϖ' := by
      have huassoc : Associated ϖ ϖ' := ⟨u⁻¹, by simp [ϖ', mul_comm]⟩
      exact huassoc.irreducible hϖ
    refine ⟨ϖ', hϖ', ?_⟩
    have hu_cancel :
        ((↑(u⁻¹) : 𝒪[K]) : K) * ((u : K) * (π : K)) = (π : K) := by
      rw [← mul_assoc]
      have hu_inv :
        ((↑(u⁻¹) : 𝒪[K]) : K) * ((u : 𝒪[K]) : K) = 1 := by
        have hu_inv' := congrArg (fun x : 𝒪[K] => (x : K)) (Units.inv_mul u)
        simpa only [Subring.coe_mul, Subring.coe_one] using hu_inv'
      rw [hu_inv, one_mul]
    dsimp only [ϖ']
    rw [Subring.coe_mul, ← hu, Units.smul_def]
    have hu_coe : algebraMap 𝒪[K] K (u : 𝒪[K]) = (u : K) := by rfl
    simpa only [Algebra.smul_def, hu_coe] using hu_cancel
  · rintro ⟨ϖ, hϖ, hϖπ⟩
    have hπϖ : π = Units.mk0 (ϖ : K) (fun h => hϖ.ne_zero (Subtype.ext h)) := by
      apply Units.ext
      exact hϖπ.symm
    rw [isUniformizer_def, hπϖ, normalizedValuation_irreducible hϖ]

variable (K) in
/-- Uniformizers exist in every nonarchimedean local field. -/
theorem exists_isUniformizer : ∃ π : Kˣ, IsUniformizer (K := K) π := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪[K])
  refine ⟨Units.mk0 (ϖ : K) (fun h => hϖ.ne_zero (Subtype.ext h)), ?_⟩
  exact (isUniformizer_iff_exists_irreducible K _).2 ⟨ϖ, hϖ, rfl⟩

end TauCeti
