/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation

/-!
# Uniformizers of a nonarchimedean local field

This file records the uniformizer predicate used by the local quadratic-form invariants.  It is
formulated on `Kˣ`, where the normalized valuation is defined.  The characterization below
connects it with the irreducible elements of the ring of integers, the convention used by the
local-fields infrastructure.
-/

public section
noncomputable section

open scoped WithZero
open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (K) in
/-- A uniformizer is a unit whose normalized valuation is one. -/
def IsUniformizer (π : Kˣ) : Prop :=
  normalizedValuation K π = Multiplicative.ofAdd 1

variable (K) in
/-- A uniformizer has the same order of vanishing as an irreducible element of the ring of
integers. -/
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
    -- The associated element is defined in the integer ring, so expose its field coercion.
    change ((↑(u⁻¹) : 𝒪[K]) : K) * (ϖ : K) = (π : K)
    rw [← hu]
    -- Expose the scalar action of the integer-ring unit before cancelling it in `K`.
    change ((↑(u⁻¹) : 𝒪[K]) : K) * ((u : K) • (π : K)) = (π : K)
    rw [smul_eq_mul]
    have huO : (↑(u⁻¹) : 𝒪[K]) * (u : 𝒪[K]) = 1 := by simp
    calc
      ((↑(u⁻¹) : 𝒪[K]) : K) * ((u : K) * (π : K)) =
          (((↑(u⁻¹) : 𝒪[K]) * (u : 𝒪[K]) : 𝒪[K]) : K) * (π : K) := by
            rw [← mul_assoc]
            rfl
      _ = (π : K) := by rw [huO]; simp
  · rintro ⟨ϖ, hϖ, hϖπ⟩
    have hπϖ : π = Units.mk0 (ϖ : K) (fun h => hϖ.ne_zero (Subtype.ext h)) := by
      apply Units.ext
      exact hϖπ.symm
    -- Unfold the predicate only after transporting the chosen representative to `π`.
    change normalizedValuation K π = Multiplicative.ofAdd 1
    rw [hπϖ, normalizedValuation_irreducible hϖ]

/-- Uniformizers exist in every nonarchimedean local field. -/
theorem exists_isUniformizer : ∃ π : Kˣ, IsUniformizer (K := K) π := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪[K])
  refine ⟨Units.mk0 (ϖ : K) (fun h => hϖ.ne_zero (Subtype.ext h)), ?_⟩
  exact normalizedValuation_irreducible hϖ

end TauCeti
