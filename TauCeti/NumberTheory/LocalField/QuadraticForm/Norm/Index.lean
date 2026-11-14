/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClasses
public import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass

/-!
# The norm index of an unramified quadratic class

For the unramified quadratic square class of a nonarchimedean local field, the norm subgroup
consists exactly of elements of even normalized valuation. Every integer-ring unit is therefore a
norm, so `TauCeti.unitQuadraticNormSquareClasses` equals `TauCeti.unitSquareClasses K`, while a
uniformizer changes valuation parity and gives index two in `Kˣ`. This is the unramified case of
the quadratic norm-index calculation used to make the local Hilbert symbol multiplicative.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Membership in the norm subgroup of an unramified quadratic class is equivalent to even
normalized valuation. This packages the norm-equation criterion as a subgroup membership test. -/
theorem mem_quadraticNormSubgroup_iff_even_of_unramified_class {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) (b : Kˣ) :
    b ∈ quadraticNormSubgroup (Δ : K) ↔ Even (normalizedValuation K b).toAdd := by
  rw [← hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup Δ b,
    hilbertSymbol_eq_one_iff]
  exact hΔ b

/-- For an unramified quadratic class, every unit square class is represented by a valuation-one
norm. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_unramified_class {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) :
    unitQuadraticNormSquareClasses (Δ : K) = unitSquareClasses K := by
  refine le_antisymm (unitQuadraticNormSquareClasses_le_unitSquareClasses _) fun q hq ↦ ?_
  obtain ⟨u, rfl⟩ := (mem_unitSquareClasses_iff K q).mp hq
  let b : Kˣ := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u
  have hbv : valuation K (b : K) = 1 :=
    (Valuation.integer.integers (valuation K)).valuation_unit u
  have hbeven : Even (normalizedValuation K b).toAdd := by
    rw [(normalizedValuation_eq_one_iff b).mpr hbv, toAdd_one]
    exact Even.zero
  exact (mem_unitQuadraticNormSquareClasses_iff (Δ : K) _).mpr
    ⟨b, (mem_quadraticNormSubgroup_iff_even_of_unramified_class hΔ b).mpr hbeven, hbv,
      squareClassHom_apply b⟩

/-- The norm subgroup of an unramified quadratic class has index two. -/
theorem quadraticNormSubgroup_index_eq_two_of_unramified_class {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) :
    (quadraticNormSubgroup (Δ : K)).index = 2 := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  have hmem (b : Kˣ) : b ∈ quadraticNormSubgroup (Δ : K) ↔
      Even (normalizedValuation K b).toAdd :=
    mem_quadraticNormSubgroup_iff_even_of_unramified_class hΔ b
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨π, ?_, fun b ↦ ?_⟩
  · rw [hmem, (isUniformizer_def π).mp hπ, toAdd_ofAdd]
    exact Int.not_even_one
  · rw [hmem, hmem, map_mul, toAdd_mul, (isUniformizer_def π).mp hπ, toAdd_ofAdd]
    by_cases hb : Even (normalizedValuation K b).toAdd
    · exact Or.inr hb
    · exact Or.inl (Int.even_add_one.mpr hb)

/-- There is a nonsquare local radicand whose quadratic norm subgroup has index two. -/
theorem exists_quadraticNormSubgroup_index_eq_two (h2 : (2 : K) ≠ 0) :
    ∃ Δ : Kˣ, ¬IsSquare Δ ∧ (quadraticNormSubgroup (Δ : K)).index = 2 := by
  obtain ⟨Δ, hnsq, -, -, hΔ⟩ := exists_unramified_class h2
  exact ⟨Δ, hnsq, quadraticNormSubgroup_index_eq_two_of_unramified_class hΔ⟩

end TauCeti
