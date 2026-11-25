/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AdelicComponentGroup
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ResidueField

/-!
# Checks for the congruence groups of the `GL₂` components

The first two checks concern the congruence groups `Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹`
(`TauCeti.AdelicExamples.GL2.componentGroup`) at principal levels `K(N)` and `g = 1`, and go
through `TauCeti.AdelicExamples.GL2.mapGL_mem_componentGroup_principalLevel_one_iff`. The last
concerns only the congruence subgroups `Γ₀(3)`, `Γ₁(3)` and `Γ(3)` of `SL₂(ℤ)`.

* At principal level `1` the component of `1` has group `Γ(1) = SL₂(ℤ)`.
* The scalar `-1` lies in the component group at principal level `2`, but not at principal
  level `3`.
* The matrix `[[1, 1], [0, 1]]` lies in `Γ₀(3)` and `Γ₁(3)` but not in `Γ(3)`.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix CongruenceSubgroup
open TauCeti.AdelicExamples.GL2
open scoped MatrixGroups

namespace TauCeti.Examples.AdelicComponentGroup

/-- At principal level `1`, the component of `1` has group `Γ(1) = SL₂(ℤ)`. -/
theorem componentGroup_principalLevel_one :
    componentGroup (principalLevel ℚ (Ideal.span {((1 : ℕ) : ℤ)})) 1 =
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ).range := by
  ext γ
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- Elements of `Γ_{1,K(1)}` have determinant `1` and integral entries.
    refine mem_range_mapGL_of_det_eq_one (det_eq_one_of_mem_componentGroup
      (isCompact_principalLevel ℚ (by simp)) h) ?_
    simpa [principalLevel_top] using (mem_componentGroup_iff.mp h).2
  · rintro ⟨γ, rfl⟩
    exact mapGL_mem_componentGroup_principalLevel_one_iff.mpr (by simp [Gamma_one_top])

/-- The scalar `-1` lies in the component group of `1` at principal level `2`. -/
theorem neg_one_mem_componentGroup_principalLevel_two :
    -1 ∈ componentGroup (principalLevel ℚ (Ideal.span {((2 : ℕ) : ℤ)})) 1 := by
  have h : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
    rw [mem_Gamma_iff_dvd]
    decide
  simpa using mapGL_mem_componentGroup_principalLevel_one_iff.mpr h

/-- The scalar `-1` does not lie in the component group of `1` at principal level `3`. -/
theorem neg_one_notMem_componentGroup_principalLevel_three :
    -1 ∉ componentGroup (principalLevel ℚ (Ideal.span {((3 : ℕ) : ℤ)})) 1 := by
  have h : (-1 : SL(2, ℤ)) ∉ Gamma 3 := by
    rw [mem_Gamma_iff_dvd]
    decide
  simpa using mapGL_mem_componentGroup_principalLevel_one_iff.not.mpr h

/-- The matrix `[[1, 1], [0, 1]]` lies in `Γ₀(3)` and `Γ₁(3)` but not in `Γ(3)`. -/
theorem T_mem_Gamma0_three_and_Gamma1_three_and_notMem_Gamma_three :
    ModularGroup.T ∈ Gamma0 3 ∧ ModularGroup.T ∈ Gamma1 3 ∧ ModularGroup.T ∉ Gamma 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_Gamma0_iff_dvd]
    decide
  · rw [mem_Gamma1_iff_dvd_lowerRow]
    decide
  · rw [mem_Gamma_iff_dvd]
    decide

end TauCeti.Examples.AdelicComponentGroup
