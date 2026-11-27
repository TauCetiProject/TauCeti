/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel
import Mathlib.RingTheory.IntegralDomain

/-!
# Checks for the congruence levels of `GL₂` over the finite adeles

Let `R` be a Dedekind domain with fraction field `K`, `Ô` its integral finite adeles and `N` an
ideal of `R`. This file checks properties of the levels `K(N) ≤ K₁(N) ≤ K₀(N)` of `GL₂(𝔸_f)`
(`IsDedekindDomain.FiniteAdeleRing.principalLevel`, `IsDedekindDomain.FiniteAdeleRing.level1`,
`IsDedekindDomain.FiniteAdeleRing.level0`).

* For a proper nonzero `N`, the unipotent matrix `[[1, 1], [0, 1]]` lies in `K₁(N)` but not in
  `K(N)`: its entry `b = 1` is not in `NÔ`.
* At the zero ideal the principal level is trivial, `K(0) = {1}`
  (`IsDedekindDomain.FiniteAdeleRing.principalLevel_bot`). When `R` is not a field and has finite
  residue fields, `K(0)` is not open: an open `{1}` would make `GL₂(𝔸_f)` discrete, so its compact
  subgroup `GL₂(Ô)` would be finite, while it contains the infinitely many matrices
  `[[1, r], [0, 1]]`, `r ∈ R`.
* Over `ℚ`, the level `N = (n)`, `n ≠ 0`, gives the natural-number levels of `SL₂(ℤ)`: an element
  of `SL₂(ℤ)` has its image in `K(N)`, `K₁(N)` or `K₀(N)` exactly when it lies in `Γ(n)`, `Γ₁(n)`
  or `Γ₀(n)` (`mem_principalLevel_iff_mem_Gamma`, `mem_level1_iff_mem_Gamma1`,
  `mem_level0_iff_mem_Gamma0`).
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix.GeneralLinearGroup

namespace TauCeti.Examples.CongruenceLevel

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The unipotent matrix `[[1, 1], [0, 1]]` lies in `K₁(N)` for every ideal `N`. -/
theorem upperRightHom_one_mem_level1 (N : Ideal R) :
    upperRightHom (1 : 𝔸ᶠ[R, K]) ∈ level1 K N :=
  upperRightHom_mem_level1 (one_mem _) N

/-- For a proper nonzero ideal `N`, the unipotent matrix `[[1, 1], [0, 1]]` does not lie in
`K(N)`: its entry `b = 1` is not in `NÔ`. -/
theorem upperRightHom_one_notMem_principalLevel {N : Ideal R} (hN₀ : N ≠ ⊥) (hN : N ≠ ⊤) :
    upperRightHom (1 : 𝔸ᶠ[R, K]) ∉ principalLevel K N := by
  rw [← map_one (algebraMap R 𝔸ᶠ[R, K]), upperRightHom_algebraMap_mem_principalLevel_iff hN₀]
  exact (Ideal.ne_top_iff_one N).mp hN

/-- When `R` is not a field and has finite residue fields, the principal level `K(0) = {1}` is not
open in `GL₂(𝔸_f)`. -/
theorem not_isOpen_principalLevel_bot [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
    (hR : ¬ IsField R) :
    ¬ IsOpen (principalLevel K (⊥ : Ideal R) : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  intro h
  rw [principalLevel_bot, Subgroup.coe_bot] at h
  have := discreteTopology_of_isOpen_singleton_one h
  -- `GL₂(Ô)` is compact, hence finite, and contains `[[1, r], [0, 1]]` for every `r ∈ R`.
  have hfin : ((integralGL K (Fin 2) (R := R)).range : Set (GL (Fin 2) 𝔸ᶠ[R, K])).Finite := by
    rw [← level0_top]
    exact (isCompact_level0 K top_ne_bot).finite_of_discrete
  have hmem (r : R) : upperRightHom (algebraMap R 𝔸ᶠ[R, K] r) ∈ (integralGL K (Fin 2)).range :=
    level1_top (R := R) K ▸ upperRightHom_mem_level1 ((integralAdeles R K).algebraMap_mem r) ⊤
  have := hfin.to_subtype
  have : Finite R := Finite.of_injective
    (fun r ↦ (⟨_, hmem r⟩ : ((integralGL K (Fin 2) (R := R)).range : Set (GL (Fin 2) 𝔸ᶠ[R, K]))))
    fun r s h ↦ IsFractionRing.injective R K <| algebraMap_injective K hR <| by
      simpa [← IsScalarTower.algebraMap_apply] using
        injective_upperRightHom (congrArg Subtype.val h)
  exact hR (Finite.isField_of_domain R)

/-! ### Over `ℚ`: the natural-number levels -/

section Rat

open CongruenceSubgroup
open scoped MatrixGroups

variable {n : ℕ} [NeZero n]

private theorem span_ne_bot : Ideal.span {(n : ℤ)} ≠ ⊥ := by
  simp [NeZero.ne n]

/-- **`K(n) ∩ SL₂(ℤ) = Γ(n)`**: an element of `SL₂(ℤ)` has its image in the principal level of
`(n) ⊆ ℤ` exactly when it lies in the principal congruence subgroup `Γ(n)`. -/
theorem mem_principalLevel_iff_mem_Gamma (γ : SL(2, ℤ)) :
    map (algebraMap ℤ 𝔸ᶠ[ℤ, ℚ]) γ.toGL ∈ principalLevel ℚ (Ideal.span {(n : ℤ)}) ↔
      γ ∈ Gamma n := by
  rw [map_algebraMap_mem_principalLevel_iff (K := ℚ) span_ne_bot, mem_Gamma_iff_dvd]
  simp [Fin.forall_fin_two, Ideal.mem_span_singleton, and_assoc]

/-- **`K₁(n) ∩ SL₂(ℤ) = Γ₁(n)`**: an element of `SL₂(ℤ)` has its image in the level `K₁` of
`(n) ⊆ ℤ` exactly when it lies in `Γ₁(n)`. -/
theorem mem_level1_iff_mem_Gamma1 (γ : SL(2, ℤ)) :
    map (algebraMap ℤ 𝔸ᶠ[ℤ, ℚ]) γ.toGL ∈ level1 ℚ (Ideal.span {(n : ℤ)}) ↔ γ ∈ Gamma1 n := by
  rw [map_algebraMap_mem_level1_iff (K := ℚ) span_ne_bot, mem_Gamma1_iff_dvd_lowerRow]
  simp [Ideal.mem_span_singleton]

/-- **`K₀(n) ∩ SL₂(ℤ) = Γ₀(n)`**: an element of `SL₂(ℤ)` has its image in the level `K₀` of
`(n) ⊆ ℤ` exactly when it lies in `Γ₀(n)`. -/
theorem mem_level0_iff_mem_Gamma0 (γ : SL(2, ℤ)) :
    map (algebraMap ℤ 𝔸ᶠ[ℤ, ℚ]) γ.toGL ∈ level0 ℚ (Ideal.span {(n : ℤ)}) ↔ γ ∈ Gamma0 n := by
  rw [map_algebraMap_mem_level0_iff (K := ℚ) span_ne_bot, mem_Gamma0_iff_dvd]
  simp [Ideal.mem_span_singleton]

end Rat

end TauCeti.Examples.CongruenceLevel
