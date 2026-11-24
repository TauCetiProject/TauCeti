/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel
import Mathlib.RingTheory.IntegralDomain

/-!
# Checks for the congruence levels of `GL₂` over the finite adeles

Let `R` be a Dedekind domain with fraction field `K`, `Ô` its integral finite adeles and `N` an
ideal of `R`. This file checks two properties of the levels `K(N) ≤ K₁(N)` of `GL₂(𝔸_f)`
(`IsDedekindDomain.FiniteAdeleRing.principalLevel`, `IsDedekindDomain.FiniteAdeleRing.level1`).

* For a proper nonzero `N`, the unipotent matrix `[[1, 1], [0, 1]]` lies in `K₁(N)` but not in
  `K(N)`: its entry `b = 1` is not in `NÔ`.
* At the zero ideal the entry conditions still make sense, and the principal level is trivial,
  `K(0) = {1}`. When `R` is not a field and has finite residue fields, `K(0)` is not open: an
  open `{1}` would make `GL₂(𝔸_f)` discrete, so its compact subgroup `GL₂(Ô)` would be finite,
  while it contains the infinitely many matrices `[[1, r], [0, 1]]`, `r ∈ R`.
-/

public section

open Matrix.GeneralLinearGroup

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The unipotent matrix `[[1, 1], [0, 1]]` lies in `K₁(N)` for every ideal `N`. -/
theorem upperRightHom_one_mem_level1 (N : Ideal R) :
    upperRightHom (1 : 𝔸ᶠ[R, K]) ∈ level1 K N := by
  have hint : ∀ i j, (upperRightHom (1 : 𝔸ᶠ[R, K]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈
      integralAdeles R K := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  refine mem_level1_iff.mpr ⟨hint, fun i j ↦ ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  · convert zero_mem (completedIdeal K N)
    exact Subtype.ext (by simp)
  · convert zero_mem (completedIdeal K N)
    exact Subtype.ext (by simp)

/-- For a proper nonzero ideal `N`, the unipotent matrix `[[1, 1], [0, 1]]` does not lie in
`K(N)`: its entry `b = 1` is not in `NÔ`. -/
theorem upperRightHom_one_notMem_principalLevel {N : Ideal R} (hN₀ : N ≠ ⊥) (hN : N ≠ ⊤) :
    upperRightHom (1 : 𝔸ᶠ[R, K]) ∉ principalLevel K N := by
  intro h
  obtain ⟨hg, -, h⟩ := mem_principalLevel_iff.mp h
  have h01 := h 0 1
  have : (1 : integralAdeles R K) = algebraMap R (integralAdeles R K) 1 := (map_one _).symm
  rw [show (⟨_, hg 0 1⟩ - (1 : Matrix (Fin 2) (Fin 2) (integralAdeles R K)) 0 1 :
      integralAdeles R K) = 1 from Subtype.ext (by simp), this,
    algebraMap_mem_completedIdeal_iff hN₀] at h01
  exact hN ((Ideal.eq_top_iff_one N).mpr h01)

/-- At the zero ideal the principal level is trivial: `K(0) = {1}`. -/
theorem principalLevel_bot : principalLevel K (⊥ : Ideal R) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_
  obtain ⟨hg, -, h⟩ := mem_principalLevel_iff.mp hg
  simp only [completedIdeal_bot, Ideal.mem_bot, sub_eq_zero] at h
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  have := congr(Subtype.val $(h i j))
  fin_cases i <;> fin_cases j <;> simpa [Matrix.one_apply] using this

/-- If `R` is not a field, the diagonal map `R → 𝔸_f` is injective. -/
private theorem algebraMap_finiteAdeleRing_injective (hR : ¬ IsField R) :
    Function.Injective (algebraMap R 𝔸ᶠ[R, K]) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  let v : HeightOneSpectrum R :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM hR⟩
  rw [IsScalarTower.algebraMap_eq R K 𝔸ᶠ[R, K], RingHom.coe_comp]
  refine Function.Injective.comp (fun x y hxy ↦ ?_) (IsFractionRing.injective R K)
  have := congr($hxy v)
  simpa using this

/-- When `R` is not a field and has finite residue fields, the principal level `K(0) = {1}` is not
open in `GL₂(𝔸_f)`. -/
theorem not_isOpen_principalLevel_bot [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
    (hR : ¬ IsField R) :
    ¬ IsOpen (principalLevel K (⊥ : Ideal R) : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  intro h
  rw [principalLevel_bot, Subgroup.coe_bot] at h
  have := discreteTopology_of_isOpen_singleton_one h
  -- `GL₂(Ô)` is compact, hence finite, and contains `[[1, r], [0, 1]]` for every `r ∈ R`.
  have hfin : ((integralGL K 2 (R := R)).range : Set (GL (Fin 2) 𝔸ᶠ[R, K])).Finite := by
    rw [← level0_top]
    exact (isCompact_level0 K top_ne_bot).finite_of_discrete
  have hmem (r : R) : upperRightHom (algebraMap R 𝔸ᶠ[R, K] r) ∈ (integralGL K 2).range := by
    have hr : algebraMap R 𝔸ᶠ[R, K] r ∈ integralAdeles R K :=
      (integralAdeles R K).algebraMap_mem r
    refine mem_range_integralGL_iff.mpr ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem, hr]
    · fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem, hr]
  have := hfin.to_subtype
  have : Finite R := Finite.of_injective
    (fun r ↦ (⟨_, hmem r⟩ : ((integralGL K 2 (R := R)).range : Set (GL (Fin 2) 𝔸ᶠ[R, K]))))
    fun r s h ↦ algebraMap_finiteAdeleRing_injective K hR
      (injective_upperRightHom (congrArg Subtype.val h))
  exact hR (Finite.isField_of_domain R)

end IsDedekindDomain.FiniteAdeleRing
