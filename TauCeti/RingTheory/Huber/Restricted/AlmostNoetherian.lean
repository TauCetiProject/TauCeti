/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AlmostNoetherian

/-!
# Kiehl's almost noetherianity theorem for completed integral restricted power series

Let `K` be a complete nontrivially normed ultrametric field with valuation ring `𝒪[K]`. The
completed integral restricted power-series ring `𝒪[K]⟨X₁, …, Xₙ⟩`
(`TauCeti.Huber.restrictedMvPowerSeriesCompletion n 𝒪[K]`) is bicontinuously isomorphic to the
Gauss unit ball `K⟨X₁, …, Xₙ⟩°` via
`TauCeti.Huber.restrictedMvPowerSeriesCompletionIntegerEquiv`. Transporting Kiehl's Satz 5.1 from
`K⟨X₁, …, Xₙ⟩°` (`RingHom.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall`) yields the
almost noetherianity theorem directly for arbitrary ring quotients and `𝒪[K]`-algebra quotients of
`𝒪[K]⟨X₁, …, Xₙ⟩`: for every finitely generated module `M` over a quotient `A₀`, every submodule
`N ≤ M`, and every `0 < ε < 1`, there exists a single finitely generated submodule `N' ≤ N`
containing `c • x` for all `c ∈ 𝒪[K]` with `‖(c : K)‖ ≤ ε` and all `x ∈ N`.

## Main results

* `RingHom.exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion`: Kiehl's
  almost noetherianity theorem for ring quotients of `𝒪[K]⟨X₁, …, Xₙ⟩`.
* `AlgHom.exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion`: Kiehl's
  almost noetherianity theorem for `𝒪[K]`-algebra quotients of `𝒪[K]⟨X₁, …, Xₙ⟩`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138).
-/

public section

open _root_.MvPowerSeries TauCeti TauCeti.Huber TauCeti.MvPowerSeries
open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Kiehl's almost noetherianity theorem for quotients of `𝒪[K]⟨X₁, …, Xₙ⟩` (ring-homomorphism
form).** Over a complete nontrivially normed ultrametric field `K`, for any surjective ring
homomorphism `φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀`, any finitely generated
`A₀`-module `M`, any submodule `N ≤ M`, and any `0 < ε < 1`, there exists a finitely generated
submodule `N' ≤ N` containing `φ (algebraMap 𝒪[K] _ c) • x` for all `c ∈ 𝒪[K]` with `‖(c : K)‖ ≤ ε`
and all `x ∈ N`. -/
theorem RingHom.exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion
    {n : ℕ} {A₀ : Type*} [CommRing A₀] (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀)
    (hφ : Function.Surjective φ) {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M]
    (N : Submodule A₀ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule A₀ M, N'.FG ∧ N' ≤ N ∧
      ∀ c : 𝒪[K], ‖(c : K)‖ ≤ ε → ∀ x ∈ N, φ (algebraMap 𝒪[K] _ c) • x ∈ N' := by
  let e := restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n
  have hsurj : Function.Surjective (φ.comp e.symm.toRingHom) := hφ.comp e.symm.surjective
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    (φ.comp e.symm.toRingHom).exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall
      hsurj N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  have heq : (φ.comp e.symm.toRingHom)
      (unitClosedBallCoeffHom (σ := Fin n) (r := fun _ ↦ 1) (integerUnitClosedBallEquiv c)) =
      φ (algebraMap 𝒪[K] _ c) := by
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      restrictedMvPowerSeriesCompletionIntegerEquiv_symm_unitClosedBallCoeffHom,
      RingEquiv.symm_apply_apply]
  have hc' : ‖(integerUnitClosedBallEquiv c : K)‖ ≤ ε := by
    rwa [coe_integerUnitClosedBallEquiv]
  exact heq ▸ hsmul (integerUnitClosedBallEquiv c) hc' x hx

/-- **Kiehl's almost noetherianity theorem for `𝒪[K]`-algebra quotients of `𝒪[K]⟨X₁, …, Xₙ⟩`.**
Over a complete nontrivially normed ultrametric field `K`, let `A₀` be a commutative `𝒪[K]`-algebra
admitting a surjective `𝒪[K]`-algebra homomorphism from `restrictedMvPowerSeriesCompletion n 𝒪[K]`,
and let `M` be a finitely generated `A₀`-module with the induced `𝒪[K]`-module structure. For every
`N : Submodule A₀ M` and every `0 < ε < 1`, there exists a finitely generated `A₀`-submodule
`N' ≤ N` such that `c • x ∈ N'` for all `c : 𝒪[K]` with `‖(c : K)‖ ≤ ε` and all `x ∈ N`. -/
theorem AlgHom.exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion
    {n : ℕ} {A₀ : Type*} [CommRing A₀] [Algebra 𝒪[K] A₀]
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →ₐ[𝒪[K]] A₀) (hφ : Function.Surjective φ)
    {M : Type*} [AddCommGroup M] [Module 𝒪[K] M] [Module A₀ M] [IsScalarTower 𝒪[K] A₀ M]
    [Module.Finite A₀ M] (N : Submodule A₀ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule A₀ M, N'.FG ∧ N' ≤ N ∧
      ∀ c : 𝒪[K], ‖(c : K)‖ ≤ ε → ∀ x ∈ N, c • x ∈ N' := by
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    φ.toRingHom.exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion
      hφ N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    algebraMap_smul] using hsmul c hc x hx
