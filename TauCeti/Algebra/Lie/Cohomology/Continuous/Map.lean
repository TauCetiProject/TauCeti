/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.Continuous.Basic

/-!
# Functoriality of continuous second Lie algebra cohomology

For discrete trivial coefficients, a continuous Lie algebra morphism `φ : L' → L` and a linear
coefficient map `e : M → M'` induce a linear map
`H²_cont(L, M) → H²_cont(L', M')`. On representatives it sends a cocycle `c` to
`(x, y) ↦ e (c (φ x) (φ y))`. The differential of a continuous one-cochain transforms by the
same formula, so this is well-defined on cohomology classes, not just on cocycles.

The maps are contravariant in the Lie algebra and covariant in the coefficients, with identity
and composition laws. A Lie equivalence continuous in both directions and a coefficient linear
equivalence therefore give a linear equivalence on continuous second cohomology. These maps
allow continuous central-extension classes to be transported under changes of coordinates and
coefficients. No topology on the coefficient modules is needed: continuity of cochains means
continuity for discrete coefficients throughout.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for continuous cohomology of
  formal loop algebras and its central-extension interpretation.
-/

public section

namespace TauCeti.LieModule.Cohomology

open _root_.LieModule.Cohomology

variable {R L L' M M' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M']

/-- Pullback along `φ` and coefficient pushforward along `e`, restricted to continuous
two-cocycles with discrete trivial coefficients. -/
def continuousTwoCocycleMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) (hφ : Continuous φ) :
    continuousTwoCocycle R L M →ₗ[R] continuousTwoCocycle R L' M' :=
  (twoCochainMap e φ).restrict fun _ hc => twoCochainMap_mem_continuousTwoCocycle e hφ hc

/-- The underlying cochain of the induced continuous cocycle. -/
@[simp]
theorem coe_continuousTwoCocycleMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) (hφ : Continuous φ)
    (c : continuousTwoCocycle R L M) :
    (continuousTwoCocycleMap e φ hφ c : twoCochain R L' M') = twoCochainMap e φ c :=
  (rfl)

/-- Continuous coboundaries remain continuous coboundaries under pullback and coefficient
pushforward. -/
theorem continuousTwoCocycleMap_mem_continuousTwoCoboundary (e : M →ₗ[R] M')
    (φ : L' →ₗ⁅R⁆ L) (hφ : Continuous φ) {c : continuousTwoCocycle R L M}
    (hc : c ∈ continuousTwoCoboundary R L M) :
    continuousTwoCocycleMap e φ hφ c ∈ continuousTwoCoboundary R L' M' := by
  obtain ⟨f, hf, hfc⟩ := mem_continuousTwoCoboundary_iff.mp hc
  refine mem_continuousTwoCoboundary_iff.mpr
    ⟨e ∘ₗ f ∘ₗ φ.toLinearMap,
      comp_mem_continuousOneCochain e (comp_lieHom_mem_continuousOneCochain hφ hf), ?_⟩
  rw [← twoCochainMap_d₁₂, hfc, coe_continuousTwoCocycleMap]

/-- The map on continuous second cohomology induced by a continuous Lie algebra morphism and a
linear map of discrete trivial coefficient modules. -/
def continuousSecondCohomologyMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) (hφ : Continuous φ) :
    continuousSecondCohomology R L M →ₗ[R] continuousSecondCohomology R L' M' :=
  (continuousTwoCoboundary R L M).mapQ (continuousTwoCoboundary R L' M')
    (continuousTwoCocycleMap e φ hφ)
    (fun _ hc => continuousTwoCocycleMap_mem_continuousTwoCoboundary e φ hφ hc)

/-- The induced map sends the class of `c` to the class of its transformed cocycle. -/
@[simp]
theorem continuousSecondCohomologyMap_mk (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (hφ : Continuous φ) (c : continuousTwoCocycle R L M) :
    continuousSecondCohomologyMap e φ hφ (continuousSecondCohomologyMk R L M c) =
      continuousSecondCohomologyMk R L' M' (continuousTwoCocycleMap e φ hφ c) := by
  rw [continuousSecondCohomologyMk_eq_mkQ, continuousSecondCohomologyMk_eq_mkQ]
  exact Submodule.mapQ_apply _ _ _ c

/-- Identity maps on the Lie algebra and coefficients induce the identity on continuous
two-cocycles. -/
@[simp]
theorem continuousTwoCocycleMap_id :
    continuousTwoCocycleMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L)
      (by exact continuous_id) = LinearMap.id := by
  ext c : 1
  apply Subtype.ext
  exact LinearMap.congr_fun twoCochainMap_id (c : twoCochain R L M)

/-- Identity maps induce the identity on continuous second cohomology. -/
@[simp]
theorem continuousSecondCohomologyMap_id :
    continuousSecondCohomologyMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L)
      (by exact continuous_id) = LinearMap.id := by
  simp only [continuousSecondCohomologyMap, continuousTwoCocycleMap_id, Submodule.mapQ_id]

section Composition

variable {L'' M'' : Type*} [LieRing L''] [LieAlgebra R L''] [TopologicalSpace L'']
  [AddCommGroup M''] [Module R M''] [LieRingModule L'' M''] [LieModule R L'' M'']
  [LieModule.IsTrivial L'' M'']

/-- Successive continuous cocycle maps compose covariantly on coefficients and contravariantly
on Lie algebras. -/
theorem continuousTwoCocycleMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L') (hφ : Continuous φ) (hψ : Continuous ψ) :
    (continuousTwoCocycleMap e' ψ hψ).comp (continuousTwoCocycleMap e φ hφ) =
      continuousTwoCocycleMap (e'.comp e) (φ.comp ψ) (by exact hφ.comp hψ) := by
  simpa only [continuousTwoCocycleMap, twoCochainMap_comp] using
    (LinearMap.restrict_comp
      (fun _ hc => twoCochainMap_mem_continuousTwoCocycle e hφ hc)
      (fun _ hc => twoCochainMap_mem_continuousTwoCocycle e' hψ hc)).symm

/-- Functoriality of continuous second cohomology: coefficient maps compose in the same order,
while Lie algebra maps compose in the reverse order. -/
theorem continuousSecondCohomologyMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L') (hφ : Continuous φ) (hψ : Continuous ψ) :
    (continuousSecondCohomologyMap e' ψ hψ).comp (continuousSecondCohomologyMap e φ hφ) =
      continuousSecondCohomologyMap (e'.comp e) (φ.comp ψ) (by exact hφ.comp hψ) := by
  simpa only [continuousSecondCohomologyMap, continuousTwoCocycleMap_comp] using
    (Submodule.mapQ_comp (continuousTwoCoboundary R L M)
      (continuousTwoCoboundary R L' M') (continuousTwoCoboundary R L'' M'')
      (continuousTwoCocycleMap e φ hφ) (continuousTwoCocycleMap e' ψ hψ)
      (fun _ hc => continuousTwoCocycleMap_mem_continuousTwoCoboundary e φ hφ hc)
      (fun _ hc => continuousTwoCocycleMap_mem_continuousTwoCoboundary e' ψ hψ hc)).symm

end Composition

/-- Transport of continuous second cohomology under a bicontinuous Lie equivalence and a
linear equivalence of discrete trivial coefficients. The Lie equivalence is used by pullback. -/
def continuousSecondCohomologyEquiv (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) :
    continuousSecondCohomology R L M ≃ₗ[R] continuousSecondCohomology R L' M' :=
  LinearEquiv.ofLinearMap (continuousSecondCohomologyMap e.toLinearMap φ.toLieHom hφ)
    (continuousSecondCohomologyMap e.symm.toLinearMap φ.symm.toLieHom hφ')
    (by
      have hp : φ.symm.toLieHom.comp φ.toLieHom = LieHom.id := by ext; simp
      simpa only [e.comp_symm, hp, continuousSecondCohomologyMap_id] using
        continuousSecondCohomologyMap_comp e.symm.toLinearMap e.toLinearMap
          φ.symm.toLieHom φ.toLieHom hφ' hφ)
    (by
      have hp : φ.toLieHom.comp φ.symm.toLieHom = LieHom.id := by ext; simp
      simpa only [e.symm_comp, hp, continuousSecondCohomologyMap_id] using
        continuousSecondCohomologyMap_comp e.toLinearMap e.symm.toLinearMap
          φ.toLieHom φ.symm.toLieHom hφ hφ')

/-- The forward linear map of cohomology transport is pullback and coefficient pushforward. -/
@[simp]
theorem continuousSecondCohomologyEquiv_toLinearMap (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) :
    (continuousSecondCohomologyEquiv e φ hφ hφ').toLinearMap =
      continuousSecondCohomologyMap e.toLinearMap φ.toLieHom hφ :=
  (rfl)

/-- The inverse transport uses the inverse Lie and coefficient equivalences. -/
@[simp]
theorem continuousSecondCohomologyEquiv_symm_toLinearMap (e : M ≃ₗ[R] M')
    (φ : L' ≃ₗ⁅R⁆ L) (hφ : Continuous φ) (hφ' : Continuous φ.symm) :
    (continuousSecondCohomologyEquiv e φ hφ hφ').symm.toLinearMap =
      continuousSecondCohomologyMap e.symm.toLinearMap φ.symm.toLieHom hφ' :=
  (rfl)

/-- Applying cohomology transport is pullback and coefficient pushforward. -/
@[simp]
theorem continuousSecondCohomologyEquiv_apply (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) (x : continuousSecondCohomology R L M) :
    continuousSecondCohomologyEquiv e φ hφ hφ' x =
      continuousSecondCohomologyMap e.toLinearMap φ.toLieHom hφ x :=
  (rfl)

/-- Applying inverse cohomology transport uses the inverse Lie and coefficient equivalences. -/
@[simp]
theorem continuousSecondCohomologyEquiv_symm_apply (e : M ≃ₗ[R] M') (φ : L' ≃ₗ⁅R⁆ L)
    (hφ : Continuous φ) (hφ' : Continuous φ.symm) (x : continuousSecondCohomology R L' M') :
    (continuousSecondCohomologyEquiv e φ hφ hφ').symm x =
      continuousSecondCohomologyMap e.symm.toLinearMap φ.symm.toLieHom hφ' x :=
  (rfl)

end TauCeti.LieModule.Cohomology
