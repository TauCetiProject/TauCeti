/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.RingTheory.KoszulComplex.Basic

/-!
# Augmentations of Koszul complexes

The Koszul complex of a linear functional `φ : M →ₗ[R] R` augments to `R/I` whenever
`φ(M) ⊆ I`. In degree zero the augmentation is the quotient map under `⋀⁰ M ≃ R`.
It commutes with the chain maps induced by maps of linear functionals. If `I = φ(M)`,
it induces an isomorphism on zeroth homology, without any regularity hypothesis.
These maps are the augmentations used to resolve quotients by regular sequences.

The construction uses Mathlib's `ChainComplex.toSingle₀Equiv` and the computation of
zeroth Koszul homology in `TauCeti.RingTheory.KoszulComplex.Basic`.
See [The Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622).
-/

public section

noncomputable section

universe u

open CategoryTheory HomologicalComplex

namespace TauCeti.koszulComplex

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The augmentation `K(φ) → (R/I)[0]` when `φ` takes values in `I`. -/
def augmentation (φ : Module.Dual R M) (I : Ideal R) (hφ : LinearMap.range φ ≤ I) :
    koszulComplex φ ⟶ (ChainComplex.single₀ _).obj (ModuleCat.of R (R ⧸ I)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (I.mkQ ∘ₗ (exteriorPower.zeroEquiv R M).toLinearMap), by
      rw [koszulComplex_d]
      apply ModuleCat.hom_ext
      -- The bundled terms are exterior powers; rewriting `hom_ofHom` cannot identify their
      -- inferred module structures until these fixed-degree wrappers are reduced.
      change (I.mkQ ∘ₗ (exteriorPower.zeroEquiv R M).toLinearMap) ∘ₗ
        koszulDifferential φ 0 = 0
      rw [LinearMap.comp_assoc, zeroEquiv_comp_koszulDifferential_zero,
        ← LinearMap.comp_assoc]
      have h : I.mkQ ∘ₗ φ = 0 := LinearMap.range_le_ker_iff.mp (by simpa using hφ)
      rw [h, LinearMap.zero_comp]⟩

/-- In degree zero the augmentation is the quotient map under `⋀⁰ M ≃ R`. -/
@[simp]
theorem augmentation_f_zero (φ : Module.Dual R M) (I : Ideal R)
    (hφ : LinearMap.range φ ≤ I) :
    (augmentation φ I hφ).f 0 =
      ModuleCat.ofHom (I.mkQ ∘ₗ (exteriorPower.zeroEquiv R M).toLinearMap) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- A map of linear functionals commutes with augmentation to the same quotient. -/
@[reassoc (attr := simp)]
theorem map_comp_augmentation {N : Type u} [AddCommGroup N] [Module R N]
    {φ : Module.Dual R M} {ψ : Module.Dual R N} (g : M →ₗ[R] N) (hg : ψ ∘ₗ g = φ)
    (I : Ideal R) (hψ : LinearMap.range ψ ≤ I) :
    map g hg ≫ augmentation ψ I hψ =
      augmentation φ I (by rw [← hg]; exact (LinearMap.range_comp_le_range g ψ).trans hψ) := by
  apply to_single_hom_ext
  simp only [comp_f, map_f, augmentation_f_zero]
  apply ModuleCat.hom_ext
  -- The complex terms are bundled exterior powers, as in `augmentation`.
  change (I.mkQ ∘ₗ (exteriorPower.zeroEquiv R N).toLinearMap) ∘ₗ
    exteriorPower.map 0 g = I.mkQ ∘ₗ (exteriorPower.zeroEquiv R M).toLinearMap
  rw [LinearMap.comp_assoc, exteriorPower.zeroEquiv_naturality]

/-- If `I = φ(M)`, the augmentation induces an isomorphism on zeroth homology. -/
theorem quasiIsoAt_augmentation_zero (φ : Module.Dual R M) (I : Ideal R)
    (hI : LinearMap.range φ = I) : QuasiIsoAt (augmentation φ I hI.le) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
  refine ⟨?_, ?_⟩
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    simp only [shortComplexFunctor'_obj_f, shortComplexFunctor'_map_τ₂,
      koszulComplex_d, augmentation_f_zero]
    -- Reduce the fixed-degree short-complex and bundled-map wrappers to linear maps.
    change LinearMap.range (koszulDifferential φ 0) =
      LinearMap.ker (I.mkQ ∘ₗ (exteriorPower.zeroEquiv R M).toLinearMap)
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    apply (Submodule.map_injective_of_injective (exteriorPower.zeroEquiv R M).injective)
    rw [map_zeroEquiv_range_koszulDifferential_zero,
      Submodule.map_comap_eq_of_surjective (exteriorPower.zeroEquiv R M).surjective, hI]
  · rw [ModuleCat.epi_iff_surjective]
    rw [shortComplexFunctor'_map_τ₂, augmentation_f_zero]
    exact (Submodule.mkQ_surjective I).comp (exteriorPower.zeroEquiv R M).surjective

end TauCeti.koszulComplex
