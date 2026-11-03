/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Continuous.Cohomology
public import TauCeti.Topology.Algebra.Algebra.Unitization

/-!
# Relative continuous cyclic cochains

For a possibly nonunital topological algebra `A`, relative continuous cyclic cochains are the
kernel of restriction from its forced unitization to the scalars. The augmentation splits this
restriction continuously for uniform convergence on products of bounded sets. The resulting
projection commutes with the Hochschild differential, giving the relative continuous cyclic
complex and its quotient cohomology. Coboundaries are actual images, not their closures.

A relative cocycle is a relative coboundary exactly when it is a coboundary on the unitization:
subtracting the augmentation part of a primitive makes that primitive relative. Consequently
relative continuous cyclic cohomology injects into the full theory of the forced unitization.
The construction does not use completeness, local convexity or Hausdorffness of the quotient.
It is not the reduced theory obtained from an algebra's own unit inclusion.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §1.4.

The splitting uses Mathlib's `ContinuousLinearEquiv.equivOfRightInverse`.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

variable (𝕜 A M : Type*) [NormedField 𝕜] [NonUnitalRing A] [Module 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [TopologicalSpace A]
  [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul 𝕜 M]

/-- Continuous restriction of cyclic cochains to the scalar subalgebra of the forced
unitization. -/
def continuousUnitizationScalarRestriction (n : ℕ) :
    continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n →L[𝕜]
      continuousCyclicCochains 𝕜 𝕜 M n :=
  ⟨continuousCyclicCochainsMap M
    ⟨(Algebra.ofId 𝕜 (Unitization 𝕜 A)).toLinearMap,
      Unitization.continuous_algebraMap_prod⟩ n,
    continuous_continuousCyclicCochainsMap _ n⟩

/-- Continuous pullback of scalar cochains along the augmentation of the forced unitization. -/
def continuousUnitizationAugmentationPullback (n : ℕ) :
    continuousCyclicCochains 𝕜 𝕜 M n →L[𝕜]
      continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n :=
  ⟨continuousCyclicCochainsMap M
    ⟨(Unitization.fstHom 𝕜 A).toLinearMap, Unitization.continuous_fst_prod⟩ n,
    continuous_continuousCyclicCochainsMap _ n⟩

@[simp]
theorem continuousUnitizationScalarRestriction_apply (n : ℕ)
    (φ : continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) (a : Fin (n + 1) → 𝕜) :
    (continuousUnitizationScalarRestriction 𝕜 A M n φ).1 a =
      φ.1 (fun i ↦ algebraMap 𝕜 (Unitization 𝕜 A) (a i)) := by
  simp only [continuousUnitizationScalarRestriction, ContinuousLinearMap.coe_mk',
    coe_continuousCyclicCochainsMap_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- The bundled continuous map evaluates by its underlying algebra homomorphism.
  congr 1

@[simp]
theorem continuousUnitizationAugmentationPullback_apply (n : ℕ)
    (φ : continuousCyclicCochains 𝕜 𝕜 M n) (a : Fin (n + 1) → Unitization 𝕜 A) :
    (continuousUnitizationAugmentationPullback 𝕜 A M n φ).1 a =
      φ.1 (fun i ↦ (a i).fst) := by
  simp only [continuousUnitizationAugmentationPullback, ContinuousLinearMap.coe_mk',
    coe_continuousCyclicCochainsMap_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- The bundled continuous map evaluates by its underlying augmentation homomorphism.
  congr 1

/-- The augmentation pullback is a continuous right inverse to scalar restriction. -/
@[simp]
theorem continuousUnitizationScalarRestriction_comp_continuousUnitizationAugmentationPullback
    (n : ℕ) :
    (continuousUnitizationScalarRestriction 𝕜 A M n).comp
      (continuousUnitizationAugmentationPullback 𝕜 A M n) = ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro φ
  apply Subtype.ext
  apply ContinuousMultilinearMap.ext
  intro a
  simp [Unitization.algebraMap_eq_inl]

private theorem continuousUnitization_rightInverse (n : ℕ) :
    Function.RightInverse (continuousUnitizationAugmentationPullback 𝕜 A M n)
      (continuousUnitizationScalarRestriction 𝕜 A M n) :=
  fun φ ↦ DFunLike.congr_fun
    (continuousUnitizationScalarRestriction_comp_continuousUnitizationAugmentationPullback
      𝕜 A M n) φ

/-- Continuous cyclic cochains on the forced unitization vanishing on scalar tuples. -/
def continuousRelativeCyclicCochains (n : ℕ) :
    Submodule 𝕜 (continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) :=
  (continuousUnitizationScalarRestriction 𝕜 A M n).ker

@[simp]
theorem mem_continuousRelativeCyclicCochains_iff {n : ℕ}
    {φ : continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n} :
    φ ∈ continuousRelativeCyclicCochains 𝕜 A M n ↔
      continuousUnitizationScalarRestriction 𝕜 A M n φ = 0 := LinearMap.mem_ker

/-- Relative means vanishing when all arguments are scalars, not vanishing whenever
any one argument is a unit. -/
theorem mem_continuousRelativeCyclicCochains_iff_forall {n : ℕ}
    {φ : continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n} :
    φ ∈ continuousRelativeCyclicCochains 𝕜 A M n ↔
      ∀ a : Fin (n + 1) → 𝕜,
        φ.1 (fun i ↦ algebraMap 𝕜 (Unitization 𝕜 A) (a i)) = 0 := by
  rw [mem_continuousRelativeCyclicCochains_iff, Subtype.ext_iff,
    ContinuousMultilinearMap.ext_iff]
  simp

/-- Relative continuous cochains inherit their additive group structure. -/
instance continuousRelativeCyclicCochainsAddCommGroup (n : ℕ) :
    AddCommGroup (continuousRelativeCyclicCochains 𝕜 A M n) :=
  Submodule.addCommGroup (M := continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n)
    (continuousRelativeCyclicCochains 𝕜 A M n)

instance continuousRelativeCyclicCochainsModule (n : ℕ) :
    Module 𝕜 (continuousRelativeCyclicCochains 𝕜 A M n) :=
  inferInstanceAs (Module 𝕜 (continuousUnitizationScalarRestriction 𝕜 A M n).ker)

instance continuousRelativeCyclicCochainsIsTopologicalAddGroup (n : ℕ) :
    IsTopologicalAddGroup (continuousRelativeCyclicCochains 𝕜 A M n) :=
  Submodule.isTopologicalAddGroup
    (M := continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n)
    (continuousRelativeCyclicCochains 𝕜 A M n)

/-- Scalar and relative continuous cyclic cochains give a topological direct-sum decomposition
of the cochains of the forced unitization. -/
def continuousUnitizationCyclicCochainsEquiv (n : ℕ) :
    continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n ≃L[𝕜]
      continuousCyclicCochains 𝕜 𝕜 M n × continuousRelativeCyclicCochains 𝕜 A M n :=
  ContinuousLinearEquiv.equivOfRightInverse
    (M := continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n)
    (M₂ := continuousCyclicCochains 𝕜 𝕜 M n) _ _
    (continuousUnitization_rightInverse 𝕜 A M n)

@[simp]
theorem continuousUnitizationCyclicCochainsEquiv_fst {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) :
    (continuousUnitizationCyclicCochainsEquiv 𝕜 A M n φ).1 =
      continuousUnitizationScalarRestriction 𝕜 A M n φ := (rfl)

@[simp]
theorem continuousUnitizationCyclicCochainsEquiv_symm_apply {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 𝕜 M n) (ψ : continuousRelativeCyclicCochains 𝕜 A M n) :
    (continuousUnitizationCyclicCochainsEquiv 𝕜 A M n).symm (φ, ψ) =
      continuousUnitizationAugmentationPullback 𝕜 A M n φ + ψ.1 := (rfl)

/-- Projection to relative cochains by subtracting the pullback of scalar restriction. -/
def continuousRelativeCyclicProjection (n : ℕ) :
    continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n →L[𝕜]
      continuousRelativeCyclicCochains 𝕜 A M n :=
  (ContinuousLinearMap.snd 𝕜 _ _).comp
    (continuousUnitizationCyclicCochainsEquiv 𝕜 A M n).toContinuousLinearMap

@[simp]
theorem continuousUnitizationCyclicCochainsEquiv_snd {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) :
    (continuousUnitizationCyclicCochainsEquiv 𝕜 A M n φ).2 =
      continuousRelativeCyclicProjection 𝕜 A M n φ := (rfl)

@[simp]
theorem coe_continuousRelativeCyclicProjection {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) :
    (continuousRelativeCyclicProjection 𝕜 A M n φ :
        continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) =
      φ - continuousUnitizationAugmentationPullback 𝕜 A M n
        (continuousUnitizationScalarRestriction 𝕜 A M n φ) := by
  rw [continuousRelativeCyclicProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
    continuousUnitizationCyclicCochainsEquiv]
  -- Relative cochains carry the submodule topology on the restriction kernel.
  erw [ContinuousLinearEquiv.snd_equivOfRightInverse]

@[simp]
theorem continuousRelativeCyclicProjection_coe {n : ℕ}
    (φ : continuousRelativeCyclicCochains 𝕜 A M n) :
    continuousRelativeCyclicProjection 𝕜 A M n φ = φ := by
  apply Subtype.ext
  rw [coe_continuousRelativeCyclicProjection,
    (mem_continuousRelativeCyclicCochains_iff 𝕜 A M).1 φ.2, map_zero]
  exact sub_zero φ.1

variable [IsTopologicalAddGroup A] [ContinuousMul A] [ContinuousSMul 𝕜 A]

/-- Scalar restriction commutes with the continuous Hochschild differential. -/
theorem continuousUnitizationScalarRestriction_continuousCyclicHochschildCoboundary {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) :
    continuousUnitizationScalarRestriction 𝕜 A M (n + 1)
        (continuousCyclicHochschildCoboundary 𝕜 (Unitization 𝕜 A) M n φ) =
      continuousCyclicHochschildCoboundary 𝕜 𝕜 M n
        (continuousUnitizationScalarRestriction 𝕜 A M n φ) :=
  (continuousCyclicHochschildCoboundary_continuousCyclicCochainsMap
    (Algebra.ofId 𝕜 (Unitization 𝕜 A)).toNonUnitalAlgHom
    (continuous_algebraMap 𝕜 (Unitization 𝕜 A)) φ).symm

/-- The augmentation pullback commutes with the continuous Hochschild differential. -/
theorem continuousUnitizationAugmentationPullback_continuousCyclicHochschildCoboundary {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 𝕜 M n) :
    continuousUnitizationAugmentationPullback 𝕜 A M (n + 1)
        (continuousCyclicHochschildCoboundary 𝕜 𝕜 M n φ) =
      continuousCyclicHochschildCoboundary 𝕜 (Unitization 𝕜 A) M n
        (continuousUnitizationAugmentationPullback 𝕜 A M n φ) :=
  (continuousCyclicHochschildCoboundary_continuousCyclicCochainsMap
    (Unitization.fstHom 𝕜 A).toNonUnitalAlgHom Unitization.continuous_fst_prod φ).symm

/-- The relative continuous Hochschild differential, continuous for bounded convergence. -/
def continuousRelativeCyclicHochschildCoboundary (n : ℕ) :
    continuousRelativeCyclicCochains 𝕜 A M n →L[𝕜]
      continuousRelativeCyclicCochains 𝕜 A M (n + 1) :=
  (⟨continuousCyclicHochschildCoboundary 𝕜 (Unitization 𝕜 A) M n,
    continuous_continuousCyclicHochschildCoboundary 𝕜 (Unitization 𝕜 A) M n⟩ :
    continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n →L[𝕜]
      continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M (n + 1)).restrict fun φ hφ ↦ by
        simp only [ContinuousLinearMap.coe_mk']
        rw [mem_continuousRelativeCyclicCochains_iff,
          continuousUnitizationScalarRestriction_continuousCyclicHochschildCoboundary,
          (mem_continuousRelativeCyclicCochains_iff 𝕜 A M).1 hφ, map_zero]

@[simp]
theorem coe_continuousRelativeCyclicHochschildCoboundary {n : ℕ}
    (φ : continuousRelativeCyclicCochains 𝕜 A M n) :
    (continuousRelativeCyclicHochschildCoboundary 𝕜 A M n φ :
        continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M (n + 1)) =
      continuousCyclicHochschildCoboundary 𝕜 (Unitization 𝕜 A) M n φ := (rfl)

/-- The relative projection is a cochain projection. -/
theorem continuousRelativeCyclicProjection_continuousCyclicHochschildCoboundary {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) :
    continuousRelativeCyclicProjection 𝕜 A M (n + 1)
        (continuousCyclicHochschildCoboundary 𝕜 (Unitization 𝕜 A) M n φ) =
      continuousRelativeCyclicHochschildCoboundary 𝕜 A M n
        (continuousRelativeCyclicProjection 𝕜 A M n φ) := by
  apply Subtype.ext
  simp only [coe_continuousRelativeCyclicProjection,
    coe_continuousRelativeCyclicHochschildCoboundary,
    continuousUnitizationScalarRestriction_continuousCyclicHochschildCoboundary,
    continuousUnitizationAugmentationPullback_continuousCyclicHochschildCoboundary]
  exact (map_sub (continuousCyclicHochschildCoboundary 𝕜 (Unitization 𝕜 A) M n) _ _).symm

@[simp]
theorem continuousRelativeCyclicHochschildCoboundary_continuousRelativeCyclicHochschildCoboundary
    {n : ℕ}
    (φ : continuousRelativeCyclicCochains 𝕜 A M n) :
    continuousRelativeCyclicHochschildCoboundary 𝕜 A M (n + 1)
      (continuousRelativeCyclicHochschildCoboundary 𝕜 A M n φ) = 0 := by
  apply Subtype.ext
  simp

/-- The native cochain complex of relative continuous cyclic cochains. -/
def continuousRelativeCyclicCochainComplex : CochainComplex (ModuleCat 𝕜) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of 𝕜 (continuousRelativeCyclicCochains 𝕜 A M n))
    (fun n ↦ ModuleCat.ofHom (continuousRelativeCyclicHochschildCoboundary 𝕜 A M n).toLinearMap)
    (fun _n ↦ ModuleCat.hom_ext (LinearMap.ext fun φ ↦
      continuousRelativeCyclicHochschildCoboundary_continuousRelativeCyclicHochschildCoboundary
        𝕜 A M φ))

/-- Identify each term of the relative continuous complex with its cochains. -/
def continuousRelativeCyclicCochainComplexXIso (n : ℕ) :
    (continuousRelativeCyclicCochainComplex 𝕜 A M).X n ≅
      ModuleCat.of 𝕜 (continuousRelativeCyclicCochains 𝕜 A M n) := Iso.refl _

/-- The native differential agrees with the relative continuous Hochschild differential. -/
@[reassoc]
theorem continuousRelativeCyclicCochainComplex_d (n : ℕ) :
    (continuousRelativeCyclicCochainComplex 𝕜 A M).d n (n + 1) ≫
        (continuousRelativeCyclicCochainComplexXIso 𝕜 A M (n + 1)).hom =
      (continuousRelativeCyclicCochainComplexXIso 𝕜 A M n).hom ≫
        ModuleCat.ofHom (continuousRelativeCyclicHochschildCoboundary 𝕜 A M n).toLinearMap := by
  simp [continuousRelativeCyclicCochainComplex, continuousRelativeCyclicCochainComplexXIso]

/-- Relative continuous cyclic cocycles. -/
def continuousRelativeCyclicCocycles (n : ℕ) :
    Submodule 𝕜 (continuousRelativeCyclicCochains 𝕜 A M n) :=
  (continuousRelativeCyclicHochschildCoboundary 𝕜 A M n).ker

@[simp]
theorem mem_continuousRelativeCyclicCocycles_iff {n : ℕ}
    {φ : continuousRelativeCyclicCochains 𝕜 A M n} :
    φ ∈ continuousRelativeCyclicCocycles 𝕜 A M n ↔
      continuousRelativeCyclicHochschildCoboundary 𝕜 A M n φ = 0 := LinearMap.mem_ker

/-- Relative continuous cocycles inherit their additive group structure. -/
instance continuousRelativeCyclicCocyclesAddCommGroup (n : ℕ) :
    AddCommGroup (continuousRelativeCyclicCocycles 𝕜 A M n) :=
  Submodule.addCommGroup (M := continuousRelativeCyclicCochains 𝕜 A M n)
    (continuousRelativeCyclicCocycles 𝕜 A M n)

instance continuousRelativeCyclicCocyclesModule (n : ℕ) :
    Module 𝕜 (continuousRelativeCyclicCocycles 𝕜 A M n) :=
  inferInstanceAs (Module 𝕜 (continuousRelativeCyclicHochschildCoboundary 𝕜 A M n).ker)

instance continuousRelativeCyclicCocyclesIsTopologicalAddGroup (n : ℕ) :
    IsTopologicalAddGroup (continuousRelativeCyclicCocycles 𝕜 A M n) :=
  Submodule.isTopologicalAddGroup (M := continuousRelativeCyclicCochains 𝕜 A M n)
    (continuousRelativeCyclicCocycles 𝕜 A M n)

/-- Inclusion of relative continuous cocycles into the cocycles of the forced unitization. -/
def continuousRelativeCyclicCocycles.toUnitization (n : ℕ) :
    continuousRelativeCyclicCocycles 𝕜 A M n →L[𝕜]
      continuousCyclicCocycles 𝕜 (Unitization 𝕜 A) M n :=
  (continuousRelativeCyclicCochains 𝕜 A M n).subtypeL.restrict fun φ hφ ↦ by
    rw [mem_continuousCyclicCocycles_iff]
    simpa only [coe_continuousRelativeCyclicHochschildCoboundary, Submodule.coe_zero,
      Submodule.subtypeL_apply] using
      congrArg Subtype.val ((mem_continuousRelativeCyclicCocycles_iff 𝕜 A M).1 hφ)

@[simp]
theorem continuousRelativeCyclicCocycles.coe_toUnitization {n : ℕ}
    (φ : continuousRelativeCyclicCocycles 𝕜 A M n) :
    (continuousRelativeCyclicCocycles.toUnitization 𝕜 A M n φ :
      continuousCyclicCochains 𝕜 (Unitization 𝕜 A) M n) = φ.1.1 := (rfl)

/-- Actual relative continuous coboundaries, without taking a closure. -/
def continuousRelativeCyclicCoboundaries :
    (n : ℕ) → Submodule 𝕜 (continuousRelativeCyclicCochains 𝕜 A M n)
  | 0 => ⊥
  | n + 1 => (continuousRelativeCyclicHochschildCoboundary 𝕜 A M n).range

@[simp]
theorem continuousRelativeCyclicCoboundaries_zero :
    continuousRelativeCyclicCoboundaries 𝕜 A M 0 = ⊥ := (rfl)

@[simp]
theorem mem_continuousRelativeCyclicCoboundaries_succ_iff {n : ℕ}
    {φ : continuousRelativeCyclicCochains 𝕜 A M (n + 1)} :
    φ ∈ continuousRelativeCyclicCoboundaries 𝕜 A M (n + 1) ↔
      ∃ ψ, continuousRelativeCyclicHochschildCoboundary 𝕜 A M n ψ = φ := LinearMap.mem_range

/-- Relative continuous coboundaries are cocycles. -/
theorem continuousRelativeCyclicCoboundaries_le_continuousRelativeCyclicCocycles (n : ℕ) :
    continuousRelativeCyclicCoboundaries 𝕜 A M n ≤ continuousRelativeCyclicCocycles 𝕜 A M n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨φ, rfl⟩
    simp

/-- A relative continuous cochain has a relative primitive if and only if it has any
continuous cyclic primitive on the forced unitization. -/
theorem mem_continuousRelativeCyclicCoboundaries_iff {n : ℕ}
    (φ : continuousRelativeCyclicCochains 𝕜 A M n) :
    φ ∈ continuousRelativeCyclicCoboundaries 𝕜 A M n ↔
      φ.1 ∈ continuousCyclicCoboundaries 𝕜 (Unitization 𝕜 A) M n := by
  cases n with
  | zero =>
    rw [continuousRelativeCyclicCoboundaries_zero, continuousCyclicCoboundaries_zero,
      Submodule.mem_bot, Submodule.mem_bot]
    exact Subtype.val_inj.symm
  | succ n =>
    rw [mem_continuousRelativeCyclicCoboundaries_succ_iff,
      mem_continuousCyclicCoboundaries_succ_iff]
    constructor
    · rintro ⟨ψ, rfl⟩
      exact ⟨ψ.1, (coe_continuousRelativeCyclicHochschildCoboundary 𝕜 A M ψ).symm⟩
    · rintro ⟨ψ, hψ⟩
      exact ⟨continuousRelativeCyclicProjection 𝕜 A M n ψ, by
        rw [← continuousRelativeCyclicProjection_continuousCyclicHochschildCoboundary, hψ,
          continuousRelativeCyclicProjection_coe]⟩

/-- Relative continuous cyclic cohomology with the quotient topology on relative cocycles
modulo actual relative coboundaries. -/
abbrev continuousRelativeCyclicCohomology (n : ℕ) :=
  (continuousRelativeCyclicCocycles 𝕜 A M n) ⧸
    (continuousRelativeCyclicCoboundaries 𝕜 A M n).comap
      (continuousRelativeCyclicCocycles 𝕜 A M n).subtype

namespace continuousRelativeCyclicCohomology

/-- The continuous linear relative cohomology class map. -/
def mk (n : ℕ) : continuousRelativeCyclicCocycles 𝕜 A M n →L[𝕜]
    continuousRelativeCyclicCohomology 𝕜 A M n := Submodule.mkQL _

/-- The relative class map is an open quotient map. -/
theorem isOpenQuotientMap_mk (n : ℕ) : IsOpenQuotientMap (mk 𝕜 A M n) :=
  Submodule.isOpenQuotientMap_mkQL _

/-- Every relative class has a relative continuous cocycle representative. -/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk 𝕜 A M n) :=
  (isOpenQuotientMap_mk 𝕜 A M n).surjective

@[simp]
theorem mk_eq_zero_iff {n : ℕ} (φ : continuousRelativeCyclicCocycles 𝕜 A M n) :
    mk 𝕜 A M n φ = 0 ↔ φ.1 ∈ continuousRelativeCyclicCoboundaries 𝕜 A M n :=
  Submodule.Quotient.mk_eq_zero _

/-- Equality of relative cohomology classes is equality modulo actual relative coboundaries. -/
theorem mk_eq_mk_iff {n : ℕ} (φ ψ : continuousRelativeCyclicCocycles 𝕜 A M n) :
    mk 𝕜 A M n φ = mk 𝕜 A M n ψ ↔
      φ.1 - ψ.1 ∈ continuousRelativeCyclicCoboundaries 𝕜 A M n := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  simp

variable {𝕜 A M} {N : Type*} [AddCommGroup N] [Module 𝕜 N] [TopologicalSpace N]

/-- The continuous linear universal property of relative continuous cyclic cohomology. -/
def desc {n : ℕ} (f : continuousRelativeCyclicCocycles 𝕜 A M n →L[𝕜] N)
    (hf : ∀ φ, φ.1 ∈ continuousRelativeCyclicCoboundaries 𝕜 A M n → f φ = 0) :
    continuousRelativeCyclicCohomology 𝕜 A M n →L[𝕜] N := Submodule.liftQL _ f hf

@[simp]
theorem desc_mk {n : ℕ} (f : continuousRelativeCyclicCocycles 𝕜 A M n →L[𝕜] N)
    (hf : ∀ φ, φ.1 ∈ continuousRelativeCyclicCoboundaries 𝕜 A M n → f φ = 0)
    (φ : continuousRelativeCyclicCocycles 𝕜 A M n) :
    desc f hf (mk 𝕜 A M n φ) = f φ := (rfl)

/-- Continuous linear maps from relative cohomology are determined on cocycle classes. -/
@[ext]
theorem hom_ext {n : ℕ} {f g : continuousRelativeCyclicCohomology 𝕜 A M n →L[𝕜] N}
    (h : ∀ φ, f (mk 𝕜 A M n φ) = g (mk 𝕜 A M n φ)) : f = g :=
  ContinuousLinearMap.ext fun x ↦ by
    obtain ⟨φ, rfl⟩ := mk_surjective 𝕜 A M n x
    exact h φ

variable (𝕜 A M)

/-- Inclusion of relative continuous cyclic cohomology into the full continuous theory of
the forced unitization. -/
def toUnitization (n : ℕ) : continuousRelativeCyclicCohomology 𝕜 A M n →L[𝕜]
    continuousCyclicCohomology 𝕜 (Unitization 𝕜 A) M n :=
  desc ((continuousCyclicCohomology.mk 𝕜 (Unitization 𝕜 A) M n).comp
    (continuousRelativeCyclicCocycles.toUnitization 𝕜 A M n)) fun φ hφ ↦
      (continuousCyclicCohomology.mk_eq_zero_iff 𝕜 (Unitization 𝕜 A) M _).2
        ((mem_continuousRelativeCyclicCoboundaries_iff 𝕜 A M φ.1).1 hφ)

@[simp]
theorem toUnitization_mk {n : ℕ} (φ : continuousRelativeCyclicCocycles 𝕜 A M n) :
    toUnitization 𝕜 A M n (mk 𝕜 A M n φ) =
      continuousCyclicCohomology.mk 𝕜 (Unitization 𝕜 A) M n
        (continuousRelativeCyclicCocycles.toUnitization 𝕜 A M n φ) := (rfl)

/-- The scalar splitting makes inclusion of relative cohomology injective, even when
coboundaries are not closed. -/
theorem toUnitization_injective (n : ℕ) : Function.Injective (toUnitization 𝕜 A M n) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  obtain ⟨φ, rfl⟩ := mk_surjective 𝕜 A M n z
  rw [toUnitization_mk, continuousCyclicCohomology.mk_eq_zero_iff] at hz
  exact (mk_eq_zero_iff 𝕜 A M φ).2
    ((mem_continuousRelativeCyclicCoboundaries_iff 𝕜 A M φ.1).2 hz)

end continuousRelativeCyclicCohomology

end TauCeti
