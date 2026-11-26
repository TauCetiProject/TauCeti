/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.BaseChange
public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Basic
import Mathlib.Logic.Equiv.Nat

/-!
# Base change for two-sided restricted series `A⟨T, T⁻¹⟩`

Reindexing `ℤ` along a bijection with `Fin 1 →₀ ℕ` transports `restrictedMvPowerSeriesBaseChange`
to the coordinate-free Laurent comparison `A⟨T, T⁻¹⟩ ⊗[A] M →ₗ[A] M⟨T, T⁻¹⟩` sending `f ⊗ₜ v` to
`n ↦ f n • v` (`TauCeti.Huber.restrictedLaurentSeriesTensorToNull`), yielding surjectivity for
finite modules and bijectivity (`restrictedLaurentSeriesTensorToNullEquiv`) for finitely presented
naturally complete modules over a complete Hausdorff Tate ring (Kedlaya–Liu II, Corollary 2.4.9(c)).

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Corollary 2.4.9(c).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.39 and Remark 8.29.
-/

public section

open Filter Topology
open scoped TensorProduct

namespace TauCeti.Huber

private noncomputable def intEquivFinOneFinsupp : ℤ ≃ (Fin 1 →₀ ℕ) :=
  Equiv.intEquivNat.trans (Finsupp.uniqueEquiv (0 : Fin 1)).symm

private noncomputable def twoSidedToRestrictedSubringLinearEquiv (A : Type*) [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] :
    twoSidedRestrictedSubmodule A A ≃ₗ[A] restrictedMvPowerSeriesSubring 1 A :=
  twoSidedRestrictedSubmoduleEquivZeroAtFilter A A ≪≫ₗ
    zeroAtFilterCofiniteCongr A A intEquivFinOneFinsupp ≪≫ₗ
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A A).symm ≪≫ₗ
    (restrictedMvPowerSeriesSubringLinearEquiv 1 A).symm

private theorem coeff_twoSidedToRestrictedSubringLinearEquiv {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] (f : twoSidedRestrictedSubmodule A A)
    (ν : Fin 1 →₀ ℕ) :
    MvPowerSeries.coeff ν
        (twoSidedToRestrictedSubringLinearEquiv A f : MvPowerSeries (Fin 1) A) =
      (f : ℤ → A) (intEquivFinOneFinsupp.symm ν) := by
  rw [MvPowerSeries.coeff_apply]
  simp only [twoSidedToRestrictedSubringLinearEquiv, LinearEquiv.trans_apply,
    coe_restrictedMvPowerSeriesSubringLinearEquiv_symm,
    coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter_symm,
    coe_zeroAtFilterCofiniteCongr_apply, coe_twoSidedRestrictedSubmoduleEquivZeroAtFilter]

section Comparison

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
  [ContinuousSMul A M]

/-- **The natural Laurent comparison `A⟨T, T⁻¹⟩ ⊗[A] M →ₗ[A] M⟨T, T⁻¹⟩`** sending `f ⊗ₜ v` to the
two-sided null family `n ↦ f n • v` (Kedlaya–Liu II, Corollary 2.4.9(c)). -/
noncomputable def restrictedLaurentSeriesTensorToNull :
    twoSidedRestrictedSubmodule A A ⊗[A] M →ₗ[A] twoSidedRestrictedSubmodule A M :=
  (twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm.toLinearMap ∘ₗ
    (zeroAtFilterCofiniteCongr A M intEquivFinOneFinsupp.symm).toLinearMap ∘ₗ
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).toLinearMap ∘ₗ
    restrictedMvPowerSeriesBaseChange ∘ₗ
    (LinearEquiv.lTensor M (twoSidedToRestrictedSubringLinearEquiv A)).toLinearMap ∘ₗ
    (TensorProduct.comm A (twoSidedRestrictedSubmodule A A) M).toLinearMap

/-- On a pure tensor `f ⊗ₜ v`, the `n`-th Laurent coefficient is `f n • v`. -/
@[simp]
theorem restrictedLaurentSeriesTensorToNull_tmul
    (f : twoSidedRestrictedSubmodule A A) (v : M) (n : ℤ) :
    (restrictedLaurentSeriesTensorToNull (f ⊗ₜ[A] v) : ℤ → M) n = (f : ℤ → A) n • v := by
  simp only [restrictedLaurentSeriesTensorToNull, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, TensorProduct.comm_tmul, LinearEquiv.lTensor_tmul,
    coe_twoSidedRestrictedSubmoduleEquivZeroAtFilter_symm, coe_zeroAtFilterCofiniteCongr_apply,
    Equiv.symm_symm, coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter]
  rw [coeff_restrictedMvPowerSeriesBaseChange_tmul,
    coeff_twoSidedToRestrictedSubringLinearEquiv, Equiv.symm_apply_apply]

end Comparison

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (surjective case for `A⟨T, T⁻¹⟩`).** -/
theorem restrictedLaurentSeriesTensorToNull_surjective {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] [(𝓝 (0 : A)).IsCountablyGenerated] {M : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] [TopologicalSpace M] [ContinuousAdd M]
    [IsModuleTopology A M] :
    Function.Surjective (restrictedLaurentSeriesTensorToNull (A := A) (M := M)) :=
  (twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm.surjective.comp <|
    (zeroAtFilterCofiniteCongr A M _).surjective.comp <|
      (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).surjective.comp <|
        restrictedMvPowerSeriesBaseChange_surjective_of_finite.comp <|
          (LinearEquiv.lTensor M _).surjective.comp (TensorProduct.comm A _ M).surjective

section NaturallyComplete

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] {M : Type*} [AddCommGroup M] [Module A M]
  [Module.FinitePresentation A M] [TopologicalSpace M] [ContinuousAdd M] [IsModuleTopology A M]

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (bijective case for `A⟨T, T⁻¹⟩`).** -/
theorem restrictedLaurentSeriesTensorToNull_bijective (hM : IsNaturallyComplete A M) :
    Function.Bijective (restrictedLaurentSeriesTensorToNull (A := A) (M := M)) :=
  (twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm.bijective.comp <|
    (zeroAtFilterCofiniteCongr A M _).bijective.comp <|
      (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).bijective.comp <|
        (restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete hM).comp <|
          (LinearEquiv.lTensor M _).bijective.comp (TensorProduct.comm A _ M).bijective

/-- `restrictedLaurentSeriesTensorToNull_bijective` packaged as an `A`-linear equivalence. -/
noncomputable def restrictedLaurentSeriesTensorToNullEquiv (hM : IsNaturallyComplete A M) :
    twoSidedRestrictedSubmodule A A ⊗[A] M ≃ₗ[A] twoSidedRestrictedSubmodule A M :=
  LinearEquiv.ofBijective restrictedLaurentSeriesTensorToNull
    (restrictedLaurentSeriesTensorToNull_bijective hM)

/-- `restrictedLaurentSeriesTensorToNullEquiv` agrees with the comparison map
`restrictedLaurentSeriesTensorToNull`. -/
@[simp]
theorem restrictedLaurentSeriesTensorToNullEquiv_apply (hM : IsNaturallyComplete A M)
    (x : twoSidedRestrictedSubmodule A A ⊗[A] M) :
    restrictedLaurentSeriesTensorToNullEquiv hM x = restrictedLaurentSeriesTensorToNull x := (rfl)

end NaturallyComplete

end TauCeti.Huber
