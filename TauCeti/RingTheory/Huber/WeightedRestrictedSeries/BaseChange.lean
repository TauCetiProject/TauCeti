/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.BaseChange
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete

/-!
# Base change for completed one-variable restricted series `A⟨T⟩`

Composing `restrictedMvPowerSeriesCompletionSubringAlgEquiv 1 A` with
`restrictedMvPowerSeriesBaseChange` and `Finsupp.uniqueEquiv` yields the comparison
`A⟨T⟩ ⊗[A] M →ₗ[A] c₀(ℕ, M)` sending `f ⊗ₜ v` to `n ↦ restrictedCoeff n f • v`
(`TauCeti.Huber.restrictedPowerSeriesTensorToNull`), which is surjective for finite modules and
bijective (`restrictedPowerSeriesTensorToNullEquiv`) for finitely presented naturally complete
modules over a complete Hausdorff Tate ring (Kedlaya–Liu II, Corollary 2.4.9(c)).

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Corollary 2.4.9(c).
-/

public section

open Filter Topology
open scoped TensorProduct

namespace TauCeti.Huber

section Comparison

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [T0Space A] [NonarchimedeanRing A] {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
  [Module A M] [ContinuousAdd M] [ContinuousSMul A M]

/-- **The natural comparison `A⟨T⟩ ⊗[A] M →ₗ[A] c₀(ℕ, M)`** sending `f ⊗ₜ v` to the null sequence
`n ↦ restrictedCoeff n f • v` (Kedlaya–Liu II, Corollary 2.4.9(c)). -/
noncomputable def restrictedPowerSeriesTensorToNull :
    restrictedMvPowerSeriesCompletion 1 A ⊗[A] M →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ) :=
  (zeroAtFilterCofiniteCongr A M (Finsupp.uniqueEquiv (0 : Fin 1))).toLinearMap ∘ₗ
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).toLinearMap ∘ₗ
    restrictedMvPowerSeriesBaseChange ∘ₗ
    (LinearEquiv.lTensor M
      (restrictedMvPowerSeriesCompletionSubringAlgEquiv 1 A).toLinearEquiv).toLinearMap ∘ₗ
    (TensorProduct.comm A (restrictedMvPowerSeriesCompletion 1 A) M).toLinearMap

/-- On a pure tensor `f ⊗ₜ v`, the `n`-th term is `restrictedCoeff n f • v`. -/
@[simp]
theorem coe_restrictedPowerSeriesTensorToNull_tmul
    (f : restrictedMvPowerSeriesCompletion 1 A) (v : M) (n : ℕ) :
    (restrictedPowerSeriesTensorToNull (f ⊗ₜ[A] v) : ℕ → M) n = restrictedCoeff n f • v := by
  simp only [restrictedPowerSeriesTensorToNull, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.comm_tmul, LinearEquiv.lTensor_tmul, AlgEquiv.toLinearEquiv_apply,
    coe_zeroAtFilterCofiniteCongr_apply, coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter]
  have hsingle : (Finsupp.uniqueEquiv (0 : Fin 1)).symm n = Finsupp.single 0 n :=
    Finsupp.ext fun i ↦ by simp [Subsingleton.elim i 0]
  rw [hsingle, coeff_restrictedMvPowerSeriesBaseChange_tmul,
    coe_restrictedMvPowerSeriesCompletionSubringAlgEquiv, ← restrictedCoeff_apply]

end Comparison

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (surjective case for `A⟨T⟩`).** -/
theorem restrictedPowerSeriesTensorToNull_surjective {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    [(𝓝 (0 : A)).IsCountablyGenerated] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [TopologicalSpace M] [ContinuousAdd M] [IsModuleTopology A M] :
    Function.Surjective (restrictedPowerSeriesTensorToNull (A := A) (M := M)) :=
  (zeroAtFilterCofiniteCongr A M _).surjective.comp <|
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).surjective.comp <|
      restrictedMvPowerSeriesBaseChange_surjective_of_finite.comp <|
        (LinearEquiv.lTensor M _).surjective.comp (TensorProduct.comm A _ M).surjective

section NaturallyComplete

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] {M : Type*} [AddCommGroup M] [Module A M]
  [Module.FinitePresentation A M] [TopologicalSpace M] [ContinuousAdd M] [IsModuleTopology A M]

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (bijective case for `A⟨T⟩`).** -/
theorem restrictedPowerSeriesTensorToNull_bijective (hM : IsNaturallyComplete A M) :
    Function.Bijective (restrictedPowerSeriesTensorToNull (A := A) (M := M)) :=
  (zeroAtFilterCofiniteCongr A M _).bijective.comp <|
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).bijective.comp <|
      (restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete hM).comp <|
        (LinearEquiv.lTensor M _).bijective.comp (TensorProduct.comm A _ M).bijective

/-- `restrictedPowerSeriesTensorToNull_bijective` packaged as an `A`-linear equivalence. -/
noncomputable def restrictedPowerSeriesTensorToNullEquiv (hM : IsNaturallyComplete A M) :
    restrictedMvPowerSeriesCompletion 1 A ⊗[A] M ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ) :=
  LinearEquiv.ofBijective restrictedPowerSeriesTensorToNull
    (restrictedPowerSeriesTensorToNull_bijective hM)

/-- `restrictedPowerSeriesTensorToNullEquiv` agrees with `restrictedPowerSeriesTensorToNull`. -/
@[simp]
theorem restrictedPowerSeriesTensorToNullEquiv_apply (hM : IsNaturallyComplete A M)
    (x : restrictedMvPowerSeriesCompletion 1 A ⊗[A] M) :
    restrictedPowerSeriesTensorToNullEquiv hM x = restrictedPowerSeriesTensorToNull x := (rfl)

end NaturallyComplete

end TauCeti.Huber
