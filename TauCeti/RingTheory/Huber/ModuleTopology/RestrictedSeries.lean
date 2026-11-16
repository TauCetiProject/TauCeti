/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete
public import TauCeti.RingTheory.Huber.Restricted.BaseChange
public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Ring
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
import Mathlib.Logic.Equiv.Nat
import TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# Non-noetherian restricted-series base change and null-sequence comparisons

Over any complete Hausdorff Tate ring `A` (with no noetherian hypothesis), the comparison map
`M ⊗[A] A⟨X₁, …, Xₖ⟩ → M⟨X₁, …, Xₖ⟩` of `TauCeti.RingTheory.Huber.Restricted.BaseChange` is
surjective for every finite `A`-module `M` with its module topology (requiring only that `A` be a
nonarchimedean ring with countably generated neighbourhoods of `0`), and bijective whenever `M` is
finitely presented and naturally complete over `A`
(`TauCeti.Huber.restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete`). Indeed,
natural completeness makes the kernel of any finite free presentation `Aⁿ →[u] Aᵐ →[p] M → 0`
closed, so Henkel's open mapping theorem makes `u` strict onto its image.

Specialising to one-variable restricted power series and two-sided restricted Laurent series yields
Kedlaya–Liu II, Corollary 2.4.9(c), together with the uniform-convergence carrier
`TauCeti.Huber.RestrictedLaurentSeries` for `A⟨T, T⁻¹⟩`.

## Main definitions

* `TauCeti.Huber.zeroAtFilterCofiniteCongr`: reindexing `c₀(ι, M)` along an equivalence `ι ≃ κ`.
* `TauCeti.Huber.restrictedCoeff`: the `n`-th coefficient `A⟨T⟩ →ₗ[A] A` on
  `restrictedMvPowerSeriesCompletion 1 A`.
* `TauCeti.Huber.restrictedPowerSeriesTensorToNull`: the comparison map
  `A⟨T⟩ ⊗[A] M →ₗ[A] c₀(ℕ, M)` sending `f ⊗ₜ v` to `n ↦ restrictedCoeff n f • v`.
* `TauCeti.Huber.restrictedLaurentSeriesTensorToNull`: the Laurent comparison map
  `A⟨T, T⁻¹⟩ ⊗[A] M →ₗ[A] M⟨T, T⁻¹⟩` sending `f ⊗ₜ v` to `n ↦ f n • v` for `n : ℤ`.
* `TauCeti.Huber.RestrictedLaurentSeries`: the commutative `A`-algebra `A⟨T, T⁻¹⟩` equipped with
  the uniformity of uniform convergence of coefficients.

## Main results

* `TauCeti.Huber.exists_retract_zeroAtFilterSubmodule_nat`: for countable `ι`, `c₀(ι, M)` is an
  `A`-linear retract of `c₀(ℕ, M)`.
* `TauCeti.Huber.restrictedMvPowerSeriesBaseChange_surjective_of_finite` and
  `TauCeti.Huber.restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete`.
* `TauCeti.Huber.restrictedPowerSeriesTensorToNull_surjective`,
  `TauCeti.Huber.restrictedPowerSeriesTensorToNull_bijective`,
  `TauCeti.Huber.restrictedLaurentSeriesTensorToNull_surjective`, and
  `TauCeti.Huber.restrictedLaurentSeriesTensorToNull_bijective`: Corollary 2.4.9(c).

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Corollary 2.4.9(c).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.49, Example 6.39, and Remark 8.29.
-/

public section

open Filter Topology
open scoped TensorProduct Uniformity

namespace TauCeti.Huber

/-! ### Reindexing and countable retracts of null-family modules -/

section NullFamilies

/-- Reindexing along an equivalence `e : ι ≃ κ` identifies the `A`-modules of `M`-valued null
families along `Filter.cofinite`. -/
def zeroAtFilterCofiniteCongr (A M : Type*) [Semiring A] [AddCommMonoid M] [TopologicalSpace M]
    [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] {ι κ : Type*} (e : ι ≃ κ) :
    Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι) ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter κ) where
  toFun f := ⟨fun k ↦ (f : ι → M) (e.symm k),
    Filter.Tendsto.comp f.2 e.symm.injective.tendsto_cofinite⟩
  invFun g := ⟨fun i ↦ (g : κ → M) (e i),
    Filter.Tendsto.comp g.2 e.injective.tendsto_cofinite⟩
  left_inv f := Subtype.ext <| funext fun i ↦ congrArg (f : ι → M) (e.symm_apply_apply i)
  right_inv g := Subtype.ext <| funext fun k ↦ congrArg (g : κ → M) (e.apply_symm_apply k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_zeroAtFilterCofiniteCongr_apply {A M : Type*} [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] {ι κ : Type*}
    (e : ι ≃ κ) (f : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι))
    (k : κ) :
    (zeroAtFilterCofiniteCongr A M e f : κ → M) k = (f : ι → M) (e.symm k) := (rfl)

@[simp]
theorem coe_zeroAtFilterCofiniteCongr_symm_apply {A M : Type*} [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] {ι κ : Type*}
    (e : ι ≃ κ) (g : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter κ))
    (i : ι) :
    ((zeroAtFilterCofiniteCongr A M e).symm g : ι → M) i = (g : κ → M) (e i) := (rfl)

/-- Unfolding `restrictedMvPowerSeriesSubmodule k A M` as `Filter.zeroAtFilterSubmodule` at
`Filter.cofinite` on `Fin k →₀ ℕ`. -/
def restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter (k : ℕ) (A M : Type*) [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] :
    restrictedMvPowerSeriesSubmodule k A M ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter (Fin k →₀ ℕ)) where
  toFun f := ⟨(f.1 : (Fin k →₀ ℕ) → M),
    isRestricted_iff.mp (mem_restrictedMvPowerSeriesSubmodule.mp f.2)⟩
  invFun g := ⟨(g : (Fin k →₀ ℕ) → M),
    mem_restrictedMvPowerSeriesSubmodule.mpr (isRestricted_iff.mpr g.2)⟩
  left_inv _ := rfl; right_inv _ := rfl; map_add' _ _ := rfl; map_smul' _ _ := rfl

@[simp]
theorem coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter {k : ℕ} {A M : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] (f : restrictedMvPowerSeriesSubmodule k A M) :
    ((restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter k A M f :
        Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter (Fin k →₀ ℕ))) :
      (Fin k →₀ ℕ) → M) = (f.1 : (Fin k →₀ ℕ) → M) := (rfl)

@[simp]
theorem coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter_symm {k : ℕ} {A M : Type*}
    [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M]
    (g : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter (Fin k →₀ ℕ))) :
    (((restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter k A M).symm g).1 : (Fin k →₀ ℕ) → M) =
      (g : (Fin k →₀ ℕ) → M) := (rfl)

/-- Unfolding `twoSidedRestrictedSubmodule A M` as `Filter.zeroAtFilterSubmodule` at
`Filter.cofinite` on `ℤ`. -/
def twoSidedRestrictedSubmoduleEquivZeroAtFilter (A M : Type*) [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] :
    twoSidedRestrictedSubmodule A M ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℤ) where
  toFun f := ⟨(f : ℤ → M), mem_twoSidedRestrictedSubmodule.mp f.2⟩
  invFun g := ⟨(g : ℤ → M), mem_twoSidedRestrictedSubmodule.mpr g.2⟩
  left_inv _ := rfl; right_inv _ := rfl; map_add' _ _ := rfl; map_smul' _ _ := rfl

@[simp]
theorem coe_twoSidedRestrictedSubmoduleEquivZeroAtFilter {A M : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] (f : twoSidedRestrictedSubmodule A M) :
    ((twoSidedRestrictedSubmoduleEquivZeroAtFilter A M f :
        Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℤ)) : ℤ → M) =
      (f : ℤ → M) := (rfl)

@[simp]
theorem coe_twoSidedRestrictedSubmoduleEquivZeroAtFilter_symm {A M : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M]
    (g : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℤ)) :
    (((twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm g :
        twoSidedRestrictedSubmodule A M) : ℤ → M) = (g : ℤ → M) := (rfl)

/-- For any countable index type `ι`, the module of `ι`-indexed null families is an `A`-linear
retract of the module of `ℕ`-indexed null families: choose an injection `ι → ℕ`, extend outside its
image by `0`, and restrict back. -/
theorem exists_retract_zeroAtFilterSubmodule_nat (A M ι : Type*) [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] [Countable ι] :
    ∃ (emb : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι) →ₗ[A]
          Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ))
      (proj : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ) →ₗ[A]
          Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι)),
      proj ∘ₗ emb = LinearMap.id := by
  classical
  obtain ⟨j, hj⟩ := Countable.exists_injective_nat ι
  let emb : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι) →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ) :=
    { toFun := fun f ↦
        ⟨fun n ↦ if h : ∃ i, j i = n then (f : ι → M) h.choose else 0, fun U hU ↦ by
          rw [Filter.mem_map, Filter.mem_cofinite]
          refine ((Filter.mem_cofinite.mp (Filter.mem_map.mp (f.2 hU))).image j).subset
            fun n hn ↦ ?_
          simp only [Set.mem_preimage, Set.mem_compl_iff] at hn
          by_cases h : ∃ i, j i = n
          · exact ⟨h.choose, by simpa [h] using hn, h.choose_spec⟩
          · exact absurd (by simpa [h] using mem_of_mem_nhds hU) hn⟩
      map_add' := fun _ _ ↦ Subtype.ext <| funext fun n ↦ by by_cases h : ∃ i, j i = n <;> simp [h]
      map_smul' := fun _ _ ↦ Subtype.ext <| funext fun n ↦ by
        by_cases h : ∃ i, j i = n <;> simp [h] }
  let proj : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ) →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι) :=
    { toFun := fun g ↦ ⟨fun i ↦ (g : ℕ → M) (j i), Filter.Tendsto.comp g.2 hj.tendsto_cofinite⟩
      map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  refine ⟨emb, proj, LinearMap.ext fun f ↦ Subtype.ext <| funext fun i ↦ ?_⟩
  dsimp [proj, emb]; split_ifs with h'
  · exact congrArg (f : ι → M) (hj h'.choose_spec)
  · exact absurd ⟨i, rfl⟩ h'

end NullFamilies

/-! ### Non-noetherian restricted power-series base change over a complete Tate ring -/

section BaseChangeNonNoetherian

/-- **Surjectivity of `M ⊗[A] A⟨T₁, …, Tₖ⟩ → M⟨T₁, …, Tₖ⟩` without noetherianity**
(Kedlaya–Liu II, Corollary 2.4.9(c), surjectivity half). Over any nonarchimedean commutative ring
`A` with countably generated neighbourhoods of `0`, the restricted power-series comparison map is
surjective for every finitely generated `A`-module `M` endowed with its module topology. -/
theorem restrictedMvPowerSeriesBaseChange_surjective_of_finite {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] [(𝓝 (0 : A)).IsCountablyGenerated] {M : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] [TopologicalSpace M] [ContinuousAdd M]
    [IsModuleTopology A M] :
    Function.Surjective (restrictedMvPowerSeriesBaseChange :
      M ⊗[A] restrictedMvPowerSeriesSubring k A → restrictedMvPowerSeriesSubmodule k A M) := by
  obtain ⟨m, p, hsurj⟩ := Module.Finite.exists_fin' A M
  exact restrictedMvPowerSeriesBaseChange_surjective_of_presentation p
    (IsModuleTopology.continuous_of_linearMap p).continuousAt hsurj
    (map_zero p ▸ (IsModuleTopology.isOpenMap_of_surjective hsurj).nhds_le 0)

section Tate

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M] [ContinuousAdd M]
  [IsModuleTopology A M]

/-- **Bijectivity of `M ⊗[A] A⟨T₁, …, Tₖ⟩ → M⟨T₁, …, Tₖ⟩` for finitely presented naturally
complete modules** (Kedlaya–Liu II, Corollary 2.4.9(c), bijectivity half). Over a complete
Hausdorff Tate ring `A`, natural completeness of `M` makes the relation map of any finite free
presentation strict onto its image by the open mapping theorem, supplying both halves of Remark 8.29
with no noetherian hypothesis on `A`. -/
theorem restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete
    [Module.FinitePresentation A M] (hM : IsNaturallyComplete A M) :
    Function.Bijective (restrictedMvPowerSeriesBaseChange :
      M ⊗[A] restrictedMvPowerSeriesSubring k A → restrictedMvPowerSeriesSubmodule k A M) := by
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : FirstCountableTopology A := UniformSpace.firstCountableTopology A
  obtain ⟨m, n, p, u, hsurj, hexact⟩ := Module.FinitePresentation.exists_fin' A M
  have hu := IsModuleTopology.continuous_of_linearMap u
  have hp := IsModuleTopology.continuous_of_linearMap p
  have hstrict : Topology.IsStrictMap u := u.isStrictMap_of_isClosed_range_of_isTateRing
    hu.continuousAt ((LinearMap.exact_iff.mp hexact).symm ▸
      (isNaturallyComplete_iff_isClosed_ker hsurj).mp hM)
  exact ⟨restrictedMvPowerSeriesBaseChange_injective_of_presentation u hu.continuousAt p
      hp.continuousAt hsurj (LinearMap.exact_iff.mp hexact).symm (map_zero u.rangeRestrict ▸
        (LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp hstrict).isOpenMap.nhds_le 0),
    restrictedMvPowerSeriesBaseChange_surjective_of_presentation p hp.continuousAt hsurj
      (map_zero p ▸ (IsModuleTopology.isOpenMap_of_surjective hsurj).nhds_le 0)⟩

/-- `restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete` packaged as an `A`-linear
equivalence. -/
noncomputable def restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete
    [Module.FinitePresentation A M] (hM : IsNaturallyComplete A M) :
    M ⊗[A] restrictedMvPowerSeriesSubring k A ≃ₗ[A] restrictedMvPowerSeriesSubmodule k A M :=
  LinearEquiv.ofBijective restrictedMvPowerSeriesBaseChange
    (restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete hM)

@[simp]
theorem restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply
    [Module.FinitePresentation A M] (hM : IsNaturallyComplete A M)
    (x : M ⊗[A] restrictedMvPowerSeriesSubring k A) :
    restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete hM x =
      restrictedMvPowerSeriesBaseChange x := (rfl)

end Tate

end BaseChangeNonNoetherian

/-! ### Coefficients and null-sequence comparison for `A⟨T⟩` -/

section OneVariablePowerSeries

/-- The `A`-algebra isomorphism `A⟨X₁, …, Xₖ⟩ ≃ₐ[A] restrictedMvPowerSeriesSubring k A` over a
complete Hausdorff nonarchimedean base. -/
noncomputable def restrictedMvPowerSeriesCompletionSubringAlgEquiv (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] :
    restrictedMvPowerSeriesCompletion k A ≃ₐ[A] restrictedMvPowerSeriesSubring k A :=
  (restrictedMvPowerSeriesCompletionAlgEquiv k A).trans <|
    AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr weightedRestrictedSubring_one_weight)
      subringCongr_one_weight_weightedC

@[simp]
theorem coe_restrictedMvPowerSeriesCompletionSubringAlgEquiv (k : ℕ) {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    (f : restrictedMvPowerSeriesCompletion k A) :
    ((restrictedMvPowerSeriesCompletionSubringAlgEquiv k A f : restrictedMvPowerSeriesSubring k A) :
        MvPowerSeries (Fin k) A) =
      ((restrictedMvPowerSeriesCompletionEquiv k A f :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          MvPowerSeries (Fin k) A) := by
  simp [restrictedMvPowerSeriesCompletionSubringAlgEquiv]

/-- **The `n`-th coefficient `A⟨T⟩ →ₗ[A] A`** of a one-variable completed restricted power series,
read through `restrictedMvPowerSeriesCompletionEquiv`. -/
noncomputable def restrictedCoeff {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] (n : ℕ) :
    restrictedMvPowerSeriesCompletion 1 A →ₗ[A] A where
  toFun f := MvPowerSeries.coeff (Finsupp.single 0 n)
    ((restrictedMvPowerSeriesCompletionEquiv 1 A f :
      weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
        MvPowerSeries (Fin 1) A)
  map_add' f g := by simp [map_add]
  map_smul' a f := by
    have hsmul := map_smul (restrictedMvPowerSeriesCompletionAlgEquiv 1 A) a f
    rw [coe_restrictedMvPowerSeriesCompletionAlgEquiv] at hsmul
    rw [hsmul]; simp [Algebra.smul_def]

@[simp]
theorem restrictedCoeff_coe {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] (n : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedCoeff n (f : restrictedMvPowerSeriesCompletion 1 A) =
      MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) A) := by
  simp [restrictedCoeff]

theorem restrictedCoeff_algebraMap {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] (n : ℕ) (a : A) :
    restrictedCoeff n (algebraMap A (restrictedMvPowerSeriesCompletion 1 A) a) =
      if n = 0 then a else 0 := by
  change restrictedCoeff n ((weightedC _ isWeightFamily_one_weight a :
    weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
      restrictedMvPowerSeriesCompletion 1 A) = _
  rw [restrictedCoeff_coe, coe_weightedC, MvPowerSeries.coeff_C]
  simp [Finsupp.single_eq_zero (a := (0 : Fin 1))]

/-- On the variable `T` (`weightedX _ isWeightFamily_one_weight 0`), `restrictedCoeff n` returns `1`
for `n = 1` and `0` otherwise. -/
theorem restrictedCoeff_weightedX {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] (n : ℕ) :
    restrictedCoeff n
        ((weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion 1 A) =
      if n = 1 then 1 else 0 := by
  rw [restrictedCoeff_coe, coe_weightedX, MvPowerSeries.coeff_X]; simp

theorem uniformContinuous_restrictedCoeff {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] (n : ℕ) :
    UniformContinuous (restrictedCoeff (A := A) n) :=
  (uniformContinuous_coeff_one_weight (Finsupp.single 0 n)).comp
    uniformContinuous_restrictedMvPowerSeriesCompletionEquiv

theorem continuous_restrictedCoeff {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] (n : ℕ) :
    Continuous (restrictedCoeff (A := A) n) :=
  (uniformContinuous_restrictedCoeff n).continuous

/-- **The natural comparison `A⟨T⟩ ⊗[A] M →ₗ[A] c₀(ℕ, M)`** sending `f ⊗ₜ v` to the null sequence
`n ↦ restrictedCoeff n f • v` (Kedlaya–Liu II, Corollary 2.4.9(c)). -/
noncomputable def restrictedPowerSeriesTensorToNull {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] {M : Type*}
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousSMul A M] :
    restrictedMvPowerSeriesCompletion 1 A ⊗[A] M →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ) :=
  (zeroAtFilterCofiniteCongr A M (Finsupp.uniqueEquiv (0 : Fin 1))).toLinearMap ∘ₗ
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).toLinearMap ∘ₗ
    restrictedMvPowerSeriesBaseChange ∘ₗ
    (LinearEquiv.lTensor M
      (restrictedMvPowerSeriesCompletionSubringAlgEquiv 1 A).toLinearEquiv).toLinearMap ∘ₗ
    (TensorProduct.comm A (restrictedMvPowerSeriesCompletion 1 A) M).toLinearMap

@[simp]
theorem coe_restrictedPowerSeriesTensorToNull_tmul {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] {M : Type*}
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousSMul A M]
    (f : restrictedMvPowerSeriesCompletion 1 A) (v : M) (n : ℕ) :
    (restrictedPowerSeriesTensorToNull (f ⊗ₜ[A] v) : ℕ → M) n = restrictedCoeff n f • v := by
  simp only [restrictedPowerSeriesTensorToNull, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.comm_tmul, LinearEquiv.lTensor_tmul, AlgEquiv.toLinearEquiv_apply,
    coe_zeroAtFilterCofiniteCongr_apply, coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter]
  have hsingle : (Finsupp.uniqueEquiv (0 : Fin 1)).symm n = Finsupp.single 0 n :=
    Finsupp.ext fun i ↦ by simp [Subsingleton.elim i 0]
  rw [hsingle, coeff_restrictedMvPowerSeriesBaseChange_tmul,
    coe_restrictedMvPowerSeriesCompletionSubringAlgEquiv]; rfl

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

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (bijective case for `A⟨T⟩`).** -/
theorem restrictedPowerSeriesTensorToNull_bijective {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [TopologicalSpace M]
    [ContinuousAdd M] [IsModuleTopology A M] (hM : IsNaturallyComplete A M) :
    Function.Bijective (restrictedPowerSeriesTensorToNull (A := A) (M := M)) :=
  (zeroAtFilterCofiniteCongr A M _).bijective.comp <|
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).bijective.comp <|
      (restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete hM).comp <|
        (LinearEquiv.lTensor M _).bijective.comp (TensorProduct.comm A _ M).bijective

/-- `restrictedPowerSeriesTensorToNull_bijective` packaged as an `A`-linear equivalence. -/
noncomputable def restrictedPowerSeriesTensorToNullEquiv {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [TopologicalSpace M]
    [ContinuousAdd M] [IsModuleTopology A M] (hM : IsNaturallyComplete A M) :
    restrictedMvPowerSeriesCompletion 1 A ⊗[A] M ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ) :=
  LinearEquiv.ofBijective restrictedPowerSeriesTensorToNull
    (restrictedPowerSeriesTensorToNull_bijective hM)

end OneVariablePowerSeries

/-! ### Null-sequence comparison and uniform carrier for `A⟨T, T⁻¹⟩` -/

section LaurentSeries

/-- Bijection between `ℤ` and one-variable exponents `Fin 1 →₀ ℕ`. -/
noncomputable def intEquivFinOneFinsupp : ℤ ≃ (Fin 1 →₀ ℕ) :=
  Equiv.intEquivNat.trans (Finsupp.uniqueEquiv (0 : Fin 1)).symm

/-- `A`-linear equivalence between `twoSidedRestrictedSubmodule A A` and
`restrictedMvPowerSeriesSubring 1 A`, reindexing coefficients along `intEquivFinOneFinsupp`. -/
noncomputable def twoSidedToRestrictedSubringLinearEquiv (A : Type*) [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] :
    twoSidedRestrictedSubmodule A A ≃ₗ[A] restrictedMvPowerSeriesSubring 1 A :=
  twoSidedRestrictedSubmoduleEquivZeroAtFilter A A ≪≫ₗ
    zeroAtFilterCofiniteCongr A A intEquivFinOneFinsupp ≪≫ₗ
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A A).symm ≪≫ₗ
    (restrictedMvPowerSeriesSubringLinearEquiv 1 A).symm

@[simp]
theorem coeff_twoSidedToRestrictedSubringLinearEquiv {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] (f : twoSidedRestrictedSubmodule A A)
    (ν : Fin 1 →₀ ℕ) :
    MvPowerSeries.coeff ν
        (twoSidedToRestrictedSubringLinearEquiv A f : MvPowerSeries (Fin 1) A) =
      (f : ℤ → A) (intEquivFinOneFinsupp.symm ν) := by
  rw [MvPowerSeries.coeff_apply]; dsimp [twoSidedToRestrictedSubringLinearEquiv]
  rw [coe_restrictedMvPowerSeriesSubringLinearEquiv_symm]
  exact congrFun (coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter_symm _) ν

/-- **The natural Laurent comparison `A⟨T, T⁻¹⟩ ⊗[A] M →ₗ[A] M⟨T, T⁻¹⟩`** sending `f ⊗ₜ v` to the
two-sided null family `n ↦ f n • v` (Kedlaya–Liu II, Corollary 2.4.9(c)). -/
noncomputable def restrictedLaurentSeriesTensorToNull {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousSMul A M] :
    twoSidedRestrictedSubmodule A A ⊗[A] M →ₗ[A] twoSidedRestrictedSubmodule A M :=
  (twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm.toLinearMap ∘ₗ
    (zeroAtFilterCofiniteCongr A M intEquivFinOneFinsupp.symm).toLinearMap ∘ₗ
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).toLinearMap ∘ₗ
    restrictedMvPowerSeriesBaseChange ∘ₗ
    (LinearEquiv.lTensor M (twoSidedToRestrictedSubringLinearEquiv A)).toLinearMap ∘ₗ
    (TensorProduct.comm A (twoSidedRestrictedSubmodule A A) M).toLinearMap

@[simp]
theorem restrictedLaurentSeriesTensorToNull_tmul {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousSMul A M]
    (f : twoSidedRestrictedSubmodule A A) (v : M) (n : ℤ) :
    (restrictedLaurentSeriesTensorToNull (f ⊗ₜ[A] v) : ℤ → M) n = (f : ℤ → A) n • v := by
  simp only [restrictedLaurentSeriesTensorToNull, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, TensorProduct.comm_tmul, LinearEquiv.lTensor_tmul,
    coe_twoSidedRestrictedSubmoduleEquivZeroAtFilter_symm, coe_zeroAtFilterCofiniteCongr_apply,
    Equiv.symm_symm, coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter]
  rw [coeff_restrictedMvPowerSeriesBaseChange_tmul,
    coeff_twoSidedToRestrictedSubringLinearEquiv, Equiv.symm_apply_apply]

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

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (bijective case for `A⟨T, T⁻¹⟩`).** -/
theorem restrictedLaurentSeriesTensorToNull_bijective {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [TopologicalSpace M]
    [ContinuousAdd M] [IsModuleTopology A M] (hM : IsNaturallyComplete A M) :
    Function.Bijective (restrictedLaurentSeriesTensorToNull (A := A) (M := M)) :=
  (twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm.bijective.comp <|
    (zeroAtFilterCofiniteCongr A M _).bijective.comp <|
      (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).bijective.comp <|
        (restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete hM).comp <|
          (LinearEquiv.lTensor M _).bijective.comp (TensorProduct.comm A _ M).bijective

/-- `restrictedLaurentSeriesTensorToNull_bijective` packaged as an `A`-linear equivalence. -/
noncomputable def restrictedLaurentSeriesTensorToNullEquiv {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [TopologicalSpace M]
    [ContinuousAdd M] [IsModuleTopology A M] (hM : IsNaturallyComplete A M) :
    twoSidedRestrictedSubmodule A A ⊗[A] M ≃ₗ[A] twoSidedRestrictedSubmodule A M :=
  LinearEquiv.ofBijective restrictedLaurentSeriesTensorToNull
    (restrictedLaurentSeriesTensorToNull_bijective hM)

/-- **The ring `A⟨T, T⁻¹⟩` of restricted Laurent series equipped with uniform coefficient
convergence.** Defined as a wrapper around `twoSidedRestrictedSubmodule A A` so its uniform
structure does not conflict with the pointwise-convergence subspace uniformity on
`twoSidedRestrictedSubmodule A A ⊆ (ℤ → A)`. -/
structure RestrictedLaurentSeries (A : Type*) [Semiring A] [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousConstSMul A A] where
  /-- The underlying two-sided restricted series. -/
  toTwoSided : twoSidedRestrictedSubmodule A A

namespace RestrictedLaurentSeries

@[ext]
theorem ext {A : Type*} [Semiring A] [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousConstSMul A A] {f g : RestrictedLaurentSeries A} (h : f.toTwoSided = g.toTwoSided) :
    f = g := by cases f; cases g; exact congrArg mk h

section Module

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

instance : AddCommGroup (RestrictedLaurentSeries A) where
  zero := ⟨0⟩; add f g := ⟨f.1 + g.1⟩; neg f := ⟨-f.1⟩; sub f g := ⟨f.1 - g.1⟩
  nsmul n f := ⟨n • f.1⟩; zsmul n f := ⟨n • f.1⟩
  add_assoc _ _ _ := congrArg mk (add_assoc _ _ _); zero_add _ := congrArg mk (zero_add _)
  add_zero _ := congrArg mk (add_zero _); nsmul_zero _ := congrArg mk (zero_smul ℕ _)
  nsmul_succ n f := congrArg mk (succ_nsmul f.1 n); zsmul_zero' _ := congrArg mk (zero_smul ℤ _)
  zsmul_succ' n f := congrArg mk (SubNegMonoid.zsmul_succ' n f.1)
  zsmul_neg' n f := congrArg mk (SubNegMonoid.zsmul_neg' n f.1)
  neg_add_cancel _ := congrArg mk (neg_add_cancel _); add_comm _ _ := congrArg mk (add_comm _ _)
  sub_eq_add_neg _ _ := congrArg mk (sub_eq_add_neg _ _)

instance : Module A (RestrictedLaurentSeries A) where
  smul a f := ⟨a • f.1⟩; one_smul _ := congrArg mk (one_smul _ _)
  mul_smul _ _ _ := congrArg mk (mul_smul _ _ _); smul_zero _ := congrArg mk (smul_zero _)
  smul_add _ _ _ := congrArg mk (smul_add _ _ _); add_smul _ _ _ := congrArg mk (add_smul _ _ _)
  zero_smul _ := congrArg mk (zero_smul _ _)

@[simp] theorem toTwoSided_zero : (0 : RestrictedLaurentSeries A).toTwoSided = 0 := rfl
@[simp] theorem toTwoSided_add (f g : RestrictedLaurentSeries A) :
    (f + g).toTwoSided = f.toTwoSided + g.toTwoSided := rfl
@[simp] theorem toTwoSided_neg (f : RestrictedLaurentSeries A) :
    (-f).toTwoSided = -f.toTwoSided := rfl
@[simp] theorem toTwoSided_sub (f g : RestrictedLaurentSeries A) :
    (f - g).toTwoSided = f.toTwoSided - g.toTwoSided := rfl
@[simp] theorem toTwoSided_smul (a : A) (f : RestrictedLaurentSeries A) :
    (a • f).toTwoSided = a • f.toTwoSided := rfl

/-- The tautological `A`-linear equivalence `RestrictedLaurentSeries A ≃ₗ[A]
twoSidedRestrictedSubmodule A A`. -/
def toTwoSidedLinearEquiv (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    RestrictedLaurentSeries A ≃ₗ[A] twoSidedRestrictedSubmodule A A where
  toFun := toTwoSided; invFun := mk
  left_inv _ := rfl; right_inv _ := rfl; map_add' _ _ := rfl; map_smul' _ _ := rfl

/-- Coefficient-reindexing `A`-linear equivalence between `RestrictedLaurentSeries A` and the
one-variable trivial-weight restricted power-series ring. -/
noncomputable def toWeightedLinearEquiv (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] :
    RestrictedLaurentSeries A ≃ₗ[A]
      weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  toTwoSidedLinearEquiv A ≪≫ₗ twoSidedToRestrictedSubringLinearEquiv A ≪≫ₗ
    (AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr (weightedRestrictedSubring_one_weight (k := 1) (A := A)))
      subringCongr_one_weight_weightedC).symm.toLinearEquiv

end Module

section Algebra

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]

/-- The uniform structure of uniform convergence of coefficients on `RestrictedLaurentSeries A`,
pulled back along `toWeightedLinearEquiv`. -/
noncomputable instance instUniformSpace : UniformSpace (RestrictedLaurentSeries A) :=
  UniformSpace.comap (toWeightedLinearEquiv A) inferInstance

/-- `toWeightedLinearEquiv` as a uniform equivalence. -/
noncomputable def toWeightedUniformEquiv (A : Type*) [CommRing A] [UniformSpace A]
    [NonarchimedeanRing A] :
    RestrictedLaurentSeries A ≃ᵤ
      weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight where
  toEquiv := (toWeightedLinearEquiv A).toEquiv
  uniformContinuous_toFun := uniformContinuous_comap
  uniformContinuous_invFun := uniformContinuous_iff_le_comap.mpr <| by
    dsimp [instUniformSpace]; rw [← UniformSpace.comap_comap]
    have hcomp : ⇑(toWeightedLinearEquiv A) ∘ ⇑(toWeightedLinearEquiv A).symm = id :=
      funext (toWeightedLinearEquiv A).apply_symm_apply
    rw [hcomp, UniformSpace.comap_id]; exact le_rfl

theorem uniformContinuous_toWeightedLinearEquiv (A : Type*) [CommRing A] [UniformSpace A]
    [NonarchimedeanRing A] : UniformContinuous (toWeightedLinearEquiv A) :=
  (toWeightedUniformEquiv A).uniformContinuous_toFun

theorem uniformContinuous_toWeightedLinearEquiv_symm (A : Type*) [CommRing A] [UniformSpace A]
    [NonarchimedeanRing A] : UniformContinuous (toWeightedLinearEquiv A).symm :=
  (toWeightedUniformEquiv A).uniformContinuous_invFun

noncomputable instance : IsUniformAddGroup (RestrictedLaurentSeries A) where
  uniformContinuous_sub := uniformContinuous_comap' <| by
    have hsub : ⇑(toWeightedLinearEquiv A) ∘
          (fun p : RestrictedLaurentSeries A × RestrictedLaurentSeries A ↦ p.1 - p.2) =
        (fun q ↦ q.1 - q.2) ∘ Prod.map (toWeightedLinearEquiv A) (toWeightedLinearEquiv A) :=
      funext fun ⟨f, g⟩ ↦ map_sub (toWeightedLinearEquiv A) f g
    rw [hsub]
    exact uniformContinuous_sub.comp (uniformContinuous_comap.prodMap uniformContinuous_comap)

instance [CompleteSpace A] : CompleteSpace (RestrictedLaurentSeries A) :=
  (toWeightedUniformEquiv A).completeSpace_iff.mpr inferInstance

instance [T0Space A] : T2Space (RestrictedLaurentSeries A) :=
  have : T2Space
      (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :=
    inferInstance
  .of_injective_continuous (toWeightedLinearEquiv A).injective
    (toWeightedUniformEquiv A).continuous

instance [(𝓝 (0 : A)).IsCountablyGenerated] :
    (𝓤 (RestrictedLaurentSeries A)).IsCountablyGenerated := by
  have : (𝓤 (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
      isWeightFamily_one_weight)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  exact Filter.comap.isCountablyGenerated _ _

noncomputable instance [CompleteSpace A] [T0Space A] : CommRing (RestrictedLaurentSeries A) :=
  { (inferInstance : AddCommGroup (RestrictedLaurentSeries A)) with
    one := ⟨1⟩
    mul f g := ⟨f.1 * g.1⟩
    npow n f := ⟨f.1 ^ n⟩
    natCast n := ⟨n⟩
    intCast n := ⟨n⟩
    mul_assoc _ _ _ := congrArg mk (mul_assoc _ _ _)
    one_mul _ := congrArg mk (one_mul _)
    mul_one _ := congrArg mk (mul_one _)
    left_distrib _ _ _ := congrArg mk (left_distrib _ _ _)
    right_distrib _ _ _ := congrArg mk (right_distrib _ _ _)
    zero_mul _ := congrArg mk (zero_mul _)
    mul_zero _ := congrArg mk (mul_zero _)
    npow_zero _ := congrArg mk (pow_zero _)
    npow_succ _ _ := congrArg mk (pow_succ _ _)
    natCast_zero := congrArg mk Nat.cast_zero
    natCast_succ _ := congrArg mk (Nat.cast_succ _)
    intCast_ofNat _ := congrArg mk (Int.cast_natCast _)
    intCast_negSucc _ := congrArg mk (Int.cast_negSucc _)
    mul_comm _ _ := congrArg mk (mul_comm _ _) }

noncomputable instance [CompleteSpace A] [T0Space A] : Algebra A (RestrictedLaurentSeries A) :=
  Algebra.ofModule (fun r x y ↦ congrArg mk (Algebra.smul_mul_assoc r x.1 y.1))
    (fun r x y ↦ congrArg mk (Algebra.mul_smul_comm r x.1 y.1))

@[simp] theorem toTwoSided_one [CompleteSpace A] [T0Space A] :
    (1 : RestrictedLaurentSeries A).toTwoSided = 1 := rfl
@[simp] theorem toTwoSided_mul [CompleteSpace A] [T0Space A] (f g : RestrictedLaurentSeries A) :
    (f * g).toTwoSided = f.toTwoSided * g.toTwoSided := rfl
@[simp] theorem toTwoSided_pow [CompleteSpace A] [T0Space A] (f : RestrictedLaurentSeries A)
    (n : ℕ) : (f ^ n).toTwoSided = f.toTwoSided ^ n := rfl
@[simp] theorem toTwoSided_algebraMap [CompleteSpace A] [T0Space A] (r : A) :
    (algebraMap A (RestrictedLaurentSeries A) r).toTwoSided =
      algebraMap A (twoSidedRestrictedSubmodule A A) r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]; rfl

end Algebra

end RestrictedLaurentSeries

end LaurentSeries

end TauCeti.Huber
