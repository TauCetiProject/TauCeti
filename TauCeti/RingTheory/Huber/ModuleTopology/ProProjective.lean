/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.PseudoFlat
public import TauCeti.RingTheory.Huber.Restricted.BaseChange
public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Ring
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Logic.Equiv.Nat
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# Pro-projective modules, restricted series, and base change to null sequences

Let `A` be a complete Hausdorff Tate ring. Kedlaya and Liu (*Relative p-adic Hodge theory, II*,
§2.4, Definition 2.4.6, Lemma 2.4.7, and Corollaries 2.4.8–2.4.9) introduce *pro-projective*
topological `A`-modules as a unified source of `2`-pseudoflat modules encompassing both finite
projective modules and algebras of restricted power and Laurent series.

In Kedlaya–Liu's Banach setting, a pro-projective module `B` is a complete Banach `A`-module
carrying a compatible sequence of uniformly bounded continuous `A`-linear projectors `πₖ : B → B`
with finite projective images converging pointwise to the identity, where the summands admit
uniformly bounded coordinate splittings. In the norm-free topological setting of Huber rings used
throughout `TauCeti.Huber`, a sequence of continuous projectors onto finite projective summands
without uniform splitting bounds can have unbounded open-mapping constants across degrees; the
norm-free counterpart of uniform coordinate splittings is that `B` is an `A`-linear retract of the
module `c₀(ℕ, A)` (`Filter.zeroAtFilterSubmodule A Filter.cofinite`) of null sequences in `A`.
`TauCeti.Huber.IsProProjective` records completeness, the Hausdorff property (ruling out indiscrete
modules, on which `πₖ = 0` converges to every element), a countably generated uniformity, the
compatible projector sequence `πₖ`, and the null-sequence retraction.

The engine behind both `Tor₁`-vanishing for pro-projective modules and the null-sequence base-change
isomorphisms is `TauCeti.Huber.restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete`:
over any complete Hausdorff Tate ring `A` (with no noetherian hypothesis), the comparison map
`M ⊗[A] A⟨X₁, …, Xₖ⟩ → M⟨X₁, …, Xₖ⟩` of `TauCeti.RingTheory.Huber.Restricted.BaseChange` is
surjective for every finite `A`-module `M` with its module topology (requiring only that `A` be a
nonarchimedean ring with countably generated neighbourhoods of `0`), and bijective whenever `M` is
finitely presented and naturally complete over a complete Hausdorff Tate ring `A`. Indeed, natural
completeness of `M` makes the kernel of any finite free presentation `Aⁿ →[u] Aᵐ →[p] M → 0`
closed in `Aᵐ`, so Henkel's open mapping theorem
(`LinearMap.isStrictMap_of_isClosed_range_of_isTateRing`) makes `u` strict onto its image,
supplying the input of `restrictedMvPowerSeriesBaseChange_injective_of_presentation`.

## Main definitions

* `TauCeti.Huber.restrictedCoeff`: the `n`-th coefficient `A⟨T⟩ →ₗ[A] A` on
  `restrictedMvPowerSeriesCompletion 1 A`.
* `TauCeti.Huber.restrictedPowerSeriesTensorToNull`: the comparison map
  `A⟨T⟩ ⊗[A] M →ₗ[A] c₀(ℕ, M)` sending `f ⊗ₜ v` to `n ↦ restrictedCoeff n f • v`.
* `TauCeti.Huber.restrictedLaurentSeriesTensorToNull`: the two-sided Laurent comparison map
  `A⟨T, T⁻¹⟩ ⊗[A] M →ₗ[A] M⟨T, T⁻¹⟩` sending `f ⊗ₜ v` to `n ↦ f n • v` for `n : ℤ`.
* `TauCeti.Huber.RestrictedLaurentSeries`: the commutative `A`-algebra `A⟨T, T⁻¹⟩` equipped with
  the uniformity of uniform convergence of coefficients (avoiding a typeclass diamond with the
  pointwise-convergence subspace uniformity on `twoSidedRestrictedSubmodule A A ⊆ (ℤ → A)`).
* `TauCeti.Huber.IsProProjective`: pro-projective uniform `A`-modules (Kedlaya–Liu II,
  Definition 2.4.6).

## Main results

* `TauCeti.Huber.restrictedPowerSeriesTensorToNull_surjective` and
  `TauCeti.Huber.restrictedPowerSeriesTensorToNull_bijective`: Corollary 2.4.9(c) for `A⟨T⟩`.
* `TauCeti.Huber.restrictedLaurentSeriesTensorToNull_surjective` and
  `TauCeti.Huber.restrictedLaurentSeriesTensorToNull_bijective`: Corollary 2.4.9(c) for `A⟨T, T⁻¹⟩`.
* `TauCeti.Huber.IsProProjective.rTensor_injective` and
  `TauCeti.Huber.IsPseudoFlat.of_isProProjective`: Lemma 2.4.7 (`Tor₁` vanishing) and
  Corollary 2.4.8 (pro-projective modules are `2`-pseudoflat).
* `TauCeti.Huber.isProProjective_restrictedMvPowerSeriesCompletion` and
  `TauCeti.Huber.isPseudoFlat_restrictedMvPowerSeriesCompletion`: Corollary 2.4.9(a) for all
  `k : ℕ`.
* `TauCeti.Huber.isProProjective_restrictedLaurentSeries`,
  `TauCeti.Huber.isPseudoFlat_restrictedLaurentSeries`, and
  `TauCeti.Huber.isPseudoFlat_twoSidedRestrictedSubmodule`: Corollary 2.4.9(b).

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Definition 2.4.6, Lemma 2.4.7, and Corollaries 2.4.8–2.4.9.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.49, Example 6.39, and Remark 8.29.
-/

public section

open Filter Topology
open scoped TensorProduct Uniformity

namespace TauCeti.Huber

universe u v

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
    (zeroAtFilterCofiniteCongr A M e f : κ → M) k = (f : ι → M) (e.symm k) :=
  (rfl)

@[simp]
theorem coe_zeroAtFilterCofiniteCongr_symm_apply {A M : Type*} [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] {ι κ : Type*}
    (e : ι ≃ κ) (g : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter κ))
    (i : ι) :
    ((zeroAtFilterCofiniteCongr A M e).symm g : ι → M) i = (g : κ → M) (e i) :=
  (rfl)

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
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter {k : ℕ} {A M : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] (f : restrictedMvPowerSeriesSubmodule k A M) :
    ((restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter k A M f :
        Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter (Fin k →₀ ℕ))) :
      (Fin k →₀ ℕ) → M) = (f.1 : (Fin k →₀ ℕ) → M) :=
  (rfl)

@[simp]
theorem coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter_symm {k : ℕ} {A M : Type*}
    [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M]
    (g : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter (Fin k →₀ ℕ))) :
    (((restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter k A M).symm g).1 : (Fin k →₀ ℕ) → M) =
      (g : (Fin k →₀ ℕ) → M) :=
  (rfl)

/-- Unfolding `twoSidedRestrictedSubmodule A M` as `Filter.zeroAtFilterSubmodule` at
`Filter.cofinite` on `ℤ`. -/
def twoSidedRestrictedSubmoduleEquivZeroAtFilter (A M : Type*) [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] :
    twoSidedRestrictedSubmodule A M ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℤ) where
  toFun f := ⟨(f : ℤ → M), mem_twoSidedRestrictedSubmodule.mp f.2⟩
  invFun g := ⟨(g : ℤ → M), mem_twoSidedRestrictedSubmodule.mpr g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_twoSidedRestrictedSubmoduleEquivZeroAtFilter {A M : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M] (f : twoSidedRestrictedSubmodule A M) :
    ((twoSidedRestrictedSubmoduleEquivZeroAtFilter A M f :
        Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℤ)) : ℤ → M) =
      (f : ℤ → M) :=
  (rfl)

@[simp]
theorem coe_twoSidedRestrictedSubmoduleEquivZeroAtFilter_symm {A M : Type*} [Semiring A]
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousConstSMul A M]
    (g : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℤ)) :
    (((twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm g :
        twoSidedRestrictedSubmodule A M) : ℤ → M) = (g : ℤ → M) :=
  (rfl)

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
          have hfU : {i : ι | (f : ι → M) i ∉ U}.Finite :=
            Filter.mem_cofinite.mp (Filter.mem_map.mp (f.2 hU))
          refine (hfU.image j).subset fun n hn ↦ ?_
          simp only [Set.mem_preimage, Set.mem_compl_iff] at hn
          by_cases h : ∃ i, j i = n
          · exact ⟨h.choose, by simpa [h] using hn, h.choose_spec⟩
          · exact absurd (by simpa [h] using mem_of_mem_nhds hU) hn⟩
      map_add' := fun f₁ f₂ ↦ Subtype.ext <| funext fun n ↦ by
        by_cases h : ∃ i, j i = n <;> simp [h]
      map_smul' := fun a f ↦ Subtype.ext <| funext fun n ↦ by
        by_cases h : ∃ i, j i = n <;> simp [h] }
  let proj : Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ℕ) →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι) :=
    { toFun := fun g ↦ ⟨fun i ↦ (g : ℕ → M) (j i), Filter.Tendsto.comp g.2 hj.tendsto_cofinite⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine ⟨emb, proj, LinearMap.ext fun f ↦ Subtype.ext <| funext fun i ↦ ?_⟩
  dsimp [proj, emb]
  split_ifs with h'
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
  have hp : Continuous p := IsModuleTopology.continuous_of_linearMap p
  have hopen : IsOpenMap p := IsModuleTopology.isOpenMap_of_surjective hsurj
  exact restrictedMvPowerSeriesBaseChange_surjective_of_presentation p hp.continuousAt hsurj
    (map_zero p ▸ hopen.nhds_le 0)

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
  have hu : Continuous u := IsModuleTopology.continuous_of_linearMap u
  have hp : Continuous p := IsModuleTopology.continuous_of_linearMap p
  have hopen : IsOpenMap p := IsModuleTopology.isOpenMap_of_surjective hsurj
  have hker : IsClosed (LinearMap.ker p : Set (Fin m → A)) :=
    (isNaturallyComplete_iff_isClosed_ker hsurj).mp hM
  have hrange : IsClosed (LinearMap.range u : Set (Fin m → A)) :=
    (LinearMap.exact_iff.mp hexact).symm ▸ hker
  have hstrict : Topology.IsStrictMap u :=
    u.isStrictMap_of_isClosed_range_of_isTateRing hu.continuousAt hrange
  exact ⟨restrictedMvPowerSeriesBaseChange_injective_of_presentation u hu.continuousAt p
      hp.continuousAt hsurj (LinearMap.exact_iff.mp hexact).symm (map_zero u.rangeRestrict ▸
        (LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp hstrict).isOpenMap.nhds_le 0),
    restrictedMvPowerSeriesBaseChange_surjective_of_presentation p hp.continuousAt hsurj
      (map_zero p ▸ hopen.nhds_le 0)⟩

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
      restrictedMvPowerSeriesBaseChange x :=
  (rfl)

end Tate

end BaseChangeNonNoetherian

/-! ### Coefficients and null-sequence comparison for `A⟨T⟩` -/

section OneVariablePowerSeries

/-- The `A`-algebra isomorphism `A⟨X₁, …, Xₖ⟩ ≃ₐ[A] restrictedMvPowerSeriesSubring k A` over a
complete Hausdorff nonarchimedean base, composing `restrictedMvPowerSeriesCompletionAlgEquiv` with
`weightedRestrictedSubring_one_weight`. -/
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
    rw [hsmul]
    simp [Algebra.smul_def]

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
  have halg : algebraMap A (restrictedMvPowerSeriesCompletion 1 A) a =
      ((weightedC _ isWeightFamily_one_weight a :
        weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion 1 A) := rfl
  rw [halg, restrictedCoeff_coe, coe_weightedC, MvPowerSeries.coeff_C]
  simp [(Finsupp.single_eq_zero (a := (0 : Fin 1)))]

/-- On the variable `T` (`weightedX _ isWeightFamily_one_weight 0`), `restrictedCoeff n` returns `1`
for `n = 1` and `0` otherwise. -/
theorem restrictedCoeff_weightedX {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T0Space A] [NonarchimedeanRing A] (n : ℕ) :
    restrictedCoeff n
        ((weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion 1 A) =
      if n = 1 then 1 else 0 := by
  rw [restrictedCoeff_coe, coe_weightedX, MvPowerSeries.coeff_X]
  simp

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
    coe_restrictedMvPowerSeriesCompletionSubringAlgEquiv]
  rfl

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (surjective case for `A⟨T⟩`).** For a finite `A`-module `M`
with its module topology over a complete Hausdorff nonarchimedean ring `A` with countably generated
neighbourhoods of `0`, `restrictedPowerSeriesTensorToNull` is surjective. -/
theorem restrictedPowerSeriesTensorToNull_surjective {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    [(𝓝 (0 : A)).IsCountablyGenerated] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [TopologicalSpace M] [ContinuousAdd M] [IsModuleTopology A M] :
    Function.Surjective
      (restrictedPowerSeriesTensorToNull (A := A) (M := M)) :=
  (zeroAtFilterCofiniteCongr A M (Finsupp.uniqueEquiv (0 : Fin 1))).surjective.comp <|
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).surjective.comp <|
      restrictedMvPowerSeriesBaseChange_surjective_of_finite.comp <|
        (LinearEquiv.lTensor M
          (restrictedMvPowerSeriesCompletionSubringAlgEquiv 1 A).toLinearEquiv).surjective.comp <|
          (TensorProduct.comm A (restrictedMvPowerSeriesCompletion 1 A) M).surjective

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (bijective case for `A⟨T⟩`).** For a finitely presented
naturally complete `A`-module `M` with its module topology over a complete Hausdorff Tate ring `A`,
`restrictedPowerSeriesTensorToNull` is bijective. -/
theorem restrictedPowerSeriesTensorToNull_bijective {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [TopologicalSpace M]
    [ContinuousAdd M] [IsModuleTopology A M] (hM : IsNaturallyComplete A M) :
    Function.Bijective
      (restrictedPowerSeriesTensorToNull (A := A) (M := M)) :=
  (zeroAtFilterCofiniteCongr A M (Finsupp.uniqueEquiv (0 : Fin 1))).bijective.comp <|
    (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).bijective.comp <|
      (restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete hM).comp <|
        (LinearEquiv.lTensor M
          (restrictedMvPowerSeriesCompletionSubringAlgEquiv 1 A).toLinearEquiv).bijective.comp <|
          (TensorProduct.comm A (restrictedMvPowerSeriesCompletion 1 A) M).bijective

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

/-- Bijection between `ℤ` and one-variable exponents `Fin 1 →₀ ℕ`, used to transport module-level
null-sequence properties between `A⟨T, T⁻¹⟩` and `A⟨T⟩`. -/
noncomputable def intEquivFinOneFinsupp : ℤ ≃ (Fin 1 →₀ ℕ) :=
  Equiv.intEquivNat.trans (Finsupp.uniqueEquiv (0 : Fin 1)).symm

/-- `A`-linear equivalence between two-sided restricted `A`-series `twoSidedRestrictedSubmodule A A`
and one-variable restricted power series `restrictedMvPowerSeriesSubring 1 A`, reindexing
coefficients along `intEquivFinOneFinsupp`. -/
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
  rw [MvPowerSeries.coeff_apply]
  dsimp [twoSidedToRestrictedSubringLinearEquiv]
  rw [coe_restrictedMvPowerSeriesSubringLinearEquiv_symm]
  exact congrFun (coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter_symm _) ν

/-- **The natural Laurent comparison `A⟨T, T⁻¹⟩ ⊗[A] M →ₗ[A] M⟨T, T⁻¹⟩`** sending `f ⊗ₜ v` to the
two-sided null family `n ↦ f n • v` (Kedlaya–Liu II, Corollary 2.4.9(c)). Both domain and codomain
are built directly on `twoSidedRestrictedSubmodule` (`Filter.zeroAtFilterSubmodule` at
`Filter.cofinite` on `ℤ`). -/
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
    coe_twoSidedRestrictedSubmoduleEquivZeroAtFilter_symm,
    coe_zeroAtFilterCofiniteCongr_apply, Equiv.symm_symm,
    coe_restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter]
  rw [coeff_restrictedMvPowerSeriesBaseChange_tmul,
    coeff_twoSidedToRestrictedSubringLinearEquiv, Equiv.symm_apply_apply]

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (surjective case for `A⟨T, T⁻¹⟩`).** For a finite
`A`-module `M` with its module topology over a nonarchimedean commutative ring `A` with countably
generated neighbourhoods of `0`, `restrictedLaurentSeriesTensorToNull` is surjective. -/
theorem restrictedLaurentSeriesTensorToNull_surjective {A : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] [(𝓝 (0 : A)).IsCountablyGenerated] {M : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] [TopologicalSpace M] [ContinuousAdd M]
    [IsModuleTopology A M] :
    Function.Surjective (restrictedLaurentSeriesTensorToNull (A := A) (M := M)) :=
  (twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm.surjective.comp <|
    (zeroAtFilterCofiniteCongr A M intEquivFinOneFinsupp.symm).surjective.comp <|
      (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).surjective.comp <|
        restrictedMvPowerSeriesBaseChange_surjective_of_finite.comp <|
          (LinearEquiv.lTensor M (twoSidedToRestrictedSubringLinearEquiv A)).surjective.comp <|
            (TensorProduct.comm A (twoSidedRestrictedSubmodule A A) M).surjective

/-- **Kedlaya–Liu II, Corollary 2.4.9(c) (bijective case for `A⟨T, T⁻¹⟩`).** For a finitely
presented naturally complete `A`-module `M` with its module topology over a complete Hausdorff Tate
ring `A`, `restrictedLaurentSeriesTensorToNull` is bijective. -/
theorem restrictedLaurentSeriesTensorToNull_bijective {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [TopologicalSpace M]
    [ContinuousAdd M] [IsModuleTopology A M] (hM : IsNaturallyComplete A M) :
    Function.Bijective (restrictedLaurentSeriesTensorToNull (A := A) (M := M)) :=
  (twoSidedRestrictedSubmoduleEquivZeroAtFilter A M).symm.bijective.comp <|
    (zeroAtFilterCofiniteCongr A M intEquivFinOneFinsupp.symm).bijective.comp <|
      (restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A M).bijective.comp <|
        (restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete hM).comp <|
          (LinearEquiv.lTensor M (twoSidedToRestrictedSubringLinearEquiv A)).bijective.comp <|
            (TensorProduct.comm A (twoSidedRestrictedSubmodule A A) M).bijective

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
    f = g := by
  cases f; cases g; exact congrArg mk h

section Module

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

instance : AddCommGroup (RestrictedLaurentSeries A) where
  zero := ⟨0⟩
  add f g := ⟨f.1 + g.1⟩
  neg f := ⟨-f.1⟩
  sub f g := ⟨f.1 - g.1⟩
  nsmul n f := ⟨n • f.1⟩
  zsmul n f := ⟨n • f.1⟩
  add_assoc _ _ _ := congrArg mk (add_assoc _ _ _)
  zero_add _ := congrArg mk (zero_add _)
  add_zero _ := congrArg mk (add_zero _)
  nsmul_zero _ := congrArg mk (zero_smul ℕ _)
  nsmul_succ n f := congrArg mk (succ_nsmul f.1 n)
  zsmul_zero' _ := congrArg mk (zero_smul ℤ _)
  zsmul_succ' n f := congrArg mk (SubNegMonoid.zsmul_succ' n f.1)
  zsmul_neg' n f := congrArg mk (SubNegMonoid.zsmul_neg' n f.1)
  neg_add_cancel _ := congrArg mk (neg_add_cancel _)
  add_comm _ _ := congrArg mk (add_comm _ _)
  sub_eq_add_neg _ _ := congrArg mk (sub_eq_add_neg _ _)

instance : Module A (RestrictedLaurentSeries A) where
  smul a f := ⟨a • f.1⟩
  one_smul _ := congrArg mk (one_smul _ _)
  mul_smul _ _ _ := congrArg mk (mul_smul _ _ _)
  smul_zero _ := congrArg mk (smul_zero _)
  smul_add _ _ _ := congrArg mk (smul_add _ _ _)
  add_smul _ _ _ := congrArg mk (add_smul _ _ _)
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
  toFun := toTwoSided
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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
    dsimp [instUniformSpace]
    rw [← UniformSpace.comap_comap]
    have hcomp : ⇑(toWeightedLinearEquiv A) ∘ ⇑(toWeightedLinearEquiv A).symm = id :=
      funext (toWeightedLinearEquiv A).apply_symm_apply
    rw [hcomp, UniformSpace.comap_id]
    exact le_rfl

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
  Algebra.ofModule
    (fun r x y ↦ congrArg mk (Algebra.smul_mul_assoc r x.1 y.1))
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

/-! ### Pro-projective modules and `2`-pseudoflatness -/

section ProProjective

/-- A uniform `A`-module `B` is *pro-projective* over `A` (Kedlaya–Liu II, Definition 2.4.6) if `B`
is complete, Hausdorff, and has countably generated uniformity, carries a compatible sequence of
continuous `A`-linear projectors `π : ℕ → B →ₗ[A] B` with finite projective images converging
pointwise to the identity, and is an `A`-linear retract of `c₀(ℕ, A)`.

In a norm-free setting, continuous projectors onto finite projective summands alone do not force
uniform coordinate-splitting bounds: over `A = ℚ_p⟨X, Y⟩`, the `c₀`-direct sum `B` of copies
`(A, ‖·‖ₖ)` (`k ≥ 1`) with `‖h‖ₖ = max(|h(p ^ k, p ^ k)|_p, p ^ (-k : ℤ) * ‖h‖_Gauss)` carries
norm-`1` finite-free truncation projectors converging pointwise to `id`, yet
`Tor₁^A(A ⧸ (X, Y), B) ≠ 0` because `Y ⊗ (X)ₖ - X ⊗ (Y)ₖ ∈ ker((X, Y) ⊗[A] B → B)` has unique
Koszul preimage `(1, 1, …) ∉ B`. Requiring `exists_nullSequence_retract` expresses uniform
coordinate splittings without choosing Banach norms. -/
structure IsProProjective (A : Type u) [CommRing A] [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousConstSMul A A] (B : Type v) [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B]
    [Module A B] : Prop where
  /-- `B` is complete. -/
  completeSpace : CompleteSpace B
  /-- `B` is Hausdorff. -/
  t2Space : T2Space B
  /-- The uniformity of `B` is countably generated. -/
  isCountablyGenerated : (𝓤 B).IsCountablyGenerated
  /-- Compatible continuous `A`-linear projectors with finite projective images converging
  pointwise to the identity. -/
  exists_projectors :
    ∃ π : ℕ → B →ₗ[A] B,
      (∀ k, Continuous (π k)) ∧
      (∀ k, Module.Finite A (LinearMap.range (π k))) ∧
      (∀ k, Module.Projective A (LinearMap.range (π k))) ∧
      (∀ ⦃k l⦄, k ≤ l → π l ∘ₗ π k = π k) ∧
      (∀ b : B, Tendsto (fun k ↦ π k b) atTop (nhds b))
  /-- Uniform coordinate-splitting witness: `B` is an `A`-linear retract of `c₀(ℕ, A)`. -/
  exists_nullSequence_retract :
    ∃ (emb : B →ₗ[A] Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ))
      (proj : Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) →ₗ[A] B),
      proj ∘ₗ emb = LinearMap.id

namespace IsProProjective

section Basic

variable {A : Type u} [CommRing A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul A A]
  {B : Type v} [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B] [Module A B]

/-- An indiscrete nontrivial uniform `A`-module is not pro-projective: even though the zero
projectors `πₖ = 0` are continuous with finite projective image and converge to every element, a
pro-projective module must be Hausdorff. -/
theorem not_of_not_t2Space (hnot : ¬ T2Space B) : ¬ IsProProjective A B :=
  fun h ↦ hnot h.t2Space

/-- Pro-projectivity is invariant under `A`-linear equivalences that are uniform equivalences. -/
theorem of_uniformLinearEquiv {B' : Type*} [AddCommGroup B'] [UniformSpace B']
    [IsUniformAddGroup B'] [Module A B'] (e : B ≃ₗ[A] B') (he : UniformContinuous e)
    (he_symm : UniformContinuous e.symm) (hB : IsProProjective A B) : IsProProjective A B' := by
  let ue : B ≃ᵤ B' :=
    { toEquiv := e.toEquiv
      uniformContinuous_toFun := he
      uniformContinuous_invFun := he_symm }
  have : CompleteSpace B := hB.completeSpace
  have : T2Space B := hB.t2Space
  have : (𝓤 B).IsCountablyGenerated := hB.isCountablyGenerated
  have hcomp : CompleteSpace B' := ue.completeSpace_iff.mp inferInstance
  have ht2 : T2Space B' := .of_injective_continuous e.symm.injective he_symm.continuous
  have hcg : (𝓤 B').IsCountablyGenerated := by
    rw [← ue.symm.isUniformInducing.comap_uniformity]
    exact Filter.comap.isCountablyGenerated _ _
  obtain ⟨π, hπ_cont, hπ_fin, hπ_proj, hπ_compat, hπ_lim⟩ := hB.exists_projectors
  obtain ⟨emb, proj, hretract⟩ := hB.exists_nullSequence_retract
  let π' : ℕ → B' →ₗ[A] B' := fun k ↦ e.toLinearMap ∘ₗ π k ∘ₗ e.symm.toLinearMap
  refine ⟨hcomp, ht2, hcg, ⟨π', fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_, fun k l hkl ↦ ?_,
      fun b' ↦ ?_⟩,
    ⟨emb ∘ₗ e.symm.toLinearMap, e.toLinearMap ∘ₗ proj, ?_⟩⟩
  · exact he.continuous.comp ((hπ_cont k).comp he_symm.continuous)
  · have hrange_eq : LinearMap.range (π' k) = (LinearMap.range (π k)).map e.toLinearMap := by
      ext y
      simp only [π', LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        Submodule.mem_map]
      exact ⟨fun ⟨x, hx⟩ ↦ ⟨π k (e.symm x), ⟨e.symm x, rfl⟩, hx⟩,
        fun ⟨z, ⟨x, hx⟩, hy⟩ ↦ ⟨e x, by simpa [hx] using hy⟩⟩
    rw [hrange_eq]
    have := hπ_fin k
    exact Module.Finite.equiv (e.submoduleMap (LinearMap.range (π k)))
  · have hrange_eq : LinearMap.range (π' k) = (LinearMap.range (π k)).map e.toLinearMap := by
      ext y
      simp only [π', LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        Submodule.mem_map]
      exact ⟨fun ⟨x, hx⟩ ↦ ⟨π k (e.symm x), ⟨e.symm x, rfl⟩, hx⟩,
        fun ⟨z, ⟨x, hx⟩, hy⟩ ↦ ⟨e x, by simpa [hx] using hy⟩⟩
    rw [hrange_eq]
    have := hπ_proj k
    exact Module.Projective.of_equiv (e.submoduleMap (LinearMap.range (π k)))
  · ext x
    simp only [π', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, e.symm_apply_apply]
    exact congrArg e congr($(hπ_compat hkl) (e.symm x))
  · have hlim := (he.continuous.tendsto (e.symm b')).comp (hπ_lim (e.symm b'))
    simpa [π', Function.comp_def, e.apply_symm_apply] using hlim
  · ext b'
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]
    have hb : proj (emb (e.symm b')) = e.symm b' := congr($hretract (e.symm b'))
    rw [hb, e.apply_symm_apply]

/-- **Every finite projective module (with its natural topology) over a complete Hausdorff
first-countable commutative ring is pro-projective** (Kedlaya–Liu II, Definition 2.4.6). -/
theorem of_projective {A : Type u} [CommRing A] [UniformSpace A] [IsTopologicalRing A]
    [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] [FirstCountableTopology A]
    {P : Type v} [AddCommGroup P] [UniformSpace P] [IsUniformAddGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P] [IsModuleTopology A P] :
    IsProProjective A P := by
  have hnc : IsNaturallyComplete A P := IsNaturallyComplete.of_projective
  obtain ⟨hcomp, ht2⟩ := isNaturallyComplete_iff.mp hnc
  have : FirstCountableTopology P := by
    rw [eq_moduleTopology A P]
    exact firstCountableTopology_moduleTopology
  have hcg : (𝓤 P).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let toNat : (Fin n → A) →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) :=
    { toFun := fun x ↦
        ⟨fun m ↦ if h : m < n then x ⟨m, h⟩ else 0, fun U hU ↦ by
          rw [Filter.mem_map, Filter.mem_cofinite]
          refine (Set.finite_lt_nat n).subset fun m hm ↦ ?_
          simp only [Set.mem_preimage, Set.mem_compl_iff] at hm
          split_ifs at hm with hmn
          · exact hmn
          · exact absurd (mem_of_mem_nhds hU) hm⟩
      map_add' := fun x y ↦ Subtype.ext <| funext fun m ↦ by
        by_cases h : m < n <;> simp [h]
      map_smul' := fun a x ↦ Subtype.ext <| funext fun m ↦ by
        by_cases h : m < n <;> simp [h] }
  let fromNat :
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) →ₗ[A] (Fin n → A) :=
    { toFun := fun s i ↦ (s : ℕ → A) i.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hfn : fromNat ∘ₗ toNat = LinearMap.id :=
    LinearMap.ext fun x ↦ funext fun i ↦ by
      dsimp [fromNat, toNat]
      simp [i.2]
  refine ⟨hcomp, ht2, hcg,
    ⟨fun _ ↦ LinearMap.id, fun _ ↦ continuous_id,
      fun _ ↦ by rw [LinearMap.range_id]; exact Module.Finite.equiv Submodule.topEquiv.symm,
      fun _ ↦ by rw [LinearMap.range_id]; exact Module.Projective.of_equiv Submodule.topEquiv.symm,
      fun _ _ _ ↦ LinearMap.id_comp LinearMap.id, fun b ↦ tendsto_const_nhds⟩,
    ⟨toNat ∘ₗ g, f ∘ₗ fromNat, ?_⟩⟩
  calc (f ∘ₗ fromNat) ∘ₗ (toNat ∘ₗ g)
      = f ∘ₗ (fromNat ∘ₗ toNat) ∘ₗ g := by ext; rfl
    _ = f ∘ₗ g := by rw [hfn, LinearMap.id_comp]
    _ = LinearMap.id := hfg

/-- **A binary product of pro-projective modules is pro-projective.** -/
theorem prod {B' : Type*} [AddCommGroup B'] [UniformSpace B'] [IsUniformAddGroup B']
    [Module A B'] (hB : IsProProjective A B) (hB' : IsProProjective A B') :
    IsProProjective A (B × B') := by
  -- Step 1: Extract uniform hypotheses, projector systems, and `c₀(ℕ, A)` retractions.
  have := hB.completeSpace
  have := hB'.completeSpace
  have := hB.t2Space
  have := hB'.t2Space
  have := hB.isCountablyGenerated
  have := hB'.isCountablyGenerated
  obtain ⟨π₁, hπ₁c, hπ₁f, hπ₁p, hπ₁m, hπ₁l⟩ := hB.exists_projectors
  obtain ⟨π₂, hπ₂c, hπ₂f, hπ₂p, hπ₂m, hπ₂l⟩ := hB'.exists_projectors
  obtain ⟨i₁, r₁, hr₁⟩ := hB.exists_nullSequence_retract
  obtain ⟨i₂, r₂, hr₂⟩ := hB'.exists_nullSequence_retract
  let π : ℕ → (B × B') →ₗ[A] (B × B') := fun k ↦ (π₁ k).prodMap (π₂ k)
  have hrange (k : ℕ) :
      LinearMap.range (π k) = (LinearMap.range (π₁ k)).prod (LinearMap.range (π₂ k)) := by
    ext ⟨y₁, y₂⟩
    simp [π, Submodule.mem_prod]
  -- Step 2: Interleave `c₀(ℕ, A) × c₀(ℕ, A)` into `c₀(ℕ, A)` via `ℕ ⊕ ℕ ≃ ℕ`.
  let merge : (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) ×
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter (ℕ ⊕ ℕ)) :=
    { toFun := fun ⟨f, g⟩ ↦
        ⟨Sum.elim (f : ℕ → A) (g : ℕ → A), fun U hU ↦ by
          rw [Filter.mem_map, Filter.mem_cofinite]
          have hfU : {n : ℕ | (f : ℕ → A) n ∉ U}.Finite :=
            Filter.mem_cofinite.mp (Filter.mem_map.mp (f.2 hU))
          have hgU : {n : ℕ | (g : ℕ → A) n ∉ U}.Finite :=
            Filter.mem_cofinite.mp (Filter.mem_map.mp (g.2 hU))
          refine ((hfU.image Sum.inl).union (hgU.image Sum.inr)).subset fun s hs ↦ ?_
          rcases s with n | n
          · exact Or.inl ⟨n, hs, rfl⟩
          · exact Or.inr ⟨n, hs, rfl⟩⟩
      map_add' := fun ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ ↦ Subtype.ext <| funext fun s ↦ by cases s <;> rfl
      map_smul' := fun a ⟨f, g⟩ ↦ Subtype.ext <| funext fun s ↦ by cases s <;> rfl }
  let split : Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter (ℕ ⊕ ℕ)) →ₗ[A]
      (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) ×
        Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) :=
    { toFun := fun h ↦
        (⟨fun n ↦ (h : ℕ ⊕ ℕ → A) (Sum.inl n),
            Filter.Tendsto.comp h.2 Sum.inl_injective.tendsto_cofinite⟩,
          ⟨fun n ↦ (h : ℕ ⊕ ℕ → A) (Sum.inr n),
            Filter.Tendsto.comp h.2 Sum.inr_injective.tendsto_cofinite⟩)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eSum := zeroAtFilterCofiniteCongr A A Equiv.natSumNatEquivNat
  -- Step 3: Verify finite projective ranges, compatibility, and the product retraction.
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨π, fun k ↦ (hπ₁c k).prodMap (hπ₂c k), fun k ↦ ?_, fun k ↦ ?_, fun k l hkl ↦ ?_,
      fun ⟨b₁, b₂⟩ ↦ (hπ₁l b₁).prodMk_nhds (hπ₂l b₂)⟩,
    ⟨eSum.toLinearMap ∘ₗ merge ∘ₗ i₁.prodMap i₂,
      (r₁.prodMap r₂) ∘ₗ split ∘ₗ eSum.symm.toLinearMap, ?_⟩⟩
  · rw [hrange k]
    have := hπ₁f k
    have := hπ₂f k
    exact Module.Finite.equiv
      (Submodule.prodEquiv (LinearMap.range (π₁ k)) (LinearMap.range (π₂ k))).symm
  · rw [hrange k]
    have := hπ₁p k
    have := hπ₂p k
    exact Module.Projective.of_equiv
      (Submodule.prodEquiv (LinearMap.range (π₁ k)) (LinearMap.range (π₂ k))).symm
  · refine LinearMap.ext fun ⟨b₁, b₂⟩ ↦ ?_
    have h₁ := congr($(hπ₁m hkl) b₁)
    have h₂ := congr($(hπ₂m hkl) b₂)
    exact Prod.ext (by simpa [π] using h₁) (by simpa [π] using h₂)
  · refine LinearMap.ext fun ⟨b₁, b₂⟩ ↦ Prod.ext ?_ ?_
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.prodMap_apply,
        eSum.symm_apply_apply]
      exact congr($hr₁ b₁)
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.prodMap_apply,
        eSum.symm_apply_apply]
      exact congr($hr₂ b₂)

end Basic

section PseudoFlat

/-- **Vanishing of `Tor₁` against `c₀(ℕ, A)`** (core of Kedlaya–Liu II, Lemma 2.4.7). Over a
complete Hausdorff Tate ring `A`, for any short exact sequence `0 → M →[i] N →[p] P → 0` with `N`
finite projective and `P` `2`-pseudocoherent, `i.rTensor c₀(ℕ, A)` is injective. -/
theorem rTensor_injective_zeroAtFilterSubmodule_nat {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Projective A N] [AddCommGroup P] [Module A P]
    {i : M →ₗ[A] N} {p : N →ₗ[A] P} (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : Function.Exact i p) (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective
      (i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ))) := by
  -- Step 1: Deduce finite presentation and natural completeness of `M` from `2`-pseudocoherence.
  have hP' : IsPseudoCoherentOver A P ((1 : ℕ∞) + 1) := hP
  have hker_coh : IsPseudoCoherentOver A (LinearMap.ker p) 1 := hP'.ker_of_projective hp
  let eM : M ≃ₗ[A] LinearMap.ker p :=
    LinearEquiv.ofBijective (i.codRestrict (LinearMap.ker p) hexact.apply_apply_eq_zero)
      ⟨fun x y hxy ↦ hi (congrArg Subtype.val hxy), fun ⟨y, hy⟩ ↦ by
        obtain ⟨x, rfl⟩ := (hexact y).mp hy
        exact ⟨x, rfl⟩⟩
  have hM_coh : IsPseudoCoherentOver A M 1 := hker_coh.of_equiv eM.symm
  have : Module.FinitePresentation A M := IsPseudoCoherentOver.one_iff.mp hM_coh
  have : Module.Finite A M := hM_coh.finite
  have : Module.FinitePresentation A N :=
    IsPseudoCoherentOver.one_iff.mp (IsPseudoCoherentOver.of_projective.mono le_top)
  have hN_nc : IsNaturallyComplete A N := IsNaturallyComplete.of_projective
  have hM_nc : IsNaturallyComplete A M := hN_nc.of_injective hi
  -- Step 2: Identify `M ⊗[A] A⟨T⟩ ≃ₗ[A] M⟨T⟩` and deduce injectivity of `i.rTensor A⟨T⟩`.
  let _ : TopologicalSpace M := moduleTopology A M
  let _ : TopologicalSpace N := moduleTopology A N
  have _ : IsModuleTopology A M := ⟨rfl⟩
  have _ : IsModuleTopology A N := ⟨rfl⟩
  have _ : ContinuousAdd M := IsModuleTopology.toContinuousAdd A M
  have _ : ContinuousAdd N := IsModuleTopology.toContinuousAdd A N
  have _ : ContinuousSMul A M := IsModuleTopology.toContinuousSMul A M
  have _ : ContinuousSMul A N := IsModuleTopology.toContinuousSMul A N
  have hi_cont : Continuous i := IsModuleTopology.continuous_of_linearMap i
  let S := restrictedMvPowerSeriesSubring 1 A
  let bcM : M ⊗[A] S ≃ₗ[A] restrictedMvPowerSeriesSubmodule 1 A M :=
    restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete hM_nc
  have hinj_S : Function.Injective (i.rTensor S) := by
    intro z₁ z₂ hz
    apply bcM.injective
    apply restrictedMvPowerSeriesSubmoduleMap_injective i hi_cont.continuousAt hi
    rw [restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply,
      restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply,
      restrictedMvPowerSeriesSubmoduleMap_baseChange i hi_cont.continuousAt z₁,
      restrictedMvPowerSeriesSubmoduleMap_baseChange i hi_cont.continuousAt z₂]
    exact congrArg restrictedMvPowerSeriesBaseChange hz
  -- Step 3: Transport injectivity along the `A`-linear equivalence `A⟨T⟩ ≃ₗ[A] c₀(ℕ, A)`.
  let eNat : S ≃ₗ[A] Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) :=
    restrictedMvPowerSeriesSubringLinearEquiv 1 A ≪≫ₗ
      restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A A ≪≫ₗ
      zeroAtFilterCofiniteCongr A A (Finsupp.uniqueEquiv (0 : Fin 1))
  have hcomm (w) :
      LinearEquiv.lTensor N eNat (i.rTensor S (LinearEquiv.lTensor M eNat.symm w)) =
        i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) w := by
    induction w using TensorProduct.inductionOn with
    | tmul m c => simp [LinearEquiv.lTensor_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  intro w₁ w₂ hw
  apply (LinearEquiv.lTensor M eNat.symm).injective
  apply hinj_S
  apply (LinearEquiv.lTensor N eNat).injective
  rw [hcomm, hcomm, hw]

/-- **Kedlaya–Liu II, Lemma 2.4.7 (`Tor₁` half).** Over a complete Hausdorff Tate ring `A`, if `B`
is a pro-projective `A`-module and `0 → M →[i] N →[p] P → 0` is a short exact sequence of
`A`-modules with `N` finite projective and `P` `2`-pseudocoherent (in particular, strictly or stably
`2`-pseudocoherent), then `i.rTensor B : M ⊗[A] B → N ⊗[A] B` is injective. -/
theorem rTensor_injective {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type v} [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B] [Module A B]
    (hB : IsProProjective A B) {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [Module.Finite A N] [Module.Projective A N] [AddCommGroup P] [Module A P]
    {i : M →ₗ[A] N} {p : N →ₗ[A] P} (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : Function.Exact i p) (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective (i.rTensor B) := by
  obtain ⟨emb, proj, hretract⟩ := hB.exists_nullSequence_retract
  have hli : LinearMap.lTensor M proj ∘ₗ LinearMap.lTensor M emb = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hretract, LinearMap.lTensor_id]
  have hinj_emb : Function.Injective (LinearMap.lTensor M emb) :=
    Function.LeftInverse.injective fun z ↦ congr($hli z)
  have hsq : LinearMap.lTensor N emb ∘ₗ i.rTensor B =
      i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) ∘ₗ
        LinearMap.lTensor M emb := by
    ext m b
    rfl
  exact Function.Injective.of_comp (f := LinearMap.lTensor N emb) <| by
    rw [← LinearMap.coe_comp, hsq]
    exact (rTensor_injective_zeroAtFilterSubmodule_nat hi hp hexact hP).comp hinj_emb

end PseudoFlat

end IsProProjective

/-- **Kedlaya–Liu II, Corollary 2.4.8.** Over a complete Hausdorff Tate ring `A`, every
pro-projective `A`-module is `2`-pseudoflat. -/
theorem IsPseudoFlat.of_isProProjective {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type v} [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B] [Module A B]
    (hB : IsProProjective A B) : IsPseudoFlat A B 2 :=
  isPseudoFlat_iff.mpr fun _ K hK ↦ hB.rTensor_injective K.injective_subtype
    (Submodule.mkQ_surjective K) (LinearMap.exact_subtype_mkQ K) hK.isPseudoCoherentOver

/-- A pro-projective module over a complete Hausdorff Tate ring is `m`-pseudoflat for every
`2 ≤ m`, and in particular `⊤`-pseudoflat. -/
theorem IsPseudoFlat.of_isProProjective_of_le {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type v} [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B] [Module A B]
    {m : ℕ∞} (hB : IsProProjective A B) (hm : 2 ≤ m) : IsPseudoFlat A B m :=
  (IsPseudoFlat.of_isProProjective hB).mono hm

end ProProjective

/-! ### Pro-projectivity and `2`-pseudoflatness of `A⟨X₁, …, Xₖ⟩` and `A⟨T, T⁻¹⟩` -/

section RestrictedProProjective

private def boxTruncSeries {k : ℕ} {A : Type*} [CommRing A] (N : ℕ)
    (f : MvPowerSeries (Fin k) A) : MvPowerSeries (Fin k) A :=
  fun ν ↦ if ∀ i : Fin k, ν i ≤ N then MvPowerSeries.coeff ν f else 0

@[simp]
private theorem coeff_boxTruncSeries {k : ℕ} {A : Type*} [CommRing A] (N : ℕ)
    (f : MvPowerSeries (Fin k) A) (ν : Fin k →₀ ℕ) :
    MvPowerSeries.coeff ν (boxTruncSeries N f) =
      if ∀ i : Fin k, ν i ≤ N then MvPowerSeries.coeff ν f else 0 :=
  rfl

private def boxBuildSeries {k N : ℕ} {A : Type*} [CommRing A]
    (c : (Fin k → Fin (N + 1)) → A) : MvPowerSeries (Fin k) A :=
  fun ν ↦ if h : ∀ i : Fin k, ν i ≤ N then c (fun i ↦ ⟨ν i, Nat.lt_succ_of_le (h i)⟩) else 0

@[simp]
private theorem coeff_boxBuildSeries {k N : ℕ} {A : Type*} [CommRing A]
    (c : (Fin k → Fin (N + 1)) → A) (ν : Fin k →₀ ℕ) :
    MvPowerSeries.coeff ν (boxBuildSeries c) =
      if h : ∀ i : Fin k, ν i ≤ N then c (fun i ↦ ⟨ν i, Nat.lt_succ_of_le (h i)⟩) else 0 :=
  rfl

private theorem boxTruncSeries_mem {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (N : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    boxTruncSeries N (f : MvPowerSeries (Fin k) A) ∈
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  mem_weightedRestrictedSubring.mpr <| isWeightedRestricted_one_weight_iff.mpr <| by
    have hf : ZeroAtFilter cofinite
        (fun ν ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) :=
      isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp f.2)
    exact hf.of_eventually_eq_or_eq_zero (.of_forall fun ν ↦ by
      rw [coeff_boxTruncSeries]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl)

private theorem coe_smul_one_weight {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (a : A)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ((a • f).1 : MvPowerSeries (Fin k) A) =
      MvPowerSeries.C a * (f : MvPowerSeries (Fin k) A) := by
  rw [Algebra.smul_def, Subring.coe_mul, algebraMap_weightedRestrictedSubring, coe_weightedC]

/-- Hypercube truncation projector on the trivial-weight restricted power-series ring
`weightedRestrictedSubring`, retaining multi-indices `ν : Fin k →₀ ℕ` with `∀ i, ν i ≤ N`. -/
private noncomputable def weightedBoxTrunc {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (N : ℕ) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →ₗ[A]
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight where
  toFun f := ⟨boxTruncSeries N (f : MvPowerSeries (Fin k) A), boxTruncSeries_mem N f⟩
  map_add' f g := Subtype.ext <| MvPowerSeries.ext fun ν ↦ by
    -- Strip the subtype membership proof before rewriting `.1` on `f + g`.
    change MvPowerSeries.coeff ν (boxTruncSeries N ((f + g).1 : MvPowerSeries (Fin k) A)) =
      MvPowerSeries.coeff ν
        (boxTruncSeries N (f : MvPowerSeries (Fin k) A) +
          boxTruncSeries N (g : MvPowerSeries (Fin k) A))
    rw [Subring.coe_add, map_add, coeff_boxTruncSeries, coeff_boxTruncSeries, coeff_boxTruncSeries,
      map_add]
    split_ifs <;> simp
  map_smul' a f := Subtype.ext <| MvPowerSeries.ext fun ν ↦ by
    -- Strip the subtype membership proof before rewriting `.1` on `a • f`.
    change MvPowerSeries.coeff ν (boxTruncSeries N ((a • f).1 : MvPowerSeries (Fin k) A)) =
      MvPowerSeries.coeff ν
        ((a • (⟨boxTruncSeries N (f : MvPowerSeries (Fin k) A), boxTruncSeries_mem N f⟩ :
            weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
              isWeightFamily_one_weight)).1 :
          MvPowerSeries (Fin k) A)
    rw [coe_smul_one_weight, coe_smul_one_weight, coeff_boxTruncSeries,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, coeff_boxTruncSeries]
    split_ifs <;> simp

@[simp]
private theorem coeff_weightedBoxTrunc {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (N : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
    (ν : Fin k →₀ ℕ) :
    MvPowerSeries.coeff ν (weightedBoxTrunc N f : MvPowerSeries (Fin k) A) =
      if ∀ i : Fin k, ν i ≤ N then
        MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) else 0 :=
  rfl

/-- **The trivial-weight restricted power-series ring is pro-projective** for every `k : ℕ` over a
complete Hausdorff nonarchimedean ring with countably generated neighbourhoods of `0`. -/
theorem isProProjective_weightedRestrictedSubring (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    [(𝓝 (0 : A)).IsCountablyGenerated] :
    IsProProjective A
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) := by
  -- Step 1: Build the `c₀(ℕ, A)` retraction via `c₀(Fin k →₀ ℕ, A)` and countable reindexing.
  have : (𝓤 (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨emb₀, proj₀, hretract₀⟩ :=
    exists_retract_zeroAtFilterSubmodule_nat A A (Fin k →₀ ℕ)
  let eW : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter (Fin k →₀ ℕ)) :=
    (AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr (weightedRestrictedSubring_one_weight (k := k) (A := A)))
      subringCongr_one_weight_weightedC).toLinearEquiv ≪≫ₗ
      restrictedMvPowerSeriesSubringLinearEquiv k A ≪≫ₗ
      restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter k A A
  -- Step 2: Identify the image of `weightedBoxTrunc N` with the finite free module
  -- `(Fin k → Fin (N + 1)) → A` of hypercube polynomials.
  have hbox_mem {N : ℕ} (c : (Fin k → Fin (N + 1)) → A) :
      boxBuildSeries c ∈
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight := by
    rw [mem_weightedRestrictedSubring, isWeightedRestricted_one_weight_iff]
    intro U hU
    rw [Filter.mem_map, Filter.mem_cofinite]
    let boxMap : (Fin k → Fin (N + 1)) → (Fin k →₀ ℕ) :=
      fun g ↦ Finsupp.equivFunOnFinite.symm (fun i ↦ (g i).1)
    refine (Set.finite_range boxMap).subset fun ν hν ↦ ?_
    simp only [Set.mem_preimage, Set.mem_compl_iff, coeff_boxBuildSeries] at hν
    by_cases h : ∀ i : Fin k, ν i ≤ N
    · refine ⟨fun i ↦ ⟨ν i, Nat.lt_succ_of_le (h i)⟩, ?_⟩
      exact Finsupp.ext fun i ↦ by simp [boxMap]
    · exact absurd (by simpa [h] using mem_of_mem_nhds hU) hν
  let eBox (N : ℕ) : ((Fin k → Fin (N + 1)) → A) ≃ₗ[A]
      LinearMap.range (weightedBoxTrunc (k := k) (A := A) N) := by
    let toBoxR : LinearMap.range (weightedBoxTrunc (k := k) (A := A) N) →ₗ[A]
        ((Fin k → Fin (N + 1)) → A) :=
      { toFun := fun f g ↦
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i ↦ (g i).1))
            (f.1 : MvPowerSeries (Fin k) A)
        map_add' := fun _ _ ↦ funext fun _ ↦ by simp
        map_smul' := fun a f ↦ funext fun g ↦ by
          -- Strip the range-submodule projection before rewriting scalar multiplication.
          change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i ↦ (g i).1))
              ((a • f.1).1 : MvPowerSeries (Fin k) A) =
            a * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i ↦ (g i).1))
              (f.1 : MvPowerSeries (Fin k) A)
          rw [coe_smul_one_weight, MvPowerSeries.coeff_C_mul] }
    let fromBoxR : ((Fin k → Fin (N + 1)) → A) →ₗ[A]
        LinearMap.range (weightedBoxTrunc (k := k) (A := A) N) :=
      { toFun := fun c ↦ ⟨weightedBoxTrunc N ⟨boxBuildSeries c, hbox_mem c⟩, ⟨_, rfl⟩⟩
        map_add' := fun c₁ c₂ ↦ Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun ν ↦ by
          -- Strip the nested subtype projections without unfolding `weightedBoxTrunc` in `HAdd`.
          change MvPowerSeries.coeff ν (boxTruncSeries N (boxBuildSeries (c₁ + c₂))) =
            MvPowerSeries.coeff ν
              (boxTruncSeries N (boxBuildSeries c₁) + boxTruncSeries N (boxBuildSeries c₂))
          rw [map_add, coeff_boxTruncSeries, coeff_boxTruncSeries, coeff_boxTruncSeries,
            coeff_boxBuildSeries, coeff_boxBuildSeries, coeff_boxBuildSeries]
          split_ifs <;> simp
        map_smul' := fun a c ↦ Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun ν ↦ by
          -- Strip the nested subtype projections before rewriting `.1` on `a • weightedBoxTrunc`.
          change MvPowerSeries.coeff ν (boxTruncSeries N (boxBuildSeries (a • c))) =
            MvPowerSeries.coeff ν
              ((a • weightedBoxTrunc N ⟨boxBuildSeries c, hbox_mem c⟩).1 :
                MvPowerSeries (Fin k) A)
          rw [coe_smul_one_weight, coeff_boxTruncSeries, coeff_boxBuildSeries,
            MvPowerSeries.coeff_C_mul, coeff_weightedBoxTrunc, coeff_boxBuildSeries]
          split_ifs <;> simp }
    refine LinearEquiv.ofLinearMap fromBoxR toBoxR
      (LinearMap.ext fun ⟨_, ⟨f, rfl⟩⟩ ↦ Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun ν ↦ ?_)
      (LinearMap.ext fun c ↦ funext fun g ↦ ?_)
    · -- Unfold `fromBoxR ∘ₗ toBoxR` without unfolding `weightedBoxTrunc` inside its range type.
      change MvPowerSeries.coeff ν
          (boxTruncSeries N (boxBuildSeries (toBoxR ⟨weightedBoxTrunc N f, ⟨f, rfl⟩⟩))) =
        MvPowerSeries.coeff ν (boxTruncSeries N (f : MvPowerSeries (Fin k) A))
      rw [coeff_boxTruncSeries, coeff_boxTruncSeries, coeff_boxBuildSeries]
      split_ifs with h
      · -- Unfold `toBoxR` on the surviving hypercube index.
        change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i ↦ ν i))
            (boxTruncSeries N (f : MvPowerSeries (Fin k) A)) =
          MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)
        have hν : Finsupp.equivFunOnFinite.symm (fun i ↦ ν i) = ν :=
          Finsupp.ext fun i ↦ by simp
        rw [hν, coeff_boxTruncSeries]
        split_ifs
        exact rfl
      · rfl
    · have hg : ∀ i : Fin k,
          (Finsupp.equivFunOnFinite.symm (fun i ↦ (g i).1)) i ≤ N := fun i ↦ by
        simpa using Nat.le_of_lt_succ (g i).2
      -- Unfold `toBoxR ∘ₗ fromBoxR` without unfolding `weightedBoxTrunc` inside its range type.
      change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i ↦ (g i).1))
          (boxTruncSeries N (boxBuildSeries c)) = c g
      simp only [coeff_boxTruncSeries, coeff_boxBuildSeries, hg, implies_true, ↓reduceIte,
        ↓reduceDIte]
      exact congrArg c (funext fun i ↦ Fin.ext (by simp))
  -- Step 3: Verify continuity, compatibility, and uniform convergence of `weightedBoxTrunc N`.
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨fun N ↦ weightedBoxTrunc (k := k) (A := A) N, fun N ↦ ?_,
      fun N ↦ Module.Finite.equiv (eBox N), fun N ↦ Module.Projective.of_equiv (eBox N),
      fun N M hNM ↦ ?_, fun f ↦ ?_⟩,
    ⟨emb₀ ∘ₗ eW.toLinearMap, eW.symm.toLinearMap ∘ₗ proj₀, ?_⟩⟩
  · refine continuous_of_continuousAt_zero (weightedBoxTrunc (k := k) (A := A) N).toAddMonoidHom ?_
    rw [ContinuousAt, map_zero,
      (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_iff
        (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight)]
    intro U _
    refine ⟨U, trivial, fun f hf ↦ ?_⟩
    rw [SetLike.mem_coe, mem_weightedNhd] at hf ⊢
    intro ν
    rw [LinearMap.toAddMonoidHom_coe, coeff_weightedBoxTrunc]
    split_ifs
    · exact hf ν
    · exact (weightMul (fun _ : Fin k ↦ ({1} : Set A)) ν U.toAddSubgroup).zero_mem
  · refine LinearMap.ext fun f ↦ Subtype.ext <| MvPowerSeries.ext fun ν ↦ ?_
    rw [LinearMap.comp_apply, coeff_weightedBoxTrunc, coeff_weightedBoxTrunc]
    split_ifs with hM hN hN'
    · rfl
    · rfl
    · exact absurd (fun i ↦ le_trans (hN' i) hNM) hM
    · rfl
  · rw [← tendsto_sub_nhds_zero_iff,
      (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_right_iff]
    intro U _
    have hfU : {ν : Fin k →₀ ℕ |
        MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∉ (U : Set A)}.Finite := by
      have hlim := isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp f.2)
      exact Filter.mem_cofinite.mp (Filter.mem_map.mp (hlim (U.isOpen.mem_nhds U.zero_mem)))
    let N₀ : ℕ := hfU.toFinset.sup fun ν ↦ Finset.univ.sup fun i ↦ ν i
    refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN ↦ ?_⟩
    rw [SetLike.mem_coe, mem_weightedNhd]
    intro ν
    rw [weightMul_one_weight, AddSubgroupClass.coe_sub, map_sub, coeff_weightedBoxTrunc]
    split_ifs with hbox
    · simp
    · have hmemU : MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ U.toAddSubgroup := by
        by_contra hnotU
        have hν_in : ν ∈ hfU.toFinset := hfU.mem_toFinset.mpr hnotU
        have hall : ∀ i : Fin k, ν i ≤ N := fun i ↦ by
          have hle₁ : ν i ≤ Finset.univ.sup fun j ↦ ν j :=
            Finset.le_sup (f := fun j ↦ ν j) (Finset.mem_univ i)
          have hle₂ : (Finset.univ.sup fun j ↦ ν j) ≤ N₀ :=
            Finset.le_sup (f := fun μ : Fin k →₀ ℕ ↦ Finset.univ.sup fun j ↦ μ j) hν_in
          omega
        exact hbox hall
      simpa using neg_mem hmemU
  · ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]
    have hx : proj₀ (emb₀ (eW x)) = eW x := congr($hretract₀ (eW x))
    rw [hx, eW.symm_apply_apply]

/-- **Kedlaya–Liu II, Corollary 2.4.9(a) (pro-projectivity).** Over a complete Hausdorff
nonarchimedean ring `A` with countably generated neighbourhoods of `0` (in particular, any complete
Hausdorff Huber or Tate ring), the completed restricted power-series algebra `A⟨X₁, …, Xₖ⟩` is
pro-projective over `A` for every `k : ℕ`. -/
theorem isProProjective_restrictedMvPowerSeriesCompletion (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    [(𝓝 (0 : A)).IsCountablyGenerated] :
    IsProProjective A (restrictedMvPowerSeriesCompletion k A) :=
  (isProProjective_weightedRestrictedSubring k A).of_uniformLinearEquiv
    (restrictedMvPowerSeriesCompletionAlgEquiv k A).symm.toLinearEquiv
    (by
      rw [AlgEquiv.coe_toLinearEquiv, coe_restrictedMvPowerSeriesCompletionAlgEquiv_symm]
      exact uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm)
    (by
      -- Identify `((e.symm).toLinearEquiv).symm` with `⇑e` to apply `coe_...AlgEquiv`.
      change UniformContinuous ⇑(restrictedMvPowerSeriesCompletionAlgEquiv k A)
      rw [coe_restrictedMvPowerSeriesCompletionAlgEquiv]
      exact uniformContinuous_restrictedMvPowerSeriesCompletionEquiv)

/-- **Kedlaya–Liu II, Corollary 2.4.9(a) (`2`-pseudoflatness).** Over a complete Hausdorff Tate
ring `A`, `A⟨X₁, …, Xₖ⟩` is `2`-pseudoflat over `A` for every `k : ℕ`. -/
theorem isPseudoFlat_restrictedMvPowerSeriesCompletion (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
    [IsTateRing A] :
    IsPseudoFlat A (restrictedMvPowerSeriesCompletion k A) 2 :=
  IsPseudoFlat.of_isProProjective (isProProjective_restrictedMvPowerSeriesCompletion k A)

/-- **Kedlaya–Liu II, Corollary 2.4.9(b) (pro-projectivity).** Over a complete Hausdorff
nonarchimedean ring `A` with countably generated neighbourhoods of `0`, the ring
`RestrictedLaurentSeries A` (`A⟨T, T⁻¹⟩`) of restricted Laurent series is pro-projective over
`A`. -/
theorem isProProjective_restrictedLaurentSeries (A : Type*) [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    [(𝓝 (0 : A)).IsCountablyGenerated] :
    IsProProjective A (RestrictedLaurentSeries A) :=
  (isProProjective_weightedRestrictedSubring 1 A).of_uniformLinearEquiv
    (RestrictedLaurentSeries.toWeightedLinearEquiv A).symm
    (RestrictedLaurentSeries.toWeightedUniformEquiv A).uniformContinuous_invFun
    (RestrictedLaurentSeries.toWeightedUniformEquiv A).uniformContinuous_toFun

/-- **Kedlaya–Liu II, Corollary 2.4.9(b) (`2`-pseudoflatness on `RestrictedLaurentSeries`).** Over
a complete Hausdorff Tate ring `A`, `RestrictedLaurentSeries A` is `2`-pseudoflat over `A`. -/
theorem isPseudoFlat_restrictedLaurentSeries (A : Type*) [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A] :
    IsPseudoFlat A (RestrictedLaurentSeries A) 2 :=
  IsPseudoFlat.of_isProProjective (isProProjective_restrictedLaurentSeries A)

/-- **Kedlaya–Liu II, Corollary 2.4.9(b) (`2`-pseudoflatness on `twoSidedRestrictedSubmodule`).**
Over a complete Hausdorff Tate ring `A`, `twoSidedRestrictedSubmodule A A` (`A⟨T, T⁻¹⟩`) is
`2`-pseudoflat over `A`. -/
theorem isPseudoFlat_twoSidedRestrictedSubmodule (A : Type*) [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A] :
    IsPseudoFlat A (twoSidedRestrictedSubmodule A A) 2 :=
  (isPseudoFlat_restrictedLaurentSeries A).of_equiv
    (RestrictedLaurentSeries.toTwoSidedLinearEquiv A)

end RestrictedProProjective

end TauCeti.Huber
