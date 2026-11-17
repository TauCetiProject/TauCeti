/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.RingTheory.Huber.ModuleTopology.PseudoFlat
public import TauCeti.RingTheory.Huber.Restricted.BaseChange
public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Ring
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import Mathlib.Logic.Equiv.Nat
import TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# Non-noetherian restricted-series base change and `2`-pseudoflatness

Over any complete Hausdorff Tate ring `A` (with no noetherian hypothesis), the comparison map
`M ⊗[A] A⟨X₁, …, Xₖ⟩ → M⟨X₁, …, Xₖ⟩` of `TauCeti.RingTheory.Huber.Restricted.BaseChange` is
surjective for every finite `A`-module `M` with its module topology (requiring only that `A` be a
nonarchimedean ring with countably generated neighbourhoods of `0`), and bijective whenever `M` is
finitely presented and naturally complete over `A`
(`TauCeti.Huber.restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete`). Indeed,
natural completeness makes the kernel of any finite free presentation `Aⁿ →[u] Aᵐ →[p] M → 0`
closed, so Henkel's open mapping theorem makes `u` strict onto its image.

Specialising to one-variable restricted power series and two-sided restricted Laurent series yields
Kedlaya–Liu II, Corollary 2.4.9(c), and shows that for every index type `ι` the null-family module
`c₀(ι, A)` (`Filter.zeroAtFilterSubmodule (β := A) A Filter.cofinite`) satisfies
`Tor₁^A(P, c₀(ι, A)) = 0` for all `2`-pseudocoherent `A`-modules `P`
(`TauCeti.Huber.rTensor_injective_zeroAtFilterSubmodule`), hence is `2`-pseudoflat
(`TauCeti.Huber.isPseudoFlat_zeroAtFilterSubmodule`). By transport along linear equivalences,
`A⟨X₁, …, Xₖ⟩` (`TauCeti.Huber.isPseudoFlat_restrictedMvPowerSeriesCompletion`) and `A⟨T, T⁻¹⟩`
(`TauCeti.Huber.isPseudoFlat_twoSidedRestrictedSubmodule`) are `2`-pseudoflat (Kedlaya–Liu II,
Corollary 2.4.9(a)–(b)), and every `A`-linear retract of `c₀(ι, A)` is `2`-pseudoflat by
`TauCeti.Huber.IsPseudoFlat.of_retract`.

We intentionally do not define a general pro-projectivity predicate (Kedlaya–Liu II,
Definition 2.4.6) here: continuous finite-projective projectors converging pointwise to the identity
on a complete metrizable (indeed, ultrametric Banach) `A`-module do not by themselves imply
`2`-pseudoflatness, as verified by the formal counterexample in
`TauCeti.Examples.RingTheory.Huber.ModuleTopology.PseudoFlat`.

## Main definitions

* `TauCeti.Huber.zeroAtFilterCofiniteCongr`: reindexing `c₀(ι, M)` along an equivalence `ι ≃ κ`.
* `TauCeti.Huber.restrictedCoeff`: the `n`-th coefficient `A⟨T⟩ →ₗ[A] A` on
  `restrictedMvPowerSeriesCompletion 1 A`.
* `TauCeti.Huber.restrictedPowerSeriesTensorToNull`: the comparison map
  `A⟨T⟩ ⊗[A] M →ₗ[A] c₀(ℕ, M)` sending `f ⊗ₜ v` to `n ↦ restrictedCoeff n f • v`.
* `TauCeti.Huber.restrictedLaurentSeriesTensorToNull`: the Laurent comparison map
  `A⟨T, T⁻¹⟩ ⊗[A] M →ₗ[A] M⟨T, T⁻¹⟩` sending `f ⊗ₜ v` to `n ↦ f n • v` for `n : ℤ`.

## Main results

* `TauCeti.Huber.exists_retract_zeroAtFilterSubmodule_nat`: for countable `ι`, `c₀(ι, M)` is an
  `A`-linear retract of `c₀(ℕ, M)`.
* `TauCeti.Huber.restrictedMvPowerSeriesBaseChange_surjective_of_finite` and
  `TauCeti.Huber.restrictedMvPowerSeriesBaseChange_bijective_of_isNaturallyComplete`.
* `TauCeti.Huber.restrictedPowerSeriesTensorToNull_surjective`,
  `TauCeti.Huber.restrictedPowerSeriesTensorToNull_bijective`,
  `TauCeti.Huber.restrictedLaurentSeriesTensorToNull_surjective`, and
  `TauCeti.Huber.restrictedLaurentSeriesTensorToNull_bijective`: Corollary 2.4.9(c).
* `TauCeti.Huber.rTensor_injective_zeroAtFilterSubmodule` and
  `TauCeti.Huber.isPseudoFlat_zeroAtFilterSubmodule`: `Tor₁` vanishing and `2`-pseudoflatness for
  `c₀(ι, A)` with arbitrary index type `ι`.
* `TauCeti.Huber.isPseudoFlat_restrictedMvPowerSeriesCompletion` and
  `TauCeti.Huber.isPseudoFlat_twoSidedRestrictedSubmodule`: `2`-pseudoflatness of
  `A⟨X₁, …, Xₖ⟩` and `A⟨T, T⁻¹⟩` (Corollary 2.4.9(a)–(b)).

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Lemma 2.4.7 and Corollaries 2.4.8–2.4.9.
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

private noncomputable def zeroAtFilterExtend (A M : Type*) [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] {κ ι : Type*}
    (j : κ → ι) :
    Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter κ) →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι) where
  toFun f := by
    classical
    refine ⟨fun x ↦ if h : ∃ i, j i = x then (f : κ → M) h.choose else 0, fun U hU ↦ ?_⟩
    rw [Filter.mem_map, Filter.mem_cofinite]
    refine ((Filter.mem_cofinite.mp (Filter.mem_map.mp (f.2 hU))).image j).subset fun x hx ↦ ?_
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hx
    by_cases h : ∃ i, j i = x
    · exact ⟨h.choose, by simpa [h] using hx, h.choose_spec⟩
    · exact absurd (by simpa [h] using mem_of_mem_nhds hU) hx
  map_add' _ _ := by
    classical exact Subtype.ext <| funext fun x ↦ by by_cases h : ∃ i, j i = x <;> simp [h]
  map_smul' _ _ := by
    classical exact Subtype.ext <| funext fun x ↦ by by_cases h : ∃ i, j i = x <;> simp [h]

private def zeroAtFilterRestrict (A M : Type*) [Semiring A] [AddCommMonoid M] [TopologicalSpace M]
    [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] {κ ι : Type*} {j : κ → ι}
    (hj : Function.Injective j) :
    Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter ι) →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := M) A (Filter.cofinite : Filter κ) where
  toFun g := ⟨fun i ↦ (g : ι → M) (j i), Filter.Tendsto.comp g.2 hj.tendsto_cofinite⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem zeroAtFilterRestrict_comp_extend (A M : Type*) [Semiring A] [AddCommMonoid M]
    [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M] {κ ι : Type*}
    {j : κ → ι} (hj : Function.Injective j) :
    zeroAtFilterRestrict A M hj ∘ₗ zeroAtFilterExtend A M j = LinearMap.id := by
  classical
  refine LinearMap.ext fun f ↦ Subtype.ext <| funext fun i ↦ ?_
  dsimp [zeroAtFilterRestrict, zeroAtFilterExtend]
  split_ifs with h'
  · exact congrArg (f : κ → M) (hj h'.choose_spec)
  · exact absurd ⟨i, rfl⟩ h'

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
  obtain ⟨j, hj⟩ := Countable.exists_injective_nat ι
  exact ⟨zeroAtFilterExtend A M j, zeroAtFilterRestrict A M hj,
    zeroAtFilterRestrict_comp_extend A M hj⟩

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

/-! ### Null-sequence comparison for `A⟨T, T⁻¹⟩` -/

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

end LaurentSeries

/-! ### `Tor₁` vanishing and `2`-pseudoflatness for null families and restricted series -/

section PseudoFlat

private theorem countable_support_of_mem_zeroAtFilterSubmodule {A ι : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [ContinuousConstSMul A A] [T0Space A]
    [(𝓤 A).IsCountablyGenerated]
    (f : Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ι)) :
    (Function.support (f : ι → A)).Countable := by
  have : FirstCountableTopology A := UniformSpace.firstCountableTopology A
  obtain ⟨U, hU⟩ := Filter.exists_antitone_basis (𝓝 (0 : A))
  have hsub : Function.support (f : ι → A) ⊆ ⋃ n : ℕ, {x : ι | (f : ι → A) x ∉ U n} := by
    intro x hx
    rw [Set.mem_iUnion]
    by_contra! hall
    apply hx
    exact tendsto_nhds_unique (f := fun _ : ℕ ↦ (f : ι → A) x) (l := atTop) tendsto_const_nhds
      (hU.tendsto_right_iff.mpr fun n _ ↦ Filter.Eventually.of_forall fun _ ↦ not_not.mp (hall n))
  exact (Set.countable_iUnion fun n ↦
    (Filter.mem_cofinite.mp (Filter.mem_map.mp (f.2 (hU.mem n)))).countable).mono hsub

private theorem zeroAtFilterExtend_comp_inclusion {A ι : Type*} [Semiring A] [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousConstSMul A A] {S₁ S₂ : Set ι} (hsub : S₁ ⊆ S₂) :
    zeroAtFilterExtend A A (Subtype.val : S₂ → ι) ∘ₗ
        zeroAtFilterExtend A A (Set.inclusion hsub) =
      zeroAtFilterExtend A A (Subtype.val : S₁ → ι) := by
  classical
  refine LinearMap.ext fun f ↦ Subtype.ext <| funext fun x ↦ ?_
  change (if h₂ : ∃ s : S₂, s.1 = x then
      if h₁ : ∃ s₁ : S₁, Set.inclusion hsub s₁ = h₂.choose then (f : S₁ → A) h₁.choose else 0
    else 0) =
    if h : ∃ s₁ : S₁, s₁.1 = x then (f : S₁ → A) h.choose else 0
  by_cases hx : x ∈ S₁
  · have h₂ : ∃ s : S₂, s.1 = x := ⟨⟨x, hsub hx⟩, rfl⟩
    have h₁ : ∃ s₁ : S₁, Set.inclusion hsub s₁ = h₂.choose :=
      ⟨⟨x, hx⟩, Subtype.ext h₂.choose_spec.symm⟩
    have h : ∃ s₁ : S₁, s₁.1 = x := ⟨⟨x, hx⟩, rfl⟩
    simp only [h₂, h₁, h, ↓reduceDIte]
    exact congrArg (f : S₁ → A) (Subtype.ext <| (congrArg Subtype.val h₁.choose_spec).trans
      (h₂.choose_spec.trans h.choose_spec.symm))
  · have h : ¬ ∃ s₁ : S₁, s₁.1 = x := fun ⟨s₁, hs₁⟩ ↦ hx (hs₁ ▸ s₁.2)
    simp only [h, ↓reduceDIte]
    split_ifs with h₂ h₁
    · exact absurd ((congrArg Subtype.val h₁.choose_spec).trans h₂.choose_spec ▸ h₁.choose.2) hx
    · rfl
    · rfl

private theorem rTensor_injective_zeroAtFilterSubmodule_nat {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
    [IsTateRing A] {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Projective A N] [AddCommGroup P] [Module A P]
    {i : M →ₗ[A] N} {p : N →ₗ[A] P} (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : Function.Exact i p) (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective
      (i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ))) := by
  have hker_coh : IsPseudoCoherentOver A (LinearMap.ker p) 1 :=
    (hP : IsPseudoCoherentOver A P ((1 : ℕ∞) + 1)).ker_of_projective hp
  let eM : M ≃ₗ[A] LinearMap.ker p :=
    LinearEquiv.ofBijective (i.codRestrict (LinearMap.ker p) hexact.apply_apply_eq_zero)
      ⟨fun x y hxy ↦ hi (congrArg Subtype.val hxy), fun ⟨y, hy⟩ ↦
        let ⟨x, hx⟩ := (hexact y).mp hy; ⟨x, Subtype.ext hx⟩⟩
  have hM_coh : IsPseudoCoherentOver A M 1 := hker_coh.of_equiv eM.symm
  have : Module.FinitePresentation A M := IsPseudoCoherentOver.one_iff.mp hM_coh
  have : Module.Finite A M := hM_coh.finite
  have : Module.FinitePresentation A N :=
    IsPseudoCoherentOver.one_iff.mp (IsPseudoCoherentOver.of_projective.mono le_top)
  have hN_nc : IsNaturallyComplete A N := IsNaturallyComplete.of_projective
  have hM_nc : IsNaturallyComplete A M := hN_nc.of_injective hi
  let _ : TopologicalSpace M := moduleTopology A M; let _ : TopologicalSpace N := moduleTopology A N
  have _ : IsModuleTopology A M := ⟨rfl⟩; have _ : IsModuleTopology A N := ⟨rfl⟩
  have _ := IsModuleTopology.toContinuousAdd A M; have _ := IsModuleTopology.toContinuousAdd A N
  have _ := IsModuleTopology.toContinuousSMul A M; have _ := IsModuleTopology.toContinuousSMul A N
  have hi_cont : Continuous i := IsModuleTopology.continuous_of_linearMap i
  let S := restrictedMvPowerSeriesSubring 1 A
  have hinj_S : Function.Injective (i.rTensor S) := fun z₁ z₂ hz ↦
    (restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete (k := 1) hM_nc).injective <|
      restrictedMvPowerSeriesSubmoduleMap_injective i hi_cont.continuousAt hi <| by
        rw [restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply,
          restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply,
          restrictedMvPowerSeriesSubmoduleMap_baseChange i hi_cont.continuousAt z₁,
          restrictedMvPowerSeriesSubmoduleMap_baseChange i hi_cont.continuousAt z₂]
        exact congrArg restrictedMvPowerSeriesBaseChange hz
  let eNat : S ≃ₗ[A] Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) :=
    restrictedMvPowerSeriesSubringLinearEquiv 1 A ≪≫ₗ
      restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A A ≪≫ₗ
      zeroAtFilterCofiniteCongr A A (Finsupp.uniqueEquiv (0 : Fin 1))
  have hcomm : (LinearEquiv.lTensor N eNat).toLinearMap ∘ₗ i.rTensor S ∘ₗ
      (LinearEquiv.lTensor M eNat.symm).toLinearMap =
      i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) := by
    ext; simp
  rw [← hcomm]
  exact (LinearEquiv.lTensor N eNat).injective.comp
    (hinj_S.comp (LinearEquiv.lTensor M eNat.symm).injective)

private theorem rTensor_injective_zeroAtFilterSubmodule_countable {A : Type*} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
    [IsTateRing A] (ι : Type*) [Countable ι] {M N P : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N] [AddCommGroup P]
    [Module A P] {i : M →ₗ[A] N} {p : N →ₗ[A] P} (hi : Function.Injective i)
    (hp : Function.Surjective p) (hexact : Function.Exact i p)
    (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective
      (i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ι))) := by
  obtain ⟨emb, proj, hret⟩ := exists_retract_zeroAtFilterSubmodule_nat A A ι
  have hli : LinearMap.lTensor M proj ∘ₗ LinearMap.lTensor M emb = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hret, LinearMap.lTensor_id]
  have hsq : LinearMap.lTensor N emb ∘ₗ i.rTensor _ =
      i.rTensor _ ∘ₗ LinearMap.lTensor M emb := by ext; rfl
  exact Function.Injective.of_comp (f := LinearMap.lTensor N emb) <| by
    rw [← LinearMap.coe_comp, hsq]
    exact (rTensor_injective_zeroAtFilterSubmodule_nat hi hp hexact hP).comp
      (Function.LeftInverse.injective fun z ↦ congr($hli z))

/-- **Vanishing of `Tor₁` against `c₀(ι, A)` for any index type `ι`** (the null-family core of
Kedlaya–Liu II, Lemma 2.4.7). Over a complete Hausdorff Tate ring `A`, for any index type `ι`
(not necessarily countable) and any short exact sequence `0 → M →[i] N →[p] P → 0` with `N` finite
projective and `P` `2`-pseudocoherent, `i.rTensor c₀(ι, A)` is injective. -/
theorem rTensor_injective_zeroAtFilterSubmodule {A : Type*} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    (ι : Type*) {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Projective A N] [AddCommGroup P] [Module A P]
    {i : M →ₗ[A] N} {p : N →ₗ[A] P} (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : Function.Exact i p) (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective
      (i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ι))) := by
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have hsupp : ∀ z : M ⊗[A] Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ι),
      ∃ (S : Set ι), S.Countable ∧
        ∃ w : M ⊗[A] Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter S),
          LinearMap.lTensor M (zeroAtFilterExtend A A (Subtype.val : S → ι)) w = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m f =>
      refine ⟨Function.support (f : ι → A), countable_support_of_mem_zeroAtFilterSubmodule f,
        m ⊗ₜ[A] zeroAtFilterRestrict A A Subtype.val_injective f, ?_⟩
      simp only [LinearMap.lTensor_tmul]
      congr 1; classical
      refine Subtype.ext <| funext fun x ↦ ?_
      change (if h : ∃ s : Function.support (f : ι → A), s.1 = x then
          (f : ι → A) h.choose.1 else 0) = (f : ι → A) x
      by_cases hx : (f : ι → A) x = 0
      · split_ifs with h
        · rw [h.choose_spec, hx]
        · exact hx.symm
      · have h : ∃ s : Function.support (f : ι → A), s.1 = x := ⟨⟨x, hx⟩, rfl⟩
        simp only [h, ↓reduceDIte, h.choose_spec]
    | add z₁ z₂ ih₁ ih₂ =>
      obtain ⟨S₁, hS₁, w₁, rfl⟩ := ih₁
      obtain ⟨S₂, hS₂, w₂, rfl⟩ := ih₂
      refine ⟨S₁ ∪ S₂, hS₁.union hS₂,
        LinearMap.lTensor M (zeroAtFilterExtend A A (Set.inclusion Set.subset_union_left)) w₁ +
          LinearMap.lTensor M (zeroAtFilterExtend A A (Set.inclusion Set.subset_union_right)) w₂,
        ?_⟩
      rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        ← LinearMap.lTensor_comp, zeroAtFilterExtend_comp_inclusion,
        zeroAtFilterExtend_comp_inclusion]
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨S, hS, w, rfl⟩ := hsupp z
  have : Countable S := hS.to_subtype
  have hret := zeroAtFilterRestrict_comp_extend A A (Subtype.val_injective (p := (· ∈ S)))
  have hw : i.rTensor _ w = 0 := by
    have hnat :
        LinearMap.lTensor N (zeroAtFilterRestrict A A (Subtype.val_injective (p := (· ∈ S)))) ∘ₗ
            i.rTensor _ ∘ₗ
            LinearMap.lTensor M (zeroAtFilterExtend A A (Subtype.val : S → ι)) =
          i.rTensor _ := by
      refine TensorProduct.ext' fun m f ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
      congr 1
      exact congr($hret f)
    rw [← hnat, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero]
  have hw0 : w = 0 :=
    rTensor_injective_zeroAtFilterSubmodule_countable S hi hp hexact hP
      (hw.trans (map_zero _).symm)
  rw [hw0, map_zero]

/-- **Null-family modules `c₀(ι, A)` are `2`-pseudoflat** over a complete Hausdorff Tate ring `A`,
for every index type `ι`. Any `A`-linear retract of `c₀(ι, A)` is therefore also `2`-pseudoflat by
`TauCeti.Huber.IsPseudoFlat.of_retract`. -/
theorem isPseudoFlat_zeroAtFilterSubmodule (ι : Type*) (A : Type*) [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A] :
    IsPseudoFlat A (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ι)) 2 :=
  isPseudoFlat_iff.mpr fun _ K hK ↦ rTensor_injective_zeroAtFilterSubmodule ι
    K.injective_subtype (Submodule.mkQ_surjective K) (LinearMap.exact_subtype_mkQ K)
    hK.isPseudoCoherentOver

/-- **Kedlaya–Liu II, Corollary 2.4.9(a)–(b) (`2`-pseudoflatness of `A⟨X₁, …, Xₖ⟩`).** Over a
complete Hausdorff Tate ring `A`, the completed restricted power-series algebra `A⟨X₁, …, Xₖ⟩` is
`2`-pseudoflat over `A`. -/
theorem isPseudoFlat_restrictedMvPowerSeriesCompletion (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
    [IsTateRing A] :
    IsPseudoFlat A (restrictedMvPowerSeriesCompletion k A) 2 :=
  (isPseudoFlat_zeroAtFilterSubmodule (Fin k →₀ ℕ) A).of_equiv
    ((restrictedMvPowerSeriesCompletionSubringAlgEquiv k A).toLinearEquiv ≪≫ₗ
      restrictedMvPowerSeriesSubringLinearEquiv k A ≪≫ₗ
      restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter k A A).symm

/-- **Kedlaya–Liu II, Corollary 2.4.9(a)–(b) (`2`-pseudoflatness of `A⟨T, T⁻¹⟩`).** Over a complete
Hausdorff Tate ring `A`, the two-sided restricted Laurent-series algebra `A⟨T, T⁻¹⟩` is
`2`-pseudoflat over `A`. -/
theorem isPseudoFlat_twoSidedRestrictedSubmodule (A : Type*) [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A] :
    IsPseudoFlat A (twoSidedRestrictedSubmodule A A) 2 :=
  (isPseudoFlat_zeroAtFilterSubmodule ℤ A).of_equiv
    (twoSidedRestrictedSubmoduleEquivZeroAtFilter A A).symm

end PseudoFlat

end TauCeti.Huber
