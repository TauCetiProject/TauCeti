/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.PseudoFlat
public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.TensorProduct.ZeroAtFilter
import TauCeti.RingTheory.Huber.Restricted.BaseChange

/-!
# `2`-pseudoflatness for null-family modules and restricted series

Over a complete Hausdorff Tate ring `A`, bijectivity of `M ⊗[A] A⟨T⟩ ≃ₗ[A] M⟨T⟩` for finitely
presented naturally complete modules (`restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete`)
shows that for every index type `ι` the null-family module `c₀(ι, A)` satisfies
`Tor₁^A(P, c₀(ι, A)) = 0` for all `2`-pseudocoherent `A`-modules `P`
(`TauCeti.Huber.rTensor_injective_zeroAtFilterSubmodule`), hence is `2`-pseudoflat
(`TauCeti.Huber.isPseudoFlat_zeroAtFilterSubmodule`). By linear equivalence, `A⟨X₁, …, Xₖ⟩`
(`TauCeti.Huber.isPseudoFlat_restrictedMvPowerSeriesCompletion`) and `A⟨T, T⁻¹⟩`
(`TauCeti.Huber.isPseudoFlat_twoSidedRestrictedSubmodule`) are `2`-pseudoflat (Kedlaya–Liu II,
Corollary 2.4.9(a)–(b)), as is any `A`-linear retract of `c₀(ι, A)` (`IsPseudoFlat.of_retract`).
Continuous projectors onto finite projective summands converging pointwise to `id` on an ultrametric
Banach `A`-module do not suffice without uniform coordinate splittings; see
`TauCeti.Examples.exists_banach_projectors_not_isPseudoFlat`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Lemma 2.4.7 and Corollaries 2.4.8–2.4.9.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.49, Example 6.39, and Remark 8.29.
-/

public section

open Filter Topology
open scoped TensorProduct Uniformity

namespace TauCeti.Huber

section TorVanishing

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] {M N P : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N] [AddCommGroup P]
  [Module A P] {i : M →ₗ[A] N} {p : N →ₗ[A] P}

private theorem rTensor_injective_zeroAtFilterSubmodule_nat (hi : Function.Injective i)
    (hp : Function.Surjective p) (hexact : Function.Exact i p) (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective
      (i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ))) := by
  have hker_coh : IsPseudoCoherentOver A (LinearMap.ker p) 1 :=
    (hP : IsPseudoCoherentOver A P ((1 : ℕ∞) + 1)).ker_of_projective hp
  let eM : M ≃ₗ[A] LinearMap.ker p :=
    LinearEquiv.ofBijective (i.codRestrict (LinearMap.ker p) hexact.apply_apply_eq_zero)
      ⟨fun _ _ hxy ↦ hi (congrArg Subtype.val hxy), fun ⟨y, hy⟩ ↦
        let ⟨x, hx⟩ := (hexact y).mp hy; ⟨x, Subtype.ext hx⟩⟩
  have hM_coh : IsPseudoCoherentOver A M 1 := hker_coh.of_equiv eM.symm
  have := IsPseudoCoherentOver.one_iff.mp hM_coh; have := hM_coh.finite
  have := IsPseudoCoherentOver.one_iff.mp (IsPseudoCoherentOver.of_projective.mono le_top :
    IsPseudoCoherentOver A N 1)
  have hM_nc : IsNaturallyComplete A M :=
    (IsNaturallyComplete.of_projective (M := N)).of_injective hi
  let _ : TopologicalSpace M := moduleTopology A M; let _ : TopologicalSpace N := moduleTopology A N
  have _ : IsModuleTopology A M := ⟨rfl⟩; have _ : IsModuleTopology A N := ⟨rfl⟩
  have _ := IsModuleTopology.toContinuousAdd A M; have _ := IsModuleTopology.toContinuousAdd A N
  have _ := IsModuleTopology.toContinuousSMul A M; have _ := IsModuleTopology.toContinuousSMul A N
  have hi_cont : ContinuousAt i 0 := (IsModuleTopology.continuous_of_linearMap i).continuousAt
  let S := restrictedMvPowerSeriesSubring 1 A
  have hinj_S : Function.Injective (i.rTensor S) := fun z₁ z₂ hz ↦
    (restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete (k := 1) hM_nc).injective <|
      restrictedMvPowerSeriesSubmoduleMap_injective i hi_cont hi <| by
        rw [restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply,
          restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply,
          restrictedMvPowerSeriesSubmoduleMap_baseChange i hi_cont z₁,
          restrictedMvPowerSeriesSubmoduleMap_baseChange i hi_cont z₂]
        exact congrArg restrictedMvPowerSeriesBaseChange hz
  exact (i.injective_rTensor_congr (restrictedMvPowerSeriesSubringLinearEquiv 1 A ≪≫ₗ
    restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A A ≪≫ₗ
    zeroAtFilterCofiniteCongr A A (Finsupp.uniqueEquiv (0 : Fin 1)))).mp hinj_S

private theorem rTensor_injective_zeroAtFilterSubmodule_countable (ι : Type*) [Countable ι]
    (hi : Function.Injective i) (hp : Function.Surjective p) (hexact : Function.Exact i p)
    (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective
      (i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ι))) := by
  obtain ⟨emb, proj, hret⟩ := exists_retract_zeroAtFilterSubmodule_nat A A ι
  exact i.injective_rTensor_of_comp_eq_id hret
    (rTensor_injective_zeroAtFilterSubmodule_nat hi hp hexact hP)

/-- **Vanishing of `Tor₁` against `c₀(ι, A)` for any index type `ι`** (the null-family core of
Kedlaya–Liu II, Lemma 2.4.7). Over a complete Hausdorff Tate ring `A`, for any index type `ι`
(not necessarily countable) and any short exact sequence `0 → M →[i] N →[p] P → 0` with `N` finite
projective and `P` `2`-pseudocoherent, `i.rTensor c₀(ι, A)` is injective. -/
theorem rTensor_injective_zeroAtFilterSubmodule (ι : Type*) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hexact : Function.Exact i p) (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective
      (i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ι))) := by
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : FirstCountableTopology A := UniformSpace.firstCountableTopology A
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨S, hS, w, rfl⟩ := z.exists_countable_lTensor_zeroAtFilterExtend_eq
  have : Countable S := hS.to_subtype
  have hret := zeroAtFilterComap_comp_extend A A (Subtype.val_injective (p := (· ∈ S)))
  have hw : i.rTensor _ w = 0 := by
    have hnat : LinearMap.lTensor N
        (zeroAtFilterComap A A (Subtype.val_injective (p := (· ∈ S))).tendsto_cofinite) ∘ₗ
        (i.rTensor _ ∘ₗ LinearMap.lTensor M (zeroAtFilterExtend A A (Subtype.val : S → ι))) =
        i.rTensor _ := by
      rw [← LinearMap.comp_assoc, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
        LinearMap.comp_assoc, ← LinearMap.lTensor_comp, hret, LinearMap.lTensor_id,
        LinearMap.comp_id]
    rw [← hnat, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero]
  rw [rTensor_injective_zeroAtFilterSubmodule_countable S hi hp hexact hP
    (hw.trans (map_zero _).symm), map_zero]

end TorVanishing

section PseudoFlat

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
