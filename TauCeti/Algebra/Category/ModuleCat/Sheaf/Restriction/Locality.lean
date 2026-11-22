/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction.OpenSubspace
import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism

/-!
# Open-cover locality for sheaves of modules

Using open-subspace restriction `TopologicalSpace.Opens.sheafOfModulesRestrict` and its
identification with pullback along `Opens.sheafInclusionHom`, isomorphisms, monomorphisms,
epimorphisms, and vanishing of sheaves of modules on a topological space `X` can be tested on the
members of an open cover of `X`.

## Main results

* `SheafOfModules.jointlyReflectIsomorphisms_sheafOfModulesRestrict` and
  `SheafOfModules.jointlyReflectIsomorphisms_pullback_sheafInclusionHom`: open-subspace
  restrictions and open-inclusion pullbacks over an open cover jointly reflect isomorphisms;
* `SheafOfModules.isIso_iff_sheafOfModulesRestrict_of_isOpenCover`,
  `SheafOfModules.isIso_iff_pullback_of_isOpenCover`,
  `SheafOfModules.mono_iff_sheafOfModulesRestrict_of_isOpenCover`,
  `SheafOfModules.mono_iff_pullback_of_isOpenCover`,
  `SheafOfModules.epi_iff_sheafOfModulesRestrict_of_isOpenCover`,
  `SheafOfModules.epi_iff_pullback_of_isOpenCover`,
  `SheafOfModules.isZero_iff_sheafOfModulesRestrict_of_isOpenCover`, and
  `SheafOfModules.isZero_iff_pullback_of_isOpenCover`: open-cover locality of isomorphisms,
  monomorphisms, epimorphisms, and zero objects.

## References

* [The Stacks Project, Tag 008F](https://stacks.math.columbia.edu/tag/008F)
-/

public section

open CategoryTheory Limits TopologicalSpace

universe v u

noncomputable section

namespace SheafOfModules

section OpenCoverLocality

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
  {ι : Type*} {U : ι → Opens X}

/-- Open-subspace restrictions to the members of an open cover jointly reflect isomorphisms of
module sheaves. -/
theorem jointlyReflectIsomorphisms_sheafOfModulesRestrict (hU : IsOpenCover U) :
    JointlyReflectIsomorphisms (fun i ↦ (U i).sheafOfModulesRestrict.{v} R) where
  isIso φ h := by
    refine isIso_of_coversTop ((Opens.coversTop_iff X U).mpr hU) fun i ↦ ?_
    have hmap : IsIso (((U i).sheafOfModulesEquivOver R).functor.map (φ.over (U i))) :=
      (NatIso.isIso_map_iff ((U i).overFunctorCompSheafOfModulesEquivOver R) φ).mpr (h i)
    exact isIso_of_reflects_iso (φ.over (U i)) ((U i).sheafOfModulesEquivOver R).functor

/-- Pullbacks along the open inclusions of an open cover jointly reflect isomorphisms of module
sheaves. -/
theorem jointlyReflectIsomorphisms_pullback_sheafInclusionHom (hU : IsOpenCover U) :
    JointlyReflectIsomorphisms
      (fun i ↦ pullback.{v} ((U i).sheafInclusionHom RingCat.{u} R)) where
  isIso φ h := by
    have : ∀ i, IsIso (((U i).sheafOfModulesRestrict.{v} R).map φ) := fun i ↦
      (NatIso.isIso_map_iff ((U i).sheafOfModulesRestrictIsoPullback.{v} R) φ).mpr (h i)
    exact (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).isIso φ

/-- A morphism of module sheaves on `X` is an isomorphism if and only if its restrictions to the
members of an open cover are isomorphisms. -/
theorem isIso_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ i, IsIso (((U i).sheafOfModulesRestrict.{v} R).map φ) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦
    (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).isIso φ⟩

/-- A morphism of module sheaves on `X` is an isomorphism if and only if its pullbacks to the
members of an open cover are isomorphisms. -/
theorem isIso_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ i, IsIso ((pullback.{v} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦
    (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).isIso φ⟩

/-- Monomorphisms of module sheaves on `X` can be checked after open-subspace restriction to an open
cover. -/
theorem mono_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Mono φ ↔ ∀ i, Mono (((U i).sheafOfModulesRestrict.{u} R).map φ) :=
  (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).jointlyReflectMonomorphisms.mono_iff φ

/-- Monomorphisms of module sheaves on `X` can be checked after pullback to an open cover. -/
theorem mono_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Mono φ ↔ ∀ i, Mono ((pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).jointlyReflectMonomorphisms.mono_iff φ

/-- Epimorphisms of module sheaves on `X` can be checked after open-subspace restriction to an open
cover. -/
theorem epi_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Epi φ ↔ ∀ i, Epi (((U i).sheafOfModulesRestrict.{u} R).map φ) :=
  haveI : ∀ i, ((U i).sheafOfModulesRestrict.{u} R).PreservesEpimorphisms :=
    fun _ ↦ Functor.preservesEpimorphisms_of_isLeftAdjoint _
  (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).jointlyReflectEpimorphisms.epi_iff φ

/-- Epimorphisms of module sheaves on `X` can be checked after pullback to an open cover. -/
theorem epi_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Epi φ ↔ ∀ i, Epi ((pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  haveI : ∀ i, (pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).PreservesEpimorphisms :=
    fun _ ↦ Functor.preservesEpimorphisms_of_isLeftAdjoint _
  (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).jointlyReflectEpimorphisms.epi_iff φ

/-- A module sheaf on `X` is zero if and only if its restrictions to the members of an open cover
are zero. -/
theorem isZero_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    (M : SheafOfModules.{v} R) :
    IsZero M ↔ ∀ i, IsZero (((U i).sheafOfModulesRestrict.{v} R).obj M) := by
  refine ⟨fun hM i ↦ ((U i).sheafOfModulesRestrict.{v} R).map_isZero hM, fun h ↦ ?_⟩
  rw [IsZero.iff_id_eq_zero]
  have : IsIso (0 : M ⟶ M) := by
    rw [isIso_iff_sheafOfModulesRestrict_of_isOpenCover hU]
    intro i
    rw [Functor.map_zero, ← (h i).eq_of_src (𝟙 _) 0]
    infer_instance
  rw [← cancel_epi (0 : M ⟶ M), comp_zero, zero_comp]

/-- A module sheaf on `X` is zero if and only if its pullbacks to the members of an open cover are
zero. -/
theorem isZero_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    (M : SheafOfModules.{v} R) :
    IsZero M ↔ ∀ i, IsZero ((pullback.{v} ((U i).sheafInclusionHom RingCat.{u} R)).obj M) := by
  rw [isZero_iff_sheafOfModulesRestrict_of_isOpenCover hU]
  exact forall_congr' fun i ↦ (((U i).sheafOfModulesRestrictIsoPullback.{v} R).app M).isZero_iff

end OpenCoverLocality

end SheafOfModules

end
