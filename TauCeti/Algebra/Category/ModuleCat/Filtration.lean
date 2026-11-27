/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import TauCeti.CategoryTheory.Filtration.Basic

/-!
# Filtrations of modules by submodules

A family `F : I → Submodule R M` of submodules, indexed by a category `I` and with `F i ≤ F j`
for every morphism `i ⟶ j`, is a filtered object of `ModuleCat R` indexed by `I`
(`CategoryTheory.FilteredObject.ofSubmodules`), whose step `F_i` is the subobject of `F i`
(`step_ofSubmodules`). An antitone family `ℤ → Submodule R M`, read at `ℤᵒᵖ`, is a decreasing
filtration, and a monotone family on a preorder an increasing one. Mathlib's order isomorphism
`ModuleCat.subobjectModule` between subobjects and submodules carries the steps to the submodules
`F i` (`subobjectModule_step_ofSubmodules`), so the lattice conditions on the steps read in the
lattice of submodules.

## Main results

* `isExhaustive_ofSubmodules_iff_iSup`, `isExhaustive_ofSubmodules_iff_forall_mem`: the
  filtration is exhaustive exactly when `⨆ i, F i = ⊤`, that is, for a filtered index category,
  when every element lies in some `F i`.
* `isSeparated_ofSubmodules_iff_iInf`, `isSeparated_ofSubmodules_iff_forall_mem`: the filtration
  is separated exactly when `⨅ i, F i = ⊥`, that is, when only `0` lies in every `F i`.
* `cokernel_π_stepι_ofSubmodules_apply_eq_iff`: through `ModuleCat.cokernelIsoRangeQuotient`,
  two elements of `M` agree in the quotient `M / F_i` exactly when their difference lies in `F i`.
* `comp_cokernel_π_stepι_ofSubmodules_eq_iff`: two maps `f g : A ⟶ M` agree in the quotient
  `M / F_i` exactly when `f a - g a ∈ F i` for all `a`.
-/

public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.FilteredObject

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {I : Type*} [Category* I]

/-- The filtered module with steps a family `F` of submodules that increases along the morphisms
of the index category. -/
noncomputable abbrev ofSubmodules (F : I → Submodule R M) (hF : ∀ ⦃i j⦄, (i ⟶ j) → F i ≤ F j) :
    FilteredObject (ModuleCat.{v} R) I where
  X := ModuleCat.of R M
  filtration.toMonoOver :=
    { obj i := MonoOver.mk (hf := ModuleCat.mono_as_hom'_subtype (X := ModuleCat.of R M) (F i))
        (ModuleCat.ofHom (F i).subtype)
      map f := MonoOver.homMk (ModuleCat.ofHom (Submodule.inclusion (hF f))) rfl }

variable (F : I → Submodule R M) (hF : ∀ ⦃i j⦄, (i ⟶ j) → F i ≤ F j)

/-- The inclusion of the step `F_i` of `ofSubmodules F hF` is the inclusion of `F i`. -/
@[simp]
theorem stepι_ofSubmodules (i : I) :
    (ofSubmodules F hF).stepι i = ModuleCat.ofHom (F i).subtype := by
  rw [← FilteredObject.filtration_ι_app]
  rfl

/-- The linear map underlying the inclusion of the step `F_i` is the inclusion of `F i`. -/
theorem hom_stepι_ofSubmodules (i : I) : ((ofSubmodules F hF).stepι i).hom = (F i).subtype := by
  rw [stepι_ofSubmodules]
  -- The rewritten `ModuleCat.Hom.hom` still carries the step and `X` of `ofSubmodules F hF` as its
  -- implicit objects, which are `ModuleCat.of R (F i)` and `ModuleCat.of R M` only up to
  -- unfolding, so `ModuleCat.hom_ofHom` is applied by `exact` rather than by `rw`.
  exact ModuleCat.hom_ofHom _

/-- The step `F_i` of `ofSubmodules F hF` is the subobject of `F i`. -/
theorem step_ofSubmodules (i : I) :
    (ofSubmodules F hF).step i = (ModuleCat.subobjectModule (ModuleCat.of R M)).symm (F i) := by
  have hm : Mono (ModuleCat.ofHom (F i).subtype) :=
    ModuleCat.mono_as_hom'_subtype (X := ModuleCat.of R M) (F i)
  rw [← FilteredObject.mk_stepι]
  exact Subobject.mk_eq_mk_of_comm _ (ModuleCat.ofHom (F i).subtype) (Iso.refl _) (by simp)

/-- `ModuleCat.subobjectModule` sends the step `F_i` of `ofSubmodules F hF` to `F i`. -/
@[simp]
theorem subobjectModule_step_ofSubmodules (i : I) :
    ModuleCat.subobjectModule (ModuleCat.of R M) ((ofSubmodules F hF).step i) = F i := by
  rw [step_ofSubmodules, OrderIso.apply_symm_apply]

/-- `ofSubmodules F hF` is exhaustive exactly when every submodule containing every `F i` is
everything. -/
theorem isExhaustive_ofSubmodules_iff :
    (ofSubmodules F hF).IsExhaustive ↔ ∀ N : Submodule R M, (∀ i, F i ≤ N) → N = ⊤ := by
  rw [isExhaustive_iff, (ModuleCat.subobjectModule (ModuleCat.of R M)).symm.surjective.forall]
  simp only [step_ofSubmodules, OrderIso.le_iff_le, map_eq_top_iff]

/-- `ofSubmodules F hF` is separated exactly when every submodule contained in every `F i` is
zero. -/
theorem isSeparated_ofSubmodules_iff :
    (ofSubmodules F hF).IsSeparated ↔ ∀ N : Submodule R M, (∀ i, N ≤ F i) → N = ⊥ := by
  rw [isSeparated_iff, (ModuleCat.subobjectModule (ModuleCat.of R M)).symm.surjective.forall]
  simp only [step_ofSubmodules, OrderIso.le_iff_le, map_eq_bot_iff]

/-- `ofSubmodules F hF` is exhaustive exactly when the `F i` generate `M`. -/
theorem isExhaustive_ofSubmodules_iff_iSup : (ofSubmodules F hF).IsExhaustive ↔ ⨆ i, F i = ⊤ := by
  rw [isExhaustive_ofSubmodules_iff]
  exact ⟨fun h ↦ h _ (le_iSup F), fun h N hN ↦ top_le_iff.1 (h ▸ iSup_le hN)⟩

/-- `ofSubmodules F hF` is separated exactly when the `F i` meet in `0`. -/
theorem isSeparated_ofSubmodules_iff_iInf : (ofSubmodules F hF).IsSeparated ↔ ⨅ i, F i = ⊥ := by
  rw [isSeparated_ofSubmodules_iff]
  exact ⟨fun h ↦ h _ (iInf_le F), fun h N hN ↦ le_bot_iff.1 (h ▸ le_iInf hN)⟩

/-- Over a filtered index category, `ofSubmodules F hF` is exhaustive exactly when every element
lies in some `F i`. -/
theorem isExhaustive_ofSubmodules_iff_forall_mem [IsFiltered I] :
    (ofSubmodules F hF).IsExhaustive ↔ ∀ x, ∃ i, x ∈ F i := by
  have hd : Directed (· ≤ ·) F := fun i j ↦
    ⟨IsFiltered.max i j, hF (IsFiltered.leftToMax i j), hF (IsFiltered.rightToMax i j)⟩
  have : Nonempty I := IsFiltered.nonempty
  simp_rw [isExhaustive_ofSubmodules_iff_iSup, Submodule.eq_top_iff',
    Submodule.mem_iSup_of_directed F hd]

/-- `ofSubmodules F hF` is separated exactly when `0` is the only element of every `F i`. -/
theorem isSeparated_ofSubmodules_iff_forall_mem :
    (ofSubmodules F hF).IsSeparated ↔ ∀ x, (∀ i, x ∈ F i) → x = 0 := by
  simp_rw [isSeparated_ofSubmodules_iff_iInf, Submodule.eq_bot_iff, Submodule.mem_iInf]

/-- Two elements of `M` have the same image in the quotient `M / F_i`, the cokernel of the
inclusion of the step `F_i`, exactly when their difference lies in `F i`. -/
theorem cokernel_π_stepι_ofSubmodules_apply_eq_iff (i : I) (x y : M) :
    (Limits.cokernel.π ((ofSubmodules F hF).stepι i)).hom x =
      (Limits.cokernel.π ((ofSubmodules F hF).stepι i)).hom y ↔ x - y ∈ F i := by
  -- Mathlib identifies the cokernel projection with `M ⟶ M ⧸ F i`.
  let e := ModuleCat.cokernelIsoRangeQuotient ((ofSubmodules F hF).stepι i)
  have h (z : M) : e.hom.hom ((Limits.cokernel.π ((ofSubmodules F hF).stepι i)).hom z) =
      (LinearMap.range ((ofSubmodules F hF).stepι i).hom).mkQ z := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom, ModuleCat.hom_ofHom]
  rw [← (ModuleCat.mono_iff_injective e.hom).1 inferInstance |>.eq_iff, h, h,
    Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hom_stepι_ofSubmodules]
  exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ z.property, fun h ↦ ⟨⟨x - y, h⟩, rfl⟩⟩

/-- Two maps into the underlying module of `ofSubmodules F hF` agree in its quotient `M / F_i`,
the cokernel of the inclusion of the step `F_i` (the leg `quotientCone_π_app` of its cone of
quotients), exactly when their difference lands in `F i`. -/
theorem comp_cokernel_π_stepι_ofSubmodules_eq_iff (i : I) {A : ModuleCat.{v} R}
    (f g : A ⟶ (ofSubmodules F hF).X) :
    f ≫ Limits.cokernel.π ((ofSubmodules F hF).stepι i) =
      g ≫ Limits.cokernel.π ((ofSubmodules F hF).stepι i) ↔ ∀ a, f.hom a - g.hom a ∈ F i := by
  simp only [ModuleCat.hom_ext_iff, LinearMap.ext_iff, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact forall_congr' fun a ↦ cokernel_π_stepι_ofSubmodules_apply_eq_iff F hF i (f.hom a) (g.hom a)

end CategoryTheory.FilteredObject
