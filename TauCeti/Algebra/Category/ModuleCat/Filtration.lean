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
# Decreasing filtrations of modules by submodules

An antitone family `F : ℤ → Submodule R M` of submodules is a decreasingly filtered object of
`ModuleCat R` (`CategoryTheory.FilteredObject.ofSubmodules`), whose step `F^p` is the subobject of
`F p` (`step_ofSubmodules`). Mathlib's order isomorphism `ModuleCat.subobjectModule` between
subobjects and submodules carries the steps to the submodules `F p`
(`subobjectModule_step_ofSubmodules`), so the lattice conditions on the steps read in the
lattice of submodules.

## Main results

* `isExhaustive_ofSubmodules_iff_iSup`, `isExhaustive_ofSubmodules_iff_forall_mem`: the
  filtration is exhaustive exactly when `⨆ p, F p = ⊤`, that is, when every element lies in some
  `F p`.
* `isSeparated_ofSubmodules_iff_iInf`, `isSeparated_ofSubmodules_iff_forall_mem`: the filtration
  is separated exactly when `⨅ p, F p = ⊥`, that is, when only `0` lies in every `F p`.
* `comp_quotientCone_π_ofSubmodules_eq_iff`: through `ModuleCat.cokernelIsoRangeQuotient`, two
  maps `f g : A ⟶ M` agree in the quotient `M / F^p` exactly when `f a - g a ∈ F p` for all `a`.
-/

public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.FilteredObject

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The decreasingly filtered module with steps an antitone family `F` of submodules. -/
noncomputable abbrev ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) :
    FilteredObject (ModuleCat.{v} R) ℤᵒᵖ where
  X := ModuleCat.of R M
  filtration.toMonoOver :=
    { obj p := MonoOver.mk (hf := ModuleCat.mono_as_hom'_subtype (X := ModuleCat.of R M) (F p.unop))
        (ModuleCat.ofHom (F p.unop).subtype)
      map {p q} f := MonoOver.homMk
        (ModuleCat.ofHom (Submodule.inclusion (hF (leOfHom f.unop)))) rfl }

/-- The inclusion of the step `F^p` of `ofSubmodules F hF` is the inclusion of `F p`. -/
@[simp]
theorem stepι_ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) (p : ℤ) :
    (ofSubmodules F hF).stepι (op p) = ModuleCat.ofHom (F p).subtype := by
  rw [← FilteredObject.filtration_ι_app]
  rfl

/-- The linear map underlying the inclusion of the step `F^p` is the inclusion of `F p`. -/
theorem stepι_hom_ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) (p : ℤ) :
    ((ofSubmodules F hF).stepι (op p)).hom = (F p).subtype := by
  rw [stepι_ofSubmodules]
  rfl

/-- The step `F^p` of `ofSubmodules F hF` is the subobject of `F p`. -/
theorem step_ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) (p : ℤ) :
    (ofSubmodules F hF).step (op p) =
      (ModuleCat.subobjectModule (ModuleCat.of R M)).symm (F p) := by
  have hm : Mono (ModuleCat.ofHom (F p).subtype) :=
    ModuleCat.mono_as_hom'_subtype (X := ModuleCat.of R M) (F p)
  rw [← FilteredObject.mk_stepι]
  exact Subobject.mk_eq_mk_of_comm _ (ModuleCat.ofHom (F p).subtype) (Iso.refl _) (by simp)

/-- `ModuleCat.subobjectModule` sends the step `F^p` of `ofSubmodules F hF` to `F p`. -/
theorem subobjectModule_step_ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) (p : ℤ) :
    ModuleCat.subobjectModule (ModuleCat.of R M) ((ofSubmodules F hF).step (op p)) = F p := by
  rw [step_ofSubmodules, OrderIso.apply_symm_apply]

/-- `ofSubmodules F hF` is exhaustive exactly when every submodule containing every `F p` is
everything. -/
theorem isExhaustive_ofSubmodules_iff (F : ℤ → Submodule R M) (hF : Antitone F) :
    (ofSubmodules F hF).IsExhaustive ↔ ∀ N : Submodule R M, (∀ p, F p ≤ N) → N = ⊤ := by
  rw [isExhaustive_iff, (ModuleCat.subobjectModule (ModuleCat.of R M)).symm.surjective.forall]
  simp only [op_surjective.forall, step_ofSubmodules, OrderIso.le_iff_le, map_eq_top_iff]

/-- `ofSubmodules F hF` is separated exactly when every submodule contained in every `F p` is
zero. -/
theorem isSeparated_ofSubmodules_iff (F : ℤ → Submodule R M) (hF : Antitone F) :
    (ofSubmodules F hF).IsSeparated ↔ ∀ N : Submodule R M, (∀ p, N ≤ F p) → N = ⊥ := by
  rw [isSeparated_iff, (ModuleCat.subobjectModule (ModuleCat.of R M)).symm.surjective.forall]
  simp only [op_surjective.forall, step_ofSubmodules, OrderIso.le_iff_le, map_eq_bot_iff]

/-- `ofSubmodules F hF` is exhaustive exactly when the `F p` generate `M`. -/
theorem isExhaustive_ofSubmodules_iff_iSup (F : ℤ → Submodule R M) (hF : Antitone F) :
    (ofSubmodules F hF).IsExhaustive ↔ ⨆ p, F p = ⊤ := by
  rw [isExhaustive_ofSubmodules_iff]
  exact ⟨fun h ↦ h _ (le_iSup F), fun h N hN ↦ top_le_iff.1 (h ▸ iSup_le hN)⟩

/-- `ofSubmodules F hF` is separated exactly when the `F p` meet in `0`. -/
theorem isSeparated_ofSubmodules_iff_iInf (F : ℤ → Submodule R M) (hF : Antitone F) :
    (ofSubmodules F hF).IsSeparated ↔ ⨅ p, F p = ⊥ := by
  rw [isSeparated_ofSubmodules_iff]
  exact ⟨fun h ↦ h _ (iInf_le F), fun h N hN ↦ le_bot_iff.1 (h ▸ le_iInf hN)⟩

/-- `ofSubmodules F hF` is exhaustive exactly when every element lies in some `F p`. -/
theorem isExhaustive_ofSubmodules_iff_forall_mem (F : ℤ → Submodule R M) (hF : Antitone F) :
    (ofSubmodules F hF).IsExhaustive ↔ ∀ x, ∃ p, x ∈ F p := by
  simp_rw [isExhaustive_ofSubmodules_iff_iSup, Submodule.eq_top_iff',
    Submodule.mem_iSup_of_directed F hF.directed_le]

/-- `ofSubmodules F hF` is separated exactly when `0` is the only element of every `F p`. -/
theorem isSeparated_ofSubmodules_iff_forall_mem (F : ℤ → Submodule R M) (hF : Antitone F) :
    (ofSubmodules F hF).IsSeparated ↔ ∀ x, (∀ p, x ∈ F p) → x = 0 := by
  simp_rw [isSeparated_ofSubmodules_iff_iInf, Submodule.eq_bot_iff, Submodule.mem_iInf]

/-- Two maps into the underlying module of `ofSubmodules F hF`, seen as the vertex of its cone of
quotients, agree in the quotient `M / F p` exactly when their difference lands in `F p`. -/
theorem comp_quotientCone_π_ofSubmodules_eq_iff (F : ℤ → Submodule R M) (hF : Antitone F)
    (p : ℤ) {A : ModuleCat.{v} R} (f g : A ⟶ (ofSubmodules F hF).quotientCone.pt) :
    f ≫ (ofSubmodules F hF).quotientCone.π.app (op p) =
      g ≫ (ofSubmodules F hF).quotientCone.π.app (op p) ↔ ∀ a, f.hom a - g.hom a ∈ F p := by
  -- The quotient `M / F^p` of the diagram is by definition the cokernel of the inclusion of
  -- `F^p`, and its projection the cokernel projection, which Mathlib identifies with
  -- `M ⟶ M ⧸ F p`.
  let e : (ofSubmodules F hF).quotientDiagram.obj (op p) ≅
      ModuleCat.of R (M ⧸ LinearMap.range ((ofSubmodules F hF).stepι (op p)).hom) :=
    ModuleCat.cokernelIsoRangeQuotient _
  have hπ : (ofSubmodules F hF).quotientCone.π.app (op p) ≫ e.hom =
      ModuleCat.ofHom (LinearMap.range ((ofSubmodules F hF).stepι (op p)).hom).mkQ :=
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _
  have key (x y : M) : (LinearMap.range ((ofSubmodules F hF).stepι (op p)).hom).mkQ x =
      (LinearMap.range ((ofSubmodules F hF).stepι (op p)).hom).mkQ y ↔ x - y ∈ F p := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, stepι_hom_ofSubmodules]
    exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ z.property, fun h ↦ ⟨⟨x - y, h⟩, rfl⟩⟩
  rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hπ, ModuleCat.hom_ext_iff,
    LinearMap.ext_iff]
  -- The codomain `quotientCone.pt` of `f` and `g` is only definitionally `M`, so `key` is applied
  -- up to unfolding rather than by rewriting.
  exact forall_congr' fun a ↦ key (f.hom a) (g.hom a)

end CategoryTheory.FilteredObject
