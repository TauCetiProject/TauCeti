/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheaf

import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheaves of locally constant functions with values in a module

For a topological space `X`, a ring `R`, and an `R`-module `M`, the locally constant `M`-valued
functions on open subsets of `X` form a sheaf of `R`-modules
`TopCat.locallyConstantModuleSheaf X R M`. This is the constant sheaf with values in `M`, realised
directly in `ModuleCat R` without needing commutativity of `R` or forcing `X`, `R`, and `M` into
the same universe.

A continuous map `f : X ⟶ Y` induces the pullback morphism
`TopCat.Hom.locallyConstantModulePullback f R M : M_Y ⟶ f_* M_X` by precomposition with `f`
on each open subset. This pullback is strictly functorial with respect to identities and
compositions of continuous maps and respects pointwise ring operations when `M` is a ring.

## Main definitions

* `TopCat.locallyConstantModulePresheaf X R M`: the presheaf of `R`-modules of locally constant
  `M`-valued functions on `X`.
* `TopCat.locallyConstantModuleSheaf X R M`: the same presheaf bundled as a sheaf of `R`-modules.
* `TopCat.Hom.locallyConstantModulePullback f R M`: precomposition pullback
  `M_Y ⟶ f_* M_X` along a continuous map `f : X ⟶ Y`.

## Main results

* `TopCat.isSheaf_locallyConstantModulePresheaf`: locally constant `M`-valued functions satisfy
  the sheaf condition.
* `TopCat.Hom.locallyConstantModulePullback_id`,
  `TopCat.Hom.locallyConstantModulePullback_comp`: functoriality of pullback on locally constant
  module presheaves.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u uR v

namespace TopCat

section Presheaf

variable (X : TopCat.{u}) (R : Type uR) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The presheaf of `R`-modules of locally constant `M`-valued functions on `X`. -/
@[expose] def locallyConstantModulePresheaf : X.Presheaf (ModuleCat.{max u v} R) where
  obj U := ModuleCat.of R (LocallyConstant U.unop M)
  map i := ModuleCat.ofHom
    (LocallyConstant.comapₗ R ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩)

@[simp]
theorem locallyConstantModulePresheaf_obj (U : (Opens X)ᵒᵖ) :
    (locallyConstantModulePresheaf X R M).obj U = ModuleCat.of R (LocallyConstant U.unop M) :=
  (rfl)

variable {X R M} in
@[simp]
theorem locallyConstantModulePresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : LocallyConstant U.unop M) :
    (locallyConstantModulePresheaf X R M).map i s =
      s.comap ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩ :=
  (rfl)

/-- Locally constant `M`-valued functions glue uniquely, so `locallyConstantModulePresheaf X R M`
is a sheaf of `R`-modules. -/
theorem isSheaf_locallyConstantModulePresheaf : (locallyConstantModulePresheaf X R M).IsSheaf := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max u v} R) := ModuleCat.hasLimitsOfSize.{u, u, max u v}
  refine (Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr fun ι U sf hsf ↦ ?_
  -- The sections of `locallyConstantModulePresheaf X R M` over `U i` are `LocallyConstant (U i) M`
  -- up to unfolding `ModuleCat.of`; restate `sf` so its entries coerce directly to functions.
  change ∀ i, LocallyConstant (U i) M at sf
  have hmem (x : ↥(iSup U)) : ∃ i, x.1 ∈ U i := Opens.mem_iSup.mp x.2
  let g : ↥(iSup U) → M := fun x ↦ sf (hmem x).choose ⟨x, (hmem x).choose_spec⟩
  have hg (i : ι) (x : ↥(iSup U)) (hx : x.1 ∈ U i) : g x = sf i ⟨x, hx⟩ := by
    have h := hsf (hmem x).choose i
    simp only [locallyConstantModulePresheaf_map_apply] at h
    exact DFunLike.congr_fun (F := LocallyConstant ↥(U (hmem x).choose ⊓ U i) M) h
      ⟨x, (hmem x).choose_spec, hx⟩
  have hj (i : ι) : Topology.IsOpenEmbedding
      (Set.inclusion (Opens.leSupr U i).le : U i → ↥(iSup U)) :=
    .inclusion _ ((U i).isOpen.preimage continuous_subtype_val)
  have hgc : IsLocallyConstant g := by
    refine (IsLocallyConstant.iff_eventually_eq g).mpr fun x ↦ ?_
    obtain ⟨i, hx⟩ := hmem x
    rw [← Set.inclusion_right (Opens.leSupr U i).le x hx, ← (hj i).map_nhds_eq,
      Filter.eventually_map]
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (sf i).isLocallyConstant
      ⟨x, hx⟩] with z hz
    rw [hg i _ z.2, hg i _ hx]
    exact hz
  refine ⟨(⟨g, hgc⟩ : LocallyConstant ↥(iSup U) M), fun i ↦ ?_, fun t ht ↦ ?_⟩
  · refine LocallyConstant.ext fun x ↦ ?_
    exact hg i ⟨x.1, (Opens.leSupr U i).le x.2⟩ x.2
  · refine LocallyConstant.ext fun x ↦ ?_
    obtain ⟨i, hx⟩ := hmem x
    have h := DFunLike.congr_fun (F := LocallyConstant (U i) M) (ht i) ⟨x, hx⟩
    exact h.trans (hg i x hx).symm

/-- The sheaf of `R`-modules of locally constant `M`-valued functions on `X`. -/
@[expose] def locallyConstantModuleSheaf : X.Sheaf (ModuleCat.{max u v} R) :=
  ⟨locallyConstantModulePresheaf X R M, isSheaf_locallyConstantModulePresheaf X R M⟩

@[simp]
theorem locallyConstantModuleSheaf_presheaf :
    (locallyConstantModuleSheaf X R M).presheaf = locallyConstantModulePresheaf X R M :=
  (rfl)

end Presheaf

namespace Hom

variable {X Y Z : TopCat.{u}}

/-- Precomposition pullback `M_Y ⟶ f_* M_X` on sheaves of locally constant `M`-valued functions
along a continuous map `f : X ⟶ Y`. -/
def locallyConstantModulePullback (f : X ⟶ Y) (R : Type uR) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] :
    locallyConstantModulePresheaf Y R M ⟶
      (TopCat.Presheaf.pushforward (ModuleCat.{max u v} R) f).obj
        (locallyConstantModulePresheaf X R M) where
  app U := ModuleCat.ofHom (LocallyConstant.comapₗ R
    ⟨fun x ↦ ⟨f x.1, x.2⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩)
  naturality _ _ _ := by
    ext s
    rfl

@[simp]
theorem locallyConstantModulePullback_app_apply (f : X ⟶ Y) (R : Type uR) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] (U : (Opens Y)ᵒᵖ)
    (s : LocallyConstant U.unop M) :
    dsimp% only [TopCat.Presheaf.pushforward_obj_obj]
      ((f.locallyConstantModulePullback R M).app U s =
        (s.comap ⟨fun x : (Opens.map f).obj U.unop ↦ ⟨f x.1, x.2⟩,
          (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩ :
          LocallyConstant ((Opens.map f).obj U.unop) M)) :=
  (rfl)

@[simp]
theorem locallyConstantModulePullback_id (X : TopCat.{u}) (R : Type uR) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    locallyConstantModulePullback (𝟙 X) R M = 𝟙 (locallyConstantModulePresheaf X R M) := by
  ext U s
  rfl

@[simp]
theorem locallyConstantModulePullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (R : Type uR) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    locallyConstantModulePullback (f ≫ g) R M =
      g.locallyConstantModulePullback R M ≫
        (TopCat.Presheaf.pushforward (ModuleCat.{max u v} R) g).map
          (f.locallyConstantModulePullback R M) := by
  ext U s
  rfl

theorem locallyConstantModulePullback_app_one (f : X ⟶ Y) (R : Type uR) [Ring R]
    {S : Type v} [AddCommGroup S] [Module R S] [One S] (U : (Opens Y)ᵒᵖ) :
    (f.locallyConstantModulePullback R S).app U (1 : LocallyConstant U.unop S) =
      (1 : LocallyConstant ((Opens.map f).obj U.unop) S) :=
  (rfl)

theorem locallyConstantModulePullback_app_mul (f : X ⟶ Y) (R : Type uR) [CommRing R]
    {S : Type v} [Ring S] [Algebra R S] (U : (Opens Y)ᵒᵖ)
    (s t : LocallyConstant U.unop S) :
    (f.locallyConstantModulePullback R S).app U
        (LinearMap.mul R (LocallyConstant U.unop S) s t) =
      LinearMap.mul R (LocallyConstant ((Opens.map f).obj U.unop) S)
        ((f.locallyConstantModulePullback R S).app U s)
        ((f.locallyConstantModulePullback R S).app U t) :=
  (rfl)

end Hom

end TopCat
