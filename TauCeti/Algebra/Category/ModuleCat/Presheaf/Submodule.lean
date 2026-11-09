/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# Factoring a morphism through a submodule of a presheaf of modules

Mathlib's `PresheafOfModules.Submodule` packages a family of submodules of the sections of a
presheaf of modules `M`, stable under restriction, together with the inclusion `N.ι` of the
associated presheaf of modules into `M`. This file supplies the universal property of that
inclusion, in the style of `CategoryTheory.Subfunctor.lift`: a morphism all of whose sections land
in `N` factors through `N`, uniquely because `N.ι` is a monomorphism.

## Main declarations

* `PresheafOfModules.Submodule.lift`: the factorization, with `lift_ι` recording that it does
  factor the given morphism;
* `PresheafOfModules.Submodule.isIso_lift`: the factorization is an isomorphism when the morphism
  is injective on sections with image exactly `N`;
* `PresheafOfModules.Submodule.range_ι_app`: the sections of `N` are exactly the image of `N.ι`.

The factorization is `AddMonoidHom.codRestrict` applied section by section, assembled by Mathlib's
`PresheafOfModules.homMk`.
-/

public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M P : PresheafOfModules.{v} R}

/-- A morphism of presheaves of modules all of whose sections lie in a submodule `N` of the
target factors through the presheaf of modules attached to `N`. -/
noncomputable def lift (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) :
    P ⟶ N.toPresheafOfModules :=
  homMk
    { app U := AddCommGrpCat.ofHom ((φ.app U).hom.toAddMonoidHom.codRestrict _ (hφ U))
      naturality U V f := by
        ext x
        exact Subtype.ext (naturality_apply φ f x) }
    fun U r m ↦ Subtype.ext ((φ.app U).hom.map_smul r m)

/-- On sections, `N.lift φ hφ` followed by the inclusion of `N` is `φ`. -/
@[simp]
lemma lift_app_coe (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) (U : Cᵒᵖ) (s : P.obj U) :
    ((N.lift φ hφ).app U s).val = φ.app U s :=
  (rfl)

/-- `N.lift φ hφ` factors `φ` through the inclusion `N.ι`. -/
@[reassoc (attr := simp)]
lemma lift_ι (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) :
    N.lift φ hφ ≫ N.ι = φ :=
  (rfl)

/-- The inclusion `N.ι` sends every section of `N` into the defining submodule. -/
lemma ι_app_mem (N : M.Submodule) (U : Cᵒᵖ) (s : N.toPresheafOfModules.obj U) :
    N.ι.app U s ∈ N.obj U :=
  s.2

/-- The image of the inclusion `N.ι` on sections is the defining submodule. -/
@[simp]
lemma range_ι_app (N : M.Submodule) (U : Cᵒᵖ) : Set.range (N.ι.app U) = N.obj U := by
  ext s
  exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ N.ι_app_mem U t, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩

/-- The factorization `N.lift φ hφ` is an isomorphism when `φ` is injective on sections and every
section of `N` is in the image of `φ`. -/
lemma isIso_lift (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U)
    (hinj : ∀ U : Cᵒᵖ, Function.Injective (φ.app U))
    (hsurj : ∀ U : Cᵒᵖ, ∀ s ∈ N.obj U, ∃ t, φ.app U t = s) :
    IsIso (N.lift φ hφ) := by
  have (U : Cᵒᵖ) : IsIso ((N.lift φ hφ).app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ hinj U (by simpa using congrArg Subtype.val hab), fun s ↦ ?_⟩
    obtain ⟨t, ht⟩ := hsurj U s.1 s.2
    exact ⟨t, Subtype.ext (by simpa using ht)⟩
  exact (isoMk (fun U ↦ asIso ((N.lift φ hφ).app U))
    fun _ _ f ↦ (N.lift φ hφ).naturality f).isIso_hom

end PresheafOfModules.Submodule
