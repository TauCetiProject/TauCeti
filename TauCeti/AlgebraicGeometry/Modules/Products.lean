/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Sections of products of modules on a scheme

Limits of `𝒪_X`-modules are computed on sections: taking sections over an open `U` preserves
limits. In particular the sections over `U` of a product `∏ⱼ Fⱼ` of `𝒪_X`-modules are the
families of sections of the factors. This file records the consequence used to compute modules
assembled as products of modules supported on disjoint open sets: if every factor other than
`Fᵢ` has no nonzero section over `U`, then the projection `Γ(∏ⱼ Fⱼ, U) → Γ(Fᵢ, U)` is bijective
(`AlgebraicGeometry.Scheme.Modules.bijective_app_π_of_subsingleton`).
-/

public section

open CategoryTheory Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Over an open `U` on which every factor other than `F i` has only the zero section, the
projection from the sections of a product of `𝒪_X`-modules to the sections of `F i` is
bijective. -/
theorem bijective_app_π_of_subsingleton {ι : Type v} [Small.{u} ι] (F : ι → X.Modules)
    [HasProduct F] (i : ι) (U : X.Opens) (h : ∀ j ≠ i, Subsingleton Γ(F j, U)) :
    Function.Bijective ((Pi.π F i).app U) := by
  classical
  -- Sections over `U` form a limit-preserving functor to types, so they turn the product into
  -- the product of the types of sections.
  let G : X.Modules ⥤ Type u :=
    toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op U) ⋙ CategoryTheory.forget Ab
  have : PreservesLimitsOfSize.{u, u}
      ((evaluation (Opens X)ᵒᵖ Ab.{u}).obj (Opposite.op U) ⋙ CategoryTheory.forget Ab.{u}) :=
    comp_preservesLimits _ _
  have : PreservesLimitsOfSize.{u, u} G := comp_preservesLimits _ _
  -- `ι` is `u`-small, so `G` preserves `ι`-indexed products.
  have : PreservesLimitsOfShape (Discrete ι) G :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence (equivShrink.{u} ι).symm) G
  let e := PreservesProduct.iso G F ≪≫ Types.Small.productIso fun j ↦ G.obj (F j)
  have he : G.map (Pi.π F i) =
      e.hom ≫ ↾fun s ↦ (equivShrink (∀ j, G.obj (F j))).symm s i := by
    simp [e, piComparison_comp_π]
  have hev : Function.Bijective fun s : (∀ j, G.obj (F j)) ↦ s i := by
    refine ⟨fun s t hst ↦ funext fun j ↦ ?_,
      fun x ↦ ⟨Function.update (fun j ↦ (0 : Γ(F j, U))) i x, Function.update_self ..⟩⟩
    by_cases hj : j = i
    · subst hj
      exact hst
    · exact (h j hj).elim _ _
  -- `G.map φ` is by definition the map `φ.app U` on sections over `U`.
  change Function.Bijective (G.map (Pi.π F i))
  rw [he, types_comp]
  exact (hev.comp (equivShrink _).symm.bijective).comp
    ((isIso_iff_bijective e.hom).mp inferInstance)

end AlgebraicGeometry.Scheme.Modules
