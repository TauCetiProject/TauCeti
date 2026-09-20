/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Category
public import TauCeti.Geometry.Hodge.Projection
public import TauCeti.Geometry.Hodge.Mixed.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Detecting monomorphisms and epimorphisms of polarizable Hodge structures

In the category of polarizable rational Hodge structures, a morphism is monic exactly when its
rational map is injective, and epic exactly when its rational map is surjective. These criteria
allow categorical subobjects to be identified with rational Hodge substructures, and hence allow
orthogonal complements to be used to split categorical monomorphisms.

The converse to cancellation uses Hodge projectors: a monomorphism kills the projector onto its
kernel, while an epimorphism forces the projector onto its image to be the identity. This uses
polarizability only as a property; no polarization is chosen as part of a categorical object.
Isomorphisms are detected by the rational realization using the existing mixed-Hodge inverse.
Consequently the category is balanced, and the rational realization preserves monomorphisms
and epimorphisms and reflects isomorphisms.

## References

Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2;
Peters--Steenbrink, *Mixed Hodge Structures*, §2.
-/

public section

namespace TauCeti.Hodge.PolarizableHodgeStructureCat

open CategoryTheory Limits

universe u

variable {n : ℤ} {X Y : PolarizableHodgeStructureCat.{u} n}

/-- A morphism of polarizable rational Hodge structures is monic exactly when its rational map
is injective. -/
theorem mono_iff_injective (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f.hom.toRatLinearMap := by
  constructor
  · intro hf
    have hfC := Hom.isMorphism f
    rw [MixedHodgeStructure.Hom.toLinearMap_def] at hfC
    let W := RationalHodgeSubstructure.ofRationalMorphismKer hfC
    obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 X.isPolarizable
    let e : X ⟶ X := Hom.ofIsMorphism (W.projection P)
      (W.isMorphism_rationalMapToComplex_projection P)
    have he : e.hom.toRatLinearMap = W.projection P := Hom.ofIsMorphism_toRatLinearMap _ _
    have hr : LinearMap.range e.hom.toRatLinearMap = LinearMap.ker f.hom.toRatLinearMap := by
      rw [he, RationalHodgeSubstructure.range_projection]
      exact RationalHodgeSubstructure.ofRationalMorphismKer_WQ _
    have hzero : e ≫ f = 0 := by
      apply Hom.ext
      simpa only [comp_toRatLinearMap, zero_toRatLinearMap] using
        LinearMap.range_le_ker_iff.1 hr.le
    have hezero : e = 0 := (cancel_mono f).1 (hzero.trans zero_comp.symm)
    rw [← LinearMap.ker_eq_bot, ← hr, hezero, zero_toRatLinearMap, LinearMap.range_zero]
  · intro hf
    apply rational.mono_of_mono_map
    rw [rational_map]
    have : Mono (ModuleCat.ofHom f.hom.toRatLinearMap) :=
      (ModuleCat.mono_iff_injective _).2 hf
    infer_instance

/-- A morphism of polarizable rational Hodge structures is epic exactly when its rational map
is surjective. -/
theorem epi_iff_surjective (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f.hom.toRatLinearMap := by
  constructor
  · intro hf
    have hfC := Hom.isMorphism f
    rw [MixedHodgeStructure.Hom.toLinearMap_def] at hfC
    let W := RationalHodgeSubstructure.ofRationalMorphismRange hfC
    obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 Y.isPolarizable
    let e : Y ⟶ Y := Hom.ofIsMorphism (W.projection P)
      (W.isMorphism_rationalMapToComplex_projection P)
    have he : e.hom.toRatLinearMap = W.projection P := Hom.ofIsMorphism_toRatLinearMap _ _
    have hr : LinearMap.range e.hom.toRatLinearMap = LinearMap.range f.hom.toRatLinearMap := by
      rw [he, RationalHodgeSubstructure.range_projection]
      exact RationalHodgeSubstructure.ofRationalMorphismRange_WQ _
    have hcomp : f ≫ e = f ≫ 𝟙 Y := by
      apply Hom.ext
      simp only [comp_toRatLinearMap, id_toRatLinearMap, LinearMap.id_comp, he]
      apply (LinearMap.IsIdempotentElem.comp_eq_right_iff
        (W.isIdempotentElem_projection P) _).2
      rw [← he, hr]
    have heid : e = 𝟙 Y := (cancel_epi f).1 hcomp
    rw [← LinearMap.range_eq_top, ← hr, heid, id_toRatLinearMap, LinearMap.range_id]
  · intro hf
    apply rational.epi_of_epi_map
    rw [rational_map]
    have : Epi (ModuleCat.ofHom f.hom.toRatLinearMap) :=
      (ModuleCat.epi_iff_surjective _).2 hf
    infer_instance

/-- The rational realization preserves monomorphisms. -/
instance : (rational (n := n)).PreservesMonomorphisms where
  preserves f hf := by
    rw [rational_map]
    have : Mono (ModuleCat.ofHom f.hom.toRatLinearMap) :=
      (ModuleCat.mono_iff_injective _).2 ((mono_iff_injective f).1 hf)
    infer_instance

/-- The rational realization preserves epimorphisms. -/
instance : (rational (n := n)).PreservesEpimorphisms where
  preserves f hf := by
    rw [rational_map]
    have : Epi (ModuleCat.ofHom f.hom.toRatLinearMap) :=
      (ModuleCat.epi_iff_surjective _).2 ((epi_iff_surjective f).1 hf)
    infer_instance

/-- A morphism of polarizable rational Hodge structures is an isomorphism exactly when its
rational map is bijective. -/
theorem isIso_iff_bijective (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective f.hom.toRatLinearMap := by
  rw [← isIso_iff_of_reflects_iso f mixed, mixed_map]
  rw [isIso_comp_left_iff, isIso_comp_right_iff]
  exact MixedHodgeStructureCat.isIso_iff_bijective f.hom

/-- The rational realization reflects isomorphisms: a rationally invertible Hodge morphism has
an inverse preserving the Hodge filtration. -/
instance : (rational (n := n)).ReflectsIsomorphisms where
  reflects f hf := by
    apply (isIso_iff_bijective f).2
    rw [rational_map] at hf
    rw [isIso_comp_left_iff, isIso_comp_right_iff] at hf
    exact ConcreteCategory.bijective_of_isIso (ModuleCat.ofHom f.hom.toRatLinearMap)

/-- A morphism of polarizable rational Hodge structures which is both monic and epic is an
isomorphism. -/
instance : Balanced (PolarizableHodgeStructureCat.{u} n) :=
  Functor.balanced_of_preserves (rational (n := n))

end TauCeti.Hodge.PolarizableHodgeStructureCat
