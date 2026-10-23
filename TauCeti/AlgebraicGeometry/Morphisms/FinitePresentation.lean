/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Cancellation for morphisms locally of finite presentation

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes. If `f ≫ g` is locally of finite
presentation and `g` is locally of finite type, then `f` is locally of finite presentation
(`AlgebraicGeometry.locallyOfFinitePresentation_of_comp`). In particular, every morphism over `Z`
between two schemes locally of finite presentation over `Z` is locally of finite presentation.

This is the scheme version of `RingHom.FinitePresentation.of_comp_finiteType`, to which the proof
reduces on affine opens. It parallels Mathlib's `AlgebraicGeometry.locallyOfFiniteType_of_comp`,
which needs no hypothesis on `g`; for finite presentation the hypothesis on `g` cannot be dropped.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_of_comp`: if `f ≫ g` is locally of finite
  presentation and `g` is locally of finite type, then `f` is locally of finite presentation.

## References

* The Stacks Project, [Tag 02FV](https://stacks.math.columbia.edu/tag/02FV).
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Cancellation for morphisms locally of finite presentation** (Stacks, Tag 02FV). If
`f ≫ g` is locally of finite presentation and `g` is locally of finite type, then `f` is locally
of finite presentation. -/
theorem locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hfg : LocallyOfFinitePresentation (f ≫ g)] [hg : LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  -- the locality instances of the two properties, from their affine-local descriptions
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FinitePresentation)
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FiniteType)
  -- reduce to `Z`, then `Y`, then `X` affine
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict hfg U.1
    rw [morphismRestrict_comp] at H
    exact this _ (g ∣_ U.1) (hfg := H) (hg := IsZariskiLocalAtTarget.restrict hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H := IsZariskiLocalAtSource.comp (P := @LocallyOfFinitePresentation) hfg (f ⁻¹ᵁ U.1).ι
    rw [← morphismRestrict_ι_assoc] at H
    have hU : LocallyOfFiniteType U.1.ι := locallyOfFiniteType_of_isOpenImmersion _
    exact this _ (U.1.ι ≫ g) (hfg := H) (hg := locallyOfFiniteType_comp _ _) inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H := IsZariskiLocalAtSource.comp (P := @LocallyOfFinitePresentation) hfg U.1.ι
    rw [← Category.assoc] at H
    exact this _ (hfg := H) inferInstance
  -- on affine schemes this is `RingHom.FinitePresentation.of_comp_finiteType`
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at hfg ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at hg
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at hfg
  exact hfg.of_comp_finiteType _ hg

end AlgebraicGeometry
