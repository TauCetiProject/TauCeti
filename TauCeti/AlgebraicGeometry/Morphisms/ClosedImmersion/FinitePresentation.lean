/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite presentation of closed immersions

A closed immersion is locally of finite presentation exactly when its kernel ideal sheaf is
locally finitely generated. We give both the affine-open and neighbourhood formulations,
without a noetherian hypothesis. Applied to `I.subschemeι`, whose kernel is `I`, these criteria
let local equations establish finite presentation of divisor inclusions over arbitrary bases.

## References

* Stacks Project, *Morphisms of Schemes*, closed immersions of finite presentation, Tag 01TV.
* Stacks Project, *Morphisms of Schemes*, affine-local criteria for finite presentation, Tag 01TQ.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.IsClosedImmersion

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [IsClosedImmersion f]

/-- Over an affine open, a closed immersion is of finite presentation exactly when its kernel
ideal of sections is finitely generated. -/
theorem locallyOfFinitePresentation_morphismRestrict_iff {U : Y.affineOpens} :
    LocallyOfFinitePresentation (f ∣_ U.val) ↔ (f.ker.ideal U).FG := by
  have : IsAffine U.val.toScheme := U.property
  have : IsAffine (f ⁻¹ᵁ U.val).toScheme := U.property.preimage f
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation),
    morphismRestrict_appTop]
  -- The restriction formula changes the objects behind `CommRingCat.Hom.hom`; restate it
  -- with those objects explicit so rewriting does not retain the old global-section types.
  change RingHom.FinitePresentation ((f.app (U.val.ι ''ᵁ ⊤) ≫
    X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U.val ⊤)).op).hom) ↔ _
  rw [CommRingCat.hom_comp, (HasRingHomProperty.isLocal_ringHomProperty
      @LocallyOfFinitePresentation).respectsIso.cancel_right_isIso, Scheme.Opens.ι_image_top,
    f.ker_apply U]
  refine ⟨fun h ↦ ?_, .of_surjective _ (f.app_surjective U U.property)⟩
  algebraize [(f.app U).hom]
  exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId _ _)
    (f.app_surjective U U.property)

/-- A closed immersion is locally of finite presentation exactly when its kernel ideal on every
affine open of the target is finitely generated. -/
theorem locallyOfFinitePresentation_iff :
    LocallyOfFinitePresentation f ↔ ∀ U : Y.affineOpens, (f.ker.ideal U).FG := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation)
    (fun U : Y.affineOpens ↦ U.val) (iSup_affineOpens_eq_top Y)]
  exact forall_congr' fun _ ↦ locallyOfFinitePresentation_morphismRestrict_iff

/-- Finite presentation of a closed immersion can be checked on one affine open with finitely
generated kernel ideal near each point of the target. -/
theorem locallyOfFinitePresentation_iff_exists_fg :
    LocallyOfFinitePresentation f ↔
      ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.val ∧ (f.ker.ideal U).FG := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation)
  refine ⟨fun h y ↦ ?_, fun h ↦ IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    fun y ↦ ?_⟩
  · obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top y)
    exact ⟨⟨U, hU⟩, hy, locallyOfFinitePresentation_iff.mp h ⟨U, hU⟩⟩
  · obtain ⟨U, hy, hU⟩ := h y
    exact ⟨U, hy, locallyOfFinitePresentation_morphismRestrict_iff.mpr hU⟩

end AlgebraicGeometry.IsClosedImmersion

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- An ideal sheaf with locally finitely presented closed inclusion has finitely generated
section ideals on every affine open. -/
theorem fg_ideal (I : X.IdealSheafData) [LocallyOfFinitePresentation I.subschemeι]
    (U : X.affineOpens) : (I.ideal U).FG := by
  simpa only [I.ker_subschemeι] using
    (IsClosedImmersion.locallyOfFinitePresentation_iff (f := I.subschemeι)).mp inferInstance U

/-- Finite generation of section ideals on affine neighborhoods implies finite generation
on every affine open. -/
theorem fg_ideal_of_forall_exists_fg (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧ (I.ideal U).FG)
    (U : X.affineOpens) : (I.ideal U).FG := by
  have : LocallyOfFinitePresentation I.subschemeι :=
    IsClosedImmersion.locallyOfFinitePresentation_iff_exists_fg.mpr (by
      simpa only [I.ker_subschemeι] using hI)
  exact I.fg_ideal U

/-- A locally principal ideal sheaf has a locally finitely presented closed inclusion;
the generators need not be regular. -/
theorem locallyOfFinitePresentation_subschemeι_of_locallyPrincipal (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), I.ideal U = Ideal.span {a}) :
    LocallyOfFinitePresentation I.subschemeι := by
  apply IsClosedImmersion.locallyOfFinitePresentation_iff_exists_fg.mpr
  intro x
  obtain ⟨U, hx, a, hUa⟩ := hI x
  refine ⟨U, hx, ?_⟩
  rw [I.ker_subschemeι, hUa]
  exact Submodule.fg_span_singleton a

end AlgebraicGeometry.Scheme.IdealSheafData
