/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite presentation of closed subschemes

A closed subscheme is locally of finite presentation in its ambient scheme exactly when its
ideal is locally finitely generated. We give both the affine-open and neighbourhood formulations,
without a noetherian hypothesis. These criteria let local equations establish finite presentation
of divisor inclusions over arbitrary bases.

## References

* Stacks Project, *Morphisms of Schemes*, closed immersions of finite presentation, Tag 01TV.
* Stacks Project, *Morphisms of Schemes*, affine-local criteria for finite presentation, Tag 01TQ.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- On an affine open, the inclusion of a closed subscheme is of finite presentation exactly
when its ideal of sections is finitely generated. -/
theorem locallyOfFinitePresentation_subschemeι_morphismRestrict_iff {U : X.affineOpens} :
    LocallyOfFinitePresentation (I.subschemeι ∣_ U.1) ↔ (I.ideal U).FG := by
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (I.subschemeι ⁻¹ᵁ U.1).toScheme := U.2.preimage I.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  rw [morphismRestrict_appTop]
  -- The restriction formula changes the objects behind `CommRingCat.Hom.hom`; restate it
  -- with those objects explicit so rewriting does not retain the old global-section types.
  change RingHom.FinitePresentation ((I.subschemeι.app (U.1.ι ''ᵁ ⊤) ≫
    I.subscheme.presheaf.map
      (eqToHom (image_morphismRestrict_preimage I.subschemeι U.1 ⊤)).op).hom) ↔ _
  have hPi :=
    (HasRingHomProperty.isLocal_ringHomProperty @LocallyOfFinitePresentation).respectsIso
  rw [CommRingCat.hom_comp, hPi.cancel_right_isIso, Scheme.Opens.ι_image_top]
  constructor
  · intro h
    let φ := (I.subschemeι.app U.1).hom
    let _ := φ.toAlgebra
    have : Algebra.FinitePresentation Γ(X, U.1) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) := h
    have hker := Algebra.FinitePresentation.ker_fG_of_surjective
      (Algebra.ofId Γ(X, U.1) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1))
      (I.subschemeι_app_surjective U)
    rw [← I.ker_subschemeι_app U]
    exact hker
  · intro h
    exact RingHom.FinitePresentation.of_surjective _ (I.subschemeι_app_surjective U)
      ((I.ker_subschemeι_app U).symm ▸ h)

/-- A closed subscheme is locally of finite presentation exactly when its ideal on every
ambient affine open is finitely generated. -/
theorem locallyOfFinitePresentation_subschemeι_iff :
    LocallyOfFinitePresentation I.subschemeι ↔ ∀ U : X.affineOpens, (I.ideal U).FG := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation)
    (Q := RingHom.FinitePresentation)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)]
  exact forall_congr' fun U ↦
    locallyOfFinitePresentation_subschemeι_morphismRestrict_iff (U := U)

/-- Finite presentation of a closed subscheme can be checked on one finitely generated ideal
near each point of its ambient scheme. -/
theorem locallyOfFinitePresentation_subschemeι_iff_exists_fg :
    LocallyOfFinitePresentation I.subschemeι ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ (I.ideal U).FG := by
  constructor
  · intro h x
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hx, locallyOfFinitePresentation_subschemeι_iff.mp h ⟨U, hU⟩⟩
  · intro h
    have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation)
      (Q := RingHom.FinitePresentation)
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := @LocallyOfFinitePresentation)
    intro x
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U.1, hx,
      (locallyOfFinitePresentation_subschemeι_morphismRestrict_iff (U := U)).mpr hU⟩

end TauCeti
