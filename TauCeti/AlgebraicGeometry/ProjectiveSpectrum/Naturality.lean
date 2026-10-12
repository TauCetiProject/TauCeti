/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.GlobalCoordinates

/-!
# Pullback of global homogeneous coordinates

The morphism to `Proj` defined by global homogeneous coordinates commutes with
pullback along an arbitrary scheme morphism. This is equality of scheme morphisms,
including their structure-sheaf maps. In particular it applies to families over
nonreduced rings, where equality on field-valued points would not suffice.

`AlgebraicGeometry.Proj.fromOfGlobalSections_naturality` turns identities of pulled-back
coordinate maps into identities of morphisms. Combined with invariance under unit
rescaling, it supplies the passage from semi-invariant coordinates to invariant
projective morphisms used in constructing homogeneous spaces.

The chart calculation uses `TauCeti.ProjectiveSpectrum.toBasicOpenOfGlobalSections_eq`
and Mathlib's naturality of the canonical maps from open subschemes to spectra of sections.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X Y : Scheme.{u}}

/-- On a standard open, pulling back homogeneous coordinates pulls back the projective
chart morphism. The source open is the basic open of the pulled-back coordinate. -/
@[reassoc]
theorem toBasicOpenOfGlobalSections_naturality (f : A →+* Γ(Y, ⊤)) (g : X ⟶ Y)
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    g.resLE (Y.basicOpen (f t)) (X.basicOpen (g.appTop (f t)))
        (g.preimage_basicOpen_top (f t)).ge ≫
      toBasicOpenOfGlobalSections 𝒜 f rfl hd ht =
        toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl hd ht := by
  rw [TauCeti.ProjectiveSpectrum.toBasicOpenOfGlobalSections_eq,
    TauCeti.ProjectiveSpectrum.toBasicOpenOfGlobalSections_eq]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  simp only [← Spec.map_comp_assoc]
  have hres :
      Y.presheaf.map (homOfLE le_top).op ≫
          g.appLE (Y.basicOpen (f t)) (X.basicOpen (g.appTop (f t)))
            (g.preimage_basicOpen_top (f t)).ge =
        g.appTop ≫ X.presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  congr 3
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  -- The section-ring instances in the chart formula come from the ringed space.
  erw [RingHom.comp_homogeneousLocalizationAwayLift]
  congr 1
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, hres,
    CommRingCat.hom_comp, RingHom.comp_assoc]

/-- Pulling back global homogeneous coordinates along a scheme morphism gives the
composite with the original projective morphism. -/
@[reassoc]
theorem fromOfGlobalSections_naturality (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) (g : X ⟶ Y) :
    g ≫ fromOfGlobalSections 𝒜 f hf =
      fromOfGlobalSections 𝒜 (g.appTop.hom.comp f)
        (by rw [← Ideal.map_map, hf, Ideal.map_top]) := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f)
    (by rw [← Ideal.map_map, hf, Ideal.map_top])).hom_ext _ _ fun ⟨d, t, hd, ht⟩ ↦ ?_
  have hchart := toBasicOpenOfGlobalSections_naturality 𝒜 f g hd ht
  have hy := fromOfGlobalSections_resLE 𝒜 f hf hd ht
  have hx := fromOfGlobalSections_resLE 𝒜 (g.appTop.hom.comp f)
    (by rw [← Ideal.map_map, hf, Ideal.map_top]) hd ht
  rw [← hy, ← hx] at hchart
  have h := congrArg (fun e ↦ e ≫ (basicOpen 𝒜 t).ι) hchart
  simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, openCoverOfMapIrrelevantEqTop,
    Scheme.openCoverOfIsOpenCover, RingHom.comp_apply] using h

end AlgebraicGeometry.Proj
