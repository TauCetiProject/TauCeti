/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalk.Valuation

/-!
# Global sections and stalk valuations

The canonical map from a complete Hausdorff coefficient ring to a stalk factors through
global sections. Pulling back the stalk valuation along this map recovers the point of the
adic spectrum. This connects pullback on global sections with pullback of valuations.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe u

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
  (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- The canonical map from the coefficient ring to the stalk at a point, through the
identification of the coefficient ring with global sections. -/
noncomputable def presentationLimitGlobalGerm (x : spa Aplus) :
    A →+* (presentationLimitPresheafInCommRingCat P Aplus).stalk x :=
  ((forget₂ _root_.TopCommRingCat CommRingCat).map
      (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm) ≫
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
      (toPresentationLimit (P := P) Aplus ⊤) ≫
    eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus (Opposite.op ⊤)).symm ≫
    (presentationLimitPresheafInCommRingCat P Aplus).germ ⊤ x (Opens.mem_top x)).hom

/-- The global germ is the coefficient map followed by the ordinary presheaf germ, with
transports between the bundled section objects. -/
theorem presentationLimitGlobalGerm_def (x : spa Aplus) :
    presentationLimitGlobalGerm P Aplus x =
      ((forget₂ _root_.TopCommRingCat CommRingCat).map
          (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm) ≫
        (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (toPresentationLimit (P := P) Aplus ⊤) ≫
        eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus (Opposite.op ⊤)).symm ≫
        (presentationLimitPresheafInCommRingCat P Aplus).germ ⊤ x (Opens.mem_top x)).hom := (rfl)

-- The proof uses `toPresentationLimit` and the rational-germ characterisation of
-- `presentationLimitStalkValuation`.
/-- Pulling the stalk valuation back along the canonical global germ map recovers the point
of the original adic spectrum. -/
-- Not `@[simp]`: simp normalises the underlying presheaf in the stalk type before matching.
-- Use `rw` or `exact` to apply the pullback identity.
theorem comap_presentationLimitGlobalGerm (x : spa Aplus) :
    comap (presentationLimitGlobalGerm P Aplus x) (presentationLimitStalkValuation hAplus hP x) =
      x.1 := by
  -- Use the trivial rational presentation to compute the germ of a global coefficient.
  let p := Presentation.trivial P
  have hp : IsOpen (Ideal.span (p.num : Set A) : Set A) := by
    simp [p]
  have hx : x ∈ spaBasicOpen Aplus p.num p.den :=
    mem_spaBasicOpen.mpr (by simp [p])
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have e : (presentationLimitGlobalGerm P Aplus x) =
      (CommRingCat.ofHom (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) ≫
        (Presentation.completionLocObjCommRingCatIso p).inv ≫
          presentationLimitRationalGerm hAplus p hp x hx).hom := by
    rw [presentationLimitGlobalGerm]
    apply congrArg CommRingCat.Hom.hom
    rw [presentationLimitRationalGerm_def]
    have hcanon : toPresentationLimit (P := P) Aplus (spaBasicOpen Aplus p.num p.den) ≫
        (presentationLimitRationalIso Aplus hAplus p hp).hom = p.toCompletionLocObjHom := by
      simp
    have hcanon' := congrArg
      ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map)
      ((Iso.eq_comp_inv _).mpr hcanon)
    rw [Functor.map_comp] at hcanon'
    rw [presentationLimitRationalIsoInCommRingCat_inv, Category.assoc]
    have hstruct : CommRingCat.ofHom (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) ≫
        (Presentation.completionLocObjCommRingCatIso p).inv =
        (forget₂ _root_.TopCommRingCat CommRingCat).map
          (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm) ≫
        (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          p.toCompletionLocObjHom := by
      simp only [Presentation.completionLocObjCommRingCatIso_inv, Functor.comp_map,
        ObjectProperty.ι_map, Presentation.toCompletionLocObjHom_hom, Functor.map_comp]
      simp only [← Functor.map_comp_assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rfl
    simp only [← Category.assoc]
    rw [hstruct]
    have hcanon'' := congrArg (fun f ↦
      (forget₂ _root_.TopCommRingCat CommRingCat).map
        (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm) ≫ f) hcanon'
    simp only [← Category.assoc] at hcanon''
    erw [← hcanon'']
    have hR : spaBasicOpen Aplus p.num p.den = ⊤ := by
      ext y
      simp [mem_spaBasicOpen, p]
    -- Generalize the membership proof before transporting its open to the whole space.
    revert hx
    erw [hR]
    intro hx
    rfl
  rw [e]
  exact comap_presentationLimitStalkValuation hAplus hP p hp x hx

end TauCeti.ValuationSpectrum

end
