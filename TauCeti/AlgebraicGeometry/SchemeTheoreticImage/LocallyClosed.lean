/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Scheme structures on locally closed images

A quasi-compact morphism with locally closed topological image factors through an
immersion with exactly that image. The intermediate scheme is the scheme-theoretic
image inside the coborder, the complement of `closure (Set.range f) \ Set.range f`.
The first map is surjective and scheme-theoretically dominant; if the source is reduced,
the intermediate scheme
is reduced as well. This gives a scheme structure on a locally closed orbit.

The scheme structure is supplied by the morphism, including when the source
is nonreduced. Local closedness alone does not imply flatness.

## References

* Mathlib's `Scheme.Hom.toImage` and `IsOpenImmersion.lift` constructions.
* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f (orbit schemes).
* The Stacks Project, Tag 01R5 (scheme-theoretic images).
-/

public section

open CategoryTheory Topology

namespace AlgebraicGeometry.Scheme.Hom

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The largest open subset of the target in which the topological image is closed. -/
def coborderRangeOfIsLocallyClosed (h : IsLocallyClosed (Set.range f)) : Y.Opens :=
  ⟨coborder (Set.range f), h.isOpen_coborder⟩

/-- The open used for the locally closed image has the coborder as its underlying set. -/
@[simp]
theorem coe_coborderRangeOfIsLocallyClosed (h : IsLocallyClosed (Set.range f)) :
    (f.coborderRangeOfIsLocallyClosed h : Set Y) = coborder (Set.range f) := (rfl)

/-- Regard a morphism with locally closed image as a morphism into the coborder of its image. -/
def liftCoborderRange (h : IsLocallyClosed (Set.range f)) :
    X ⟶ f.coborderRangeOfIsLocallyClosed h :=
  IsOpenImmersion.lift (f.coborderRangeOfIsLocallyClosed h).ι f (by
    rw [Scheme.Opens.range_ι, coe_coborderRangeOfIsLocallyClosed]
    exact subset_coborder)

/-- Composing the lift with the open inclusion recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem liftCoborderRange_ι (h : IsLocallyClosed (Set.range f)) :
    f.liftCoborderRange h ≫ (f.coborderRangeOfIsLocallyClosed h).ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The lifted image is the preimage of the original image under the open inclusion. -/
theorem range_liftCoborderRange (h : IsLocallyClosed (Set.range f)) :
    Set.range (f.liftCoborderRange h) = (f.coborderRangeOfIsLocallyClosed h).ι ⁻¹' Set.range f := by
  -- Scheme lifts use the locally ringed space lift; reuse its range formula.
  have H : Set.range f ⊆ Set.range (f.coborderRangeOfIsLocallyClosed h).ι := by
    rw [Scheme.Opens.range_ι, coe_coborderRangeOfIsLocallyClosed]
    exact subset_coborder
  exact LocallyRingedSpace.IsOpenImmersion.lift_range
    (f.coborderRangeOfIsLocallyClosed h).ι.toLRSHom f.toLRSHom H

/-- The image becomes closed inside its coborder. -/
theorem isClosed_range_liftCoborderRange (h : IsLocallyClosed (Set.range f)) :
    IsClosed (Set.range (f.liftCoborderRange h)) := by
  rw [range_liftCoborderRange]
  -- The carrier of an open subscheme is definitionally the subtype of its open set.
  exact isClosed_preimage_val_coborder

instance instQuasiCompactLiftCoborderRange [QuasiCompact f]
    (h : IsLocallyClosed (Set.range f)) : QuasiCompact (f.liftCoborderRange h) := by
  have : QuasiCompact (f.liftCoborderRange h ≫ (f.coborderRangeOfIsLocallyClosed h).ι) := by
    rw [liftCoborderRange_ι]
    infer_instance
  exact QuasiCompact.of_comp _ (f.coborderRangeOfIsLocallyClosed h).ι

/-- The scheme-theoretic image formed in an open where the original image is closed. -/
abbrev locallyClosedImage (h : IsLocallyClosed (Set.range f)) : Scheme.{u} :=
  (f.liftCoborderRange h).image

/-- The immersion of the locally closed image into the original target. -/
def locallyClosedImageι (h : IsLocallyClosed (Set.range f)) :
    f.locallyClosedImage h ⟶ Y :=
  (f.liftCoborderRange h).imageι ≫ (f.coborderRangeOfIsLocallyClosed h).ι

/-- The canonical map from the source onto its locally closed scheme image. -/
def toLocallyClosedImage (h : IsLocallyClosed (Set.range f)) :
    X ⟶ f.locallyClosedImage h :=
  (f.liftCoborderRange h).toImage

/-- The inclusion factors as a closed immersion into the coborder
followed by that open subscheme's inclusion. -/
theorem locallyClosedImageι_def (h : IsLocallyClosed (Set.range f)) :
    f.locallyClosedImageι h =
      (f.liftCoborderRange h).imageι ≫ (f.coborderRangeOfIsLocallyClosed h).ι := (rfl)

/-- The image factorization map is the usual scheme-theoretic image factorization
of the lifted morphism. -/
theorem toLocallyClosedImage_def (h : IsLocallyClosed (Set.range f)) :
    f.toLocallyClosedImage h = (f.liftCoborderRange h).toImage := (rfl)

/-- The locally closed scheme image inclusion is an immersion. -/
instance instIsImmersionLocallyClosedImageι (h : IsLocallyClosed (Set.range f)) :
    IsImmersion (f.locallyClosedImageι h) := by
  rw [locallyClosedImageι_def]
  infer_instance

/-- The locally closed scheme image factorization recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem toLocallyClosedImage_locallyClosedImageι (h : IsLocallyClosed (Set.range f)) :
    f.toLocallyClosedImage h ≫ f.locallyClosedImageι h = f := by
  rw [toLocallyClosedImage_def, locallyClosedImageι_def,
    Scheme.Hom.toImage_imageι_assoc, liftCoborderRange_ι]

variable [QuasiCompact f]

/-- The map onto the locally closed scheme image is surjective on all points. -/
instance instSurjectiveToLocallyClosedImage (h : IsLocallyClosed (Set.range f)) :
    Surjective (f.toLocallyClosedImage h) := by
  rw [toLocallyClosedImage_def]
  exact ⟨(f.liftCoborderRange h).toImage_surjective_of_isClosed_range
    (f.isClosed_range_liftCoborderRange h)⟩

/-- The immersion has precisely the original topological image, including nonclosed points. -/
@[simp]
theorem range_locallyClosedImageι (h : IsLocallyClosed (Set.range f)) :
    Set.range (f.locallyClosedImageι h) = Set.range f := by
  have heq := congrArg (fun g : X ⟶ Y ↦ Set.range g)
    (f.toLocallyClosedImage_locallyClosedImageι h)
  simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (f.toLocallyClosedImage h).surjective, Set.image_univ] using heq

/-- No proper closed subscheme of the constructed image contains the factorization map. -/
instance instIsSchemeTheoreticallyDominantToLocallyClosedImage
    (h : IsLocallyClosed (Set.range f)) :
    IsSchemeTheoreticallyDominant (f.toLocallyClosedImage h) := by
  rw [toLocallyClosedImage_def]
  infer_instance

/-- The factorization map remains quasi-compact. -/
instance instQuasiCompactToLocallyClosedImage (h : IsLocallyClosed (Set.range f)) :
    QuasiCompact (f.toLocallyClosedImage h) := by
  rw [toLocallyClosedImage_def]
  infer_instance

/-- A locally finite-type morphism stays locally of finite type after factorization
through its locally closed scheme image. -/
instance instLocallyOfFiniteTypeToLocallyClosedImage [LocallyOfFiniteType f]
    (h : IsLocallyClosed (Set.range f)) :
    LocallyOfFiniteType (f.toLocallyClosedImage h) := by
  have : LocallyOfFiniteType (f.toLocallyClosedImage h ≫ f.locallyClosedImageι h) := by
    rw [toLocallyClosedImage_locallyClosedImageι]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (f.locallyClosedImageι h)

end

end AlgebraicGeometry.Scheme.Hom
