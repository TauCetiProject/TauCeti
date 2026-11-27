/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.GroupScheme.Image
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.FlatBaseChange
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.GeometricallyIntegral
import TauCeti.CategoryTheory.Comma.Over

/-!
# Scheme-theoretic images of abelian variety homomorphisms

The scheme-theoretic image of a homomorphism of abelian varieties is an abelian variety over the
original field, including over imperfect fields. Its group law is induced by the closed subgroup
criterion. Geometric integrality follows by pulling back the schematically dominant map
to the image along field extensions and descending integrality from the source.

The construction gives the surjective homomorphism onto the image, its closed immersion into
the target and the universal factorization through any abelian subvariety containing the image.
Extending the ground field preserves this factorization by flat base change of scheme-theoretic
images, as in Stacks Project, Tag 081I.
-/

public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open Hom

universe u

variable {K : Type u} [Field K] {A B C : AbelianVariety K} (f : A ⟶ B)

/-- The scheme-theoretic image of a homomorphism of abelian varieties, with its induced group
structure over the original field. -/
def image : AbelianVariety K where
  toOver := GroupScheme.imageOver (toOverHom f)
  grpObj := GroupScheme.imageGrpObj (toOverHom f)
  isProper := inferInstanceAs (IsProper ((toSchemeHom f).imageι ≫ B.toOver.hom))
  geometricallyIntegral := by
    have : GeometricallyIntegral (toSchemeHom f ≫ B.toOver.hom) := by
      rw [toSchemeHom_comp_hom]
      infer_instance
    exact inferInstanceAs (GeometricallyIntegral ((toSchemeHom f).imageι ≫ B.toOver.hom))

/-- The image over the ground field is the schematic image with the restricted structure map. -/
lemma image_toOver : (image f).toOver = GroupScheme.imageOver (toOverHom f) := (rfl)

/-- The underlying scheme of the image is the scheme-theoretic image. -/
@[simp]
lemma image_toScheme : (image f).toScheme = (toSchemeHom f).image := (rfl)

/-- The closed embedding of the image into the target abelian variety. -/
def imageι : image f ⟶ B := by
  have : IsMonHom (M := (image f).toOver) (GroupScheme.imageι (toOverHom f)) :=
    GroupScheme.isMonHom_imageι (toOverHom f)
  exact mk' (GroupScheme.imageι (toOverHom f)) (IsMonHom.one_hom _) (IsMonHom.mul_hom _)

/-- The underlying morphism over the ground field is the group-scheme image inclusion. -/
@[simp]
lemma toOverHom_imageι :
    toOverHom (imageι f) = eqToHom (image_toOver f) ≫ GroupScheme.imageι (toOverHom f) := by
  unfold imageι
  exact (toOverHom_mk' _ _ _).trans (Category.id_comp _).symm

/-- The underlying scheme morphism of the inclusion is the canonical image inclusion. -/
@[simp]
lemma toSchemeHom_imageι :
    toSchemeHom (imageι f) = eqToHom (image_toScheme f) ≫ (toSchemeHom f).imageι := by
  simpa only [Over.comp_left, Over.eqToHom_left, GroupScheme.imageι_left] using
    congrArg Over.Hom.left (toOverHom_imageι f)

/-- The image inclusion is defined by the kernel ideal sheaf of the original homomorphism. -/
-- Use explicitly: `toSchemeHom_imageι` already simplifies the morphism inside the kernel.
lemma ker_toSchemeHom_imageι : (toSchemeHom (imageι f)).ker = (toSchemeHom f).ker := by
  rw [toSchemeHom_imageι, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.imageι,
    Scheme.IdealSheafData.ker_subschemeι]

instance : IsClosedImmersion (toSchemeHom (imageι f)) := by
  rw [toSchemeHom_imageι]
  infer_instance

/-- The induced homomorphism onto the scheme-theoretic image. -/
def toImage : A ⟶ image f := by
  have : IsMonHom (N := (image f).toOver) (GroupScheme.toImage (toOverHom f)) :=
    GroupScheme.isMonHom_toImage (toOverHom f)
  exact mk' (GroupScheme.toImage (toOverHom f)) (IsMonHom.one_hom _) (IsMonHom.mul_hom _)

/-- The underlying morphism over the ground field is the group-scheme image factorization. -/
@[simp]
lemma toOverHom_toImage :
    toOverHom (toImage f) = GroupScheme.toImage (toOverHom f) ≫ eqToHom (image_toOver f).symm := by
  unfold toImage
  exact (toOverHom_mk' _ _ _).trans (Category.comp_id _).symm

/-- The underlying scheme morphism onto the image is Mathlib's canonical factorization. -/
@[simp]
lemma toSchemeHom_toImage :
    toSchemeHom (toImage f) = (toSchemeHom f).toImage ≫ eqToHom (image_toScheme f).symm := by
  simpa only [Over.comp_left, Over.eqToHom_left, GroupScheme.toImage_left] using
    congrArg Over.Hom.left (toOverHom_toImage f)

/-- The surjective factor and the inclusion compose to the original homomorphism. -/
@[reassoc (attr := simp)]
lemma toImage_imageι : toImage f ≫ imageι f = f := by
  apply toOverHom_injective
  rw [toOverHom_comp, toOverHom_toImage, toOverHom_imageι]
  simp

/-- The induced homomorphism onto the scheme-theoretic image is surjective. -/
instance : Surjective (toSchemeHom (toImage f)) := by
  rw [toSchemeHom_toImage]
  have : Surjective (toSchemeHom f).toImage := ⟨(toSchemeHom f).toImage_surjective_of_isClosed_range
    (toSchemeHom f).isClosedMap.isClosed_range⟩
  infer_instance

/-- The lift of a homomorphism through a closed immersion whose ideal vanishes on the source. -/
def liftOfKerLE (i : C ⟶ B) [IsClosedImmersion (toSchemeHom i)]
    (hk : (toSchemeHom i).ker ≤ (toSchemeHom f).ker) : A ⟶ C := by
  have : IsClosedImmersion (toOverHom i).left :=
    inferInstanceAs (IsClosedImmersion (toSchemeHom i))
  let j := closedImmersionOverLift (toOverHom i) (toOverHom f) hk
  have hj : j ≫ toOverHom i = toOverHom f := by simp [j]
  have : Mono (toOverHom i) := Over.mono_of_mono_left _
  have h₁ : η[A.toOver] ≫ j = η[C.toOver] := by
    rw [← cancel_mono (toOverHom i), Category.assoc, hj, IsMonHom.one_hom, IsMonHom.one_hom]
  have h₂ : μ[A.toOver] ≫ j = (j ⊗ₘ j) ≫ μ[C.toOver] := by
    rw [← cancel_mono (toOverHom i), Category.assoc, hj, Category.assoc,
      IsMonHom.mul_hom (toOverHom i), ← Category.assoc, tensorHom_comp_tensorHom, hj,
      IsMonHom.mul_hom (toOverHom f)]
  exact mk' j h₁ h₂

/-- Composing the lift with the closed immersion recovers the original homomorphism. -/
@[reassoc (attr := simp)]
lemma liftOfKerLE_comp (i : C ⟶ B) [IsClosedImmersion (toSchemeHom i)]
    (hk : (toSchemeHom i).ker ≤ (toSchemeHom f).ker) : liftOfKerLE f i hk ≫ i = f := by
  apply toOverHom_injective
  rw [toOverHom_comp]
  unfold liftOfKerLE
  exact (congrArg (· ≫ toOverHom i) (toOverHom_mk' _ _ _)).trans
    (closedImmersionOverLift_comp _ _ _)

/-- A homomorphism factors uniquely through a closed immersion of abelian varieties exactly
when the immersion's defining ideal vanishes under pullback along the homomorphism. -/
theorem existsUnique_comp_eq_iff_ker_le (i : C ⟶ B) [IsClosedImmersion (toSchemeHom i)] :
    (∃! j : A ⟶ C, j ≫ i = f) ↔ (toSchemeHom i).ker ≤ (toSchemeHom f).ker := by
  constructor
  · rintro ⟨j, rfl, _⟩
    rw [toSchemeHom_comp]
    exact Scheme.Hom.le_ker_comp _ _
  · intro hk
    refine ⟨liftOfKerLE f i hk, liftOfKerLE_comp f i hk, fun j hj ↦ Hom.ext ?_⟩
    rw [← cancel_mono (toSchemeHom i), ← toSchemeHom_comp, ← toSchemeHom_comp, hj, liftOfKerLE_comp]

/-- If a homomorphism factors through a closed immersion, its scheme-theoretic image factors
uniquely through the same immersion. -/
theorem existsUnique_comp_eq_imageι {i : C ⟶ B} [IsClosedImmersion (toSchemeHom i)]
    {g : A ⟶ C} (h : g ≫ i = f) : ∃! j : image f ⟶ C, j ≫ i = imageι f := by
  apply (existsUnique_comp_eq_iff_ker_le _ _).mpr
  rw [ker_toSchemeHom_imageι, ← h, toSchemeHom_comp]
  exact Scheme.Hom.le_ker_comp _ _

section BaseChange

variable (L : Type u) [Field L] [Algebra K L]

private lemma ker_baseChange_imageι :
    (toSchemeHom (Hom.baseChange (imageι f) L)).ker =
      (toSchemeHom (imageι (Hom.baseChange f L))).ker := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  -- The source transports preserve kernels; the common target transport maps both kernels.
  rw [ker_toSchemeHom_imageι, toSchemeHom_baseChange (imageι f), toSchemeHom_baseChange f]
  simp only [Over.comp_left, Scheme.Hom.ker_comp_of_isIso]
  rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_comp,
    Scheme.IdealSheafData.ker_eq_comap_of_isPullback (toSchemeHom (imageι f))
      (Over.isPullback_pullback_map_left b (toOverHom (imageι f))),
    (toSchemeHom f).ker_eq_comap_of_isPullback_of_flat
      (Over.isPullback_pullback_map_left b (toOverHom f)).flip,
    ker_toSchemeHom_imageι]

/-- The canonical isomorphism from the image after extending the ground field to the extension
of the original image. -/
def imageBaseChangeIso : image (Hom.baseChange f L) ≅ (image f).baseChange L := by
  have h := ker_baseChange_imageι f L
  let i := imageι (Hom.baseChange f L)
  let j := Hom.baseChange (imageι f) L
  refine ⟨liftOfKerLE i j h.le, liftOfKerLE j i h.ge, ?_, ?_⟩
  · exact ((existsUnique_comp_eq_iff_ker_le i i).mpr le_rfl).unique
      (by simp) (Category.id_comp _)
  · exact ((existsUnique_comp_eq_iff_ker_le j j).mpr le_rfl).unique
      (by simp) (Category.id_comp _)

/-- The comparison respects the inclusion of the image in the base-changed target. -/
@[reassoc (attr := simp)]
lemma imageBaseChangeIso_hom_comp_baseChange_imageι :
    (imageBaseChangeIso f L).hom ≫ Hom.baseChange (imageι f) L = imageι (Hom.baseChange f L) := by
  unfold imageBaseChangeIso
  apply liftOfKerLE_comp

/-- The comparison respects the map from the base-changed source onto the image. -/
@[reassoc (attr := simp)]
lemma toImage_comp_imageBaseChangeIso_hom :
    toImage (Hom.baseChange f L) ≫ (imageBaseChangeIso f L).hom = Hom.baseChange (toImage f) L := by
  apply Hom.ext
  rw [← cancel_mono (toSchemeHom (Hom.baseChange (imageι f) L)),
    ← toSchemeHom_comp, ← toSchemeHom_comp]
  simp only [Category.assoc, imageBaseChangeIso_hom_comp_baseChange_imageι, toImage_imageι,
    ← Hom.baseChange_comp]

end BaseChange

end TauCeti.AlgebraicGeometry.AbelianVariety
