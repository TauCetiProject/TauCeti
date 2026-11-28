/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.FaithfullyFlat
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange
import TauCeti.AlgebraicGeometry.AbelianVariety.DimensionZero
import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Iso
import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Rigidity
import TauCeti.AlgebraicGeometry.GroupScheme.Image
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.GeometricallyIntegral
import TauCeti.CategoryTheory.Comma.Over

/-!
# Images of homomorphisms of abelian varieties

The scheme-theoretic image of a homomorphism of abelian varieties is an abelian subvariety
of the target, over the original field. The homomorphism factors through the image by a
faithfully flat morphism. The image is minimal among closed subschemes through which the
underlying morphism factors, and extending the ground field preserves the factorization.

## Main declarations

* `AbelianVariety.image`, `AbelianVariety.toImage`, `AbelianVariety.imageι`:
  the image and its factorization.
* `AbelianVariety.imageLift`: the inclusion into any abelian subvariety through which
  the homomorphism factors.
* `AbelianVariety.imageBaseChangeIso`: the image comparison over a field extension.

## References

* J. S. Milne, *Algebraic Groups*, Theorem 5.39 and Remark 5.42, for the image of a group
  homomorphism.
* The Stacks Project, Lemma 29.26.16, Tag 081I, for flat base change of scheme-theoretic images.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj AlgebraicGeometry
open scoped TauCeti.AlgebraicGeometry.AbelianVariety.Hom

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] {A B C : AbelianVariety K}

/-- The abelian variety on the scheme-theoretic image of a homomorphism. Its group law is induced
by the group law of the target, and its ground field is the original field. -/
def image (f : A ⟶ B) : AbelianVariety K := by
  have : GeometricallyIntegral (Hom.toSchemeHom f ≫ B.toOver.hom) := by
    rw [Hom.toSchemeHom_comp_hom]
    infer_instance
  exact
    { toOver := (Hom.toOverHom f).imageOver
      grpObj := inferInstance
      isProper := inferInstanceAs (IsProper ((Hom.toSchemeHom f).imageι ≫ B.toOver.hom))
      geometricallyIntegral := (Hom.toSchemeHom f).geometricallyIntegral_imageι_comp B.toOver.hom }

/-- The underlying scheme of the image abelian variety is the scheme-theoretic image. -/
@[simp]
theorem image_toScheme (f : A ⟶ B) : (image f).toScheme = (Hom.toSchemeHom f).image :=
  (rfl)

/-- The inclusion of the image into the target abelian variety. -/
def imageι (f : A ⟶ B) : image f ⟶ B :=
  let i := (Hom.toOverHom f).imageιOver
  Hom.mk' i (IsMonHom.one_hom i) (IsMonHom.mul_hom i)

/-- The homomorphism from the source onto the image. -/
def toImage (f : A ⟶ B) : A ⟶ image f :=
  let q := (Hom.toOverHom f).toImageOver
  Hom.mk' q (IsMonHom.one_hom q) (IsMonHom.mul_hom q)

/-- On underlying schemes, the image inclusion is the scheme-theoretic image immersion. -/
@[simp]
theorem toSchemeHom_imageι (f : A ⟶ B) :
    Hom.toSchemeHom (imageι f) = eqToHom (image_toScheme f) ≫ (Hom.toSchemeHom f).imageι := by
  unfold imageι
  exact (Hom.toSchemeHom_mk' _ _ _).trans
    ((Over.Hom.imageιOver_left _).trans (Category.id_comp _).symm)

/-- On underlying schemes, the homomorphism to the image is the canonical factorization. -/
@[simp]
theorem toSchemeHom_toImage (f : A ⟶ B) :
    Hom.toSchemeHom (toImage f) =
      (Hom.toSchemeHom f).toImage ≫ eqToHom (image_toScheme f).symm := by
  unfold toImage
  exact (Hom.toSchemeHom_mk' _ _ _).trans
    ((Over.Hom.toImageOver_left _).trans (Category.comp_id _).symm)

/-- A homomorphism factors through its image abelian variety. -/
@[reassoc (attr := simp)]
theorem toImage_imageι (f : A ⟶ B) : toImage f ≫ imageι f = f := by
  apply Hom.ext
  simp

/-- The image is a closed subgroup of the target. -/
instance isClosedImmersion_imageι (f : A ⟶ B) : IsClosedImmersion (Hom.toSchemeHom (imageι f)) := by
  rw [toSchemeHom_imageι]
  infer_instance

/-- The homomorphism to the image is surjective. The original homomorphism is proper since
its source is proper over the field and its target is separated. -/
instance surjective_toImage (f : A ⟶ B) : Surjective (Hom.toSchemeHom (toImage f)) := by
  have : IsProper (Hom.toSchemeHom f ≫ B.toOver.hom) := by
    rw [Hom.toSchemeHom_comp_hom]
    infer_instance
  have : IsProper (Hom.toSchemeHom f) := IsProper.of_comp (Hom.toSchemeHom f) B.toOver.hom
  rw [toSchemeHom_toImage]
  infer_instance

/-- The surjective homomorphism to the image is flat. -/
instance flat_toImage (f : A ⟶ B) : Flat (Hom.toSchemeHom (toImage f)) :=
  AbelianVariety.flat_of_surjective (toImage f)

/-- The source-to-image map is schematically dominant. -/
instance isSchemeTheoreticallyDominant_toImage (f : A ⟶ B) :
    IsSchemeTheoreticallyDominant (Hom.toSchemeHom (toImage f)) := by
  rw [toSchemeHom_toImage]
  infer_instance

/-- The ideal of the abelian subvariety that is the image equals the ideal cut out by
the original homomorphism. -/
theorem ker_imageι (f : A ⟶ B) : (Hom.toSchemeHom (imageι f)).ker = (Hom.toSchemeHom f).ker := by
  rw [toSchemeHom_imageι, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_subschemeι _

/-- The inclusion of the image into any abelian subvariety through which the homomorphism
factors, expressed by containment of the defining ideals. -/
def imageLift (f : A ⟶ B) (i : C ⟶ B) [IsClosedImmersion (Hom.toSchemeHom i)]
    (hi : (Hom.toSchemeHom i).ker ≤ (Hom.toSchemeHom f).ker) : (image f) ⟶ C := by
  let j := Hom.toOverHom i
  have : Mono j := Over.mono_of_mono_left j
  let l := closedImmersionOverLift j (Hom.toOverHom (imageι f)) ((ker_imageι f).symm ▸ hi)
  refine (Hom.equivPointed (image f) C).symm ⟨l, ?_⟩
  apply (cancel_mono j).mp
  simp [l]

/-- The image lift commutes with the inclusions into the target. -/
@[reassoc (attr := simp)]
theorem imageLift_comp (f : A ⟶ B) (i : C ⟶ B) [IsClosedImmersion (Hom.toSchemeHom i)]
    (hi : (Hom.toSchemeHom i).ker ≤ (Hom.toSchemeHom f).ker) :
    imageLift f i hi ≫ i = (imageι f) := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, imageLift, Hom.toOverHom_equivPointed_symm_apply]
  exact closedImmersionOverLift_comp _ _ _

/-- The image is the smallest abelian subvariety through which the homomorphism factors. -/
theorem existsUnique_image_factor (f : A ⟶ B) (i : C ⟶ B)
    [IsClosedImmersion (Hom.toSchemeHom i)] (g : A ⟶ C) (hg : g ≫ i = f) :
    ∃! l : image f ⟶ C, toImage f ≫ l = g ∧ l ≫ i = imageι f := by
  have hi : (Hom.toSchemeHom i).ker ≤ (Hom.toSchemeHom f).ker := by
    rw [← hg, Hom.toSchemeHom_comp]
    exact (Hom.toSchemeHom g).le_ker_comp (Hom.toSchemeHom i)
  refine ⟨imageLift f i hi, ⟨?_, imageLift_comp f i hi⟩, fun l hl ↦ ?_⟩
  · apply Hom.ext
    apply (cancel_mono (Hom.toSchemeHom i)).mp
    simp only [← Hom.toSchemeHom_comp, Category.assoc, imageLift_comp, toImage_imageι, hg]
  · apply Hom.ext
    apply (cancel_mono (Hom.toSchemeHom i)).mp
    simpa only [← Hom.toSchemeHom_comp, imageLift_comp f] using congrArg Hom.toSchemeHom hl.2

section BaseChange

variable (L : Type u) [Field L] [Algebra K L]

private instance isClosedImmersion_baseChange_imageι (f : A ⟶ B) :
    IsClosedImmersion (Hom.toSchemeHom (Hom.baseChange (imageι f) L)) := by
  rw [Hom.toSchemeHom_baseChange]
  simp only [Over.comp_left, Over.eqToHom_left]
  have := MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) (Hom.toOverHom (imageι f)) inferInstance
  infer_instance

private theorem ker_imageι_baseChange (f : A ⟶ B) :
    (Hom.toSchemeHom (Hom.baseChange (imageι f) L)).ker =
      (Hom.toSchemeHom (Hom.baseChange f L)).ker := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hs := (Over.isPullback_pullback_map_left b (Hom.toOverHom (toImage f))).flip
  have : IsSchemeTheoreticallyDominant ((Over.pullback b).map
      (Hom.toOverHom (toImage f))).left := .of_isPullback hs
  have : IsSchemeTheoreticallyDominant (Hom.toSchemeHom (Hom.baseChange (toImage f) L)) := by
    rw [Hom.toSchemeHom_baseChange]
    simp only [Over.comp_left, Over.eqToHom_left]
    infer_instance
  calc
    _ = (Hom.toSchemeHom (Hom.baseChange (toImage f) L) ≫
        Hom.toSchemeHom (Hom.baseChange (imageι f) L)).ker :=
      (Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _).symm
    _ = _ := by
      rw [← Hom.toSchemeHom_comp, ← Hom.baseChange_comp, toImage_imageι]

/-- The image of the extended homomorphism is canonically the extension of the image,
as an abelian subvariety of the extended target. -/
def imageBaseChangeIso (f : A ⟶ B) :
    image (Hom.baseChange f L) ≅ (image f).baseChange L := by
  let i := Hom.baseChange (imageι f) L
  let fL := Hom.baseChange f L
  let l := imageLift fL i (ker_imageι_baseChange L f).le
  have hl : l ≫ i = imageι fL := imageLift_comp _ _ _
  have hl' : Hom.toSchemeHom l ≫ Hom.toSchemeHom i = Hom.toSchemeHom (imageι fL) := by
    rw [← Hom.toSchemeHom_comp, hl]
  have : IsIso (Hom.toSchemeHom l) :=
    IsClosedImmersion.isIso_of_ker_eq _ _ _ hl'
      ((ker_imageι fL).trans (ker_imageι_baseChange L f).symm)
  let e : (image fL).toOver ≅ ((image f).baseChange L).toOver :=
    Over.isoMk (asIso (Hom.toSchemeHom l)) (Hom.toOverHom l).w
  have he : e.hom = Hom.toOverHom l := Over.OverMorphism.ext (by rfl)
  have : IsMonHom e.hom := he.symm ▸ inferInstanceAs (IsMonHom (Hom.toOverHom l))
  exact InducedCategory.isoMk (CommGrp.mkIso' e)

/-- The image comparison respects the inclusions into the extended target. -/
@[reassoc (attr := simp)]
theorem imageBaseChangeIso_hom_imageι (f : A ⟶ B) :
    (imageBaseChangeIso L f).hom ≫ Hom.baseChange (imageι f) L =
      imageι (Hom.baseChange f L) := by
  have h : (imageBaseChangeIso L f).hom =
      imageLift (Hom.baseChange f L) (Hom.baseChange (imageι f) L)
        (ker_imageι_baseChange L f).le := by
    apply Hom.ext
    rfl
  rw [h, imageLift_comp]

/-- The image comparison respects the maps from the extended source. -/
@[reassoc (attr := simp)]
theorem toImage_imageBaseChangeIso_hom (f : A ⟶ B) :
    toImage (Hom.baseChange f L) ≫ (imageBaseChangeIso L f).hom =
      Hom.baseChange (toImage f) L := by
  apply Hom.ext
  apply (cancel_mono (Hom.toSchemeHom (Hom.baseChange (imageι f) L))).mp
  simp only [← Hom.toSchemeHom_comp, Category.assoc, imageBaseChangeIso_hom_imageι,
    toImage_imageι, ← Hom.baseChange_comp]

end BaseChange

/-- A nonzero homomorphism into an abelian variety whose only abelian subvarieties
are zero and itself is surjective. The zero homomorphism is written as `1`. -/
theorem surjective_of_ne_one_of_dim_eq_zero_or_isIso (f : A ⟶ B) (hf : f ≠ 1)
    (hB : ∀ {D : AbelianVariety K} (i : D ⟶ B), IsClosedImmersion (Hom.toSchemeHom i) →
      D.dim = 0 ∨ IsIso i) : Surjective (Hom.toSchemeHom f) := by
  obtain hz | hi := hB (imageι f) inferInstance
  · have hq : toImage f = 1 := ((isZero_iff_dim_eq_zero (image f)).mpr hz).eq_of_tgt _ _
    exact (hf (by rw [← toImage_imageι f, hq, Hom.one_comp])).elim
  · rw [← toImage_imageι f, Hom.toSchemeHom_comp]
    let e := asIso (imageι f)
    have : IsIso (Hom.toSchemeHom (imageι f)) :=
      isoToScheme_hom e ▸ inferInstanceAs (IsIso (isoToScheme e).hom)
    infer_instance

end TauCeti.AlgebraicGeometry.AbelianVariety
