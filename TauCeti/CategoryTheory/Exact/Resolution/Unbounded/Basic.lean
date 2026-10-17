/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Projective
public import Mathlib.Algebra.Homology.Additive

/-!
# Projective resolutions in exact categories

An unbounded projective resolution is a sequence of conflations
`Kₙ₊₁ ↪ Pₙ ↠ Kₙ`, with relatively projective `Pₙ` and an identification `K₀ ≅ X`.
Splicing these conflations gives an augmented chain complex resolving `X`. Keeping the
syzygies and their universal properties permits resolution calculus without assuming that
arbitrary kernels or cokernels exist in the ambient category.

Conflation-exact additive functors preserving relative projectives act termwise on these
resolutions. In particular the internal shift of a graded exact category can be used as such
a functor. No boundedness or finite generation is imposed on the resolving terms. Enough relative
projectives produce such a resolution by successively resolving the syzygies.

## References

* Theo Bühler, *Exact categories*, Section 12.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- A projective resolution in an exact category, recorded as successive conflations through
its syzygies. The chosen identification of the zeroth syzygy specifies the augmentation. -/
structure ProjectiveResolution (E : ExactStructure C) (Y : C) where
  /-- The syzygy in degree `n`, including the object being resolved in degree zero. -/
  K : ℕ → C
  /-- The relatively projective term in degree `n`. -/
  X : ℕ → C
  /-- The identification of the zeroth syzygy with the resolved object. -/
  iso : K 0 ≅ Y
  /-- The inflation of the next syzygy into the resolving term. -/
  ι (n : ℕ) : K (n + 1) ⟶ X n
  /-- The deflation from the resolving term onto its syzygy. -/
  π (n : ℕ) : X n ⟶ K n
  /-- The syzygy maps have zero composite. -/
  zero (n : ℕ) : ι n ≫ π n = 0
  /-- Each syzygy sequence is a distinguished conflation. -/
  conflation (n : ℕ) : E.Conflation (ShortComplex.mk (ι n) (π n) (zero n))
  /-- Every resolving term is relatively projective. -/
  isProjective (n : ℕ) : E.isProjective (X n)

namespace ProjectiveResolution

variable {E : ExactStructure C} {Y : C} (r : E.ProjectiveResolution Y)

attribute [reassoc (attr := simp)] zero

/-- The differential obtained by splicing consecutive syzygy conflations. -/
def d (n : ℕ) : r.X (n + 1) ⟶ r.X n := r.π (n + 1) ≫ r.ι n

/-- The augmentation to the resolved object. -/
def aug : r.X 0 ⟶ Y := r.π 0 ≫ r.iso.hom

/-- The splicing formula for the differential. -/
lemma d_def (n : ℕ) : r.d n = r.π (n + 1) ≫ r.ι n := (rfl)

/-- The augmentation uses the specified zeroth-syzygy identification. -/
lemma aug_def : r.aug = r.π 0 ≫ r.iso.hom := (rfl)

/-- Consecutive differentials have zero composite. -/
@[reassoc (attr := simp)]
lemma d_comp_d (n : ℕ) : r.d (n + 1) ≫ r.d n = 0 := by
  simp [d_def]

/-- The first differential has zero composite with the augmentation. -/
@[reassoc (attr := simp)]
lemma d_comp_aug : r.d 0 ≫ r.aug = 0 := by
  simp [d_def, aug_def]

/-- The chain complex formed by splicing the syzygy conflations. -/
abbrev toChainComplex : ChainComplex C ℕ := ChainComplex.of r.X r.d r.d_comp_d

/-- The differential of the spliced chain complex in consecutive degrees. -/
lemma toChainComplex_d (n : ℕ) : r.toChainComplex.d (n + 1) n = r.d n :=
  ChainComplex.of_d _ _ n

section Map

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F) (hproj : E.isProjective ≤ E'.isProjective.inverseImage F)

/-- Apply a conflation-exact functor preserving relative projectives to every term and syzygy. -/
def map : E'.ProjectiveResolution (F.obj Y) where
  K n := F.obj (r.K n)
  X n := F.obj (r.X n)
  iso := F.mapIso r.iso
  ι n := F.map (r.ι n)
  π n := F.map (r.π n)
  zero n := by rw [← F.map_comp, r.zero, F.map_zero]
  conflation n := hF.map_conflation (r.conflation n)
  isProjective n := hproj _ (r.isProjective n)

@[simp] lemma map_K (n : ℕ) : (r.map hF hproj).K n = F.obj (r.K n) := (rfl)

@[simp] lemma map_X (n : ℕ) : (r.map hF hproj).X n = F.obj (r.X n) := (rfl)

/-- The mapped syzygy identifies with the image of the original syzygy. -/
def mapKIso (n : ℕ) : (r.map hF hproj).K n ≅ F.obj (r.K n) :=
  eqToIso (r.map_K hF hproj n)

/-- The mapped term identifies with the image of the original term. -/
def mapXIso (n : ℕ) : (r.map hF hproj).X n ≅ F.obj (r.X n) :=
  eqToIso (r.map_X hF hproj n)

@[simp]
lemma map_iso_hom : (r.map hF hproj).iso.hom =
    (r.mapKIso hF hproj 0).hom ≫ F.map r.iso.hom := by
  -- After unfolding the mapped objects, the equality transport is the identity.
  dsimp [mapKIso, map]
  exact (Category.id_comp _).symm

@[simp]
lemma map_ι (n : ℕ) : (r.map hF hproj).ι n =
    (r.mapKIso hF hproj (n + 1)).hom ≫ F.map (r.ι n) ≫
      (r.mapXIso hF hproj n).inv := by
  -- Both object transports are identities after unfolding the termwise construction.
  dsimp [mapKIso, mapXIso, map]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

@[simp]
lemma map_π (n : ℕ) : (r.map hF hproj).π n =
    (r.mapXIso hF hproj n).hom ≫ F.map (r.π n) ≫
      (r.mapKIso hF hproj n).inv := by
  -- Both object transports are identities after unfolding the termwise construction.
  dsimp [mapKIso, mapXIso, map]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

@[simp]
lemma map_d (n : ℕ) : (r.map hF hproj).d n =
    (r.mapXIso hF hproj (n + 1)).hom ≫ F.map (r.d n) ≫
      (r.mapXIso hF hproj n).inv := by
  simp [d_def]

@[simp]
lemma map_aug : (r.map hF hproj).aug =
    (r.mapXIso hF hproj 0).hom ≫ F.map r.aug := by
  simp [aug_def]

/-- The complex of a mapped resolution is canonically the mapped complex. -/
def toChainComplexMapIso :
    (r.map hF hproj).toChainComplex ≅ (F.mapHomologicalComplex _).obj r.toChainComplex :=
  HomologicalComplex.Hom.isoOfComponents (r.mapXIso hF hproj) (by
    rintro _ n rfl
    simp)

@[simp] lemma toChainComplexMapIso_hom_f (n : ℕ) :
    (r.toChainComplexMapIso hF hproj).hom.f n = (r.mapXIso hF hproj n).hom := (rfl)

@[simp] lemma toChainComplexMapIso_inv_f (n : ℕ) :
    (r.toChainComplexMapIso hF hproj).inv.f n = (r.mapXIso hF hproj n).inv := (rfl)

end Map

/-! ### Existence from enough projectives -/

/-- Successively choose a projective presentation of the preceding kernel. -/
private noncomputable abbrev presentations (hE : E.EnoughProjectives) (Y : C) :
    ℕ → Σ Z : C, E.ProjectivePresentation Z :=
  Nat.rec ⟨Y, hE.projectivePresentation Y⟩
    (fun _ t => ⟨t.2.K, hE.projectivePresentation t.2.K⟩)

/-- Enough relative projectives supply an unbounded projective resolution of every object.
No ambient kernels or cokernels are used: the projective presentations contain their own
kernel-cokernel universal properties. -/
noncomputable def ofEnoughProjectives (hE : E.EnoughProjectives) (Y : C) :
    E.ProjectiveResolution Y where
  K n := (presentations hE Y n).1
  X n := (presentations hE Y n).2.P
  iso := Iso.refl Y
  ι n := (presentations hE Y n).2.i
  π n := (presentations hE Y n).2.p
  zero n := (presentations hE Y n).2.zero
  conflation n := (presentations hE Y n).2.conflation
  isProjective n := (presentations hE Y n).2.isProjective

/-- The existence construction starts with the object being resolved as its zeroth syzygy. -/
@[simp] lemma ofEnoughProjectives_K_zero (hE : E.EnoughProjectives) (Y : C) :
    (ofEnoughProjectives hE Y).K 0 = Y := (rfl)

end ProjectiveResolution

end ExactStructure

end TauCeti
