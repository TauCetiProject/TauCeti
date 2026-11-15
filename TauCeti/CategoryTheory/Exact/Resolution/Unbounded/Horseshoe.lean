/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Splitting
public import TauCeti.CategoryTheory.Exact.Resolution.Unbounded.Basic
public import TauCeti.CategoryTheory.Exact.Resolution.ConflationRow

/-!
# The unbounded projective horseshoe lemma

Given a conflation and prescribed relative projective resolutions of its outer terms, construct
a resolution of its middle term and augmentation-compatible chain maps which split in every
degree. No enough-projectives hypothesis or ambient kernels are needed: the prescribed outer
resolutions supply every projective used by the construction.

The successive syzygy conflations and linking blocks follow the negative-degree construction
of `TauCeti.ExactStructure.CompleteResolution.horseshoe`, using only projectives rather than
projective-injective objects. Transport along a conflation-exact functor preserving projectives
also transports the horseshoe; this includes internal grading shifts.

## References

* Theo Bühler, *Exact categories*, Section 12.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Lemma 2.2.8.
-/

public section

namespace TauCeti.ExactStructure.ProjectiveResolution

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (r₁ r₃ : E.ProjectiveResolution)

/-- Specialize the shared projective step to the prescribed outer resolutions. -/
private abbrev Block (n : ℕ) :=
  ConflationRow.ProjectiveStep (E := E) (ShortComplex.mk (r₁.ι n) (r₁.π n) (r₁.ι_π n))
    (ShortComplex.mk (r₃.ι n) (r₃.π n) (r₃.ι_π n))

variable {M : C} (f : r₁.Z 0 ⟶ M) (g : M ⟶ r₃.Z 0) (zero : f ≫ g = 0)
  (hS : E.Conflation (ShortComplex.mk f g zero))

/-- Iterate the syzygy conflations starting from the given conflation.
Reducibility lets the dependent `block` type identify successive choices. At degree zero the
row is exactly the supplied conflation, so its object and maps reduce to `M`, `f`, and `g`;
this also justifies the identity `iso` and the augmentation proofs in `horseshoe`. -/
@[reducible] private noncomputable def row :
    (n : ℕ) → ConflationRow E (r₁.Z n) (r₃.Z n)
  | 0 => ⟨M, f, g, zero, hS⟩
  | n + 1 => ((row n).nonempty_projectiveStep
      (r₁.conflation n) (r₃.conflation n) (r₃.projective n)).some.1

private noncomputable def block (n : ℕ) :
    Block r₁ r₃ n (row r₁ r₃ f g zero hS n) (row r₁ r₃ f g zero hS (n + 1)) :=
  ((row r₁ r₃ f g zero hS n).nonempty_projectiveStep
    (r₁.conflation n) (r₃.conflation n) (r₃.projective n)).some.2

/-- The middle resolution uses the actual biproducts of the prescribed terms.
Reducibility keeps these terms and the degree-zero row visible to the dependent chain maps
and the identity augmentation isomorphism below. -/
@[reducible] private noncomputable def middle : E.ProjectiveResolution where
  Z n := (row r₁ r₃ f g zero hS n).Z
  X n := r₁.X n ⊞ r₃.X n
  ι n := (block r₁ r₃ f g zero hS n).ι
  π n := (block r₁ r₃ f g zero hS n).π
  ι_π n := (block r₁ r₃ f g zero hS n).zero
  conflation n := (block r₁ r₃ f g zero hS n).conflation
  projective n := E.isProjective_biprod (r₁.projective n) (r₃.projective n)

private noncomputable def middleι : r₁.complex ⟶ (middle r₁ r₃ f g zero hS).complex where
  f _ := biprod.inl
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [complex_d, complex_d, d_def, d_def]
    -- The two adjacent blocks share the same syzygy row.
    rw [(block r₁ r₃ f g zero hS (j + 1)).inl_π_assoc,
      (block r₁ r₃ f g zero hS j).v_ι, Category.assoc]

private noncomputable def middleπ : (middle r₁ r₃ f g zero hS).complex ⟶ r₃.complex where
  f _ := biprod.snd
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [complex_d, complex_d, d_def, d_def]
    -- The two adjacent blocks share the same syzygy row.
    rw [Category.assoc, (block r₁ r₃ f g zero hS j).ι_snd]
    simpa only [Category.assoc] using
      ((block r₁ r₃ f g zero hS (j + 1)).π_w_assoc (r₃.ι j)).symm

variable {r₁ r₃ f g} in
/-- A projective horseshoe over `f` and `g`, with the prescribed outer resolutions.
The middle resolution resolves `M`, both chain maps respect the augmentations, and the
resulting short complex splits in each degree. -/
structure Horseshoe (f : r₁.Z 0 ⟶ M) (g : M ⟶ r₃.Z 0) where
  /-- The middle projective resolution. -/
  resolution : E.ProjectiveResolution
  /-- Its resolved object is the middle term of the original conflation. -/
  iso : resolution.Z 0 ≅ M
  /-- The injection of complexes. -/
  ι : r₁.complex ⟶ resolution.complex
  /-- The projection of complexes. -/
  π : resolution.complex ⟶ r₃.complex
  ι_π : ι ≫ π = 0
  ι_augmentation : ι.f 0 ≫ resolution.π 0 ≫ iso.hom = r₁.π 0 ≫ f
  π_augmentation : π.f 0 ≫ r₃.π 0 = resolution.π 0 ≫ iso.hom ≫ g
  /-- The short complex splits in every chain degree. -/
  split (n : ℕ) : Nonempty ((ShortComplex.mk ι π ι_π).map
    (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting

attribute [reassoc (attr := simp)] Horseshoe.ι_π Horseshoe.ι_augmentation
  Horseshoe.π_augmentation

/-- The unbounded projective horseshoe lemma in a Quillen exact category. -/
noncomputable def horseshoe : Horseshoe f g where
  resolution := middle r₁ r₃ f g zero hS
  iso := Iso.refl _
  ι := middleι r₁ r₃ f g zero hS
  π := middleπ r₁ r₃ f g zero hS
  ι_π := by ext n; simp [middleι, middleπ]
  ι_augmentation := by simpa [middleι] using (block r₁ r₃ f g zero hS 0).inl_π
  π_augmentation := by simpa [middleπ] using (block r₁ r₃ f g zero hS 0).π_w.symm
  -- Evaluation gives definitionally the standard biproduct short complex:
  -- `middle.X n` is the biproduct, and `middleι.f n`/`middleπ.f n` are its inclusion/projection.
  split n := ⟨ShortComplex.Splitting.ofHasBinaryBiproduct _ _⟩

namespace Horseshoe

variable {r₁ r₃ f g} (h : Horseshoe f g)

/-- Each middle term is the biproduct of the prescribed outer terms, via the chosen splitting. -/
noncomputable def termIsoBiprod (n : ℕ) :
    h.resolution.X n ≅ r₁.X n ⊞ r₃.X n :=
  (h.split n).some.isoBinaryBiproduct

/-- The termwise isomorphism sends the horseshoe injection to the left inclusion. -/
@[reassoc (attr := simp)]
theorem ι_f_termIsoBiprod_hom (n : ℕ) :
    h.ι.f n ≫ (h.termIsoBiprod n).hom = biprod.inl :=
  (h.split n).some.f_isoBinaryBiproduct_hom

/-- The right projection after the termwise isomorphism is the horseshoe projection. -/
@[reassoc (attr := simp)]
theorem termIsoBiprod_hom_snd (n : ℕ) :
    (h.termIsoBiprod n).hom ≫ biprod.snd = h.π.f n := by
  simp [termIsoBiprod]

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F) (hP : E.isProjective ≤ E'.isProjective.inverseImage F)

/-- Transport the prescribed horseshoe along a conflation-exact functor preserving projectives.
In particular the internal shift and its inverse transport a graded horseshoe. -/
-- Exposure is needed to type the dependent `iso` and chain-map characterizing lemmas below:
-- their domains involve the transported `resolution` field.
@[expose]
noncomputable def map : Horseshoe
    ((r₁.mapZIso hF hP 0).hom ≫ F.map f)
    (F.map g ≫ (r₃.mapZIso hF hP 0).inv) where
  resolution := h.resolution.map hF hP
  iso := h.resolution.mapZIso hF hP 0 ≪≫ F.mapIso h.iso
  ι := (r₁.mapComplexIso hF hP).hom ≫ (F.mapHomologicalComplex _).map h.ι ≫
    (h.resolution.mapComplexIso hF hP).inv
  π := (h.resolution.mapComplexIso hF hP).hom ≫ (F.mapHomologicalComplex _).map h.π ≫
    (r₃.mapComplexIso hF hP).inv
  ι_π := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc, h.ι_π]
    simp
  ι_augmentation := by
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mapComplexIso_hom_f, mapComplexIso_inv_f, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc, mapXIso_inv_comp_π_assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp, ← F.map_comp, h.ι_augmentation]
    simp
  π_augmentation := by
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mapComplexIso_hom_f, mapComplexIso_inv_f, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc, mapXIso_inv_comp_π]
    rw [← F.map_comp_assoc, h.π_augmentation]
    simp
  split n := by
    let sp := (h.split n).some.map F
    refine ⟨sp.ofIso (ShortComplex.isoMk (r₁.mapXIso hF hP n).symm
      (h.resolution.mapXIso hF hP n).symm (r₃.mapXIso hF hP n).symm ?_ ?_)⟩ <;> simp

/-- Transport retains the chosen middle resolution, rather than choosing a new horseshoe. -/
@[simp] theorem map_resolution : (h.map hF hP).resolution = h.resolution.map hF hP := (rfl)

/-- Transport retains the identification of the resolved middle object. -/
@[simp] theorem map_iso : (h.map hF hP).iso =
    h.resolution.mapZIso hF hP 0 ≪≫ F.mapIso h.iso := (rfl)

/-- The transported injection is the image of the original injection. -/
@[reassoc, simp]
theorem map_ι_comp_mapComplexIso_hom :
    (h.map hF hP).ι ≫ (h.resolution.mapComplexIso hF hP).hom =
      (r₁.mapComplexIso hF hP).hom ≫ (F.mapHomologicalComplex _).map h.ι := by
  simp [map]

/-- The transported projection is the image of the original projection. -/
@[reassoc (attr := simp)]
theorem map_π_comp_mapComplexIso_hom :
    (h.map hF hP).π ≫ (r₃.mapComplexIso hF hP).hom =
      (h.resolution.mapComplexIso hF hP).hom ≫ (F.mapHomologicalComplex _).map h.π := by
  simp [map]

end Horseshoe

end TauCeti.ExactStructure.ProjectiveResolution
