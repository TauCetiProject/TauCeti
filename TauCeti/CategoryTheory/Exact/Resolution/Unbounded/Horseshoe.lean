/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution.Unbounded.Basic

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

/-- A conflation of the prescribed outer syzygies. -/
private structure Row (n : ℕ) where
  Z : C
  v : r₁.Z n ⟶ Z
  w : Z ⟶ r₃.Z n
  zero : v ≫ w = 0
  conflation : E.Conflation (ShortComplex.mk v w zero)

/-- One application of the projective horseshoe, retaining all commuting squares. -/
private structure Block (n : ℕ) (R : Row r₁ r₃ n) (R' : Row r₁ r₃ (n + 1)) where
  ι : R'.Z ⟶ r₁.X n ⊞ r₃.X n
  π : r₁.X n ⊞ r₃.X n ⟶ R.Z
  zero : ι ≫ π = 0
  conflation : E.Conflation (ShortComplex.mk ι π zero)
  inl_π : biprod.inl ≫ π = r₁.π n ≫ R.v
  π_w : π ≫ R.w = biprod.snd ≫ r₃.π n
  v_ι : R'.v ≫ ι = r₁.ι n ≫ biprod.inl
  ι_snd : ι ≫ biprod.snd = R'.w ≫ r₃.ι n

private theorem nonempty_step {n : ℕ} (R : Row r₁ r₃ n) :
    Nonempty (Σ R' : Row r₁ r₃ (n + 1), Block r₁ r₃ n R R') := by
  obtain ⟨K, u, a, hua, v, w, hvw, hu, hv, ha₁, ha₃, hu₁, hu₃⟩ :=
    E.exists_conflation_biprod_of_conflation_of_projective R.conflation
      (r₁.conflation n) (r₃.conflation n) (r₃.projective n)
  exact ⟨⟨⟨K, v, w, hvw, hv⟩, ⟨u, a, hua, hu, ha₁, ha₃, hu₁, hu₃⟩⟩⟩

variable {M : C} (f : r₁.Z 0 ⟶ M) (g : M ⟶ r₃.Z 0) (zero : f ≫ g = 0)
  (hS : E.Conflation (ShortComplex.mk f g zero))

/-- Iterate the syzygy conflations starting from the given conflation. -/
@[reducible] private noncomputable def row : (n : ℕ) → Row r₁ r₃ n
  | 0 => ⟨M, f, g, zero, hS⟩
  | n + 1 => (nonempty_step r₁ r₃ (row n)).some.1

private noncomputable def block (n : ℕ) :
    Block r₁ r₃ n (row r₁ r₃ f g zero hS n) (row r₁ r₃ f g zero hS (n + 1)) :=
  (nonempty_step r₁ r₃ (row r₁ r₃ f g zero hS n)).some.2

/-- The middle resolution uses the actual biproducts of the prescribed terms. -/
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
    rw [← Category.assoc, (block r₁ r₃ f g zero hS (j + 1)).inl_π,
      Category.assoc, (block r₁ r₃ f g zero hS j).v_ι, Category.assoc]

private noncomputable def middleπ : (middle r₁ r₃ f g zero hS).complex ⟶ r₃.complex where
  f _ := biprod.snd
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [complex_d, complex_d, d_def, d_def]
    -- The two adjacent blocks share the same syzygy row.
    rw [Category.assoc, (block r₁ r₃ f g zero hS j).ι_snd]
    simpa only [Category.assoc] using congrArg (fun t => t ≫ r₃.ι j)
      (block r₁ r₃ f g zero hS (j + 1)).π_w.symm

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
  split n := ⟨ShortComplex.Splitting.ofHasBinaryBiproduct _ _⟩

namespace Horseshoe

variable {r₁ r₃ f g} (h : Horseshoe f g)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F) (hP : E.isProjective ≤ E'.isProjective.inverseImage F)

/-- Transport the prescribed horseshoe along a conflation-exact functor preserving projectives.
In particular the internal shift and its inverse transport a graded horseshoe. -/
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

/-- The middle complex of the transported horseshoe is the image of the original middle complex. -/
noncomputable def mapResolutionComplexIso : (h.map hF hP).resolution.complex ≅
    (F.mapHomologicalComplex _).obj h.resolution.complex :=
  h.resolution.mapComplexIso hF hP

/-- The transported injection is the image of the original injection. -/
@[reassoc (attr := simp)]
theorem map_ι_comp_mapResolutionComplexIso_hom :
    (h.map hF hP).ι ≫ (h.mapResolutionComplexIso hF hP).hom =
      (r₁.mapComplexIso hF hP).hom ≫ (F.mapHomologicalComplex _).map h.ι := by
  simp [map, mapResolutionComplexIso]

/-- The transported projection is the image of the original projection. -/
@[reassoc (attr := simp)]
theorem map_π_comp_mapComplexIso_hom :
    (h.map hF hP).π ≫ (r₃.mapComplexIso hF hP).hom =
      (h.mapResolutionComplexIso hF hP).hom ≫ (F.mapHomologicalComplex _).map h.π := by
  simp [map, mapResolutionComplexIso]

end Horseshoe

end TauCeti.ExactStructure.ProjectiveResolution
