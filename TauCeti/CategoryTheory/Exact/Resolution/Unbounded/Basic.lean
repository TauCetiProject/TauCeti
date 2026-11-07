/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Projective
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Additive

/-!
# Unbounded projective resolutions in exact categories

A projective resolution relative to an exact structure is a sequence of conflations
`Z (n + 1) ↪ X n ↠ Z n` with relatively projective middle terms. Its augmentation resolves
`Z 0`. Splicing the conflations gives an augmented chain complex, without requiring the
ambient category to have arbitrary kernels or cokernels.

Enough relative projectives supply such a resolution of every object. Conflation-exact
functors preserving relative projectives transport the entire resolution, including its
syzygies and augmentation. In particular this applies to the internal shift of a graded exact
category, not just to an ungraded category.

The syzygies are retained as data because exactness in a Quillen exact category requires
specified admissible factorizations of the differentials. They also permit the horseshoe
construction to be iterated without making ambient kernel choices.

## References

* Theo Bühler, *Exact categories*, Sections 11--12, for relative projective resolutions.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.2.

The presentation and splicing follow the conventions of
`TauCeti.ExactStructure.CompleteResolution`; no injectivity or Frobenius hypothesis is needed.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure

/-- An unbounded projective resolution relative to `E`, resolving `Z 0`: its differentials
factor through the conflations `Z (n + 1) ↪ X n ↠ Z n`. -/
structure ProjectiveResolution (E : ExactStructure C) where
  /-- The successive syzygies, starting with the resolved object. -/
  Z : ℕ → C
  /-- The resolving projective objects. -/
  X : ℕ → C
  /-- The admissible kernel of the deflation from the resolving term. -/
  ι (n : ℕ) : Z (n + 1) ⟶ X n
  /-- The admissible epimorphism onto the preceding syzygy. -/
  π (n : ℕ) : X n ⟶ Z n
  ι_π (n : ℕ) : ι n ≫ π n = 0
  /-- Each step is a distinguished conflation. -/
  conflation (n : ℕ) : E.Conflation (ShortComplex.mk (ι n) (π n) (ι_π n))
  /-- Each resolving term is relatively projective. -/
  projective (n : ℕ) : E.isProjective (X n)

namespace ProjectiveResolution

variable {E : ExactStructure C} (r : E.ProjectiveResolution)

attribute [reassoc (attr := simp)] ι_π

/-- The kernel map in each step is an inflation. -/
theorem isInflation_ι (n : ℕ) : E.IsInflation (r.ι n) :=
  E.isInflation_f (r.conflation n)

/-- The quotient map in each step is a deflation. -/
theorem isDeflation_π (n : ℕ) : E.IsDeflation (r.π n) :=
  E.isDeflation_g (r.conflation n)

/-- The spliced differential of a relative projective resolution. -/
def d (n : ℕ) : r.X (n + 1) ⟶ r.X n := r.π (n + 1) ≫ r.ι n

theorem d_def (n : ℕ) : r.d n = r.π (n + 1) ≫ r.ι n := (rfl)

/-- Each syzygy deflation kills the preceding differential, including the augmentation. -/
@[reassoc (attr := simp)]
theorem d_comp_π (n : ℕ) : r.d n ≫ r.π n = 0 := by simp [d_def]

/-- Consecutive differentials compose to zero. -/
@[reassoc (attr := simp)]
theorem d_comp_d (n : ℕ) : r.d (n + 1) ≫ r.d n = 0 := by simp [d_def]

/-- The chain complex obtained by splicing the conflations. -/
noncomputable abbrev complex : ChainComplex C ℕ :=
  ChainComplex.of r.X r.d r.d_comp_d

/-- Consecutive differentials in the chain complex are the spliced differentials. -/
theorem complex_d (n : ℕ) : r.complex.d (n + 1) n = r.d n :=
  ChainComplex.of_d _ _ n

/-- The augmentation from the spliced complex to the object in degree zero. -/
noncomputable def augmentation : r.complex ⟶ (ChainComplex.single₀ C).obj (r.Z 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨r.π 0, by
    rw [complex_d, d_comp_π]⟩

/-- The augmentation in degree zero is the first deflation. -/
@[simp]
theorem augmentation_f_zero : r.augmentation.f 0 = r.π 0 :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

section Map

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F)
  (hP : E.isProjective ≤ E'.isProjective.inverseImage F)

/-- Transport a resolution along a conflation-exact functor preserving relative projectives.
This does not assert functorial choices of resolutions. -/
def map : E'.ProjectiveResolution where
  Z n := F.obj (r.Z n)
  X n := F.obj (r.X n)
  ι n := F.map (r.ι n)
  π n := F.map (r.π n)
  ι_π n := by rw [← F.map_comp, r.ι_π, F.map_zero]
  conflation n := hF.map_conflation (r.conflation n)
  projective n := (E'.isProjective.prop_inverseImage_iff F _).mp (hP _ (r.projective n))

@[simp] theorem map_Z (n : ℕ) : (r.map hF hP).Z n = F.obj (r.Z n) := (rfl)

@[simp] theorem map_X (n : ℕ) : (r.map hF hP).X n = F.obj (r.X n) := (rfl)

/-- The syzygies of a transported resolution are the images of the original syzygies. -/
def mapZIso (n : ℕ) : (r.map hF hP).Z n ≅ F.obj (r.Z n) := Iso.refl _

/-- The projective terms of a transported resolution are the images of the original terms. -/
def mapXIso (n : ℕ) : (r.map hF hP).X n ≅ F.obj (r.X n) := Iso.refl _

/-- The transported spliced complex is canonically the image of the original complex. -/
noncomputable def mapComplexIso : (r.map hF hP).complex ≅
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj r.complex :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl : j + 1 = i := hij
    simp [d_def, map])

@[simp] theorem mapComplexIso_hom_f (n : ℕ) :
    (r.mapComplexIso hF hP).hom.f n = (r.mapXIso hF hP n).hom := (rfl)

@[simp] theorem mapComplexIso_inv_f (n : ℕ) :
    (r.mapComplexIso hF hP).inv.f n = (r.mapXIso hF hP n).inv := (rfl)

/-- Transport respects every deflation, including the augmentation at `n = 0`. -/
@[reassoc (attr := simp)]
theorem mapXIso_hom_comp_π (n : ℕ) :
    (r.mapXIso hF hP n).hom ≫ F.map (r.π n) =
      (r.map hF hP).π n ≫ (r.mapZIso hF hP n).hom := by
  simp [mapXIso, mapZIso, map]

@[reassoc (attr := simp)]
theorem mapXIso_inv_comp_π (n : ℕ) :
    (r.mapXIso hF hP n).inv ≫ (r.map hF hP).π n =
      F.map (r.π n) ≫ (r.mapZIso hF hP n).inv := by
  apply (cancel_mono (r.mapZIso hF hP n).hom).1
  rw [Category.assoc, ← mapXIso_hom_comp_π, Iso.inv_hom_id_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Transport respects the admissible factorizations of the differentials. -/
@[reassoc (attr := simp)]
theorem map_ι_comp_mapXIso_hom (n : ℕ) :
    (r.map hF hP).ι n ≫ (r.mapXIso hF hP n).hom =
      (r.mapZIso hF hP (n + 1)).hom ≫ F.map (r.ι n) := by
  simp [mapXIso, mapZIso, map]

end Map

end ProjectiveResolution

namespace EnoughProjectives

variable {E : ExactStructure C} (h : E.EnoughProjectives) (M : C)

/-- The syzygies obtained by repeatedly taking a relative projective presentation. -/
private noncomputable def resolutionSyzygy : ℕ → C
  | 0 => M
  | n + 1 => (h.projectivePresentation (resolutionSyzygy n)).K

/-- Enough relative projectives give an unbounded projective resolution of every object.
Its resolved object is identified with the original object by `projectiveResolutionIso`. -/
noncomputable def projectiveResolution : E.ProjectiveResolution where
  Z := h.resolutionSyzygy M
  X n := (h.projectivePresentation (h.resolutionSyzygy M n)).P
  ι n := (h.projectivePresentation (h.resolutionSyzygy M n)).i
  π n := (h.projectivePresentation (h.resolutionSyzygy M n)).p
  ι_π n := (h.projectivePresentation (h.resolutionSyzygy M n)).zero
  conflation n := (h.projectivePresentation (h.resolutionSyzygy M n)).conflation
  projective n := (h.projectivePresentation (h.resolutionSyzygy M n)).isProjective

/-- The constructed resolution resolves the specified object. -/
noncomputable def projectiveResolutionIso : (h.projectiveResolution M).Z 0 ≅ M :=
  Iso.refl _

end EnoughProjectives

end ExactStructure

end TauCeti
