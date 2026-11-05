/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Complexes with zero differentials

A family of objects `E i` forms a homological complex `HomologicalComplex.graded c E` with zero
differentials. It has homology in every degree, and each of its terms consists of cycles
(Mathlib's `HomologicalComplex.iCyclesIso`). Hence a family of morphisms `e i : E i ⟶ K.cycles i`
into the cycles of a complex `K` defines a morphism of complexes `K.fromGraded e`, which induces
`e i` on cycles (`HomologicalComplex.iCyclesIso_inv_cyclesMap_fromGraded`). It is surjective on
homology when every `e i` is an epimorphism (`HomologicalComplex.epi_homologyMap_fromGraded`), and
a quasi-isomorphism when every `e i ≫ K.homologyπ i` is an isomorphism
(`HomologicalComplex.quasiIso_fromGraded`). Such morphisms are the first step in the
construction of resolutions by attaching cells.

More generally, the homology of any complex in a degree where both differentials vanish is the
term in that degree (`HomologicalComplex.XIsoHomologyOfDEqZero`), so it is projective when that
term is (`HomologicalComplex.projective_homology_of_d_eq_zero`).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] (c : ComplexShape ι)

/-- The homological complex with terms `E i` and zero differentials. -/
@[simps]
abbrev graded (E : ι → C) : HomologicalComplex C c where
  X := E
  d _ _ := 0

/-- A complex with zero differentials has homology in every degree. -/
instance hasHomology_graded (E : ι → C) (i : ι) : (graded c E).HasHomology i :=
  ShortComplex.hasHomology_of_zeros _ _ _

variable {c}

/-- If the differentials into and out of degree `i` vanish, the term in degree `i` is isomorphic
to the homology in degree `i`: every element is a cycle, and none but zero is a boundary. -/
def XIsoHomologyOfDEqZero (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    (h₁ : K.d (c.prev i) i = 0) (h₂ : K.d i (c.next i) = 0) : K.X i ≅ K.homology i :=
  (K.iCyclesIso i (c.next i) rfl h₂).symm ≪≫ K.isoHomologyπ (c.prev i) i rfl h₁

/-- The isomorphism `K.XIsoHomologyOfDEqZero i h₁ h₂` sends a term to the class of the
corresponding cycle. -/
@[reassoc, simp]
lemma XIsoHomologyOfDEqZero_hom (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    (h₁ : K.d (c.prev i) i = 0) (h₂ : K.d i (c.next i) = 0) :
    (K.XIsoHomologyOfDEqZero i h₁ h₂).hom = (K.iCyclesIso i (c.next i) rfl h₂).inv ≫
      K.homologyπ i := by
  simp [XIsoHomologyOfDEqZero]

/-- The inverse of `K.XIsoHomologyOfDEqZero i h₁ h₂` sends a homology class to its unique
representing cycle, viewed as a term. -/
@[reassoc, simp]
lemma XIsoHomologyOfDEqZero_inv (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    (h₁ : K.d (c.prev i) i = 0) (h₂ : K.d i (c.next i) = 0) :
    (K.XIsoHomologyOfDEqZero i h₁ h₂).inv = (K.isoHomologyπ (c.prev i) i rfl h₁).inv ≫
      K.iCycles i := by
  simp [XIsoHomologyOfDEqZero]

/-- If the differentials into and out of degree `i` vanish, the homology in degree `i` is the
term in degree `i`, so it is projective when that term is. -/
lemma projective_homology_of_d_eq_zero (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    [Projective (K.X i)] (h₁ : K.d (c.prev i) i = 0) (h₂ : K.d i (c.next i) = 0) :
    Projective (K.homology i) :=
  Projective.of_iso (K.XIsoHomologyOfDEqZero i h₁ h₂) inferInstance

variable (K : HomologicalComplex C c) [∀ i, K.HasHomology i] {E : ι → C}
  (e : ∀ i, E i ⟶ K.cycles i)

/-- The morphism to `K` from the complex with zero differentials on a family of objects mapping
to the cycles of `K`. -/
@[simps]
abbrev fromGraded : graded c E ⟶ K where
  f i := e i ≫ K.iCycles i
  comm' _ _ _ := by simp

/-- On cycles, the morphism `K.fromGraded e` is given by `e`. -/
@[reassoc]
lemma iCyclesIso_inv_cyclesMap_fromGraded (i : ι) :
    ((graded c E).iCyclesIso i (c.next i) rfl rfl).inv ≫ cyclesMap (K.fromGraded e) i = e i := by
  simp [← cancel_mono (K.iCycles i)]

/-- If every `e i` is an epimorphism, then `K.fromGraded e` is surjective on homology. -/
lemma epi_homologyMap_fromGraded [∀ i, Epi (e i)] (i : ι) :
    Epi (homologyMap (K.fromGraded e) i) := by
  have : Epi ((((graded c E).iCyclesIso i (c.next i) rfl rfl).inv ≫ (graded c E).homologyπ i) ≫
      homologyMap (K.fromGraded e) i) := by
    rw [Category.assoc, homologyπ_naturality, reassoc_of% iCyclesIso_inv_cyclesMap_fromGraded]
    infer_instance
  exact epi_of_epi (((graded c E).iCyclesIso i (c.next i) rfl rfl).inv ≫
    (graded c E).homologyπ i) _

/-- If every `e i ≫ K.homologyπ i` is an isomorphism, for instance when each `e i` is a section
of `K.homologyπ i`, then `K.fromGraded e` is a quasi-isomorphism. -/
lemma quasiIso_fromGraded (he : ∀ i, IsIso (e i ≫ K.homologyπ i)) :
    QuasiIso (K.fromGraded e) where
  quasiIsoAt i := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have := (graded c E).isIso_homologyπ (c.prev i) i rfl rfl
    have : IsIso ((((graded c E).iCyclesIso i (c.next i) rfl rfl).inv ≫
        (graded c E).homologyπ i) ≫ homologyMap (K.fromGraded e) i) := by
      rw [Category.assoc, homologyπ_naturality, reassoc_of% iCyclesIso_inv_cyclesMap_fromGraded]
      exact he i
    exact IsIso.of_isIso_comp_left (((graded c E).iCyclesIso i (c.next i) rfl rfl).inv ≫
      (graded c E).homologyπ i) _

end HomologicalComplex
