/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Complexes with zero differentials

A family of objects `E i` forms a homological complex `HomologicalComplex.graded c E` with zero
differentials. It has homology in every degree, and each of its terms consists of cycles
(Mathlib's `HomologicalComplex.iCyclesIso`). Hence a family of morphisms `e i : E i ⟶ K.cycles i`
into the cycles of a complex `K` defines a morphism of complexes `K.fromGraded e`, which induces
`e i` on cycles (`HomologicalComplex.iCyclesIso_inv_cyclesMap_fromGraded`). It is surjective on
homology when every `e i` is an epimorphism (`HomologicalComplex.epi_homologyMap_fromGraded`).
Such morphisms are the first step in the construction of resolutions by attaching cells.
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

end HomologicalComplex
