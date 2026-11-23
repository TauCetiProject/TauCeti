/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Boundary
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.Algebra.Homology.Boundaries

/-!
# Restriction along surjective embeddings of complex shapes

An embedding of complex shapes `e : c.Embedding c'` which reflects the relations
(`ComplexShape.Embedding.IsRelIff`) and whose index map `e.f` is surjective identifies the two
shapes: it carries previous and next indices of `c` to those of `c'`
(`ComplexShape.Embedding.prev_f_of_surjective`, `ComplexShape.Embedding.next_f_of_surjective`).
So the restriction of a complex along `e` has, at every index `j`, the cycles and homology of the
complex at `e.f j` (`HomologicalComplex.restrictionCyclesIsoOfSurjective`,
`HomologicalComplex.restrictionHomologyIsoOfSurjective`), naturally in the complex
(`HomologicalComplex.homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom`). This
is Mathlib's `HomologicalComplex.restrictionHomologyIso`, whose compatibility hypotheses on
previous and next indices then hold at every index. Consequently, projectivity of cycles or
homology and splitting of cycle inclusions transport across the restriction
(`HomologicalComplex.projective_restriction_cycles_of_surjective`,
`HomologicalComplex.projective_restriction_homology_of_surjective`,
`HomologicalComplex.isSplitMono_restriction_iCycles_of_surjective`). Such embeddings are given by
bijections of indices compatible with the relations (`ComplexShape.Embedding.mk'`); they are used
to read a complex, or the pages of a spectral sequence, in other coordinates.

## Main definitions

* `HomologicalComplex.restrictionCyclesIsoOfSurjective`: the cycles of a restriction along a
  surjective embedding of complex shapes.
* `HomologicalComplex.restrictionHomologyIsoOfSurjective`: the homology of a restriction along a
  surjective embedding of complex shapes.
-/

public section

open CategoryTheory Limits

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  [e.IsRelIff]

/-- An embedding of complex shapes which is surjective and reflects the relations carries previous
indices to previous indices. -/
lemma prev_f_of_surjective (he : Function.Surjective e.f) (j : ι) :
    c'.prev (e.f j) = e.f (c.prev j) :=
  have : e.IsTruncLE := { mem_prev := fun {i' _} _ ↦ he i' }
  e.prev_f rfl

/-- An embedding of complex shapes which is surjective and reflects the relations carries next
indices to next indices. -/
lemma next_f_of_surjective (he : Function.Surjective e.f) (j : ι) :
    c'.next (e.f j) = e.f (c.next j) :=
  have : e.IsTruncGE := { mem_next := fun {_ k'} _ ↦ he k' }
  e.next_f rfl

end ComplexShape.Embedding

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι ι' : Type*} {c : ComplexShape ι}
  {c' : ComplexShape ι'} (e : c.Embedding c') [e.IsRelIff] (he : Function.Surjective e.f)

/-- The cycles of the restriction of a complex along a surjective embedding of complex shapes
which reflects the relations are the cycles of the complex at the corresponding index `j'`, the
image of `j`. -/
noncomputable def restrictionCyclesIsoOfSurjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restriction e).cycles j ≅ K.cycles j' :=
  K.restrictionCyclesIso e j _ rfl hj rfl (by rw [← hj, e.next_f_of_surjective he j])

@[reassoc (attr := simp)]
lemma restrictionCyclesIsoOfSurjective_hom_iCycles (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restrictionCyclesIsoOfSurjective e he j j' hj).hom ≫ K.iCycles j' =
      (K.restriction e).iCycles j ≫ (K.restrictionXIso e hj).hom :=
  K.restrictionCyclesIso_hom_iCycles e j _ rfl hj rfl _

@[reassoc (attr := simp)]
lemma restrictionCyclesIsoOfSurjective_inv_iCycles (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restrictionCyclesIsoOfSurjective e he j j' hj).inv ≫ (K.restriction e).iCycles j =
      K.iCycles j' ≫ (K.restrictionXIso e hj).inv :=
  K.restrictionCyclesIso_inv_iCycles e j _ rfl hj rfl _

/-- The homology of the restriction of a complex along a surjective embedding of complex shapes
which reflects the relations is the homology of the complex at the corresponding index `j'`, the
image of `j`. -/
noncomputable def restrictionHomologyIsoOfSurjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restriction e).homology j ≅ K.homology j' :=
  K.restrictionHomologyIso e _ j _ rfl rfl rfl hj rfl
    (by rw [← hj, e.prev_f_of_surjective he j]) (by rw [← hj, e.next_f_of_surjective he j])

@[reassoc (attr := simp)]
lemma homologyπ_restrictionHomologyIsoOfSurjective_hom (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restriction e).homologyπ j ≫ (K.restrictionHomologyIsoOfSurjective e he j j' hj).hom =
      (K.restrictionCyclesIsoOfSurjective e he j j' hj).hom ≫ K.homologyπ j' :=
  K.homologyπ_restrictionHomologyIso_hom e _ j _ rfl rfl rfl hj rfl _ _

@[reassoc]
lemma homologyπ_restrictionHomologyIsoOfSurjective_inv (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    K.homologyπ j' ≫ (K.restrictionHomologyIsoOfSurjective e he j j' hj).inv =
      (K.restrictionCyclesIsoOfSurjective e he j j' hj).inv ≫ (K.restriction e).homologyπ j :=
  K.homologyπ_restrictionHomologyIso_inv e _ j _ rfl rfl rfl hj rfl _ _

/-- The comparison `restrictionHomologyIsoOfSurjective` is natural in the complex. -/
@[reassoc (attr := simp)]
lemma homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom
    {K L : HomologicalComplex C c'} (φ : K ⟶ L) (j : ι) (j' : ι') (hj : e.f j = j')
    [K.HasHomology j'] [L.HasHomology j'] [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    homologyMap (restrictionMap φ e) j ≫ (L.restrictionHomologyIsoOfSurjective e he j j' hj).hom =
      (K.restrictionHomologyIsoOfSurjective e he j j' hj).hom ≫ homologyMap φ j' := by
  subst hj
  have hcycles : cyclesMap (restrictionMap φ e) j ≫
      (L.restrictionCyclesIsoOfSurjective e he j (e.f j) rfl).hom =
      (K.restrictionCyclesIsoOfSurjective e he j (e.f j) rfl).hom ≫ cyclesMap φ (e.f j) := by
    rw [← cancel_mono (L.iCycles (e.f j))]
    simp [restrictionXIso]
  rw [← cancel_epi ((K.restriction e).homologyπ j)]
  simp only [homologyπ_naturality_assoc, homologyπ_restrictionHomologyIsoOfSurjective_hom,
    homologyπ_restrictionHomologyIsoOfSurjective_hom_assoc, homologyπ_naturality]
  rw [reassoc_of% hcycles]

/-- The boundaries of `K` in degree `j' = e.f j`, read on the restriction `K.restriction e`: the
corestriction of the differential `K.X i' ⟶ B_j'` of `K` is that of `K.restriction e` followed by
the identification of the boundaries. -/
@[reassoc]
lemma restrictionXIso_inv_comp_toBoundaries_kernelMap (K : HomologicalComplex C c') (i j : ι)
    (i' j' : ι') (hi : e.f i = i') (hj : e.f j = j') [K.HasHomology j']
    [(K.restriction e).HasHomology j] [HasKernel (K.homologyπ j')]
    [HasKernel ((K.restriction e).homologyπ j)] :
    (K.restrictionXIso e hi).inv ≫ (K.restriction e).toBoundaries i j ≫
        kernel.map _ _ (K.restrictionCyclesIsoOfSurjective e he j j' hj).hom
          (K.restrictionHomologyIsoOfSurjective e he j j' hj).hom
          (K.homologyπ_restrictionHomologyIsoOfSurjective_hom e he j j' hj) =
      K.toBoundaries i' j' := by
  rw [← cancel_mono (kernel.ι _), ← cancel_mono (K.iCycles j')]
  simp [-restriction_d, restriction_d_eq K e hi hj]

include he in
/-- The cycles of a restriction along a surjective embedding reflecting relations inherit
projectivity from the corresponding cycles of `K`. -/
lemma projective_restriction_cycles_of_surjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j]
    [Projective (K.cycles j')] : Projective ((K.restriction e).cycles j) :=
  Projective.of_iso (K.restrictionCyclesIsoOfSurjective e he j j' hj).symm inferInstance

include he in
/-- The homology of a restriction along a surjective embedding reflecting relations inherit
projectivity from the corresponding homology of `K`. -/
lemma projective_restriction_homology_of_surjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j]
    [Projective (K.homology j')] : Projective ((K.restriction e).homology j) :=
  Projective.of_iso (K.restrictionHomologyIsoOfSurjective e he j j' hj).symm inferInstance

include he in
/-- A split cycle inclusion of `K` restricts to a split cycle inclusion along a surjective
embedding reflecting relations. -/
lemma isSplitMono_restriction_iCycles_of_surjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j]
    [IsSplitMono (K.iCycles j')] : IsSplitMono ((K.restriction e).iCycles j) := by
  have hfac : (K.restriction e).iCycles j =
      (K.restrictionCyclesIsoOfSurjective e he j j' hj).hom ≫ K.iCycles j' ≫
        (K.restrictionXIso e hj).inv := by
    rw [← cancel_mono (K.restrictionXIso e hj).hom, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, restrictionCyclesIsoOfSurjective_hom_iCycles]
  rw [hfac]
  infer_instance

end HomologicalComplex
