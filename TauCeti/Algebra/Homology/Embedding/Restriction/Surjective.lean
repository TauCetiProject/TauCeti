/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Boundary
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Restriction along surjective embeddings of complex shapes

An embedding of complex shapes `e : c.Embedding c'` which reflects the relations
(`ComplexShape.Embedding.IsRelIff`) and whose index map `e.f` is surjective identifies the two
shapes: it carries previous and next indices of `c` to those of `c'`
(`ComplexShape.Embedding.prev_f_of_surjective`, `ComplexShape.Embedding.next_f_of_surjective`).
So the restriction of a complex along `e` has, at every index `j`, the cycles and homology of the
complex at `e.f j` (`HomologicalComplex.restrictionCyclesIsoOfSurjective`,
`HomologicalComplex.restrictionHomologyIsoOfSurjective`), naturally in the complex
(`HomologicalComplex.cyclesMap_restrictionMap_restrictionCyclesIsoOfSurjective_hom`,
`HomologicalComplex.homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom`) and
compatible with `homologyπ` (`HomologicalComplex.homologyπ_restrictionHomologyIsoOfSurjective_hom`,
`HomologicalComplex.homologyπ_restrictionHomologyIsoOfSurjective_inv`). This packages Mathlib's
`HomologicalComplex.restrictionCyclesIso` and `HomologicalComplex.restrictionHomologyIso`, whose
compatibility hypotheses on previous and next indices then hold at every index. Consequently,
projectivity of cycles and homology and split-monomorphism status of cycle inclusions transfer
across restriction along `e` (`HomologicalComplex.projective_cycles_restriction_iff_of_surjective`,
`HomologicalComplex.projective_homology_restriction_iff_of_surjective`,
`HomologicalComplex.isSplitMono_iCycles_restriction_iff_of_surjective`). Such embeddings are given
by bijections of indices compatible with the relations (`ComplexShape.Embedding.mk'`); they are
used to read a complex, or the pages of a spectral sequence, in other coordinates.

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
  K.restrictionCyclesIso e j (c.next j) rfl hj rfl (by rw [← hj, e.next_f_of_surjective he j])

/-- The forward map of `restrictionCyclesIsoOfSurjective` commutes with `iCycles`. -/
@[reassoc (attr := simp)]
lemma restrictionCyclesIsoOfSurjective_hom_iCycles (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restrictionCyclesIsoOfSurjective e he j j' hj).hom ≫ K.iCycles j' =
      (K.restriction e).iCycles j ≫ (K.restrictionXIso e hj).hom :=
  K.restrictionCyclesIso_hom_iCycles e j (c.next j) rfl hj rfl
    (by rw [← hj, e.next_f_of_surjective he j])

/-- The inverse map of `restrictionCyclesIsoOfSurjective` commutes with `iCycles`. -/
@[reassoc (attr := simp)]
lemma restrictionCyclesIsoOfSurjective_inv_iCycles (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restrictionCyclesIsoOfSurjective e he j j' hj).inv ≫ (K.restriction e).iCycles j =
      K.iCycles j' ≫ (K.restrictionXIso e hj).inv :=
  K.restrictionCyclesIso_inv_iCycles e j (c.next j) rfl hj rfl
    (by rw [← hj, e.next_f_of_surjective he j])

/-- The comparison `restrictionCyclesIsoOfSurjective` is natural in the complex. -/
@[reassoc (attr := simp)]
lemma cyclesMap_restrictionMap_restrictionCyclesIsoOfSurjective_hom
    {K L : HomologicalComplex C c'} (φ : K ⟶ L) (j : ι) (j' : ι') (hj : e.f j = j')
    [K.HasHomology j'] [L.HasHomology j'] [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    cyclesMap (restrictionMap φ e) j ≫ (L.restrictionCyclesIsoOfSurjective e he j j' hj).hom =
      (K.restrictionCyclesIsoOfSurjective e he j j' hj).hom ≫ cyclesMap φ j' := by
  subst hj
  rw [← cancel_mono (L.iCycles (e.f j))]
  simp [restrictionXIso]

/-- The homology of the restriction of a complex along a surjective embedding of complex shapes
which reflects the relations is the homology of the complex at the corresponding index `j'`, the
image of `j`. -/
noncomputable def restrictionHomologyIsoOfSurjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restriction e).homology j ≅ K.homology j' :=
  K.restrictionHomologyIso e _ j _ rfl rfl rfl hj rfl
    (by rw [← hj, e.prev_f_of_surjective he j]) (by rw [← hj, e.next_f_of_surjective he j])

/-- The forward map of `restrictionHomologyIsoOfSurjective` commutes with `homologyπ`. -/
@[reassoc (attr := simp)]
lemma homologyπ_restrictionHomologyIsoOfSurjective_hom (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restriction e).homologyπ j ≫ (K.restrictionHomologyIsoOfSurjective e he j j' hj).hom =
      (K.restrictionCyclesIsoOfSurjective e he j j' hj).hom ≫ K.homologyπ j' :=
  K.homologyπ_restrictionHomologyIso_hom e _ j _ rfl rfl rfl hj rfl
    (by rw [← hj, e.prev_f_of_surjective he j]) (by rw [← hj, e.next_f_of_surjective he j])

/-- The inverse map of `restrictionHomologyIsoOfSurjective` commutes with `homologyπ`. -/
@[reassoc]
lemma homologyπ_restrictionHomologyIsoOfSurjective_inv (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    K.homologyπ j' ≫ (K.restrictionHomologyIsoOfSurjective e he j j' hj).inv =
      (K.restrictionCyclesIsoOfSurjective e he j j' hj).inv ≫ (K.restriction e).homologyπ j :=
  K.homologyπ_restrictionHomologyIso_inv e _ j _ rfl rfl rfl hj rfl
    (by rw [← hj, e.prev_f_of_surjective he j]) (by rw [← hj, e.next_f_of_surjective he j])

/-- The comparison `restrictionHomologyIsoOfSurjective` is natural in the complex. -/
@[reassoc (attr := simp)]
lemma homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom
    {K L : HomologicalComplex C c'} (φ : K ⟶ L) (j : ι) (j' : ι') (hj : e.f j = j')
    [K.HasHomology j'] [L.HasHomology j'] [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    homologyMap (restrictionMap φ e) j ≫ (L.restrictionHomologyIsoOfSurjective e he j j' hj).hom =
      (K.restrictionHomologyIsoOfSurjective e he j j' hj).hom ≫ homologyMap φ j' := by
  rw [← cancel_epi ((K.restriction e).homologyπ j), homologyπ_naturality_assoc,
    homologyπ_restrictionHomologyIsoOfSurjective_hom,
    homologyπ_restrictionHomologyIsoOfSurjective_hom_assoc, homologyπ_naturality,
    cyclesMap_restrictionMap_restrictionCyclesIsoOfSurjective_hom_assoc]

/-- The inverse comparison of `restrictionHomologyIsoOfSurjective` is natural in the complex. -/
@[reassoc]
lemma homologyMap_restrictionHomologyIsoOfSurjective_inv
    {K L : HomologicalComplex C c'} (φ : K ⟶ L) (j : ι) (j' : ι') (hj : e.f j = j')
    [K.HasHomology j'] [L.HasHomology j'] [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    homologyMap φ j' ≫ (L.restrictionHomologyIsoOfSurjective e he j j' hj).inv =
      (K.restrictionHomologyIsoOfSurjective e he j j' hj).inv ≫
        homologyMap (restrictionMap φ e) j := by
  rw [← cancel_epi (K.restrictionHomologyIsoOfSurjective e he j j' hj).hom,
    Iso.hom_inv_id_assoc,
    ← homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom_assoc,
    Iso.hom_inv_id, Category.comp_id]

include he in
/-- Projectivity of cycles is invariant under restriction along a surjective embedding of complex
shapes which reflects the relations. -/
lemma projective_cycles_restriction_iff_of_surjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    Projective ((K.restriction e).cycles j) ↔ Projective (K.cycles j') :=
  ⟨fun _ ↦ Projective.of_iso (K.restrictionCyclesIsoOfSurjective e he j j' hj) inferInstance,
    fun _ ↦ Projective.of_iso (K.restrictionCyclesIsoOfSurjective e he j j' hj).symm inferInstance⟩

include he in
/-- Projectivity of homology is invariant under restriction along a surjective embedding of complex
shapes which reflects the relations. -/
lemma projective_homology_restriction_iff_of_surjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    Projective ((K.restriction e).homology j) ↔ Projective (K.homology j') :=
  ⟨fun _ ↦ Projective.of_iso (K.restrictionHomologyIsoOfSurjective e he j j' hj) inferInstance,
    fun _ ↦ Projective.of_iso (K.restrictionHomologyIsoOfSurjective e he j j' hj).symm
      inferInstance⟩

include he in
/-- Being a split monomorphism for `iCycles` is invariant under restriction along a surjective
embedding of complex shapes which reflects the relations. -/
lemma isSplitMono_iCycles_restriction_iff_of_surjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    IsSplitMono ((K.restriction e).iCycles j) ↔ IsSplitMono (K.iCycles j') := by
  constructor
  · intro _
    have h : K.iCycles j' =
        (K.restrictionCyclesIsoOfSurjective e he j j' hj).inv ≫
          (K.restriction e).iCycles j ≫ (K.restrictionXIso e hj).hom := by
      rw [restrictionCyclesIsoOfSurjective_inv_iCycles_assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h]
    infer_instance
  · intro _
    have h : (K.restriction e).iCycles j =
        (K.restrictionCyclesIsoOfSurjective e he j j' hj).hom ≫
          K.iCycles j' ≫ (K.restrictionXIso e hj).inv := by
      rw [restrictionCyclesIsoOfSurjective_hom_iCycles_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h]
    infer_instance

end HomologicalComplex
