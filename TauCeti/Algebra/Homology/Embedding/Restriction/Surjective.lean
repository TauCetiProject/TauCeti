/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Boundary
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Restriction along surjective embeddings of complex shapes

An embedding of complex shapes `e : c.Embedding c'` which reflects the relations
(`ComplexShape.Embedding.IsRelIff`) and whose index map `e.f` is surjective identifies the two
shapes: it carries previous and next indices of `c` to those of `c'`
(`ComplexShape.Embedding.prev_f_of_surjective`, `ComplexShape.Embedding.next_f_of_surjective`).
So the restriction of a complex along `e` has, at every index `j`, the homology of the complex at
`e.f j` (`HomologicalComplex.restrictionHomologyIsoOfSurjective`), naturally in the complex
(`HomologicalComplex.homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom`). This
is Mathlib's `HomologicalComplex.restrictionHomologyIso`, whose compatibility hypotheses on
previous and next indices then hold at every index. Such embeddings are given by bijections of
indices compatible with the relations (`ComplexShape.Embedding.mk'`); they are used to read a
complex, or the pages of a spectral sequence, in other coordinates.

## Main definitions

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

/-- The homology of the restriction of a complex along a surjective embedding of complex shapes
which reflects the relations is the homology of the complex at the corresponding index `j'`, the
image of `j`. -/
noncomputable def restrictionHomologyIsoOfSurjective (K : HomologicalComplex C c') (j : ι)
    (j' : ι') (hj : e.f j = j') [K.HasHomology j'] [(K.restriction e).HasHomology j] :
    (K.restriction e).homology j ≅ K.homology j' :=
  K.restrictionHomologyIso e _ j _ rfl rfl rfl hj rfl
    (by rw [← hj, e.prev_f_of_surjective he j]) (by rw [← hj, e.next_f_of_surjective he j])

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
      (L.restrictionCyclesIso e j _ rfl rfl rfl (e.next_f_of_surjective he j)).hom =
      (K.restrictionCyclesIso e j _ rfl rfl rfl (e.next_f_of_surjective he j)).hom ≫
        cyclesMap φ (e.f j) := by
    rw [← cancel_mono (L.iCycles (e.f j))]
    simp [restrictionXIso]
  rw [← cancel_epi ((K.restriction e).homologyπ j)]
  simp only [restrictionHomologyIsoOfSurjective, homologyπ_naturality_assoc,
    homologyπ_restrictionHomologyIso_hom, homologyπ_restrictionHomologyIso_hom_assoc,
    homologyπ_naturality]
  rw [reassoc_of% hcycles]

end HomologicalComplex
