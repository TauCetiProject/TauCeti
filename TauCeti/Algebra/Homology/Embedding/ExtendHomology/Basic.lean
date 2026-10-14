/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Opcycles and extension by zero

The opcycles isomorphism of an extended complex is natural in chain maps and compatible with
`HomologicalComplex.opcyclesToCycles`. These identities require homology only in the degrees
involved, in a category with zero morphisms and a zero object. An extended chain map is an
epimorphism in homology in a degree of the image exactly when the original map is, the counterpart
for epimorphisms of Mathlib's `HomologicalComplex.quasiIsoAt_extendMap_iff`. Outside the image,
an extended complex has zero homology, so every extended chain map is an isomorphism in homology
there.

Adapted from [TauCetiProject/TauCeti#10141](https://github.com/TauCetiProject/TauCeti/pull/10141).
-/

public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c')

/-- The identification of the opcycles of an extended complex is natural. -/
@[reassoc (attr := simp)]
lemma extendOpcyclesIso_hom_naturality {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j] :
    letI := extend.hasHomology K e hj'
    letI := extend.hasHomology L e hj'
    opcyclesMap (extendMap φ e) j' ≫ (L.extendOpcyclesIso e hj').hom =
      (K.extendOpcyclesIso e hj').hom ≫ opcyclesMap φ j := by
  let := extend.hasHomology K e hj'
  let := extend.hasHomology L e hj'
  simp [← cancel_epi ((K.extend e).pOpcycles j'), extendMap_f φ e hj']

variable (K) in
/-- The identifications of the opcycles and cycles of an extended complex are compatible with the
maps `opcyclesToCycles`. -/
-- The left-hand side does not determine the source index `i` for the simplifier.
@[reassoc]
lemma extend_opcyclesToCycles_comp_extendCyclesIso_hom {i j : ι} {i' j' : ι'} (hi' : e.f i = i')
    (hj' : e.f j = j') [K.HasHomology i] [K.HasHomology j] :
    letI := extend.hasHomology K e hi'
    letI := extend.hasHomology K e hj'
    (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj').hom =
      (K.extendOpcyclesIso e hi').hom ≫ K.opcyclesToCycles i j := by
  let := extend.hasHomology K e hi'
  let := extend.hasHomology K e hj'
  simp [← cancel_epi ((K.extend e).pOpcycles i'), ← cancel_mono (K.iCycles j),
    K.extend_d_eq e hi' hj']

variable {e} in
/-- In a degree `j'` in the image of `e`, the map induced in homology by the extension of `φ` is an
epimorphism exactly when the map induced by `φ` is in the corresponding degree `j`. -/
lemma epi_homologyMap_extendMap_iff {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j] [(K.extend e).HasHomology j']
    [(L.extend e).HasHomology j'] :
    Epi (homologyMap (extendMap φ e) j') ↔ Epi (homologyMap φ j) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj') (by simp))

variable {e} in
/-- In a degree `j'` outside the image of `e`, the map induced in homology by the extension of `φ`
is an isomorphism, between zero objects. -/
lemma isIso_homologyMap_extendMap_of_forall_ne {j' : ι'} (hj' : ∀ j, e.f j ≠ j')
    [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j'] :
    IsIso (homologyMap (extendMap φ e) j') :=
  ⟨0, (K.extend_exactAt e j' hj').isZero_homology.eq_of_src _ _,
    (L.extend_exactAt e j' hj').isZero_homology.eq_of_src _ _⟩

end HomologicalComplex
