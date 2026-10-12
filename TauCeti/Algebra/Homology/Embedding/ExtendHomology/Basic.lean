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
involved, in a category with zero morphisms and a zero object.

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

end HomologicalComplex
