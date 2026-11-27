/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Naturality of the homology of a restricted complex

Let `e : c.Embedding c'` be an embedding of complex shapes which reflects the relations. Mathlib
identifies the cycles, opcycles and homology of the restriction of a complex `K` along `e` in degree
`j` with those of `K` in degree `e.f j` (`HomologicalComplex.restrictionCyclesIso`,
`HomologicalComplex.restrictionOpcyclesIso`, `HomologicalComplex.restrictionHomologyIso`). This file
shows that these identifications are natural in the complex, and that the identifications of
opcycles and cycles are compatible with the maps `HomologicalComplex.opcyclesToCycles`. These
identities require homology only in the degrees involved, in a category with zero morphisms. They
are the restriction counterparts of `HomologicalComplex.extendOpcyclesIso_hom_naturality` and
`HomologicalComplex.extendHomologyIso_hom_naturality`.

## Main results

* `HomologicalComplex.restrictionCyclesIso_hom_naturality`,
  `HomologicalComplex.restrictionOpcyclesIso_hom_naturality`,
  `HomologicalComplex.restrictionHomologyIso_hom_naturality`: the identifications of the cycles,
  opcycles and homology of a restricted complex are natural.
* `HomologicalComplex.restrictionOpcyclesIso_hom_opcyclesToCycles`: the identifications of the
  opcycles and cycles of a restricted complex are compatible with `opcyclesToCycles`.
-/

public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] {K L : HomologicalComplex C c'} (φ : K ⟶ L)
  (e : c.Embedding c') [e.IsRelIff]

/-- The identification of the cycles of a restricted complex is natural. -/
@[reassoc]
lemma restrictionCyclesIso_hom_naturality (j k : ι) (hk : c.next j = k) {j' k' : ι'}
    (hj' : e.f j = j') (hk' : e.f k = k') (hk'' : c'.next j' = k') [K.HasHomology j']
    [L.HasHomology j'] [(K.restriction e).HasHomology j] [(L.restriction e).HasHomology j] :
    cyclesMap (restrictionMap φ e) j ≫ (L.restrictionCyclesIso e j k hk hj' hk' hk'').hom =
      (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ cyclesMap φ j' := by
  subst hj'
  simp [← cancel_mono (L.iCycles _), restrictionXIso]

/-- The identification of the opcycles of a restricted complex is natural. -/
@[reassoc]
lemma restrictionOpcyclesIso_hom_naturality (i j : ι) (hi : c.prev j = i) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi'' : c'.prev j' = i') [K.HasHomology j']
    [L.HasHomology j'] [(K.restriction e).HasHomology j] [(L.restriction e).HasHomology j] :
    opcyclesMap (restrictionMap φ e) j ≫ (L.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom =
      (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom ≫ opcyclesMap φ j' := by
  subst hj'
  simp [← cancel_epi ((K.restriction e).pOpcycles j), restrictionXIso]

/-- The identification of the homology of a restricted complex is natural. -/
@[reassoc]
lemma restrictionHomologyIso_hom_naturality (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k) {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
    (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k') [K.HasHomology j'] [L.HasHomology j']
    [(K.restriction e).HasHomology j] [(L.restriction e).HasHomology j] :
    homologyMap (restrictionMap φ e) j ≫
        (L.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom =
      (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom ≫ homologyMap φ j' := by
  simp [← cancel_epi ((K.restriction e).homologyπ j),
    restrictionCyclesIso_hom_naturality_assoc φ e j k hk hj' hk' hk'']

variable (K) in
/-- The identifications of the opcycles and cycles of a restricted complex are compatible with the
maps `opcyclesToCycles`. -/
@[reassoc]
lemma restrictionOpcyclesIso_hom_opcyclesToCycles (i₀ i j k : ι) (h₀ : c.prev i = i₀)
    (hk : c.next j = k) {i₀' i' j' k' : ι'} (h₀' : e.f i₀ = i₀') (hi' : e.f i = i')
    (hj' : e.f j = j') (hk' : e.f k = k') (h₀'' : c'.prev i' = i₀') (hk'' : c'.next j' = k')
    [K.HasHomology i'] [K.HasHomology j'] [(K.restriction e).HasHomology i]
    [(K.restriction e).HasHomology j] :
    (K.restrictionOpcyclesIso e i₀ i h₀ h₀' hi' h₀'').hom ≫ K.opcyclesToCycles i' j' =
      (K.restriction e).opcyclesToCycles i j ≫
        (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom := by
  subst hi' hj'
  simp [← cancel_epi ((K.restriction e).pOpcycles i), ← cancel_mono (K.iCycles _), restrictionXIso]

end HomologicalComplex
