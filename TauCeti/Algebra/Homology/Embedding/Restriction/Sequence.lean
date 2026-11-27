/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import TauCeti.Algebra.Homology.Embedding.Restriction.Homology

/-!
# The homology sequence of a restricted short exact sequence

Let `e : c.Embedding c'` be an embedding of complex shapes and `S` a short exact sequence of
complexes of shape `c'` in an abelian category. Restricting `S` along `e` gives a short exact
sequence of complexes of shape `c` (`CategoryTheory.ShortComplex.ShortExact.restriction`), since in
each degree it is the short complex of `S` in the corresponding degree. Mathlib identifies the
homology of a restricted complex in degree `j` with the homology of the original complex in degree
`e.f j` (`HomologicalComplex.restrictionHomologyIso`). This file shows that the connecting maps of
the two homology sequences correspond under these identifications
(`CategoryTheory.ShortComplex.ShortExact.restriction_δ_comp_restrictionHomologyIso_hom`).

This is what allows a connecting map computed on a complex reindexed along an embedding, such as
a chain complex regraded as a cochain complex along `n ↦ -n`, to be compared with the connecting
map of the original complex. It is the restriction counterpart of
`CategoryTheory.ShortComplex.ShortExact.extend_δ_comp_extendHomologyIso_hom`.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.restriction`: restricting a short exact sequence of
  complexes along an embedding of complex shapes gives a short exact sequence.
* `CategoryTheory.ShortComplex.ShortExact.restriction_δ_comp_restrictionHomologyIso_hom`: the
  connecting maps of a short exact sequence and of its restriction correspond under
  `HomologicalComplex.restrictionHomologyIso`.
-/

public section

open CategoryTheory Category Limits HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

open HomologySequence

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [Abelian C] {S : ShortComplex (HomologicalComplex C c')}

/-- Restricting a short exact sequence of complexes along an embedding of complex shapes gives a
short exact sequence: in each degree it is the short complex of the original sequence in the
corresponding degree. -/
lemma restriction (hS : S.ShortExact) (e : c.Embedding c') [e.IsRelIff] :
    (S.map (e.restrictionFunctor C)).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun i ↦
    (shortExact_iff_degreewise_shortExact S).1 hS (e.f i)

variable (hS : S.ShortExact) (e : c.Embedding c') [e.IsRelIff]

/-- The morphism from the snake-lemma input of the restriction of `S` to that of `S`, given by the
identifications of the homology, opcycles and cycles of a restricted complex. -/
private noncomputable def restrictionSnakeInputHom (i₀ i j k : ι) (hij : c.Rel i j)
    (h₀ : c.prev i = i₀) (hk : c.next j = k) {i₀' i' j' k' : ι'} (h₀' : e.f i₀ = i₀')
    (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k') (h₀'' : c'.prev i' = i₀')
    (hk'' : c'.next j' = k') :
    snakeInput (hS.restriction e) i j hij ⟶
      snakeInput hS i' j' (hi' ▸ hj' ▸ e.rel hij) where
  f₀ :=
    { τ₁ := (S.X₁.restrictionHomologyIso e i₀ i j h₀ (c.next_eq' hij) h₀' hi' hj' h₀''
        (c'.next_eq' (hi' ▸ hj' ▸ e.rel hij))).hom
      τ₂ := (S.X₂.restrictionHomologyIso e i₀ i j h₀ (c.next_eq' hij) h₀' hi' hj' h₀''
        (c'.next_eq' (hi' ▸ hj' ▸ e.rel hij))).hom
      τ₃ := (S.X₃.restrictionHomologyIso e i₀ i j h₀ (c.next_eq' hij) h₀' hi' hj' h₀''
        (c'.next_eq' (hi' ▸ hj' ▸ e.rel hij))).hom
      comm₁₂ := (restrictionHomologyIso_hom_naturality S.f e ..).symm
      comm₂₃ := (restrictionHomologyIso_hom_naturality S.g e ..).symm }
  f₁ :=
    { τ₁ := (S.X₁.restrictionOpcyclesIso e i₀ i h₀ h₀' hi' h₀'').hom
      τ₂ := (S.X₂.restrictionOpcyclesIso e i₀ i h₀ h₀' hi' h₀'').hom
      τ₃ := (S.X₃.restrictionOpcyclesIso e i₀ i h₀ h₀' hi' h₀'').hom
      comm₁₂ := (restrictionOpcyclesIso_hom_naturality S.f e ..).symm
      comm₂₃ := (restrictionOpcyclesIso_hom_naturality S.g e ..).symm }
  f₂ :=
    { τ₁ := (S.X₁.restrictionCyclesIso e j k hk hj' hk' hk'').hom
      τ₂ := (S.X₂.restrictionCyclesIso e j k hk hj' hk' hk'').hom
      τ₃ := (S.X₃.restrictionCyclesIso e j k hk hj' hk' hk'').hom
      comm₁₂ := (restrictionCyclesIso_hom_naturality S.f e ..).symm
      comm₂₃ := (restrictionCyclesIso_hom_naturality S.g e ..).symm }
  f₃ :=
    { τ₁ := (S.X₁.restrictionHomologyIso e i j k (c.prev_eq' hij) hk hi' hj' hk'
        (c'.prev_eq' (hi' ▸ hj' ▸ e.rel hij)) hk'').hom
      τ₂ := (S.X₂.restrictionHomologyIso e i j k (c.prev_eq' hij) hk hi' hj' hk'
        (c'.prev_eq' (hi' ▸ hj' ▸ e.rel hij)) hk'').hom
      τ₃ := (S.X₃.restrictionHomologyIso e i j k (c.prev_eq' hij) hk hi' hj' hk'
        (c'.prev_eq' (hi' ▸ hj' ▸ e.rel hij)) hk'').hom
      comm₁₂ := (restrictionHomologyIso_hom_naturality S.f e ..).symm
      comm₂₃ := (restrictionHomologyIso_hom_naturality S.g e ..).symm }
  comm₀₁ := by ext <;> exact restrictionHomologyIso_hom_homologyι ..
  comm₁₂ := by
    ext <;>
      exact restrictionOpcyclesIso_hom_opcyclesToCycles _ e i₀ i j k h₀ hk h₀' hi' hj' hk' h₀'' hk''
  comm₂₃ := by ext <;> exact (homologyπ_restrictionHomologyIso_hom ..).symm

/-- **The connecting maps of a restricted short exact sequence.** Under the identifications
`HomologicalComplex.restrictionHomologyIso` of the homology of the restricted complexes with the
homology of the original ones, the connecting map of the restriction of `S` along `e` in degrees
`i ⟶ j` is the connecting map of `S` in degrees `e.f i ⟶ e.f j`. The neighbouring indices used by
the identifications are given by equations, for flexibility: the successor `j₃` of `i` and the
predecessor `i₁` of `j` need not be syntactically `j` and `i`. -/
@[reassoc]
lemma restriction_δ_comp_restrictionHomologyIso_hom (i₀ i j₃ i₁ j k : ι) (hij : c.Rel i j)
    (h₀ : c.prev i = i₀) (h₃ : c.next i = j₃) (h₁ : c.prev j = i₁) (hk : c.next j = k)
    {i₀' i' j₃' i₁' j' k' : ι'} (h₀' : e.f i₀ = i₀') (hi' : e.f i = i') (h₃' : e.f j₃ = j₃')
    (h₁' : e.f i₁ = i₁') (hj' : e.f j = j') (hk' : e.f k = k') (h₀'' : c'.prev i' = i₀')
    (h₃'' : c'.next i' = j₃') (h₁'' : c'.prev j' = i₁') (hk'' : c'.next j' = k') :
    (hS.restriction e).δ i j hij ≫
        (S.X₁.restrictionHomologyIso e i₁ j k h₁ hk h₁' hj' hk' h₁'' hk'').hom =
      (S.X₃.restrictionHomologyIso e i₀ i j₃ h₀ h₃ h₀' hi' h₃' h₀'' h₃'').hom ≫
        hS.δ i' j' (hi' ▸ hj' ▸ e.rel hij) := by
  obtain rfl : j = j₃ := (c.next_eq' hij).symm.trans h₃
  obtain rfl : i = i₁ := (c.prev_eq' hij).symm.trans h₁
  subst h₀' hi' h₃' h₁' hj' hk'
  exact SnakeInput.naturality_δ
    (restrictionSnakeInputHom hS e i₀ i j k hij h₀ hk rfl rfl rfl rfl h₀'' hk'')

end CategoryTheory.ShortComplex.ShortExact
