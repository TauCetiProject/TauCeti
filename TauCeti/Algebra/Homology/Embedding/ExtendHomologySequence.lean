/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# The homology sequence of an extended short exact sequence

Let `e : c.Embedding c'` be an embedding of complex shapes and `S` a short exact sequence of
complexes of shape `c` in an abelian category. Extending `S` by zero along `e` gives a short exact
sequence of complexes of shape `c'` (`CategoryTheory.ShortComplex.ShortExact.extend`), and Mathlib
identifies the homology of an extended complex in degree `e.f j` with the homology of the original
complex in degree `j` (`HomologicalComplex.extendHomologyIso`). This file shows that the connecting
maps of the two homology sequences correspond under these identifications
(`CategoryTheory.ShortComplex.ShortExact.extend_δ_comp_extendHomologyIso_hom`).

This is what allows a connecting map computed on a complex reindexed along an embedding, such as
the Tate complex, whose negative part is the complex of inhomogeneous chains reindexed by
`n ↦ -(n + 1)`, to be compared with the connecting map of the original complex.
-/

public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [Abelian C] (e : c.Embedding c')

variable {K L : HomologicalComplex C c} (φ : K ⟶ L)

/-- The identification of the opcycles of an extended complex is natural. -/
@[reassoc (attr := simp)]
lemma extendOpcyclesIso_hom_naturality {j : ι} {j' : ι'} (hj' : e.f j = j') :
    opcyclesMap (extendMap φ e) j' ≫ (L.extendOpcyclesIso e hj').hom =
      (K.extendOpcyclesIso e hj').hom ≫ opcyclesMap φ j := by
  simp [← cancel_epi ((K.extend e).pOpcycles j'), extendMap_f φ e hj']

variable (K) in
/-- The identifications of the opcycles and cycles of an extended complex are compatible with the
maps `opcyclesToCycles`. -/
@[reassoc]
lemma extend_opcyclesToCycles_comp_extendCyclesIso_hom {i j : ι} {i' j' : ι'} (hi' : e.f i = i')
    (hj' : e.f j = j') :
    (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj').hom =
      (K.extendOpcyclesIso e hi').hom ≫ K.opcyclesToCycles i j := by
  simp [← cancel_epi ((K.extend e).pOpcycles i'), ← cancel_mono (K.iCycles j),
    K.extend_d_eq e hi' hj']

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

open HomologicalComplex HomologySequence

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [Abelian C] {S : ShortComplex (HomologicalComplex C c)}

/-- Extending a short exact sequence of complexes by zero along an embedding of complex shapes
gives a short exact sequence. -/
lemma extend (hS : S.ShortExact) (e : c.Embedding c') :
    (S.map (e.extendFunctor C)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact ShortComplex.shortExact_of_iso (S.mapNatIso (e.extendFunctorCompEvalIso C hi).symm)
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i)
  · have h : ∀ K : HomologicalComplex C c, IsZero ((K.extend e).X i') :=
      fun K ↦ K.isZero_extend_X e i' (by simpa using hi')
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ (h _))
      ⟨fun _ _ _ ↦ (h _).eq_of_tgt _ _⟩ ⟨fun _ _ _ ↦ (h _).eq_of_src _ _⟩

variable (hS : S.ShortExact) (e : c.Embedding c') {i j : ι} (hij : c.Rel i j)
  {i' j' : ι'} (hi' : e.f i = i') (hj' : e.f j = j')

/-- The morphism from the snake-lemma input of the extension of `S` to that of `S`, given by the
identifications of the homology, opcycles and cycles of an extended complex. -/
private noncomputable def extendSnakeInputHom :
    snakeInput (hS.extend e) i' j' (by rw [← hi', ← hj']; exact e.rel hij) ⟶
      snakeInput hS i j hij where
  f₀ :=
    { τ₁ := (S.X₁.extendHomologyIso e hi').hom
      τ₂ := (S.X₂.extendHomologyIso e hi').hom
      τ₃ := (S.X₃.extendHomologyIso e hi').hom
      comm₁₂ := (extendHomologyIso_hom_naturality S.f e hi').symm
      comm₂₃ := (extendHomologyIso_hom_naturality S.g e hi').symm }
  f₁ :=
    { τ₁ := (S.X₁.extendOpcyclesIso e hi').hom
      τ₂ := (S.X₂.extendOpcyclesIso e hi').hom
      τ₃ := (S.X₃.extendOpcyclesIso e hi').hom
      comm₁₂ := (extendOpcyclesIso_hom_naturality e S.f hi').symm
      comm₂₃ := (extendOpcyclesIso_hom_naturality e S.g hi').symm }
  f₂ :=
    { τ₁ := (S.X₁.extendCyclesIso e hj').hom
      τ₂ := (S.X₂.extendCyclesIso e hj').hom
      τ₃ := (S.X₃.extendCyclesIso e hj').hom
      comm₁₂ := (extendCyclesIso_hom_naturality S.f e hj').symm
      comm₂₃ := (extendCyclesIso_hom_naturality S.g e hj').symm }
  f₃ :=
    { τ₁ := (S.X₁.extendHomologyIso e hj').hom
      τ₂ := (S.X₂.extendHomologyIso e hj').hom
      τ₃ := (S.X₃.extendHomologyIso e hj').hom
      comm₁₂ := (extendHomologyIso_hom_naturality S.f e hj').symm
      comm₂₃ := (extendHomologyIso_hom_naturality S.g e hj').symm }
  comm₀₁ := by ext <;> exact extendHomologyIso_hom_homologyι _ e hi'
  comm₁₂ := by ext <;> exact (extend_opcyclesToCycles_comp_extendCyclesIso_hom e _ hi' hj').symm
  comm₂₃ := by ext <;> exact (homologyπ_extendHomologyIso_hom _ e hj').symm

/-- **The connecting maps of an extended short exact sequence.** Under the identifications
`HomologicalComplex.extendHomologyIso` of the homology of the extended complexes with the homology
of the original ones, the connecting map of the extension of `S` along `e` in degrees
`e.f i ⟶ e.f j` is the connecting map of `S` in degrees `i ⟶ j`. -/
@[reassoc]
lemma extend_δ_comp_extendHomologyIso_hom (hij' : c'.Rel i' j') :
    (hS.extend e).δ i' j' hij' ≫ (S.X₁.extendHomologyIso e hj').hom =
      (S.X₃.extendHomologyIso e hi').hom ≫ hS.δ i j hij :=
  SnakeInput.naturality_δ (extendSnakeInputHom hS e hij hi' hj')

end CategoryTheory.ShortComplex.ShortExact
