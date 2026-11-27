/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# Commuting the identifications of an extended complex

Let `e : c.Embedding c'` be an embedding of complex shapes and `K` a complex of shape `c`. In a
degree `e.f i` the extended complex `K.extend e` is identified with `K.X i`
(`HomologicalComplex.extendXIso`). Mathlib describes the differential of `K.extend e` and the
extension of a chain map by conjugating with these identifications
(`HomologicalComplex.extend_d_eq`, `HomologicalComplex.extendMap_f`). This file records the
equivalent commutation squares, which read a differential or an extended chain map back on the
unextended complexes without cancelling an inverse.

With these squares the file compares extensions along different embeddings. Restricting
`K.extend e` along `e` gives back `K`
(`ComplexShape.Embedding.extendFunctorCompRestrictionFunctorIso`). Extending along `e` and then
along `e' : c'.Embedding c''` is extending along any embedding `e''` with `e''.f = e'.f ∘ e.f`
(`ComplexShape.Embedding.extendFunctorCompExtendFunctorIso`): both complexes have the terms of `K`
in the degrees `e''.f i` and are zero elsewhere. For instance, a chain complex placed one degree
higher by `n ↦ n + 1` and then read in cochain degrees `N - •` is the complex read in cochain
degrees `N - 1 - •`.

## Main results

* `HomologicalComplex.extend_d_comp_extendXIso_hom`: the identifications intertwine the
  differentials of `K.extend e` and of `K`.
* `HomologicalComplex.extendMap_f_comp_extendXIso_hom`: the identifications intertwine
  `extendMap φ e` and `φ`.
* `ComplexShape.Embedding.extendFunctorCompRestrictionFunctorIso`: restriction along `e` is a left
  inverse of extension along `e`.
* `ComplexShape.Embedding.extendFunctorCompExtendFunctorIso`: extending along two embeddings in
  turn is extending along their composite.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroObject C] [HasZeroMorphisms C] (e : c.Embedding c')

/-- In degrees in the image of `e.f`, the identifications of `K.extend e` with `K` intertwine
the differentials. -/
@[reassoc, elementwise]
theorem extend_d_comp_extendXIso_hom (K : HomologicalComplex C c) {i' j' : ι'} {i j : ι}
    (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' ≫ (K.extendXIso e hj).hom = (K.extendXIso e hi).hom ≫ K.d i j := by
  rw [extend_d_eq K e hi hj, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In a degree in the image of `e.f`, the identifications of the extended complexes with the
original ones intertwine the extension `extendMap φ e` of a chain map with `φ`. -/
@[reassoc, elementwise]
theorem extendMap_f_comp_extendXIso_hom {K L : HomologicalComplex C c} (φ : K ⟶ L) {i' : ι'}
    {i : ι} (h : e.f i = i') :
    (extendMap φ e).f i' ≫ (L.extendXIso e h).hom = (K.extendXIso e h).hom ≫ φ.f i := by
  rw [extendMap_f φ e h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### Extending along two embeddings in turn -/

section Composite

variable {ι'' : Type*} {c'' : ComplexShape ι''} {e} {e' : c'.Embedding c''}
  {e'' : c.Embedding c''} (he : ∀ i, e'.f (e.f i) = e''.f i) (K : HomologicalComplex C c)
include he

/-- Outside the image of `e''.f`, extending along `e` and then along `e'` gives zero. -/
theorem isZero_extend_extend_X {i'' : ι''} (hi'' : ∀ i, e''.f i ≠ i'') :
    IsZero (((K.extend e).extend e').X i'') := by
  by_cases h : ∃ i', e'.f i' = i''
  · obtain ⟨i', rfl⟩ := h
    refine IsZero.of_iso (K.isZero_extend_X e i' fun i hi ↦ hi'' i ?_)
      ((K.extend e).extendXIso e' rfl)
    rw [← he, hi]
  · exact (K.extend e).isZero_extend_X e' i'' (not_exists.1 h)

/-- The identification of the terms of `(K.extend e).extend e'` and `K.extend e''` in each degree,
through the terms of `K` in the image of `e''.f` (`HomologicalComplex.extendExtendXIso_hom`), and
between zero objects elsewhere. -/
noncomputable def extendExtendXIso (i'' : ι'') :
    ((K.extend e).extend e').X i'' ≅ (K.extend e'').X i'' :=
  open Classical in
  if h : ∃ i, e''.f i = i'' then
    (K.extend e).extendXIso e' ((he h.choose).trans h.choose_spec) ≪≫ K.extendXIso e rfl ≪≫
      (K.extendXIso e'' h.choose_spec).symm
  else
    (isZero_extend_extend_X he K (not_exists.1 h)).iso
      (K.isZero_extend_X e'' i'' (not_exists.1 h))

/-- In a degree `e''.f i`, the identification `HomologicalComplex.extendExtendXIso` is the
composite of the identifications of both sides with `K.X i`. -/
theorem extendExtendXIso_hom {i'' : ι''} {i : ι} (hi : e''.f i = i'') :
    (extendExtendXIso he K i'').hom = ((K.extend e).extendXIso e' ((he i).trans hi)).hom ≫
      (K.extendXIso e rfl).hom ≫ (K.extendXIso e'' hi).inv := by
  have h : ∃ i, e''.f i = i'' := ⟨i, hi⟩
  simp only [extendExtendXIso, h, ↓reduceDIte, Iso.trans_hom, Iso.symm_hom]
  obtain rfl : h.choose = i := e''.injective_f (h.choose_spec.trans hi.symm)
  rfl

/-- **Extending along two embeddings in turn.** If `e''.f = e'.f ∘ e.f`, extending a complex along
`e` and then along `e'` is extending it along `e''`. -/
noncomputable def extendExtendIso : (K.extend e).extend e' ≅ K.extend e'' :=
  Hom.isoOfComponents (extendExtendXIso he K) fun i'' j'' _ ↦ by
    by_cases hi : ∃ i, e''.f i = i''
    · by_cases hj : ∃ j, e''.f j = j''
      · obtain ⟨i, rfl⟩ := hi
        obtain ⟨j, rfl⟩ := hj
        rw [extendExtendXIso_hom he K rfl, extendExtendXIso_hom he K rfl, extend_d_eq K e'' rfl rfl,
          extend_d_eq (K.extend e) e' (he i) (he j), extend_d_eq K e rfl rfl]
        simp
      · exact (K.isZero_extend_X e'' j'' (not_exists.1 hj)).eq_of_tgt _ _
    · exact (isZero_extend_extend_X he K (not_exists.1 hi)).eq_of_src _ _

@[simp]
theorem extendExtendIso_hom_f (i'' : ι'') :
    (extendExtendIso he K).hom.f i'' = (extendExtendXIso he K i'').hom :=
  (rfl)

end Composite

end HomologicalComplex

namespace ComplexShape.Embedding

open HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (C : Type*) [Category* C] [HasZeroObject C] [HasZeroMorphisms C] (e : c.Embedding c')

/-- **Restriction is a left inverse of extension.** Restricting the extension `K.extend e` along
`e` gives back `K`, through the identifications `HomologicalComplex.extendXIso` in each degree. -/
noncomputable def extendFunctorCompRestrictionFunctorIso [e.IsRelIff] :
    e.extendFunctor C ⋙ e.restrictionFunctor C ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun K ↦ Hom.isoOfComponents (fun i ↦ K.extendXIso e rfl) fun i j _ ↦
      (extend_d_comp_extendXIso_hom e K rfl rfl).symm)
    fun φ ↦ by
      ext i
      exact extendMap_f_comp_extendXIso_hom e φ rfl

@[simp]
theorem extendFunctorCompRestrictionFunctorIso_hom_app_f [e.IsRelIff] (K : HomologicalComplex C c)
    (i : ι) :
    ((extendFunctorCompRestrictionFunctorIso C e).hom.app K).f i = (K.extendXIso e rfl).hom :=
  (rfl)

variable {ι'' : Type*} {c'' : ComplexShape ι''} {e} {e' : c'.Embedding c''}
  {e'' : c.Embedding c''} (he : ∀ i, e'.f (e.f i) = e''.f i)
include he

/-- **Extending along two embeddings in turn, as functors.** If `e''.f = e'.f ∘ e.f`, extending
along `e` and then along `e'` is extending along `e''`, naturally in the complex. -/
noncomputable def extendFunctorCompExtendFunctorIso :
    e.extendFunctor C ⋙ e'.extendFunctor C ≅ e''.extendFunctor C :=
  NatIso.ofComponents (fun K ↦ extendExtendIso he K) fun {K L} φ ↦ by
    ext i''
    by_cases hi : ∃ i, e''.f i = i''
    · obtain ⟨i, rfl⟩ := hi
      simp [extendExtendXIso_hom he _ rfl, extendMap_f φ e rfl, extendMap_f φ e'' rfl,
        extendMap_f (extendMap φ e) e' (he i)]
    · exact (isZero_extend_extend_X he K (not_exists.1 hi)).eq_of_src _ _

@[simp]
theorem extendFunctorCompExtendFunctorIso_hom_app (K : HomologicalComplex C c) :
    (extendFunctorCompExtendFunctorIso C he).hom.app K = (extendExtendIso he K).hom :=
  (rfl)

end ComplexShape.Embedding
