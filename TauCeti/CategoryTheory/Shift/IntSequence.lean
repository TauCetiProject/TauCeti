/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.CategoryTheory.Shift.Intertwining

/-!
# Integral shift sequences from an existing shift

An existing shift by `ℤ` gives a sequence `n ↦ X⟦n⟧` for the autoequivalence `shiftEquiv C 1`.
The comparison with reindexing is the shift addition isomorphism. This construction allows
an autoequivalence-generated shift to be compared with a previously specified integral shift,
as needed to identify stable suspension with cohomological shift on curved modules.

The construction uses Mathlib's shift addition and associativity API and Tau Ceti's
`Equivalence.IntSequence`, rather than introducing another model of integral sequences.

## References

* Kim Morrison, Johan Commelin, Andrew Yang, Joël Riou, and the Mathlib contributors,
  `Mathlib.CategoryTheory.Shift.Basic`, especially `shiftFunctorAdd'_assoc_inv_app`.
* The Tau Ceti contributors, `TauCeti.CategoryTheory.Shift.Autoequivalence`.
* The Tau Ceti contributors, `TauCeti.CategoryTheory.Shift.Intertwining`: the comparison through
  evaluation and its degree-one computation adapt `Functor.commShiftOfIntertwining` while
  retaining the specified target shift.
-/

public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Equivalence.IntSequence

universe v u

variable (C : Type u) [Category.{v} C] [HasShift C ℤ]

/-- Associate to an object its integral shift sequence for the shift-by-one autoequivalence. -/
@[expose]
noncomputable def ofShiftFunctor : C ⥤ IntSequence (shiftEquiv C (1 : ℤ)) where
  obj X :=
    { X n := X⟦n⟧
      iso n m h := (shiftFunctorAdd' C n 1 m h).symm.app X }
  map f :=
    { f n := f⟦n⟧'
      comm n m h := (shiftFunctorAdd' C n 1 m h).inv.naturality f }
  map_id X := by
    apply hom_ext
    intro n
    exact (shiftFunctor C n).map_id X
  map_comp f g := by
    apply hom_ext
    intro n
    exact (shiftFunctor C n).map_comp f g

attribute [local implicit_reducible] ofShiftFunctor

/-- The map of the canonical sequence functor in degree `n` is the shifted map. -/
@[simp]
theorem ofShiftFunctor_map_f {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    ((ofShiftFunctor C).map f).f n = f⟦n⟧' :=
  (rfl)

/-- Evaluation of the canonical shift sequence in degree zero is naturally the identity. -/
noncomputable def ofShiftFunctorCompEvalIso :
    ofShiftFunctor C ⋙ eval ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦ (shiftFunctorZero C ℤ).app X)
    (fun f ↦ (shiftFunctorZero C ℤ).hom.naturality f)

/-- The comparison with evaluation is the specified shift-zero isomorphism. -/
@[simp]
theorem ofShiftFunctorCompEvalIso_hom_app (X : C) :
    (ofShiftFunctorCompEvalIso C).hom.app X = (shiftFunctorZero C ℤ).hom.app X :=
  (rfl)

/-- The inverse comparison with evaluation is the inverse shift-zero isomorphism. -/
@[simp]
theorem ofShiftFunctorCompEvalIso_inv_app (X : C) :
    (ofShiftFunctorCompEvalIso C).inv.app X = (shiftFunctorZero C ℤ).inv.app X :=
  (rfl)

instance : (ofShiftFunctor C).IsEquivalence := by
  have : (ofShiftFunctor C ⋙ eval).IsEquivalence :=
    Functor.isEquivalence_of_iso (ofShiftFunctorCompEvalIso C).symm
  exact Functor.isEquivalence_of_comp_right (ofShiftFunctor C) eval

/-- Shifting an object and then forming its sequence is reindexing its original sequence. -/
@[expose]
noncomputable def ofShiftFunctorShiftIso (k : ℤ) :
    shiftFunctor C k ⋙ ofShiftFunctor C ≅
      ofShiftFunctor C ⋙ shiftFunctor (IntSequence (shiftEquiv C (1 : ℤ))) k := by
  let α : shiftFunctor C k ⋙ ofShiftFunctor C ⟶
      ofShiftFunctor C ⋙ shiftFunctor (IntSequence (shiftEquiv C (1 : ℤ))) k :=
    { app X :=
        { f n := (shiftFunctorAdd' C k n (n + k) (add_comm k n)).inv.app X
          comm n m h := by
            exact shiftFunctorAdd'_assoc_inv_app k n 1 (n + k) m (m + k)
              (add_comm k n) h (by omega) X }
      naturality {X Y} f := by
        apply hom_ext
        intro n
        exact (shiftFunctorAdd' C k n (n + k) (add_comm k n)).inv.naturality f }
  have : ∀ X, IsIso (α.app X) := by
    intro X
    have : IsIso (eval.map (α.app X)) := by
      change IsIso ((shiftFunctorAdd' C k 0 (0 + k) (add_comm k 0)).inv.app X)
      infer_instance
    exact isIso_of_reflects_iso (α.app X) eval
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The comparison in degree `n` is the inverse shift-addition isomorphism. -/
@[simp]
theorem ofShiftFunctorShiftIso_hom_app_f (k : ℤ) (X : C) (n : ℤ) :
    ((ofShiftFunctorShiftIso C k).hom.app X).f n =
      (shiftFunctorAdd' C k n (n + k) (add_comm k n)).inv.app X :=
  (rfl)

/-- The inverse comparison in degree `n` is the shift-addition isomorphism. -/
@[simp]
theorem ofShiftFunctorShiftIso_inv_app_f (k : ℤ) (X : C) (n : ℤ) :
    ((ofShiftFunctorShiftIso C k).inv.app X).f n =
      (shiftFunctorAdd' C k n (n + k) (add_comm k n)).hom.app X := by
  have h : ((ofShiftFunctorShiftIso C k).hom.app X).f n ≫
      ((ofShiftFunctorShiftIso C k).inv.app X).f n = 𝟙 _ := by
    rw [← comp_f, Iso.hom_inv_id_app, id_f]
  rw [ofShiftFunctorShiftIso_hom_app_f] at h
  exact (Iso.inv_ext (f := (shiftFunctorAdd' C k n (n + k) (add_comm k n)).symm.app X) h).symm

private theorem ofShiftFunctor_iso_zero_one_hom (X : C) :
    (((ofShiftFunctor C).obj X).iso 0 1 rfl).hom =
      (shiftFunctor C (1 : ℤ)).map ((shiftFunctorZero C ℤ).hom.app X) := by
  change (shiftFunctorAdd' C 0 1 1 rfl).inv.app X = _
  exact shiftFunctorAdd'_zero_add_inv_app (1 : ℤ) X

/-- The canonical sequence functor commutes coherently with every integral shift. -/
noncomputable instance ofShiftFunctorCommShift : (ofShiftFunctor C).CommShift ℤ where
  commShiftIso := ofShiftFunctorShiftIso C
  commShiftIso_zero := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply hom_ext
    intro n
    simp only [ofShiftFunctorShiftIso_hom_app_f, Functor.CommShift.isoZero_hom_app,
      comp_f, shiftFunctorZero_inv_app_f]
    simp [ofShiftFunctor, shiftFunctorAdd', shiftFunctorAdd_zero_add_inv_app]
  commShiftIso_add a b := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply hom_ext
    intro n
    rw [Functor.CommShift.isoAdd_hom_app]
    simp only [ofShiftFunctorShiftIso_hom_app_f, comp_f, shiftFunctorAdd_inv_app_f]
    have h := shiftFunctorAdd'_assoc_inv_app a b n (a + b) (n + b) (n + (a + b))
      rfl (add_comm b n) (by omega) X
    simp only [Functor.comp_obj, shiftFunctorAdd', eqToIso_refl, Iso.refl_trans,
      Iso.trans_inv, eqToIso.inv, NatTrans.comp_app, eqToHom_app, Category.assoc,
      ofShiftFunctor, Iso.trans_symm, NatIso.trans_app, shiftFunctor_eq_reindex,
      reindex_obj_X, reindex_map_f, ofShiftFunctorShiftIso_hom_app_f, eqToHom_trans] at h ⊢
    apply (cancel_epi ((shiftFunctor C n).map ((shiftFunctorAdd C a b).inv.app X))).mp
    simpa only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, eqToHom_trans,
      eqToHom_trans_assoc] using h

end CategoryTheory.Equivalence.IntSequence

namespace CategoryTheory.Functor

open CategoryTheory.Equivalence Equivalence.IntSequence

attribute [local implicit_reducible] ofShiftFunctor shiftEquiv' mapFunctor Equivalence.evalCounitIso

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [HasShift D ℤ]

namespace CommShiftOfIntertwiningWithShift

variable {e : C ≌ C} (F : C ⥤ D)
  (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ))

/-- Evaluation identifies the canonical shift sequence with the sequence induced by `α`. -/
private noncomputable def comparisonAfterEval :
    (F ⋙ ofShiftFunctor D) ⋙ eval (e := shiftEquiv D (1 : ℤ)) ≅
      ((eval (e := e)).inv ⋙ mapFunctor (e' := shiftEquiv D (1 : ℤ)) α) ⋙
        eval (e := shiftEquiv D (1 : ℤ)) :=
  (associator _ _ _ ≪≫ isoWhiskerLeft F (ofShiftFunctorCompEvalIso D) ≪≫
      rightUnitor F) ≪≫
    ((associator _ _ _ ≪≫ isoWhiskerLeft (eval (e := e)).inv
          (mapFunctorCompEvalIso (e' := shiftEquiv D (1 : ℤ)) α) ≪≫
        (associator _ _ _).symm ≪≫
        isoWhiskerRight (eval (e := e)).asEquivalence.counitIso F ≪≫ leftUnitor F).symm)

/-- Lift the evaluation comparison through the fully faithful evaluation functor. -/
private noncomputable def comparison :
    F ⋙ ofShiftFunctor D ≅
      (eval (e := e)).inv ⋙ mapFunctor (e' := shiftEquiv D (1 : ℤ)) α :=
  ((whiskeringRight C (IntSequence (shiftEquiv D (1 : ℤ))) D).obj eval).preimageIso
    (comparisonAfterEval F α)

private lemma comparison_hom_app_f_zero (X : C) :
    ((comparison F α).hom.app X).f 0 =
      (shiftFunctorZero D ℤ).hom.app (F.obj X) ≫ F.map (e.evalCounitIso X).inv := by
  change (((whiskeringRight C (IntSequence (shiftEquiv D (1 : ℤ))) D).obj eval).map
    (comparison F α).hom).app X = _
  unfold comparison
  simp only [Functor.preimageIso_hom, Functor.map_preimage]
  simp only [comparisonAfterEval, Functor.asEquivalence_functor, Iso.trans_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, Functor.comp_obj, Functor.associator_hom_app,
    Functor.id_obj, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    ofShiftFunctorCompEvalIso_hom_app, Iso.trans_symm, Iso.symm_hom, Iso.symm_inv,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
    Category.id_comp, Category.comp_id]
  erw [mapFunctorCompEvalIso_inv_app (e' := shiftEquiv D (1 : ℤ)) α,
    Category.id_comp, Category.comp_id, Category.comp_id]
  rfl

private lemma comparison_inv_app_f_zero (X : C) :
    ((comparison F α).inv.app X).f 0 =
      F.map (e.evalCounitIso X).hom ≫ (shiftFunctorZero D ℤ).inv.app (F.obj X) := by
  change (((whiskeringRight C (IntSequence (shiftEquiv D (1 : ℤ))) D).obj eval).map
    (comparison F α).inv).app X = _
  unfold comparison
  simp only [Functor.preimageIso_inv, Functor.map_preimage]
  simp only [comparisonAfterEval, Iso.trans_inv, Functor.asEquivalence_functor,
    Iso.trans_symm, Iso.symm_inv, Iso.symm_hom, isoWhiskerLeft_inv, isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.comp_obj, Functor.associator_inv_app, Functor.id_obj,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
    ofShiftFunctorCompEvalIso_inv_app, isoWhiskerRight_hom, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Category.comp_id]
  erw [mapFunctorCompEvalIso_hom_app (e' := shiftEquiv D (1 : ℤ)) α,
    Category.id_comp, Category.id_comp, Category.id_comp]
  rfl

private lemma comparison_inv_app_f_one (X : C) :
    ((comparison F α).inv.app X).f 1 =
      (((mapFunctor (e' := shiftEquiv D (1 : ℤ)) α).obj
        ((eval (e := e)).inv.obj X)).iso 0 1 rfl).inv ≫
        (shiftFunctor D (1 : ℤ)).map (((comparison F α).inv.app X).f 0) ≫
          (((ofShiftFunctor D).obj (F.obj X)).iso 0 1 rfl).hom := by
  rw [← cancel_epi
    (((mapFunctor (e' := shiftEquiv D (1 : ℤ)) α).obj
      ((eval (e := e)).inv.obj X)).iso 0 1 rfl).hom]
  simp only [Iso.hom_inv_id_assoc]
  exact (((comparison F α).inv.app X).comm 0 1 rfl).symm

end CommShiftOfIntertwiningWithShift

/-- An intertwining with an existing degree-one shift extends coherently to all integral shifts.
The source uses the shift generated by `e`; the target retains its specified `HasShift D ℤ`. -/
@[instance_reducible]
noncomputable def commShiftOfIntertwiningWithShift (F : C ⥤ D) (e : C ≌ C)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) :
    letI := e.hasShift
    F.CommShift ℤ := by
  letI := e.hasShift
  letI : (eval (e := e)).asEquivalence.functor.CommShift ℤ := e.evalCommShift
  letI : (eval (e := e)).inv.CommShift ℤ :=
    (eval (e := e)).asEquivalence.commShiftInverse ℤ
  letI : (mapFunctor (e' := shiftEquiv D (1 : ℤ)) α).CommShift ℤ :=
    mapFunctorCommShift (e' := shiftEquiv D (1 : ℤ)) α
  exact Functor.CommShift.ofComp (CommShiftOfIntertwiningWithShift.comparison F α) ℤ

namespace CommShiftOfIntertwiningWithShift

private lemma map_commShiftIso_one_hom_app_f_zero (F : C ⥤ D) (e : C ≌ C)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) (X : C) :
    letI := e.hasShift
    letI := commShiftOfIntertwiningWithShift F e α
    ((ofShiftFunctor D).map ((F.commShiftIso (1 : ℤ)).hom.app X)).f 0 =
      (shiftFunctorZero D ℤ).hom.app (F.obj ((shiftFunctor C (1 : ℤ)).obj X)) ≫
        F.map ((shiftFunctor C (1 : ℤ)).map (e.evalCounitIso X).inv) ≫
          F.map (e.shiftFunctorOneIso.hom.app (((eval (e := e)).inv.obj X).X 0)) ≫
            α.hom.app (((eval (e := e)).inv.obj X).X 0) ≫
              (shiftFunctor D (1 : ℤ)).map (F.map (e.evalCounitIso X).hom) ≫
                (shiftFunctorZero D ℤ).inv.app ((shiftFunctor D (1 : ℤ)).obj (F.obj X)) := by
  let _ := e.hasShift
  let _ : (eval (e := e)).asEquivalence.functor.CommShift ℤ := e.evalCommShift
  let _ : (eval (e := e)).inv.CommShift ℤ :=
    (eval (e := e)).asEquivalence.commShiftInverse ℤ
  let _ : (mapFunctor (e' := shiftEquiv D (1 : ℤ)) α).CommShift ℤ :=
    mapFunctorCommShift (e' := shiftEquiv D (1 : ℤ)) α
  let _ : F.CommShift ℤ := commShiftOfIntertwiningWithShift F e α
  change ((ofShiftFunctor D).map
    ((Functor.CommShift.OfComp.iso (comparison F α) (1 : ℤ)).hom.app X)).f 0 = _
  rw [Functor.CommShift.OfComp.map_iso_hom_app]
  simp only [Functor.comp_obj, shiftFunctor_eq_reindex, comp_f, reindex_obj_X,
    Int.reduceAdd, reindex_map_f]
  rw [Functor.commShiftIso_comp_hom_app]
  simp only [comp_f]
  erw [mapFunctor_map_f (e' := shiftEquiv D (1 : ℤ))]
  rw [show (mapFunctor (e' := shiftEquiv D (1 : ℤ)) α).commShiftIso (1 : ℤ) =
    mapFunctorShiftIso (e' := shiftEquiv D (1 : ℤ)) α 1 from rfl]
  erw [mapFunctorShiftIso_hom_app_f (e' := shiftEquiv D (1 : ℤ)) α]
  erw [Category.comp_id]
  rw [comparison_hom_app_f_zero]
  simp only [shiftFunctor_eq_reindex, reindex_obj_X, Int.reduceAdd]
  rw [comparison_inv_app_f_one, comparison_inv_app_f_zero]
  rw [show (ofShiftFunctor D).commShiftIso (1 : ℤ) = ofShiftFunctorShiftIso D 1 from rfl]
  rw [ofShiftFunctorShiftIso_inv_app_f, ofShiftFunctor_iso_zero_one_hom]
  simp only [mapFunctor, Functor.comp_obj, Iso.trans_inv, Functor.mapIso_inv,
    Iso.symm_inv, Iso.app_hom, Category.assoc]
  rw [e.evalInverseCommShiftIso_one_hom_app_f_zero]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc,
    Iso.hom_inv_id_map_assoc]
  erw [shiftFunctorAdd'_add_zero_hom_app (1 : ℤ) (F.obj X)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end CommShiftOfIntertwiningWithShift

/-- The coherent comparison at degree one recovers the supplied intertwining isomorphism. -/
theorem commShiftOfIntertwiningWithShift_iso_one (F : C ⥤ D) (e : C ≌ C)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) :
    letI := e.hasShift
    letI := commShiftOfIntertwiningWithShift F e α
    F.commShiftIso (1 : ℤ) = isoWhiskerRight e.shiftFunctorOneIso F ≪≫ α := by
  let _ := e.hasShift
  let _ : F.CommShift ℤ := commShiftOfIntertwiningWithShift F e α
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (ofShiftFunctor D).map_injective
  apply (eval (e := shiftEquiv D (1 : ℤ))).map_injective
  rw [eval_map, eval_map,
    CommShiftOfIntertwiningWithShift.map_commShiftIso_one_hom_app_f_zero]
  have hS := e.shiftFunctorOneIso.hom.naturality (e.evalCounitIso X).inv
  have hα := α.hom.naturality (e.evalCounitIso X).inv
  simp only [Functor.comp_map] at hS hα
  rw [← F.map_comp_assoc, hS, F.map_comp_assoc, reassoc_of% hα,
    ← Functor.map_comp_assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    Functor.whiskerRight_app, ofShiftFunctor_map_f]
  apply (cancel_mono ((shiftFunctorZero D ℤ).hom.app
    ((shiftFunctor D (1 : ℤ)).obj (F.obj X)))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  simpa only [Functor.id_map, Functor.comp_obj, Category.assoc] using
    ((shiftFunctorZero D ℤ).hom.naturality
    (F.map (e.shiftFunctorOneIso.hom.app X) ≫ α.hom.app X)).symm

end CategoryTheory.Functor
