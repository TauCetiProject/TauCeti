/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Shift.Intertwining

/-!
# Integer sequences from an existing shift

A category with an integral shift has a canonical sequence `n ↦ X⟦n⟧` for each object.
These sequences are linked by the shift by one. This realizes the category as the sequence
model of its generating autoequivalence, compatibly with all integral shifts. It lets one
compare a shift constructed from an autoequivalence with an already installed shift, without
replacing the latter.

The sequence model and its evaluation equivalence are those of
`CategoryTheory.Equivalence.IntSequence`. The coherence proofs use Mathlib's
`shiftFunctorAdd'_assoc_inv_app`.
-/

public section

noncomputable section

universe v u

namespace TauCeti.Shift

open CategoryTheory CategoryTheory.Functor CategoryTheory.Equivalence

variable (C : Type u) [Category.{v} C]

section ExistingShift

variable [HasShift C ℤ]

/-- The sequence of all integral shifts of an object, linked by the shift by one. -/
-- Exposure is required to type the component formulas with their literal shift endpoints.
@[expose, simps!]
noncomputable def sequenceFunctor : C ⥤ IntSequence (shiftEquiv C (1 : ℤ)) where
  obj X :=
    { X := fun n => X⟦n⟧
      iso := fun n m h => (shiftFunctorAdd' C n 1 m h).symm.app X }
  map f :=
    { f := fun n => f⟦n⟧'
      comm := fun n m h => by
        simpa [shiftEquiv, shiftEquiv'] using (shiftFunctorAdd' C n 1 m h).inv.naturality f }
  map_id X := by ext n; exact (shiftFunctor C n).map_id X
  map_comp f g := by ext n; exact (shiftFunctor C n).map_comp f g

/-- Evaluation of the canonical shift sequence recovers the original object. -/
noncomputable def sequenceFunctorCompEvalIso :
    sequenceFunctor C ⋙ IntSequence.eval ≅ 𝟭 C :=
  shiftFunctorZero C ℤ

@[simp]
theorem sequenceFunctorCompEvalIso_hom_app (X : C) :
    (sequenceFunctorCompEvalIso C).hom.app X = (shiftFunctorZero C ℤ).hom.app X := (rfl)

@[simp]
theorem sequenceFunctorCompEvalIso_inv_app (X : C) :
    (sequenceFunctorCompEvalIso C).inv.app X = (shiftFunctorZero C ℤ).inv.app X := (rfl)

/-- The canonical sequence construction is an equivalence. -/
instance : (sequenceFunctor C).IsEquivalence := by
  have : (sequenceFunctor C ⋙ IntSequence.eval).IsEquivalence :=
    Functor.isEquivalence_of_iso (sequenceFunctorCompEvalIso C).symm
  exact Functor.isEquivalence_of_comp_right (sequenceFunctor C) IntSequence.eval

/-- Shifting the object before forming its sequence agrees with reindexing the sequence. -/
noncomputable def sequenceFunctorShiftIso (k : ℤ) :
    shiftFunctor C k ⋙ sequenceFunctor C ≅
      sequenceFunctor C ⋙ shiftFunctor (IntSequence (shiftEquiv C (1 : ℤ))) k :=
  NatIso.ofComponents (fun X =>
    { hom :=
        { f := fun n => (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).inv.app X
          comm := fun n m h => by
            -- Expose the degreewise endpoints of reindexing, without unfolding its category.
            change ((shiftFunctorAdd' C k n (n + k) (add_comm _ _)).inv.app X)⟦(1 : ℤ)⟧' ≫
                (shiftFunctorAdd' C (n + k) 1 (m + k) (by omega)).inv.app X =
              (shiftFunctorAdd' C n 1 m h).inv.app (X⟦k⟧) ≫
                (shiftFunctorAdd' C k m (m + k) (add_comm _ _)).inv.app X
            exact shiftFunctorAdd'_assoc_inv_app k n 1 (n + k) m (m + k)
              (add_comm _ _) h (by omega) X }
      inv :=
        { f := fun n => (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).hom.app X
          comm := fun n m h => by
            -- As above, align the component types before cancellation in the base category.
            change ((shiftFunctorAdd' C k n (n + k) (add_comm _ _)).hom.app X)⟦(1 : ℤ)⟧' ≫
                (shiftFunctorAdd' C n 1 m h).inv.app (X⟦k⟧) =
              (shiftFunctorAdd' C (n + k) 1 (m + k) (by omega)).inv.app X ≫
                (shiftFunctorAdd' C k m (m + k) (add_comm _ _)).hom.app X
            rw [← cancel_mono ((shiftFunctorAdd' C k m (m + k) (add_comm _ _)).inv.app X)]
            simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
            rw [← cancel_epi
              ((shiftFunctor C (1 : ℤ)).map
                ((shiftFunctorAdd' C k n (n + k) (add_comm _ _)).inv.app X))]
            simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
            dsimp only [Functor.comp_obj]
            erw [(shiftFunctor C (1 : ℤ)).map_id, Category.id_comp]
            exact (shiftFunctorAdd'_assoc_inv_app k n 1 (n + k) m (m + k)
              (add_comm _ _) h (by omega) X).symm }
      hom_inv_id := by ext n; simp [sequenceFunctor]
      inv_hom_id := by ext n; simp [sequenceFunctor] })
    (fun f => by
      ext n
      simpa [sequenceFunctor, Functor.comp_obj, Functor.comp_map,
        IntSequence.shiftFunctor_eq_reindex, IntSequence.reindex, IntSequence.comap] using
          (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).inv.naturality f)

/-- The forward shift comparison in degree `n` is the inverse addition constraint. -/
@[simp]
theorem sequenceFunctorShiftIso_hom_app_f (k : ℤ) (X : C) (n : ℤ) :
    ((sequenceFunctorShiftIso C k).hom.app X).f n =
      (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).inv.app X := (rfl)

/-- The inverse shift comparison in degree `n` is the addition constraint. -/
@[simp]
theorem sequenceFunctorShiftIso_inv_app_f (k : ℤ) (X : C) (n : ℤ) :
    ((sequenceFunctorShiftIso C k).inv.app X).f n =
      (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).hom.app X := (rfl)

/-- Forming the sequence of shifts commutes coherently with the integral shift. -/
noncomputable instance sequenceFunctorCommShift : (sequenceFunctor C).CommShift ℤ where
  commShiftIso := sequenceFunctorShiftIso C
  commShiftIso_zero := by
    ext X n
    simp only [sequenceFunctorShiftIso_hom_app_f, CommShift.isoZero_hom_app,
      IntSequence.comp_f, sequenceFunctor_map_f, IntSequence.shiftFunctorZero_inv_app_f]
    simp [shiftFunctorAdd', shiftFunctorAdd_zero_add_inv_app]
    rfl
  commShiftIso_add a b := by
    ext X n
    simp only [sequenceFunctorShiftIso_hom_app_f, CommShift.isoAdd_hom_app,
      IntSequence.comp_f, sequenceFunctor_map_f, IntSequence.shiftFunctorAdd_inv_app_f]
    -- Reindexing and composition endpoints reduce to components of the base shift.
    change (shiftFunctorAdd' C (a + b) n (n + (a + b)) (add_comm _ _)).inv.app X =
      ((shiftFunctorAdd C a b).hom.app X)⟦n⟧' ≫
        (shiftFunctorAdd' C b n (n + b) (add_comm _ _)).inv.app (X⟦a⟧) ≫
        (shiftFunctorAdd' C a (n + b) (n + b + a) (add_comm _ _)).inv.app X ≫
        eqToHom (congrArg (fun k : ℤ => X⟦k⟧) (by omega : n + b + a = n + (a + b)))
    rw [← cancel_epi (((shiftFunctorAdd C a b).inv.app X)⟦n⟧')]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    erw [(shiftFunctor C n).map_id, Category.id_comp]
    rw [← shiftFunctorAdd'_eq_shiftFunctorAdd C a b,
      shiftFunctorAdd'_assoc_inv_app a b n (a + b) (n + b) (n + (a + b))
        rfl (add_comm _ _) (by omega) X]
    simp [shiftFunctorAdd']

/-- The shift comparison for the canonical sequence functor is its reindexing comparison. -/
@[simp]
theorem sequenceFunctor_commShiftIso (k : ℤ) :
    (sequenceFunctor C).commShiftIso k = sequenceFunctorShiftIso C k := (rfl)

/-- Evaluation is naturally the inverse of the canonical sequence equivalence. -/
private noncomputable def evalIsoSequenceInverse :
    IntSequence.eval (e := shiftEquiv C (1 : ℤ)) ≅ (sequenceFunctor C).inv :=
  (sequenceFunctorCompEvalIso C).isoInverseComp
    (G := (sequenceFunctor C).asEquivalence) ≪≫
    Functor.rightUnitor (sequenceFunctor C).inv

/-- Evaluation of shift sequences commutes with the already installed shift on the category. -/
@[instance_reducible]
noncomputable def evalCommShift :
    (IntSequence.eval (e := shiftEquiv C (1 : ℤ))).CommShift ℤ := by
  letI : (sequenceFunctor C).asEquivalence.functor.CommShift ℤ :=
    inferInstanceAs ((sequenceFunctor C).CommShift ℤ)
  letI : (sequenceFunctor C).inv.CommShift ℤ :=
    (sequenceFunctor C).asEquivalence.commShiftInverse ℤ
  exact Functor.CommShift.ofIso (evalIsoSequenceInverse C).symm ℤ

/-- The counit of the canonical sequence/evaluation comparison respects integral shifts. -/
theorem sequenceFunctorCompEvalIso_commShift :
    let := evalCommShift C
    NatTrans.CommShift (sequenceFunctorCompEvalIso C).hom ℤ := by
  let : (sequenceFunctor C).asEquivalence.functor.CommShift ℤ :=
    inferInstanceAs ((sequenceFunctor C).CommShift ℤ)
  let : (sequenceFunctor C).inv.CommShift ℤ :=
    (sequenceFunctor C).asEquivalence.commShiftInverse ℤ
  let := (sequenceFunctor C).asEquivalence.commShift_of_functor ℤ
  let := evalCommShift C
  have : NatTrans.CommShift (evalIsoSequenceInverse C).hom ℤ := by
    have := Functor.CommShift.ofIso_compatibility (evalIsoSequenceInverse C).symm ℤ
    exact NatTrans.CommShift.of_iso_symm (evalIsoSequenceInverse C).symm ℤ
  have h : sequenceFunctorCompEvalIso C =
      Functor.isoWhiskerLeft (sequenceFunctor C) (evalIsoSequenceInverse C) ≪≫
        (sequenceFunctor C).asEquivalence.unitIso.symm := by
    ext X
    suffices (sequenceFunctorCompEvalIso C).hom.app X =
        ((sequenceFunctor C).asEquivalence.counitIso.inv.app ((sequenceFunctor C).obj X)).f 0 ≫
          (sequenceFunctorCompEvalIso C).hom.app
            ((sequenceFunctor C).asEquivalence.inverse.obj ((sequenceFunctor C).obj X)) ≫
              (sequenceFunctor C).asEquivalence.unitIso.inv.app X by
      simp only [evalIsoSequenceInverse, Iso.isoInverseComp, Functor.comp_obj,
        Functor.asEquivalence_functor, Iso.trans_hom, isoWhiskerLeft_hom,
        isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app, whiskerLeft_app,
        whiskerRight_app, Functor.associator_hom_app, Functor.leftUnitor_inv_app,
        Functor.rightUnitor_hom_app, IntSequence.eval_map, Category.id_comp, Category.assoc]
      erw [Category.comp_id, Category.assoc]
      exact this
    have hn := (sequenceFunctorCompEvalIso C).hom.naturality
      ((sequenceFunctor C).asEquivalence.unitIso.inv.app X)
    dsimp only [Functor.comp_map, Functor.id_map, IntSequence.eval_map] at hn
    -- The counit of the sequence equivalence is evaluated in degree zero.
    erw [← hn]
    have hc := congrArg (fun φ => φ.f 0)
      ((sequenceFunctor C).asEquivalence.counitIso_functor_comp X)
    simp only [IntSequence.comp_f, IntSequence.id_f, Functor.asEquivalence_functor] at hc
    erw [IntSequence.eval_map, ← Category.assoc, hc, Category.id_comp]
    rfl
  rw [h]
  dsimp only [Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

/-- Evaluation's degree-one comparison is the sequence's own linking isomorphism. -/
theorem evalCommShift_iso_one :
    letI := evalCommShift C
    (IntSequence.eval (e := shiftEquiv C (1 : ℤ))).commShiftIso (1 : ℤ) =
      IntSequence.reindexOneCompEvalIso := by
  let := evalCommShift C
  have := sequenceFunctorCompEvalIso_commShift C
  apply Iso.ext
  apply ((whiskeringLeft C (IntSequence (shiftEquiv C (1 : ℤ))) C).obj
    (sequenceFunctor C)).map_injective
  ext X
  have h := NatTrans.shift_app_comm (sequenceFunctorCompEvalIso C).hom (1 : ℤ) X
  rw [Functor.commShiftIso_comp_hom_app] at h
  rw [sequenceFunctor_commShiftIso] at h
  simp only [Functor.comp_obj, Functor.commShiftIso_id_hom_app,
    IntSequence.eval_map, sequenceFunctorShiftIso_hom_app_f,
    sequenceFunctorCompEvalIso_hom_app] at h
  erw [shiftFunctorAdd'_add_zero_inv_app, Category.comp_id] at h
  dsimp only [whiskeringLeft, whiskerLeft]
  rw [IntSequence.reindexOneCompEvalIso_hom_app, sequenceFunctor_obj_iso_inv]
  -- Whiskering evaluates the comparison at the canonical sequence of `X`.
  change (IntSequence.eval.commShiftIso (1 : ℤ)).hom.app ((sequenceFunctor C).obj X) =
    (shiftFunctorAdd' C 0 1 1 (by omega)).hom.app X
  rw [shiftFunctorAdd'_zero_add_hom_app]
  -- Give the component its explicit base-category type before cancelling structural maps.
  let β : X⟦(1 : ℤ)⟧ ⟶ (X⟦(0 : ℤ)⟧)⟦(1 : ℤ)⟧ :=
    (IntSequence.eval.commShiftIso (1 : ℤ)).hom.app ((sequenceFunctor C).obj X)
  have h' : ((shiftFunctorZero C ℤ).hom.app (X⟦(1 : ℤ)⟧) ≫ β) ≫
      ((shiftFunctorZero C ℤ).hom.app X)⟦(1 : ℤ)⟧' =
      (shiftFunctorZero C ℤ).hom.app (X⟦(1 : ℤ)⟧) := h
  have hb : β ≫ ((shiftFunctorZero C ℤ).hom.app X)⟦(1 : ℤ)⟧' = 𝟙 _ := by
    apply (cancel_epi ((shiftFunctorZero C ℤ).hom.app (X⟦(1 : ℤ)⟧))).1
    simpa only [Functor.id_obj, Category.assoc, Category.comp_id] using h'
  change β = ((shiftFunctorZero C ℤ).inv.app X)⟦(1 : ℤ)⟧'
  rw [← cancel_mono (((shiftFunctorZero C ℤ).hom.app X)⟦(1 : ℤ)⟧'), hb]
  simp [← Functor.map_comp]

end ExistingShift

variable {D : Type*} [Category* D] [HasShift D ℤ]

/-- An intertwining functor, reconstructed through the sequence models. -/
private noncomputable def intertwiningComparison (e : C ≌ C) (F : C ⥤ D)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) :
    (IntSequence.eval (e := e)).inv ⋙ IntSequence.mapFunctor (e' := shiftEquiv D (1 : ℤ)) α ⋙
        IntSequence.eval (e := shiftEquiv D (1 : ℤ)) ≅ F :=
  Functor.isoWhiskerLeft _
    (IntSequence.mapFunctorCompEvalIso (e' := shiftEquiv D (1 : ℤ)) α) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (IntSequence.eval (e := e)).asEquivalence.counitIso F ≪≫
    Functor.leftUnitor F

/-- A functor intertwining an autoequivalence with an existing shift by one commutes
coherently with the generated source shift and the existing target shift. -/
@[instance_reducible]
noncomputable def commShiftOfIntertwiningToShift (e : C ≌ C) (F : C ⥤ D)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) :
    letI := e.hasShift
    F.CommShift ℤ := by
  letI := e.hasShift
  letI : (IntSequence.eval (e := e)).asEquivalence.functor.CommShift ℤ := e.evalCommShift
  letI : (IntSequence.eval (e := e)).inv.CommShift ℤ :=
    (IntSequence.eval (e := e)).asEquivalence.commShiftInverse ℤ
  letI : (IntSequence.mapFunctor (e' := shiftEquiv D (1 : ℤ)) α).CommShift ℤ :=
    IntSequence.mapFunctorCommShift (e' := shiftEquiv D (1 : ℤ)) α
  letI := evalCommShift D
  exact Functor.CommShift.ofIso (intertwiningComparison C e F α) ℤ

/-- In degree one, the coherent comparison recovers the supplied intertwining isomorphism,
preceded by the identification of the generated source shift with its autoequivalence. -/
theorem commShiftOfIntertwiningToShift_iso_one (e : C ≌ C) (F : C ⥤ D)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) :
    letI := e.hasShift
    letI := commShiftOfIntertwiningToShift C e F α
    F.commShiftIso (1 : ℤ) = isoWhiskerRight e.shiftFunctorOneIso F ≪≫ α := by
  let := e.hasShift
  let : (IntSequence.eval (e := e)).asEquivalence.functor.CommShift ℤ := e.evalCommShift
  let : (IntSequence.eval (e := e)).inv.CommShift ℤ :=
    (IntSequence.eval (e := e)).asEquivalence.commShiftInverse ℤ
  let : (IntSequence.eval (e := e)).asEquivalence.inverse.CommShift ℤ :=
    (IntSequence.eval (e := e)).asEquivalence.commShiftInverse ℤ
  let := (IntSequence.eval (e := e)).asEquivalence.commShift_of_functor ℤ
  let : (IntSequence.mapFunctor (e' := shiftEquiv D (1 : ℤ)) α).CommShift ℤ :=
    IntSequence.mapFunctorCommShift (e' := shiftEquiv D (1 : ℤ)) α
  let := evalCommShift D
  let := commShiftOfIntertwiningToShift C e F α
  apply Iso.ext
  ext X
  let _ := e.evalCommShift
  let U := (IntSequence.eval (e := e)).inv
  let c := (IntSequence.eval (e := e)).asEquivalence.counitIso
  have he := congr_app (congrArg Iso.hom e.evalCommShiftIso_one) (U.obj X)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, IntSequence.reindexOneCompEvalIso_hom_app] at he
  have hc := Adjunction.commShiftIso_hom_app_counit_app_shift
    (IntSequence.eval (e := e)).asEquivalence.toAdjunction ℤ (1 : ℤ) X
  rw [Functor.commShiftIso_comp_hom_app] at hc
  simp only [Functor.asEquivalence_functor, Functor.asEquivalence_inverse,
    Equivalence.toAdjunction_counit, IntSequence.eval_map] at hc
  have he' : ((IntSequence.eval (e := e)).commShiftIso (1 : ℤ)).hom.app (U.obj X) ≫
      e.shiftFunctorOneIso.hom.app ((U.obj X).X 0) =
      ((U.obj X).iso 0 1 rfl).inv := he
  have hc' : (((U.commShiftIso (1 : ℤ)).hom.app X).f 0) ≫
      ((IntSequence.eval (e := e)).commShiftIso (1 : ℤ)).hom.app (U.obj X) =
      c.hom.app (X⟦(1 : ℤ)⟧) ≫ (c.inv.app X)⟦(1 : ℤ)⟧' :=
    (Iso.eq_comp_inv ((shiftFunctor C (1 : ℤ)).mapIso (c.app X))).2 hc
  have hu : (((U.commShiftIso (1 : ℤ)).hom.app X).f 0) ≫
      ((U.obj X).iso 0 1 rfl).inv =
      c.hom.app (X⟦(1 : ℤ)⟧) ≫ (c.inv.app X)⟦(1 : ℤ)⟧' ≫
        e.shiftFunctorOneIso.hom.app ((U.obj X).X 0) :=
    (congrArg ((((U.commShiftIso (1 : ℤ)).hom.app X).f 0) ≫ ·) he'.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ e.shiftFunctorOneIso.hom.app ((U.obj X).X 0)) hc').trans
          (Category.assoc _ _ _)))
  let α' : e.functor ⋙ F ≅ F ⋙ (shiftEquiv D (1 : ℤ)).functor := α
  -- Expand only the public transport and component formulas; the inverse evaluation
  -- comparison is determined above by compatibility with its counit.
  change ((Functor.CommShift.ofIso (intertwiningComparison C e F α') ℤ).commShiftIso
    (1 : ℤ)).hom.app X = _
  rw [Functor.CommShift.ofIso_commShiftIso_hom_app]
  simp only [Functor.commShiftIso_comp_hom_app, evalCommShift_iso_one,
    IntSequence.eval_map, IntSequence.reindexOneCompEvalIso_hom_app]
  rw [mapFunctor_commShiftIso]
  simp only [IntSequence.mapFunctorShiftIso_hom_app_f]
  simp only [intertwiningComparison, Iso.trans_hom, Iso.trans_inv, isoWhiskerLeft_hom,
    isoWhiskerLeft_inv, isoWhiskerRight_hom, isoWhiskerRight_inv, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    IntSequence.mapFunctorCompEvalIso_hom_app, IntSequence.mapFunctorCompEvalIso_inv_app,
    Category.id_comp, Functor.comp_obj, IntSequence.mapFunctor_obj_iso_inv, Category.assoc]
  simp only [Iso.symm_inv, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_map, IntSequence.eval_map,
    IntSequence.mapFunctor_map_f]
  -- Evaluation and reindexing have definitionally equal endpoints; align them before
  -- cancelling the identity components of the comparison.
  erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.id_comp,
    Category.id_comp, Category.id_comp]
  let u : (U.obj X).X 0 ≅ X := c.app X
  let u₁ : (U.obj (X⟦(1 : ℤ)⟧)).X 0 ≅ X⟦(1 : ℤ)⟧ := c.app (X⟦(1 : ℤ)⟧)
  let β : (U.obj (X⟦(1 : ℤ)⟧)).X 0 ⟶ (U.obj X).X 1 :=
    ((U.commShiftIso (1 : ℤ)).hom.app X).f 0
  change F.map u₁.inv ≫ F.map β ≫
      (F.map ((U.obj X).iso 0 1 rfl).inv ≫ α.hom.app ((U.obj X).X 0)) ≫
        (F.map u.hom)⟦(1 : ℤ)⟧' = _
  simp only [Category.assoc]
  rw [← F.map_comp_assoc β ((U.obj X).iso 0 1 rfl).inv]
  have hβ : β ≫ ((U.obj X).iso 0 1 rfl).inv =
      u₁.hom ≫ u.inv⟦(1 : ℤ)⟧' ≫ e.shiftFunctorOneIso.hom.app ((U.obj X).X 0) := hu
  rw [hβ]
  simp only [F.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
  have hn := (isoWhiskerRight e.shiftFunctorOneIso F ≪≫ α).hom.naturality u.inv
  simp only [Iso.trans_hom, isoWhiskerRight_hom, NatTrans.comp_app,
    whiskerRight_app, Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp, Iso.inv_hom_id]
  erw [F.map_id, (shiftFunctor D (1 : ℤ)).map_id, Category.comp_id]

end TauCeti.Shift
