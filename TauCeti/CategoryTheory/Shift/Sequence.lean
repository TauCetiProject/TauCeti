/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import TauCeti.CategoryTheory.Shift.Autoequivalence

/-!
# Integer sequences from an existing shift

A category with an integral shift has a canonical sequence `n ↦ X⟦n⟧` for each object.
These sequences are linked by the shift by one. This realizes the category as the sequence
model of its generating autoequivalence, compatibly with all integral shifts. It lets one
compare a shift constructed from an autoequivalence with an already installed shift, without
replacing the latter.

The sequence model and its evaluation equivalence are those of
`CategoryTheory.Equivalence.IntSequence`.

## Main definitions

* `TauCeti.Shift.sequenceFunctor`: the sequence of existing shifts of an object.
* `TauCeti.Shift.evalCommShiftOfHasShift`: evaluation respects the existing shift.

## Main results

* `TauCeti.Shift.sequenceFunctorCompEvalIso_commShift`: evaluation's counit respects shifts.
* `TauCeti.Shift.evalCommShiftOfHasShift_iso_one`: evaluation's degree-one comparison is
  the linking isomorphism of the sequence.
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
-- The public evaluation and reindexing equations below compare morphisms whose endpoints
-- are components of this functor with morphisms between literal shifts. Lean's module system
-- needs this body exposed to type those equations; object-equality lemmas would require
-- `eqToHom` transports in their statements, even when the proofs use `:= (rfl)`.
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
    intSequenceIsoMk
      (fun n => (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).symm.app X)
      (fun n m h => by
        -- Expose the degreewise endpoints of reindexing, without unfolding its category.
        change ((shiftFunctorAdd' C k n (n + k) (add_comm _ _)).inv.app X)⟦(1 : ℤ)⟧' ≫
            (shiftFunctorAdd' C (n + k) 1 (m + k) (by omega)).inv.app X =
          (shiftFunctorAdd' C n 1 m h).inv.app (X⟦k⟧) ≫
            (shiftFunctorAdd' C k m (m + k) (add_comm _ _)).inv.app X
        exact shiftFunctorAdd'_assoc_inv_app k n 1 (n + k) m (m + k)
          (add_comm _ _) h (by omega) X))
    (fun f => by
      ext n
      simp only [IntSequence.comp_f]
      dsimp only [Functor.comp_obj, Functor.comp_map, sequenceFunctor,
        IntSequence.shiftFunctor_eq_reindex, IntSequence.reindex, IntSequence.comap]
      -- The component endpoints use the reindexed sequence; `erw` unfolds its shift functor
      -- to identify them with the explicit `(n + k)` shifts in `intSequenceIsoMk`.
      erw [intSequenceIsoMk_hom_f, intSequenceIsoMk_hom_f]
      exact (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).inv.naturality f)

/-- The forward shift comparison in degree `n` is the inverse addition constraint. -/
@[simp]
theorem sequenceFunctorShiftIso_hom_app_f (k : ℤ) (X : C) (n : ℤ) :
    ((sequenceFunctorShiftIso C k).hom.app X).f n =
      (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).inv.app X := by
  unfold sequenceFunctorShiftIso
  dsimp only [NatIso.ofComponents_hom_app]
  exact intSequenceIsoMk_hom_f _ _ _

/-- The inverse shift comparison in degree `n` is the addition constraint. -/
@[simp]
theorem sequenceFunctorShiftIso_inv_app_f (k : ℤ) (X : C) (n : ℤ) :
    ((sequenceFunctorShiftIso C k).inv.app X).f n =
      (shiftFunctorAdd' C k n (n + k) (add_comm _ _)).hom.app X := by
  unfold sequenceFunctorShiftIso
  dsimp only [NatIso.ofComponents_inv_app]
  exact intSequenceIsoMk_inv_f _ _ _

/-- Forming the sequence of shifts commutes coherently with the integral shift. -/
noncomputable instance sequenceFunctorCommShift : (sequenceFunctor C).CommShift ℤ where
  commShiftIso := sequenceFunctorShiftIso C
  commShiftIso_zero := by
    ext X n
    simp only [sequenceFunctorShiftIso_hom_app_f, CommShift.isoZero_hom_app,
      IntSequence.comp_f, sequenceFunctor_map_f, IntSequence.shiftFunctorZero_inv_app_f]
    -- Reindexing by zero leaves an equality transport on the component endpoint.
    change (shiftFunctorAdd' C 0 n (n + 0) (add_comm _ _)).inv.app X =
      ((shiftFunctorZero C ℤ).hom.app X)⟦n⟧' ≫
        eqToHom (congrArg (fun k : ℤ => X⟦k⟧) (by omega : n = n + 0))
    simp [shiftFunctorAdd', shiftFunctorAdd_zero_add_inv_app]
  commShiftIso_add a b := by
    ext X n
    simp only [sequenceFunctorShiftIso_hom_app_f, CommShift.isoAdd_hom_app,
      IntSequence.comp_f, sequenceFunctor_map_f, IntSequence.shiftFunctorAdd_inv_app_f]
    simp only [IntSequence.shiftFunctor_eq_reindex, IntSequence.reindex, IntSequence.comap,
      sequenceFunctorShiftIso_hom_app_f]
    -- Reindexing and composition endpoints reduce to components of the base shift.
    change (shiftFunctorAdd' C (a + b) n (n + (a + b)) (add_comm _ _)).inv.app X =
      ((shiftFunctorAdd C a b).hom.app X)⟦n⟧' ≫
        (shiftFunctorAdd' C b n (n + b) (add_comm _ _)).inv.app (X⟦a⟧) ≫
        (shiftFunctorAdd' C a (n + b) (n + b + a) (add_comm _ _)).inv.app X ≫
        eqToHom (congrArg (fun k : ℤ => X⟦k⟧) (by omega : n + b + a = n + (a + b)))
    rw [← cancel_epi (((shiftFunctorAdd C a b).inv.app X)⟦n⟧')]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    -- Cancellation leaves the identity at a composite shift-functor object; reduce
    -- that endpoint before applying the shift functor identity law.
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
noncomputable def evalCommShiftOfHasShift :
    (IntSequence.eval (e := shiftEquiv C (1 : ℤ))).CommShift ℤ := by
  letI : (sequenceFunctor C).asEquivalence.functor.CommShift ℤ :=
    inferInstanceAs ((sequenceFunctor C).CommShift ℤ)
  letI : (sequenceFunctor C).inv.CommShift ℤ :=
    (sequenceFunctor C).asEquivalence.commShiftInverse ℤ
  exact Functor.CommShift.ofIso (evalIsoSequenceInverse C).symm ℤ

/-- The counit of the canonical sequence/evaluation comparison respects integral shifts. -/
theorem sequenceFunctorCompEvalIso_commShift :
    let := evalCommShiftOfHasShift C
    NatTrans.CommShift (sequenceFunctorCompEvalIso C).hom ℤ := by
  let : (sequenceFunctor C).asEquivalence.functor.CommShift ℤ :=
    inferInstanceAs ((sequenceFunctor C).CommShift ℤ)
  let : (sequenceFunctor C).inv.CommShift ℤ :=
    (sequenceFunctor C).asEquivalence.commShiftInverse ℤ
  let := (sequenceFunctor C).asEquivalence.commShift_of_functor ℤ
  let := evalCommShiftOfHasShift C
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
      -- Inverse evaluation is the chosen inverse functor; reduce its object endpoints to
      -- cancel the right-unitor identity and associate the evaluated components.
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
    -- The inverse and `asEquivalence.inverse` endpoints agree after reducing the wrappers;
    -- evaluation then exposes the degree-zero component of the triangle identity.
    erw [IntSequence.eval_map, ← Category.assoc, hc, Category.id_comp]
    -- After the triangle identity, both sides are the zero-shift counit at `X`.
    change (shiftFunctorZero C ℤ).hom.app X = (shiftFunctorZero C ℤ).hom.app X
    rfl
  rw [h]
  dsimp only [Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

/-- Evaluation's degree-one comparison is the sequence's own linking isomorphism. -/
theorem evalCommShiftOfHasShift_iso_one :
    letI := evalCommShiftOfHasShift C
    (IntSequence.eval (e := shiftEquiv C (1 : ℤ))).commShiftIso (1 : ℤ) =
      IntSequence.reindexOneCompEvalIso := by
  let := evalCommShiftOfHasShift C
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
  -- The component formula uses `0 + 1`, which reduces to `1` at this degree.
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

end TauCeti.Shift
