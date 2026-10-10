/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Shift.Sequence

/-!
# Functors intertwining autoequivalences

An isomorphism `e.functor ⋙ F ≅ F ⋙ e'.functor` says that a functor intertwines two
autoequivalences. Applying `F` degreewise to their integer-sequence models commutes coherently
with the reindexing shift. This file constructs that degreewise functor and its
`Functor.CommShift ℤ` structure.

The construction uses the strict models of autoequivalence-generated shifts from
`CategoryTheory.Equivalence.IntSequence`. Applying `F` degreewise sends an `e`-sequence to an
`e'`-sequence, and this functor commutes strictly with reindexing. The compatibility can then be
transported back along evaluation in degree zero; this yields
`TauCeti.Shift.commShiftOfIntertwiningToShift`, which retains the target's already installed
shift while using the autoequivalence-generated source shift.

## Main definitions

* `CategoryTheory.Equivalence.IntSequence.mapFunctor`: apply an intertwining functor degreewise
  to an integer sequence.
* `CategoryTheory.Equivalence.IntSequence.mapFunctorCommShift`: coherent compatibility with
  reindexing.
* `TauCeti.Shift.commShiftOfIntertwiningToShift`: integral shift compatibility from the
  degree-one intertwining isomorphism.

## Main results

* `TauCeti.Shift.commShiftOfIntertwiningToShift_iso_one`: the comparison in degree one
  recovers the supplied intertwining isomorphism.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence.IntSequence

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {e : C ≌ C} {e' : D ≌ D} {F : C ⥤ D}

/-- Applying a functor degreewise to integer sequences, using an isomorphism saying that the
functor intertwines the generating autoequivalences. -/
@[expose, simps!]
def mapFunctor (α : e.functor ⋙ F ≅ F ⋙ e'.functor) : IntSequence e ⥤ IntSequence e' where
  obj X :=
    { X := fun n ↦ F.obj (X.X n)
      iso := fun n m h ↦ (α.app (X.X n)).symm ≪≫ F.mapIso (X.iso n m h) }
  map := fun {X Y} φ ↦
    { f := fun n ↦ F.map (φ.f n)
      comm := fun n m h ↦ by
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
        have hα : e'.functor.map (F.map (φ.f n)) ≫ (α.app (Y.X n)).inv =
            (α.app (X.X n)).inv ≫ F.map (e.functor.map (φ.f n)) := by
          simpa only [Functor.comp_map, Iso.app_inv] using α.inv.naturality (φ.f n)
        rw [← Category.assoc, hα]
        simp only [Category.assoc, ← F.map_comp, φ.comm]
      }
  map_id X := by apply hom_ext; intro n; exact F.map_id _
  map_comp φ ψ := by apply hom_ext; intro n; exact F.map_comp _ _

/-- Evaluation in degree zero after applying `mapFunctor` is applying the original functor after
evaluation. -/
def mapFunctorCompEvalIso (α : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    mapFunctor α ⋙ eval (e := e') ≅ eval (e := e) ⋙ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp [mapFunctor, eval])

@[simp]
theorem mapFunctorCompEvalIso_hom_app (α : e.functor ⋙ F ≅ F ⋙ e'.functor)
    (X : IntSequence e) : (mapFunctorCompEvalIso α).hom.app X = 𝟙 _ :=
  by
    -- Unfold locally to establish the component API while keeping the construction opaque.
    change (Iso.refl _).hom = _
    simp

@[simp]
theorem mapFunctorCompEvalIso_inv_app (α : e.functor ⋙ F ≅ F ⋙ e'.functor)
    (X : IntSequence e) : (mapFunctorCompEvalIso α).inv.app X = 𝟙 _ :=
  by
    -- This is the inverse component of the same locally unfolded identity isomorphism.
    change (Iso.refl _).inv = _
    change 𝟙 (F.obj (X.X 0)) = _
    change 𝟙 (F.obj (X.X 0)) = 𝟙 (F.obj (X.X 0))
    exact (Category.comp_id _).symm.trans (Category.id_comp _)

/-- Applying an intertwining functor degreewise commutes with the reindexing shift. -/
def mapFunctorShiftIso (α : e.functor ⋙ F ≅ F ⋙ e'.functor) (k : ℤ) :
    shiftFunctor (IntSequence e) k ⋙ mapFunctor α ≅
      mapFunctor α ⋙ shiftFunctor (IntSequence e') k :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    ext n
    -- The generated component lemmas for the two composite functors do not rewrite beneath
    -- `IntSequence.Hom.f`; reduction exposes those components, after which the goal is categorical.
    change F.map (f.f (n + k)) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (f.f (n + k))
    simp)

@[simp]
theorem mapFunctorShiftIso_hom_app_f (α : e.functor ⋙ F ≅ F ⋙ e'.functor) (k : ℤ)
    (X : IntSequence e) (n : ℤ) :
    ((mapFunctorShiftIso α k).hom.app X).f n = 𝟙 (F.obj (X.X (n + k))) :=
  by
    -- Unfold locally to establish the component API while keeping the construction opaque.
    change ((𝟙 ((shiftFunctor (IntSequence e) k ⋙ mapFunctor α).obj X) :
      ((shiftFunctor (IntSequence e) k ⋙ mapFunctor α).obj X) ⟶
        ((shiftFunctor (IntSequence e) k ⋙ mapFunctor α).obj X)).f n) = _
    rw [id_f]
    change 𝟙 (F.obj (((reindex k).obj X).X n)) = _
    change 𝟙 (F.obj (X.X (n + k))) = 𝟙 (F.obj (X.X (n + k)))
    exact (Category.comp_id _).symm.trans (Category.id_comp _)

@[simp]
theorem mapFunctorShiftIso_inv_app_f (α : e.functor ⋙ F ≅ F ⋙ e'.functor) (k : ℤ)
    (X : IntSequence e) (n : ℤ) :
    ((mapFunctorShiftIso α k).inv.app X).f n = 𝟙 (F.obj (X.X (n + k))) :=
  by
    -- This is the inverse component of the same locally unfolded identity isomorphism.
    change ((𝟙 ((shiftFunctor (IntSequence e) k ⋙ mapFunctor α).obj X) :
      ((shiftFunctor (IntSequence e) k ⋙ mapFunctor α).obj X) ⟶
        ((shiftFunctor (IntSequence e) k ⋙ mapFunctor α).obj X)).f n) = _
    rw [id_f]
    change 𝟙 (F.obj (((reindex k).obj X).X n)) = _
    change 𝟙 (F.obj (X.X (n + k))) = 𝟙 (F.obj (X.X (n + k)))
    exact (Category.comp_id _).symm.trans (Category.id_comp _)

private lemma shiftFunctorZero_inv_app_mapFunctor_f
    (α : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : IntSequence e) (n : ℤ) :
    ((shiftFunctorZero (IntSequence e') ℤ).inv.app ((mapFunctor α).obj X)).f n =
      F.map (eqToHom (congrArg X.X (show n = n + 0 by omega))) := by
  simp only [shiftFunctorZero_inv_app_f]
  exact (eqToHom_map F (congrArg X.X (show n = n + 0 by omega))).symm

private lemma shiftFunctorAdd_inv_app_mapFunctor_f
    (α : e.functor ⋙ F ≅ F ⋙ e'.functor) (a b : ℤ) (X : IntSequence e) (n : ℤ) :
    ((shiftFunctorAdd (IntSequence e') a b).inv.app ((mapFunctor α).obj X)).f n =
      F.map (eqToHom (congrArg X.X (show n + b + a = n + (a + b) by omega))) := by
  simp only [shiftFunctorAdd_inv_app_f]
  exact (eqToHom_map F
    (congrArg X.X (show n + b + a = n + (a + b) by omega))).symm

private lemma mapFunctor_map_shiftFunctorZero_hom_app_f
    (α : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : IntSequence e) (n : ℤ) :
    ((mapFunctor α).map ((shiftFunctorZero (IntSequence e) ℤ).hom.app X)).f n =
      F.map (eqToHom (congrArg X.X (show n + 0 = n by omega))) := by
  rw [mapFunctor_map_f, shiftFunctorZero_hom_app_f]
  congr 1

private lemma mapFunctor_map_shiftFunctorAdd_hom_app_f
    (α : e.functor ⋙ F ≅ F ⋙ e'.functor) (a b : ℤ) (X : IntSequence e)
    (n : ℤ) :
    ((mapFunctor α).map ((shiftFunctorAdd (IntSequence e) a b).hom.app X)).f n =
      F.map (eqToHom (congrArg X.X (show n + (a + b) = n + b + a by omega))) := by
  rw [mapFunctor_map_f, shiftFunctorAdd_hom_app_f]
  congr 1

/-- The degreewise functor associated to an intertwining functor commutes coherently with
reindexing. -/
noncomputable instance mapFunctorCommShift
    (α : e.functor ⋙ F ≅ F ⋙ e'.functor) : (mapFunctor α).CommShift ℤ where
  commShiftIso := mapFunctorShiftIso α
  commShiftIso_zero := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rw [Functor.CommShift.isoZero_hom_app]
    apply hom_ext
    intro n
    simp only [mapFunctorShiftIso_hom_app_f, comp_f,
      mapFunctor_map_shiftFunctorZero_hom_app_f, shiftFunctorZero_inv_app_mapFunctor_f]
    -- The component lemmas above expose every structural map. Only the source of the identity
    -- remains displayed with two propositionally equal integer expressions, so no rewrite lemma
    -- can state the required typed identity without making the same arithmetic transport explicit.
    change 𝟙 (F.obj (X.X (n + 0))) = _
    erw [← F.map_comp, ← F.map_id]
    congr 1
    rw [eqToHom_trans]
    simp
  commShiftIso_add a b := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rw [Functor.CommShift.isoAdd_hom_app]
    apply hom_ext
    intro n
    simp only [comp_f]
    simp only [mapFunctorShiftIso_hom_app_f, mapFunctor_map_shiftFunctorAdd_hom_app_f,
      shiftFunctorAdd_inv_app_mapFunctor_f]
    -- As in the zero case, this `change` only aligns the dependent type of the identity after all
    -- shift structure has been rewritten by the component API above.
    change 𝟙 (F.obj (X.X (n + (a + b)))) = _
    erw [Category.id_comp, Category.id_comp]
    erw [← F.map_comp, ← F.map_id]
    congr 1
    rw [eqToHom_trans]
    simp

end CategoryTheory.Equivalence.IntSequence

namespace TauCeti.Shift

open CategoryTheory CategoryTheory.Equivalence CategoryTheory.Equivalence.IntSequence

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {e : C ≌ C} {e' : D ≌ D} {F : C ⥤ D}

/-- The shift comparison for a degreewise intertwining functor is its reindexing comparison. -/
@[simp]
theorem intSequenceMapFunctor_commShiftIso (α : e.functor ⋙ F ≅ F ⋙ e'.functor) (k : ℤ) :
    (mapFunctor α).commShiftIso k = mapFunctorShiftIso α k := (rfl)

end TauCeti.Shift

namespace TauCeti.Shift

open CategoryTheory CategoryTheory.Functor CategoryTheory.Equivalence

variable (C : Type u₁) [Category.{v₁} C]

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

private theorem intertwiningComparison_hom_app (e : C ≌ C) (F : C ⥤ D)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) (X : C) :
    (intertwiningComparison C e F α).hom.app X =
      F.map ((IntSequence.eval (e := e)).asEquivalence.counitIso.hom.app X) := by
  simp only [Functor.comp_obj, intertwiningComparison, Functor.asEquivalence_functor,
    Iso.trans_hom, isoWhiskerLeft_hom, Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app,
    whiskerLeft_app, Functor.associator_inv_app, Functor.id_obj, whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp]
  -- The degree-zero evaluation comparison is an identity with reducibly equal endpoints.
  erw [IntSequence.mapFunctorCompEvalIso_hom_app, Category.id_comp]

private theorem intertwiningComparison_inv_app (e : C ≌ C) (F : C ⥤ D)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) (X : C) :
    (intertwiningComparison C e F α).inv.app X =
      F.map ((IntSequence.eval (e := e)).asEquivalence.counitIso.inv.app X) := by
  simp only [Functor.comp_obj, intertwiningComparison, Functor.asEquivalence_functor,
    Iso.trans_inv, isoWhiskerRight_inv, Iso.symm_inv, Category.assoc, isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.id_obj, Functor.leftUnitor_inv_app, whiskerRight_app,
    Functor.associator_hom_app, whiskerLeft_app, Category.id_comp]
  -- As above, align evaluation endpoints to use the inverse component identity.
  erw [IntSequence.mapFunctorCompEvalIso_inv_app, Category.comp_id]

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
  letI := evalCommShiftOfHasShift D
  exact Functor.CommShift.ofIso (intertwiningComparison C e F α) ℤ

/-- The inverse evaluation comparison is determined by its compatibility with the counit. -/
private theorem evalInverseCommShiftIso_one_hom_app_f_zero (e : C ≌ C) (X : C) :
    letI := e.hasShift
    letI : (IntSequence.eval (e := e)).asEquivalence.functor.CommShift ℤ := e.evalCommShift
    letI : (IntSequence.eval (e := e)).inv.CommShift ℤ :=
      (IntSequence.eval (e := e)).asEquivalence.commShiftInverse ℤ
    let U := (IntSequence.eval (e := e)).inv
    let c := (IntSequence.eval (e := e)).asEquivalence.counitIso
    (((U.commShiftIso (1 : ℤ)).hom.app X).f 0) ≫ ((U.obj X).iso 0 1 rfl).inv =
      c.hom.app (X⟦(1 : ℤ)⟧) ≫ (c.inv.app X)⟦(1 : ℤ)⟧' ≫
        e.shiftFunctorOneIso.hom.app ((U.obj X).X 0) := by
  let := e.hasShift
  let : (IntSequence.eval (e := e)).asEquivalence.functor.CommShift ℤ := e.evalCommShift
  let : (IntSequence.eval (e := e)).inv.CommShift ℤ :=
    (IntSequence.eval (e := e)).asEquivalence.commShiftInverse ℤ
  let : (IntSequence.eval (e := e)).asEquivalence.inverse.CommShift ℤ :=
    inferInstanceAs ((IntSequence.eval (e := e)).inv.CommShift ℤ)
  let := (IntSequence.eval (e := e)).asEquivalence.commShift_of_functor ℤ
  let : (IntSequence.eval (e := e)).CommShift ℤ :=
    inferInstanceAs ((IntSequence.eval (e := e)).asEquivalence.functor.CommShift ℤ)
  let U := (IntSequence.eval (e := e)).inv
  let c := (IntSequence.eval (e := e)).asEquivalence.counitIso
  -- Expand the statement's local names for inverse evaluation and its counit.
  dsimp only []
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
  -- Reindexing by one evaluates at degree one; `erw` aligns this endpoint.
  erw [← he', ← Category.assoc, hc', Category.assoc]
  -- Only the local abbreviations for inverse evaluation and its counit remain.
  rfl

/-- Conjugating the degree-one comparison by an object isomorphism uses its naturality. -/
private theorem shiftFunctorOneIso_conj (e : C ≌ C) (F : C ⥤ D)
    (α : e.functor ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) {X Y : C} (u : X ≅ Y) :
    letI := e.hasShift
    F.map (u.inv⟦(1 : ℤ)⟧') ≫ F.map (e.shiftFunctorOneIso.hom.app X) ≫
      α.hom.app X ≫ (F.map u.hom)⟦(1 : ℤ)⟧' =
        F.map (e.shiftFunctorOneIso.hom.app Y) ≫ α.hom.app Y := by
  let := e.hasShift
  have hn := (isoWhiskerRight e.shiftFunctorOneIso F ≪≫ α).hom.naturality u.inv
  simp only [Iso.trans_hom, isoWhiskerRight_hom, NatTrans.comp_app,
    whiskerRight_app, Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp, Iso.inv_hom_id]
  -- Naturality and inverse cancellation leave identities at composite-functor endpoints;
  -- reduce those endpoints to apply the two functor identity laws.
  erw [F.map_id, (shiftFunctor D (1 : ℤ)).map_id, Category.comp_id]

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
    inferInstanceAs ((IntSequence.eval (e := e)).inv.CommShift ℤ)
  let := (IntSequence.eval (e := e)).asEquivalence.commShift_of_functor ℤ
  let : (IntSequence.mapFunctor (e' := shiftEquiv D (1 : ℤ)) α).CommShift ℤ :=
    IntSequence.mapFunctorCommShift (e' := shiftEquiv D (1 : ℤ)) α
  let := evalCommShiftOfHasShift D
  let := commShiftOfIntertwiningToShift C e F α
  apply Iso.ext
  ext X
  -- Expand the transported comparison, use the inverse-evaluation counit identity,
  -- then conjugate the supplied degree-one isomorphism by that counit.
  let U := (IntSequence.eval (e := e)).inv
  let c := (IntSequence.eval (e := e)).asEquivalence.counitIso
  have hu := evalInverseCommShiftIso_one_hom_app_f_zero C e X
  -- `shiftEquiv`'s forward functor is the existing shift by one.
  let α' : e.functor ⋙ F ≅ F ⋙ (shiftEquiv D (1 : ℤ)).functor := α
  -- Expand only the public transport and component formulas; the inverse evaluation
  -- comparison is determined above by compatibility with its counit.
  change ((Functor.CommShift.ofIso (intertwiningComparison C e F α') ℤ).commShiftIso
    (1 : ℤ)).hom.app X = _
  rw [Functor.CommShift.ofIso_commShiftIso_hom_app]
  simp only [Functor.commShiftIso_comp_hom_app, evalCommShiftOfHasShift_iso_one,
    IntSequence.eval_map, IntSequence.reindexOneCompEvalIso_hom_app]
  rw [intSequenceMapFunctor_commShiftIso]
  simp only [IntSequence.mapFunctorShiftIso_hom_app_f]
  rw [intertwiningComparison_inv_app, intertwiningComparison_hom_app]
  simp only [Functor.comp_map, IntSequence.eval_map, IntSequence.mapFunctor_map_f,
    IntSequence.mapFunctor_obj_iso_inv]
  -- The degreewise reindexing comparison is an identity in the common component category.
  erw [Category.id_comp]
  let u : (U.obj X).X 0 ≅ X := c.app X
  let u₁ : (U.obj (X⟦(1 : ℤ)⟧)).X 0 ≅ X⟦(1 : ℤ)⟧ := c.app (X⟦(1 : ℤ)⟧)
  let β : (U.obj (X⟦(1 : ℤ)⟧)).X 0 ⟶ (U.obj X).X 1 :=
    ((U.commShiftIso (1 : ℤ)).hom.app X).f 0
  -- The counit components identify the zero terms with the original objects.
  change F.map u₁.inv ≫
      (F.map β ≫ F.map ((U.obj X).iso 0 1 rfl).inv ≫ α.hom.app ((U.obj X).X 0)) ≫
        (F.map u.hom)⟦(1 : ℤ)⟧' = _
  simp only [Category.assoc]
  rw [← F.map_comp_assoc β ((U.obj X).iso 0 1 rfl).inv]
  -- Express `hu` through the proof-local component and counit names; only these local
  -- abbreviations are expanded, without unfolding the inverse-evaluation construction.
  have hβ : β ≫ ((U.obj X).iso 0 1 rfl).inv =
      u₁.hom ≫ u.inv⟦(1 : ℤ)⟧' ≫ e.shiftFunctorOneIso.hom.app ((U.obj X).X 0) := hu
  rw [hβ]
  simp only [F.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
  exact shiftFunctorOneIso_conj C e F α u

end TauCeti.Shift
