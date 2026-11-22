/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
public import TauCeti.CategoryTheory.Semisimple.UnitSummands.Basic

/-!
# The universal grading groupoid of a multitensor category

In a finite semisimple monoidal category `C` with `[MonoidalPreadditive C]`, `𝟙_ C` decomposes into
pairwise orthogonal simple summands indexed by `TauCeti.UnitSimpleClasses C`. Rather than a group,
the natural universal invariant of the fusion rules is the *groupoid*
`TauCeti.universalGradingGroupoid C` (Penneys, Definition 3.16; EGNO, §4.14): objects correspond to
`UnitSimpleClasses C` via `mkObj`, and each simple class `S : SimpleClasses C` has a generator
`degree S : mkObj (leftUnitClass S.repr) ⟶ mkObj (rightUnitClass S.repr)` modulo the relation that
every nonzero `U.repr ⟶ S.repr ⊗ T.repr` equates `degree U` with `degree S ≫ degree T` (up to
`eqToHom` endpoint transports). Duality and rigidity results live in
`TauCeti/CategoryTheory/Monoidal/Grading/Groupoid/Rigid.lean`.

## Main declarations

* `TauCeti.universalGradingGroupoid`: the universal grading groupoid of `C`.
* `TauCeti.universalGradingGroupoid.mkObj`: bijection between `UnitSimpleClasses C` and the objects
  of `universalGradingGroupoid C`.
* `TauCeti.universalGradingGroupoid.degree`, `TauCeti.universalGradingGroupoid.degreeOf`: the
  universal grading morphism of a simple class or simple object, with multiplication laws
  `degree_comp` and `degreeOf_comp` and unit law `degree_unitSummand`.
* `TauCeti.universalGradingGroupoid.hom_induction`: presentation-independent induction principle
  for morphisms of `universalGradingGroupoid C`.
* `TauCeti.GroupoidGrading`, `TauCeti.GroupoidGrading.degOf`,
  `TauCeti.universalGradingGroupoid.liftEquiv`: universal property identifying gradings of `C` by
  any groupoid `G` with functors `universalGradingGroupoid C ⥤ G`.
* `TauCeti.universalGradingGroupoid.mapEquivalence`,
  `TauCeti.universalGradingGroupoid.congrEquivalence`: functorial transport of the universal grading
  groupoid along a monoidal equivalence `C ≌ D`.

## References

* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §3.3, Definition 3.16
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.3, 4.14
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

section Construction

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

namespace universalGradingGroupoid

/-- The vertex type of the quiver presenting `universalGradingGroupoid C`, wrapping
`UnitSimpleClasses C`. -/
private structure GeneratingQuiver where
  /-- The underlying simple summand class of `𝟙_ C`. -/
  unit : UnitSimpleClasses C

/-- Generating edges of `GeneratingQuiver C`: one edge from `leftUnitClass S.repr` to
`rightUnitClass S.repr` for each simple isomorphism class `S`. -/
private inductive GeneratingEdge : GeneratingQuiver C → GeneratingQuiver C → Type u₁
  | mk (S : SimpleClasses C) :
      GeneratingEdge ⟨leftUnitClass S.repr⟩ ⟨rightUnitClass S.repr⟩

private instance : Quiver (GeneratingQuiver C) where
  Hom := GeneratingEdge C

/-- The free-groupoid vertex associated to a simple summand `I` of `𝟙_ C`. -/
private def freeGeneratingObj (I : UnitSimpleClasses C) :
    Quiver.FreeGroupoid (GeneratingQuiver C) :=
  (Quiver.FreeGroupoid.of (GeneratingQuiver C)).obj ⟨I⟩

/-- The generating morphism in `Quiver.FreeGroupoid (GeneratingQuiver C)` associated to a
simple class `S`. -/
private def freeGeneratingDeg (S : SimpleClasses C) :
    freeGeneratingObj C (leftUnitClass S.repr) ⟶ freeGeneratingObj C (rightUnitClass S.repr) :=
  (Quiver.FreeGroupoid.of (GeneratingQuiver C)).map (GeneratingEdge.mk S)

/-- Tensor-constituent relations in the free groupoid on `GeneratingQuiver C`: every nonzero
morphism `U.repr ⟶ S.repr ⊗ T.repr` equates the generator of `U` with the composite of those of `S`
and `T`. -/
private inductive Rel : HomRel (Quiver.FreeGroupoid (GeneratingQuiver C))
  | step (S T U : SimpleClasses C) (f : U.repr ⟶ S.repr ⊗ T.repr) (hf : f ≠ 0) :
      Rel (freeGeneratingDeg C U)
        (eqToHom (congrArg (freeGeneratingObj C) (leftUnitClass_eq_of_hom_ne_zero hf)) ≫
          freeGeneratingDeg C S ≫
          eqToHom (congrArg (freeGeneratingObj C)
            (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
          freeGeneratingDeg C T ≫
          eqToHom (congrArg (freeGeneratingObj C) (rightUnitClass_eq_of_hom_ne_zero hf)).symm)

end universalGradingGroupoid

/-- The universal grading groupoid of a finite semisimple monoidal category `C`: its objects are
indexed by the simple summands of `𝟙_ C` (`UnitSimpleClasses C`), and its morphisms are generated by
the simple isomorphism classes `S : SimpleClasses C` modulo the tensor-constituent relations. -/
def universalGradingGroupoid : Type u₁ :=
  CategoryTheory.Quotient (universalGradingGroupoid.Rel C)

/-- A grading of the simple classes of `C` by a groupoid `G`: an object of `G` for each simple
summand of `𝟙_ C` and a morphism for each simple class `S` between its left and right unit supports,
compatible with nonzero tensor-constituent morphisms `U.repr ⟶ S.repr ⊗ T.repr`. -/
structure GroupoidGrading (G : Type u₂) [Groupoid.{v₂} G] where
  /-- Image object of each simple summand of the tensor unit. -/
  obj : UnitSimpleClasses C → G
  /-- Grading morphism assigned to each simple isomorphism class. -/
  deg : ∀ S : SimpleClasses C, obj (leftUnitClass S.repr) ⟶ obj (rightUnitClass S.repr)
  /-- Multiplicativity of degrees along nonzero morphisms `U.repr ⟶ S.repr ⊗ T.repr`. -/
  deg_comp : ∀ {S T U : SimpleClasses C} (f : U.repr ⟶ S.repr ⊗ T.repr) (hf : f ≠ 0),
    deg U = eqToHom (congrArg obj (leftUnitClass_eq_of_hom_ne_zero hf)) ≫
      deg S ≫ eqToHom (congrArg obj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
      deg T ≫ eqToHom (congrArg obj (rightUnitClass_eq_of_hom_ne_zero hf)).symm

namespace GroupoidGrading

variable {C} {G : Type u₂} [Groupoid.{v₂} G]

/-- Two groupoid gradings are equal when they agree on unit summand objects and their degrees on
every simple class agree up to `eqToHom` conjugation. -/
@[ext (iff := false)]
theorem ext {γ₁ γ₂ : GroupoidGrading C G}
    (hobj : ∀ I, γ₁.obj I = γ₂.obj I)
    (hdeg : ∀ S, γ₁.deg S = eqToHom (hobj _) ≫ γ₂.deg S ≫ eqToHom (hobj _).symm) :
    γ₁ = γ₂ := by
  have hobj' : γ₁.obj = γ₂.obj := funext hobj
  rcases γ₁ with ⟨o₁, d₁, _⟩; rcases γ₂ with ⟨o₂, d₂, _⟩
  dsimp only at hobj' hdeg; subst hobj'; congr; funext S; simpa using hdeg S

variable (γ : GroupoidGrading C G)

theorem deg_congr {S T : SimpleClasses C} (h : S = T) :
    γ.deg S = eqToHom (by rw [h]) ≫ γ.deg T ≫ eqToHom (by rw [h]) := by subst h; simp

/-- The grading morphism assigned by `γ` to an arbitrary simple object `X`. -/
def degOf (X : C) [Simple X] : γ.obj (leftUnitClass X) ⟶ γ.obj (rightUnitClass X) :=
  eqToHom (by simp) ≫ γ.deg (SimpleClasses.classOf X) ≫ eqToHom (by simp)

/-- `γ.degOf X` is `γ.deg (SimpleClasses.classOf X)` conjugated by the unit-class equalities
along `SimpleClasses.classOfReprIso X`. -/
theorem degOf_def (X : C) [Simple X] :
    γ.degOf X = eqToHom (by simp) ≫ γ.deg (SimpleClasses.classOf X) ≫ eqToHom (by simp) := (rfl)

@[simp]
theorem degOf_repr (S : SimpleClasses C) : γ.degOf S.repr = γ.deg S := by
  rw [degOf, γ.deg_congr (SimpleClasses.classOf_repr S)]; simp

/-- Multiplicativity of `γ.degOf` along any nonzero morphism `U ⟶ X ⊗ Y` between simple
objects. -/
theorem degOf_comp {X Y U : C} [Simple X] [Simple Y] [Simple U] (f : U ⟶ X ⊗ Y) (hf : f ≠ 0) :
    γ.degOf U = eqToHom (congrArg γ.obj (leftUnitClass_eq_of_hom_ne_zero hf)) ≫
      γ.degOf X ≫
      eqToHom (congrArg γ.obj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
      γ.degOf Y ≫
      eqToHom (congrArg γ.obj (rightUnitClass_eq_of_hom_ne_zero hf)).symm := by
  let eU := SimpleClasses.classOfReprIso U
  let eXY := SimpleClasses.classOfReprIso X ⊗ᵢ SimpleClasses.classOfReprIso Y
  have hf' : eU.hom ≫ f ≫ eXY.inv ≠ 0 := fun h ↦ hf <| by
    simpa [Category.assoc] using eU.inv ≫= h =≫ eXY.hom
  have hdeg := γ.deg_comp (eU.hom ≫ f ≫ eXY.inv) hf'
  simp only [degOf, hdeg, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- Every simple summand of the tensor unit has trivial degree in any groupoid grading. -/
@[simp]
theorem deg_unitSummand (I : UnitSimpleClasses C) :
    γ.deg I.val = eqToHom (by simp) := by
  let a := (UnitSimpleClasses.tensorSelfIso I).symm
  have ha : a.hom ≠ 0 := fun h ↦
    CategoryTheory.id_ne_zero I.repr (by rw [← a.hom_inv_id, h, zero_comp])
  let g : γ.obj I ⟶ γ.obj I := eqToHom (by simp) ≫ γ.deg I.val ≫ eqToHom (by simp)
  have hidem : g = g ≫ g := by
    dsimp only [g]
    nth_rw 1 [γ.deg_comp a.hom ha]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  have hg : g = 𝟙 (γ.obj I) := by simpa [Category.assoc] using Groupoid.inv g ≫= hidem.symm
  simpa [g, Category.assoc] using
    eqToHom (congrArg γ.obj (leftUnitClass_unitRepr I)) ≫= hg =≫
      eqToHom (congrArg γ.obj (rightUnitClass_unitRepr I)).symm

/-- Every unit-summand representative has trivial `degOf` in any groupoid grading. -/
theorem degOf_unitRepr (I : UnitSimpleClasses C) : γ.degOf I.repr = eqToHom (by simp) := by simp

end GroupoidGrading

end Construction

namespace universalGradingGroupoid

section Basic

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

@[instance_reducible]
def instGroupoid : Groupoid.{u₁} (universalGradingGroupoid C) := by
  unfold universalGradingGroupoid; exact inferInstance

attribute [instance] instGroupoid

private def fromQuotientFunctor :
    CategoryTheory.Quotient (Rel C) ⥤ universalGradingGroupoid C := by
  unfold universalGradingGroupoid instGroupoid; exact 𝟭 _

private def toQuotientFunctor :
    universalGradingGroupoid C ⥤ CategoryTheory.Quotient (Rel C) := by
  unfold universalGradingGroupoid instGroupoid; exact 𝟭 _

private theorem toQuotient_comp_fromQuotient :
    toQuotientFunctor (C := C) ⋙ fromQuotientFunctor (C := C) = 𝟭 (universalGradingGroupoid C) := by
  unfold universalGradingGroupoid instGroupoid fromQuotientFunctor toQuotientFunctor; rfl

private abbrev quotFunctor :
    Quiver.FreeGroupoid (GeneratingQuiver C) ⥤ universalGradingGroupoid C :=
  CategoryTheory.Quotient.functor (Rel C) ⋙ fromQuotientFunctor

/-- Bijection between simple summand classes of `𝟙_ C` and objects of
`universalGradingGroupoid C`. -/
def mkObj : UnitSimpleClasses C ≃ universalGradingGroupoid C where
  toFun I := quotFunctor.obj (freeGeneratingObj C I)
  invFun x := (toQuotientFunctor.obj x).as.as.unit
  left_inv _ := by
    unfold universalGradingGroupoid quotFunctor toQuotientFunctor fromQuotientFunctor; rfl
  right_inv x := by
    change quotFunctor.obj (freeGeneratingObj C (toQuotientFunctor.obj x).as.as.unit) = x
    unfold universalGradingGroupoid quotFunctor toQuotientFunctor fromQuotientFunctor
    rcases x with ⟨⟨⟨_⟩⟩⟩; rfl

instance : Finite (universalGradingGroupoid C) := Finite.of_equiv _ mkObj

/-- `universalGradingGroupoid C` is nonempty if and only if the tensor unit `𝟙_ C` is nonzero. -/
theorem nonempty_iff : Nonempty (universalGradingGroupoid C) ↔ ¬ IsZero (𝟙_ C) :=
  mkObj.symm.nonempty_congr.trans UnitSimpleClasses.nonempty_iff

/-- The universal grading morphism of a simple isomorphism class `S`, from its left unit support to
its right unit support. -/
def degree (S : SimpleClasses C) :
    mkObj (leftUnitClass S.repr) ⟶ mkObj (rightUnitClass S.repr) :=
  quotFunctor.map (freeGeneratingDeg C S)

theorem degree_congr {S T : SimpleClasses C} (h : S = T) :
    degree S = eqToHom (by rw [h]) ≫ degree T ≫ eqToHom (by rw [h]) := by subst h; simp

/-- The universal grading morphism of a simple object `X`. -/
def degreeOf (X : C) [Simple X] :
    mkObj (leftUnitClass X) ⟶ mkObj (rightUnitClass X) :=
  eqToHom (by simp) ≫ degree (SimpleClasses.classOf X) ≫ eqToHom (by simp)

/-- `degreeOf X` is `degree (SimpleClasses.classOf X)` conjugated by the unit-class equalities
along `SimpleClasses.classOfReprIso X`. -/
theorem degreeOf_def (X : C) [Simple X] :
    degreeOf X = eqToHom (by simp) ≫ degree (SimpleClasses.classOf X) ≫ eqToHom (by simp) := (rfl)

@[simp]
theorem degreeOf_repr (S : SimpleClasses C) : degreeOf S.repr = degree S := by
  rw [degreeOf_def, degree_congr (SimpleClasses.classOf_repr S)]; simp

/-- Isomorphic simple objects have equal universal grading degrees up to endpoint transports. -/
theorem degreeOf_congr {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    degreeOf X =
      eqToHom (congrArg mkObj (leftUnitClass_congr e)) ≫
        degreeOf Y ≫
        eqToHom (congrArg mkObj (rightUnitClass_congr e)).symm := by
  have hcls : SimpleClasses.classOf X = SimpleClasses.classOf Y :=
    (SimpleClasses.classOf_eq_iff_nonempty_iso X Y).2 ⟨e⟩
  rw [degreeOf_def, degreeOf_def, degree_congr hcls]; simp [Category.assoc]

/-- Every nonzero morphism `U.repr ⟶ S.repr ⊗ T.repr` identifies `degree U` with the composite of
`degree S` and `degree T` in `universalGradingGroupoid C`. -/
theorem degree_comp {S T U : SimpleClasses C} (f : U.repr ⟶ S.repr ⊗ T.repr) (hf : f ≠ 0) :
    degree U = eqToHom (congrArg mkObj (leftUnitClass_eq_of_hom_ne_zero hf)) ≫
      degree S ≫
      eqToHom (congrArg mkObj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
      degree T ≫
      eqToHom (congrArg mkObj (rightUnitClass_eq_of_hom_ne_zero hf)).symm := by
  have h : (CategoryTheory.Quotient.functor (Rel C)).map (freeGeneratingDeg C U) =
      (CategoryTheory.Quotient.functor (Rel C)).map
        (eqToHom (congrArg (freeGeneratingObj C) (leftUnitClass_eq_of_hom_ne_zero hf)) ≫
          freeGeneratingDeg C S ≫
          eqToHom (congrArg (freeGeneratingObj C)
            (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
          freeGeneratingDeg C T ≫
          eqToHom (congrArg (freeGeneratingObj C) (rightUnitClass_eq_of_hom_ne_zero hf)).symm) :=
    CategoryTheory.Quotient.sound (Rel C) (Rel.step S T U f hf)
  have h' := congrArg (fromQuotientFunctor (C := C)).map h
  dsimp only [degree, mkObj, quotFunctor, Functor.comp_obj, Functor.comp_map] at h' ⊢
  simpa only [CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc] using h'

private def idGrading : GroupoidGrading C (universalGradingGroupoid C) :=
  ⟨mkObj, degree, degree_comp⟩

/-- Every nonzero morphism `U ⟶ X ⊗ Y` between simple objects identifies `degreeOf U` with the
composite of `degreeOf X` and `degreeOf Y`. -/
theorem degreeOf_comp {X Y U : C} [Simple X] [Simple Y] [Simple U] (f : U ⟶ X ⊗ Y) (hf : f ≠ 0) :
    degreeOf U = eqToHom (congrArg mkObj (leftUnitClass_eq_of_hom_ne_zero hf)) ≫
      degreeOf X ≫
      eqToHom (congrArg mkObj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
      degreeOf Y ≫
      eqToHom (congrArg mkObj (rightUnitClass_eq_of_hom_ne_zero hf)).symm :=
  (idGrading (C := C)).degOf_comp f hf

/-- Every simple summand of the tensor unit has trivial universal degree. -/
@[simp]
theorem degree_unitSummand (I : UnitSimpleClasses C) : degree I.val = eqToHom (by simp) :=
  (idGrading (C := C)).deg_unitSummand I

theorem degreeOf_unitRepr (I : UnitSimpleClasses C) : degreeOf I.repr = eqToHom (by simp) := by
  simp

section UniversalProperty

variable {G : Type u₂} [Groupoid.{v₂} G]

private def prefunctorOfGrading (γ : GroupoidGrading C G) : GeneratingQuiver C ⥤q G where
  obj x := γ.obj x.unit
  map | .mk S => γ.deg S

private theorem freeLift_map_freeDeg (γ : GroupoidGrading C G) (S : SimpleClasses C) :
    (Quiver.FreeGroupoid.lift (prefunctorOfGrading γ)).map (freeGeneratingDeg C S) = γ.deg S :=
  eq_of_heq <| Quiver.heq_of_homOfEq_ext _ _ <|
    Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (prefunctorOfGrading γ))
      (GeneratingEdge.mk S)

/-- Extend a `GroupoidGrading C G` to a functor `universalGradingGroupoid C ⥤ G`. -/
def lift (γ : GroupoidGrading C G) : universalGradingGroupoid C ⥤ G :=
  toQuotientFunctor ⋙ CategoryTheory.Quotient.lift (Rel C)
    (Quiver.FreeGroupoid.lift (prefunctorOfGrading γ)) fun _ _ _ _ ⟨S, T, U, f, hf⟩ ↦ by
      simp only [CategoryTheory.Functor.map_comp, eqToHom_map, freeLift_map_freeDeg]
      exact γ.deg_comp f hf

@[simp]
theorem lift_mkObj (γ : GroupoidGrading C G) (I : UnitSimpleClasses C) :
    (lift γ).obj (mkObj I) = γ.obj I := by
  unfold universalGradingGroupoid instGroupoid lift mkObj quotFunctor toQuotientFunctor
    fromQuotientFunctor; rfl

@[simp]
theorem lift_degree (γ : GroupoidGrading C G) (S : SimpleClasses C) :
    (lift γ).map (degree S) =
      eqToHom (lift_mkObj γ _) ≫ γ.deg S ≫ eqToHom (lift_mkObj γ _).symm := by
  refine (conj_eqToHom_iff_heq _ _ (lift_mkObj γ _) (lift_mkObj γ _)).2 ?_
  have h : (lift γ).map (degree S) ≍
      (Quiver.FreeGroupoid.lift (prefunctorOfGrading γ)).map (freeGeneratingDeg C S) := by
    unfold universalGradingGroupoid instGroupoid lift degree quotFunctor toQuotientFunctor
      fromQuotientFunctor; rfl
  exact h.trans (heq_of_eq (freeLift_map_freeDeg γ S))

@[simp]
theorem lift_degreeOf (γ : GroupoidGrading C G) (X : C) [Simple X] :
    (lift γ).map (degreeOf X) =
      eqToHom (lift_mkObj γ _) ≫ γ.degOf X ≫ eqToHom (lift_mkObj γ _).symm := by
  simp [degreeOf_def, GroupoidGrading.degOf, eqToHom_map, Category.assoc]

private theorem functor_ext_of_groupoid {F₁ F₂ : universalGradingGroupoid C ⥤ G}
    (hobj : ∀ I : UnitSimpleClasses C, F₁.obj (mkObj I) = F₂.obj (mkObj I))
    (hdeg : ∀ S : SimpleClasses C,
      F₁.map (degree S) = eqToHom (hobj _) ≫ F₂.map (degree S) ≫ eqToHom (hobj _).symm) :
    F₁ = F₂ := by
  have hcomp : fromQuotientFunctor (C := C) ⋙ F₁ = fromQuotientFunctor (C := C) ⋙ F₂ := by
    apply CategoryTheory.Quotient.lift_unique' (Rel C)
    let φ := Quiver.FreeGroupoid.of (GeneratingQuiver C) ⋙q
      (CategoryTheory.Quotient.functor (Rel C) ⋙ fromQuotientFunctor ⋙ F₂).toPrefunctor
    have hφ : Quiver.FreeGroupoid.of (GeneratingQuiver C) ⋙q
        (CategoryTheory.Quotient.functor (Rel C) ⋙ fromQuotientFunctor ⋙ F₁).toPrefunctor =
        φ := by
      refine Prefunctor.ext (fun x ↦ hobj x.unit) ?_
      rintro _ _ ⟨S⟩
      have hrec : ∀ {a b c d : G} (p : b = a) (q : c = d) (m : b ⟶ c),
          m ≍ (Eq.recOn q (Eq.recOn p m : a ⟶ c) : a ⟶ d) := by
        rintro _ _ _ _ rfl rfl _; rfl
      exact eq_of_heq <| ((conj_eqToHom_iff_heq (F₁.map (degree S)) (F₂.map (degree S))
        (hobj _) (hobj _)).1 (hdeg S)).trans (hrec _ _ _)
    rw [Quiver.FreeGroupoid.lift_unique φ _ hφ, Quiver.FreeGroupoid.lift_unique φ _ rfl]
  calc F₁ = (toQuotientFunctor (C := C) ⋙ fromQuotientFunctor (C := C)) ⋙ F₁ := by
        rw [toQuotient_comp_fromQuotient, Functor.id_comp]
    _ = toQuotientFunctor (C := C) ⋙ (fromQuotientFunctor (C := C) ⋙ F₂) := congrArg _ hcomp
    _ = F₂ := by rw [← Functor.assoc, toQuotient_comp_fromQuotient, Functor.id_comp]

end UniversalProperty

/-- Functors out of `universalGradingGroupoid C` into any category are uniquely determined by
their action on unit summand objects `mkObj I` and generating simple degrees `degree S`. -/
@[ext (iff := false) high]
theorem functor_ext {G : Type u₂} [Category.{v₂} G] {F₁ F₂ : universalGradingGroupoid C ⥤ G}
    (hobj : ∀ I : UnitSimpleClasses C, F₁.obj (mkObj I) = F₂.obj (mkObj I))
    (hdeg : ∀ S : SimpleClasses C,
      F₁.map (degree S) = eqToHom (hobj _) ≫ F₂.map (degree S) ≫ eqToHom (hobj _).symm) :
    F₁ = F₂ := by
  have hcore : Core.functorToCore F₁ = Core.functorToCore F₂ := by
    refine functor_ext_of_groupoid (fun I ↦ congrArg Core.mk (hobj I)) fun S ↦ Core.hom_ext ?_
    have heq : ∀ {x y : Core G} (p : x = y),
        (eqToHom p).iso.hom = eqToHom (congrArg Core.of p) := by rintro _ _ rfl; rfl
    simpa [heq] using hdeg S
  exact congrArg (· ⋙ Core.inclusion G) hcore

section UniversalProperty

variable {G : Type u₂} [Groupoid.{v₂} G]

private def gradingOfFunctor (F : universalGradingGroupoid C ⥤ G) : GroupoidGrading C G where
  obj I := F.obj (mkObj I)
  deg S := F.map (degree S)
  deg_comp f hf := by
    rw [degree_comp f hf]; simp only [CategoryTheory.Functor.map_comp, eqToHom_map]

/-- The universal property of `universalGradingGroupoid C`: groupoid gradings of `C` by `G`
correspond bijectively to functors `universalGradingGroupoid C ⥤ G`. -/
def liftEquiv : GroupoidGrading C G ≃ (universalGradingGroupoid C ⥤ G) where
  toFun := lift
  invFun := gradingOfFunctor
  left_inv γ := GroupoidGrading.ext (lift_mkObj γ) fun S ↦ by
    simpa only [gradingOfFunctor] using lift_degree γ S
  right_inv F := functor_ext (fun _ ↦ by simp [gradingOfFunctor]) fun S ↦ by
    simp [gradingOfFunctor]

@[simp]
theorem liftEquiv_apply (γ : GroupoidGrading C G) : liftEquiv γ = lift γ := (rfl)

@[simp]
theorem liftEquiv_symm_apply_obj (F : universalGradingGroupoid C ⥤ G) (I : UnitSimpleClasses C) :
    (liftEquiv.symm F).obj I = F.obj (mkObj I) := (rfl)

@[simp]
theorem liftEquiv_symm_apply_deg (F : universalGradingGroupoid C ⥤ G) (S : SimpleClasses C) :
    (liftEquiv.symm F).deg S =
      eqToHom (liftEquiv_symm_apply_obj F _) ≫ F.map (degree S) ≫
        eqToHom (liftEquiv_symm_apply_obj F _).symm :=
  (conj_eqToHom_iff_heq _ _ (liftEquiv_symm_apply_obj F _)
    (liftEquiv_symm_apply_obj F _)).2 HEq.rfl

end UniversalProperty

section Equivalence

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [MonoidalCategory D]
  [MonoidalPreadditive D] [IsFiniteSemisimpleCategory D]

private def gradingOfEquivalence (e : C ≌ D) [e.functor.Monoidal] :
    GroupoidGrading C (universalGradingGroupoid D) where
  obj I := mkObj (UnitSimpleClasses.equiv e I)
  deg S := eqToHom (by simp) ≫ degree (SimpleClasses.equiv e S) ≫ eqToHom (by simp)
  deg_comp {S T U} f hf := by
    have : e.functor.PreservesZeroMorphisms := e.functor.preservesZeroMorphisms_of_isLeftAdjoint
    let dU := SimpleClasses.equivApplyReprIso e U
    let dST := (SimpleClasses.equivApplyReprIso e S ⊗ᵢ SimpleClasses.equivApplyReprIso e T) ≪≫
      Functor.Monoidal.μIso e.functor S.repr T.repr
    have hg : dU.hom ≫ e.functor.map f ≫ dST.inv ≠ 0 := fun h ↦ hf <| e.functor.map_injective <| by
      rw [e.functor.map_zero]
      simpa [Category.assoc] using dU.inv ≫= h =≫ dST.hom
    simp [degree_comp _ hg, Category.assoc]

/-- Functorial transport of `universalGradingGroupoid` along a monoidal equivalence `e : C ≌ D`. -/
def mapEquivalence (e : C ≌ D) [e.functor.Monoidal] :
    universalGradingGroupoid C ⥤ universalGradingGroupoid D :=
  lift (gradingOfEquivalence e)

@[simp]
theorem mapEquivalence_mkObj (e : C ≌ D) [e.functor.Monoidal] (I : UnitSimpleClasses C) :
    (mapEquivalence e).obj (mkObj I) = mkObj (UnitSimpleClasses.equiv e I) := by
  simp [mapEquivalence, gradingOfEquivalence]

@[simp]
theorem mapEquivalence_degree (e : C ≌ D) [e.functor.Monoidal] (S : SimpleClasses C) :
    (mapEquivalence e).map (degree S) =
      eqToHom (by simp) ≫ degree (SimpleClasses.equiv e S) ≫ eqToHom (by simp) := by
  simp [mapEquivalence, gradingOfEquivalence, Category.assoc]

@[simp]
theorem mapEquivalence_degreeOf (e : C ≌ D) [e.functor.Monoidal] (X : C) [Simple X] :
    (mapEquivalence e).map (degreeOf X) =
      eqToHom (by simp) ≫
        @degreeOf D _ _ _ _ _ (e.functor.obj X) (CategoryTheory.simple_obj e.functor X) ≫
        eqToHom (by simp) := by
  simp only [degreeOf_def, CategoryTheory.Functor.map_comp, eqToHom_map, mapEquivalence_degree,
    Category.assoc]
  rw [degree_congr (SimpleClasses.equiv_apply_classOf e X)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

@[simp]
theorem mapEquivalence_refl :
    mapEquivalence (CategoryTheory.Equivalence.refl (C := C)) =
      𝟭 (universalGradingGroupoid C) := by
  refine functor_ext (fun _ ↦ by simp) fun S ↦ ?_
  have hS : SimpleClasses.equiv (CategoryTheory.Equivalence.refl (C := C)) S = S :=
    (SimpleClasses.eq_iff_nonempty_iso _ _).2
      ⟨SimpleClasses.equivApplyReprIso CategoryTheory.Equivalence.refl S⟩
  simp [degree_congr hS, Category.assoc]

@[simp]
theorem mapEquivalence_trans {E : Type u₃} [Category.{v₃} E] [Abelian E] [MonoidalCategory E]
    [MonoidalPreadditive E] [IsFiniteSemisimpleCategory E]
    (e₁ : C ≌ D) (e₂ : D ≌ E) [e₁.functor.Monoidal] [e₂.functor.Monoidal] :
    mapEquivalence (e₁.trans e₂) = mapEquivalence e₁ ⋙ mapEquivalence e₂ := by
  refine functor_ext (fun _ ↦ by simp) fun S ↦ ?_
  have hS : SimpleClasses.equiv (e₁.trans e₂) S =
      SimpleClasses.equiv e₂ (SimpleClasses.equiv e₁ S) :=
    (SimpleClasses.eq_iff_nonempty_iso _ _).2
      ⟨SimpleClasses.equivApplyReprIso (e₁.trans e₂) S ≪≫
        e₂.functor.mapIso (SimpleClasses.equivApplyReprIso e₁ S).symm ≪≫
        (SimpleClasses.equivApplyReprIso e₂ (SimpleClasses.equiv e₁ S)).symm⟩
  simp [eqToHom_map, degree_congr hS, Category.assoc]

theorem mapEquivalence_comp_symm (e : C ≌ D) [e.functor.Monoidal] :
    letI := e.inverseMonoidal
    mapEquivalence e ⋙ mapEquivalence e.symm = 𝟭 (universalGradingGroupoid C) := by
  let _ := e.inverseMonoidal
  have hobj : ∀ I : UnitSimpleClasses C,
      (mapEquivalence e ⋙ mapEquivalence e.symm).obj (mkObj I) =
        (𝟭 (universalGradingGroupoid C)).obj (mkObj I) := fun I ↦ by
    simp [-UnitSimpleClasses.equiv_symm, ← UnitSimpleClasses.equiv_symm e]
  refine functor_ext hobj fun S ↦ ?_
  have hS : SimpleClasses.equiv e.symm (SimpleClasses.equiv e S) = S :=
    (SimpleClasses.eq_iff_nonempty_iso _ _).2
      ⟨SimpleClasses.equivApplyReprIso e.symm _ ≪≫
        e.inverse.mapIso (SimpleClasses.equivApplyReprIso e S) ≪≫ (e.unitIso.app S.repr).symm⟩
  simp [eqToHom_map, degree_congr hS, Category.assoc]

theorem symm_mapEquivalence_comp (e : C ≌ D) [e.functor.Monoidal] :
    letI := e.inverseMonoidal
    mapEquivalence e.symm ⋙ mapEquivalence e = 𝟭 (universalGradingGroupoid D) := by
  let _ := e.inverseMonoidal
  have hobj : ∀ J : UnitSimpleClasses D,
      (mapEquivalence e.symm ⋙ mapEquivalence e).obj (mkObj J) =
        (𝟭 (universalGradingGroupoid D)).obj (mkObj J) := fun J ↦ by
    simp [-UnitSimpleClasses.equiv_symm, ← UnitSimpleClasses.equiv_symm e]
  refine functor_ext hobj fun T ↦ ?_
  have hT : SimpleClasses.equiv e (SimpleClasses.equiv e.symm T) = T :=
    (SimpleClasses.eq_iff_nonempty_iso _ _).2
      ⟨SimpleClasses.equivApplyReprIso e _ ≪≫
        e.functor.mapIso (SimpleClasses.equivApplyReprIso e.symm T) ≪≫ e.counitIso.app T.repr⟩
  simp [eqToHom_map, degree_congr hT, Category.assoc]

/-- A monoidal equivalence `C ≌ D` induces an equivalence of universal grading groupoids. -/
def congrEquivalence (e : C ≌ D) [e.functor.Monoidal] :
    universalGradingGroupoid C ≌ universalGradingGroupoid D :=
  letI := e.inverseMonoidal
  { functor := mapEquivalence e
    inverse := mapEquivalence e.symm
    unitIso := eqToIso (mapEquivalence_comp_symm e).symm
    counitIso := eqToIso (symm_mapEquivalence_comp e)
    functor_unitIso_comp := fun _ ↦ by simp [eqToHom_map] }

@[simp]
theorem congrEquivalence_functor (e : C ≌ D) [e.functor.Monoidal] :
    (congrEquivalence e).functor = mapEquivalence e := (rfl)

@[simp]
theorem congrEquivalence_inverse (e : C ≌ D) [e.functor.Monoidal] :
    (congrEquivalence e).inverse =
      @mapEquivalence D _ _ _ _ _ C _ _ _ _ _ e.symm e.inverseMonoidal := (rfl)

end Equivalence

private theorem quotFunctor_obj_of (I : UnitSimpleClasses C) :
    fromQuotientFunctor.obj ((CategoryTheory.Quotient.functor (Rel C)).obj
      ((Quiver.FreeGroupoid.of (GeneratingQuiver C)).obj ⟨I⟩)) = mkObj I := by
  unfold mkObj quotFunctor; rfl

private theorem quotFunctor_map_of (S : SimpleClasses C) :
    fromQuotientFunctor.map ((CategoryTheory.Quotient.functor (Rel C)).map
      ((Quiver.FreeGroupoid.of (GeneratingQuiver C)).map (GeneratingEdge.mk S))) ≍ degree S := by
  unfold degree quotFunctor; exact HEq.rfl

private theorem quotFunctor_map_inv_of (S : SimpleClasses C) :
    fromQuotientFunctor.map ((CategoryTheory.Quotient.functor (Rel C)).map
      (inv ((Quiver.FreeGroupoid.of (GeneratingQuiver C)).map (GeneratingEdge.mk S)))) ≍
        inv (degree S) := by
  rw [CategoryTheory.Functor.map_inv, CategoryTheory.Functor.map_inv]
  unfold degree quotFunctor; exact HEq.rfl

/-- Presentation-independent induction principle for morphisms of `universalGradingGroupoid C`:
a property that holds on all generating degrees `degree S`, their inverses `inv (degree S)`, and
identities, and is closed under composition, holds on every morphism. -/
@[elab_as_elim]
theorem hom_induction
    {P : ∀ {x y : universalGradingGroupoid C}, (x ⟶ y) → Prop}
    (hdeg : ∀ S : SimpleClasses C, P (degree S))
    (hinv : ∀ S : SimpleClasses C, P (inv (degree S)))
    (hid : ∀ x : universalGradingGroupoid C, P (𝟙 x))
    (hcomp : ∀ {x y z : universalGradingGroupoid C} (f : x ⟶ y) (g : y ⟶ z),
      P f → P g → P (f ≫ g))
    {x y : universalGradingGroupoid C} (g : x ⟶ y) : P g := by
  have heq : ∀ {x₁ y₁ x₂ y₂ : universalGradingGroupoid C} (hx : x₂ = x₁) (hy : y₁ = y₂)
      {m : x₁ ⟶ y₁}, P m → P (eqToHom hx ≫ m ≫ eqToHom hy) := by
    rintro _ _ _ _ rfl rfl m hm; simpa using hm
  have hx := CategoryTheory.Functor.congr_obj (toQuotient_comp_fromQuotient (C := C)) x
  have hy := CategoryTheory.Functor.congr_obj (toQuotient_comp_fromQuotient (C := C)) y
  have hstep : ∀ {q₁ q₂ : CategoryTheory.Quotient (Rel C)} (g₀ : q₁ ⟶ q₂),
      P (fromQuotientFunctor.map g₀) := by
    refine CategoryTheory.Quotient.induction (r := Rel C)
      (P := fun {q₁ q₂} g₀ ↦ P (fromQuotientFunctor.map g₀)) fun p ↦ ?_
    induction p with
    | of_map e =>
      rcases e with ⟨S⟩
      rw [(conj_eqToHom_iff_heq' _ _ (quotFunctor_obj_of (leftUnitClass S.repr)).symm
        (quotFunctor_obj_of (rightUnitClass S.repr)).symm).2 (quotFunctor_map_of S)]
      exact heq _ (quotFunctor_obj_of (rightUnitClass S.repr)) (hdeg S)
    | inv_of_map e =>
      rcases e with ⟨S⟩
      rw [(conj_eqToHom_iff_heq' _ _ (quotFunctor_obj_of (rightUnitClass S.repr)).symm
        (quotFunctor_obj_of (leftUnitClass S.repr)).symm).2 (quotFunctor_map_inv_of S)]
      exact heq _ (quotFunctor_obj_of (leftUnitClass S.repr)) (hinv S)
    | id _ => rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]; exact hid _
    | comp _ _ ih₁ ih₂ =>
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]; exact hcomp _ _ ih₁ ih₂
  have hg' : g = eqToHom hx.symm ≫ fromQuotientFunctor.map (toQuotientFunctor.map g) ≫
      eqToHom hy := (conj_eqToHom_iff_heq' _ _ hx.symm hy.symm).2
    (CategoryTheory.Functor.hcongr_hom (toQuotient_comp_fromQuotient (C := C)) g).symm
  rw [hg']
  exact heq hx.symm hy (hstep (toQuotientFunctor.map g))

end Basic

end universalGradingGroupoid

end TauCeti
