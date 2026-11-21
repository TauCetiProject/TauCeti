/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
public import Mathlib.CategoryTheory.Groupoid.VertexGroup
public import Mathlib.CategoryTheory.Quotient
public import TauCeti.CategoryTheory.Monoidal.Grading.UnitSummands
public import TauCeti.CategoryTheory.SingleObj

/-!
# The universal grading groupoid of a multitensor category

In a finite semisimple monoidal category `C` with additive tensor product (`MonoidalPreadditive`),
the tensor unit `𝟙_ C` decomposes into pairwise orthogonal simple summands indexed by
`TauCeti.UnitSimpleClasses C`. Unlike the fusion case (`[Simple (𝟙_ C)]`), grading `C` by a group
collapses all unit summands to the identity element; the natural universal invariant of the fusion
rules of a multitensor or multifusion category is instead a *groupoid*
`TauCeti.universalGradingGroupoid C` (Penneys, Definition 3.16; Etingof–Gelaki–Nikshych–Ostrik,
§4.14).

Its objects correspond bijectively to `UnitSimpleClasses C` via `mkObj`, and each simple isomorphism
class `S : SimpleClasses C` has a generating morphism
`degree S : mkObj (leftUnitClass S.repr) ⟶ mkObj (rightUnitClass S.repr)`, subject to the relation
that every nonzero morphism `U.repr ⟶ S.repr ⊗ T.repr` identifies `degree U` with the composite
`degree S ≫ degree T` (up to `eqToHom` along the endpoint equalities
`leftUnitClass_eq_of_hom_ne_zero`, `rightUnitClass_eq_leftUnitClass_of_hom_ne_zero`, and
`rightUnitClass_eq_of_hom_ne_zero`).

## Main declarations

* `TauCeti.universalGradingGroupoid`: the universal grading groupoid of `C`.
* `TauCeti.universalGradingGroupoid.mkObj`: bijection between `UnitSimpleClasses C` and the objects
  of `universalGradingGroupoid C`.
* `TauCeti.universalGradingGroupoid.degree`, `TauCeti.universalGradingGroupoid.degreeOf`: the
  universal grading morphism of a simple class or simple object, with multiplication laws
  `degree_comp` and `degreeOf_comp` and unit law `degree_unitSummand`.
* `TauCeti.GroupoidGrading`, `TauCeti.universalGradingGroupoid.liftEquiv`: universal property
  identifying gradings of `C` by any groupoid `G` with functors `universalGradingGroupoid C ⥤ G`.
* `TauCeti.universalGradingGroupoid.congrEquivalence`: transport of the universal grading groupoid
  along a monoidal equivalence `C ≌ D`.
* `TauCeti.universalGradingGroupoid.degree_dual`,
  `TauCeti.universalGradingGroupoid.exists_degree_eq`,
  `TauCeti.universalGradingGroupoid.nonempty_hom_mkObj_iff`: under `[RigidCategory C]`, duals give
  inverse morphisms, every morphism in `universalGradingGroupoid C` is the degree of a simple class,
  hom-sets `mkObj I ⟶ mkObj J` are nonempty iff the `(I, J)` Peirce corner contains a simple object,
  and `[Finite (SimpleClasses C)]` makes every hom-set finite.
* `TauCeti.universalGradingGroupoid.singleObjFunctorMulEquiv`: for any abelian group `A`, functors
  `universalGradingGroupoid C ⥤ SingleObj A` are canonically isomorphic as a group to
  `universalGradingGroup C →* A` (without assuming `[Simple (𝟙_ C)]` or `[RigidCategory C]`).
* `TauCeti.universalGradingGroupoid.singleObjEquivalence`,
  `TauCeti.universalGradingGroupoid.vertexGroupMulEquiv`: when `[Simple (𝟙_ C)]`, the universal
  grading groupoid has a unique object whose vertex group is canonically isomorphic to
  `universalGradingGroup C`.

## References

* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §3.3, Definition 3.16
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.3, 4.14
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ u₁ u₂ w

namespace TauCeti

section Construction

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

namespace universalGradingGroupoid

/-- The vertex type of the quiver presenting `universalGradingGroupoid C`, wrapping
`UnitSimpleClasses C`. -/
structure GeneratingQuiver where
  /-- The underlying simple summand class of `𝟙_ C`. -/
  unit : UnitSimpleClasses C

/-- Generating edges of `GeneratingQuiver C`: one edge from `leftUnitClass S.repr` to
`rightUnitClass S.repr` for each simple isomorphism class `S`. -/
inductive GeneratingEdge : GeneratingQuiver C → GeneratingQuiver C → Type u₁
  | mk (S : SimpleClasses C) :
      GeneratingEdge ⟨leftUnitClass S.repr⟩ ⟨rightUnitClass S.repr⟩

instance : Quiver (GeneratingQuiver C) where
  Hom := GeneratingEdge C

/-- The free-groupoid vertex associated to a simple summand `I` of `𝟙_ C`. -/
def freeGeneratingObj (I : UnitSimpleClasses C) : Quiver.FreeGroupoid (GeneratingQuiver C) :=
  (Quiver.FreeGroupoid.of (GeneratingQuiver C)).obj ⟨I⟩

/-- The generating morphism in `Quiver.FreeGroupoid (GeneratingQuiver C)` associated to a
simple class `S`. -/
def freeGeneratingDeg (S : SimpleClasses C) :
    freeGeneratingObj C (leftUnitClass S.repr) ⟶ freeGeneratingObj C (rightUnitClass S.repr) :=
  (Quiver.FreeGroupoid.of (GeneratingQuiver C)).map (GeneratingEdge.mk S)

/-- Tensor-constituent relations in the free groupoid on `GeneratingQuiver C`: every nonzero
morphism `U.repr ⟶ S.repr ⊗ T.repr` equates the generator of `U` with the composite of those of `S`
and `T`. -/
inductive Rel : HomRel (Quiver.FreeGroupoid (GeneratingQuiver C))
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
abbrev universalGradingGroupoid : Type u₁ :=
  CategoryTheory.Quotient (universalGradingGroupoid.Rel C)

/-- A grading of the simple classes of `C` by a groupoid `G`: an object of `G` for each simple
summand of `𝟙_ C` and a morphism for each simple class `S` between its left and right unit supports,
compatible with nonzero tensor-constituent morphisms `U.repr ⟶ S.repr ⊗ T.repr`. -/
@[ext]
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

end Construction

namespace universalGradingGroupoid

section Basic

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

private abbrev quotFunctor :
    Quiver.FreeGroupoid (GeneratingQuiver C) ⥤ universalGradingGroupoid C :=
  CategoryTheory.Quotient.functor (Rel C)

/-- Bijection between simple summand classes of `𝟙_ C` and objects of
`universalGradingGroupoid C`. -/
def mkObj : UnitSimpleClasses C ≃ universalGradingGroupoid C where
  toFun I := quotFunctor.obj (freeGeneratingObj C I)
  invFun x := x.as.as.unit
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨⟨_⟩⟩⟩
    rfl

instance : Finite (universalGradingGroupoid C) :=
  Finite.of_equiv _ mkObj

/-- `universalGradingGroupoid C` is nonempty if and only if the tensor unit `𝟙_ C` is nonzero. -/
theorem nonempty_iff : Nonempty (universalGradingGroupoid C) ↔ ¬ IsZero (𝟙_ C) :=
  mkObj.symm.nonempty_congr.trans UnitSimpleClasses.nonempty_iff

/-- The universal grading morphism of a simple isomorphism class `S`, from its left unit support to
its right unit support. -/
def degree (S : SimpleClasses C) :
    mkObj (leftUnitClass S.repr) ⟶ mkObj (rightUnitClass S.repr) :=
  quotFunctor.map (freeGeneratingDeg C S)

theorem degree_congr {S T : SimpleClasses C} (h : S = T) :
    degree S = eqToHom (by rw [h]) ≫ degree T ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The universal grading morphism of a simple object `X`. -/
def degreeOf (X : C) [Simple X] :
    mkObj (leftUnitClass X) ⟶ mkObj (rightUnitClass X) :=
  eqToHom (by simp) ≫ degree (SimpleClasses.classOf X) ≫ eqToHom (by simp)

@[simp]
theorem degreeOf_repr (S : SimpleClasses C) : degreeOf S.repr = degree S := by
  dsimp only [degreeOf]
  rw [degree_congr (SimpleClasses.classOf_repr S)]
  simp

/-- Every nonzero morphism `U.repr ⟶ S.repr ⊗ T.repr` identifies `degree U` with the composite of
`degree S` and `degree T` in `universalGradingGroupoid C`. -/
theorem degree_comp {S T U : SimpleClasses C} (f : U.repr ⟶ S.repr ⊗ T.repr) (hf : f ≠ 0) :
    degree U = eqToHom (congrArg mkObj (leftUnitClass_eq_of_hom_ne_zero hf)) ≫
      degree S ≫
      eqToHom (congrArg mkObj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
      degree T ≫
      eqToHom (congrArg mkObj (rightUnitClass_eq_of_hom_ne_zero hf)).symm := by
  have h := CategoryTheory.Quotient.sound (Rel C) (Rel.step S T U f hf)
  dsimp only [degree, mkObj] at h ⊢
  simpa only [CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc] using h

/-- Every nonzero morphism `U ⟶ X ⊗ Y` between simple objects identifies `degreeOf U` with the
composite of `degreeOf X` and `degreeOf Y`. -/
theorem degreeOf_comp {X Y U : C} [Simple X] [Simple Y] [Simple U] (f : U ⟶ X ⊗ Y) (hf : f ≠ 0) :
    degreeOf U = eqToHom (congrArg mkObj (leftUnitClass_eq_of_hom_ne_zero hf)) ≫
      degreeOf X ≫
      eqToHom (congrArg mkObj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf)) ≫
      degreeOf Y ≫
      eqToHom (congrArg mkObj (rightUnitClass_eq_of_hom_ne_zero hf)).symm := by
  let eU := SimpleClasses.classOfReprIso U
  let eXY := SimpleClasses.classOfReprIso X ⊗ᵢ SimpleClasses.classOfReprIso Y
  have hf' : eU.hom ≫ f ≫ eXY.inv ≠ 0 := fun h ↦ hf <| by
    have h0 := eU.inv ≫= h =≫ eXY.hom
    simpa [Category.assoc] using h0
  have hdeg := degree_comp (eU.hom ≫ f ≫ eXY.inv) hf'
  simp only [degreeOf, hdeg, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- Every simple summand of the tensor unit has trivial universal degree. -/
@[simp]
theorem degree_unitSummand (I : UnitSimpleClasses C) :
    degree I.val = eqToHom (by simp) := by
  let a := (UnitSimpleClasses.tensorSelfIso I).symm
  have ha : a.hom ≠ 0 := fun h ↦
    CategoryTheory.id_ne_zero I.repr (by rw [← a.hom_inv_id, h, zero_comp])
  let g : mkObj I ⟶ mkObj I :=
    eqToHom (by simp) ≫ degree I.val ≫ eqToHom (by simp)
  have hidem : g = g ≫ g := by
    dsimp only [g]
    nth_rw 1 [degree_comp a.hom ha]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  have hg : g = 𝟙 (mkObj I) := by
    simpa [Category.assoc] using Groupoid.inv g ≫= hidem.symm
  simpa [g, Category.assoc] using
    eqToHom (congrArg mkObj (leftUnitClass_unitRepr I)) ≫= hg =≫
      eqToHom (congrArg mkObj (rightUnitClass_unitRepr I)).symm

theorem degreeOf_unitRepr (I : UnitSimpleClasses C) :
    degreeOf I.repr = eqToHom (by simp) := by
  simp

section UniversalProperty

variable {G : Type u₂} [Groupoid.{v₂} G]

private def prefunctorOfGrading (γ : GroupoidGrading C G) : GeneratingQuiver C ⥤q G where
  obj x := γ.obj x.unit
  map
    | .mk S => γ.deg S

private theorem freeLift_map_freeDeg (γ : GroupoidGrading C G) (S : SimpleClasses C) :
    (Quiver.FreeGroupoid.lift (prefunctorOfGrading γ)).map (freeGeneratingDeg C S) = γ.deg S :=
  eq_of_heq <| Quiver.heq_of_homOfEq_ext _ _ <|
    Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (prefunctorOfGrading γ))
      (GeneratingEdge.mk S)

/-- Extend a `GroupoidGrading C G` to a functor `universalGradingGroupoid C ⥤ G`. -/
def lift (γ : GroupoidGrading C G) : universalGradingGroupoid C ⥤ G :=
  CategoryTheory.Quotient.lift (Rel C)
    (Quiver.FreeGroupoid.lift (prefunctorOfGrading γ)) <| by
      rintro _ _ _ _ ⟨S, T, U, f, hf⟩
      simp only [CategoryTheory.Functor.map_comp, eqToHom_map, freeLift_map_freeDeg]
      exact γ.deg_comp f hf

@[simp]
theorem lift_mkObj (γ : GroupoidGrading C G) (I : UnitSimpleClasses C) :
    (lift γ).obj (mkObj I) = γ.obj I := by
  rfl

@[simp]
theorem lift_degree (γ : GroupoidGrading C G) (S : SimpleClasses C) :
    (lift γ).map (degree S) =
      eqToHom (lift_mkObj γ _) ≫ γ.deg S ≫ eqToHom (lift_mkObj γ _).symm :=
  (conj_eqToHom_iff_heq _ _ (lift_mkObj γ _) (lift_mkObj γ _)).2
    (heq_of_eq (freeLift_map_freeDeg γ S))

@[simp]
theorem lift_degreeOf (γ : GroupoidGrading C G) (X : C) [Simple X] :
    (lift γ).map (degreeOf X) =
      eqToHom (by simp) ≫ γ.deg (SimpleClasses.classOf X) ≫ eqToHom (by simp) := by
  simp [degreeOf, eqToHom_map, Category.assoc]

/-- Functors out of `universalGradingGroupoid C` are uniquely determined by their action on unit
summand objects `mkObj I` and generating simple degrees `degree S`. -/
theorem functor_ext {F₁ F₂ : universalGradingGroupoid C ⥤ G}
    (hobj : ∀ I : UnitSimpleClasses C, F₁.obj (mkObj I) = F₂.obj (mkObj I))
    (hdeg : ∀ S : SimpleClasses C,
      F₁.map (degree S) = eqToHom (hobj _) ≫ F₂.map (degree S) ≫ eqToHom (hobj _).symm) :
    F₁ = F₂ := by
  apply CategoryTheory.Quotient.lift_unique' (Rel C)
  let φ := Quiver.FreeGroupoid.of (GeneratingQuiver C) ⋙q (quotFunctor ⋙ F₂).toPrefunctor
  have hφ : Quiver.FreeGroupoid.of (GeneratingQuiver C) ⋙q (quotFunctor ⋙ F₁).toPrefunctor =
      φ := by
    refine Prefunctor.ext (fun x ↦ hobj x.unit) ?_
    rintro _ _ ⟨S⟩
    have hrec : ∀ {a b c d : G} (p : b = a) (q : c = d) (m : b ⟶ c),
        m ≍ (Eq.recOn q (Eq.recOn p m : a ⟶ c) : a ⟶ d) := by
      rintro _ _ _ _ rfl rfl _
      rfl
    exact eq_of_heq <| ((conj_eqToHom_iff_heq (F₁.map (degree S)) (F₂.map (degree S))
      (hobj _) (hobj _)).1 (hdeg S)).trans (hrec _ _ _)
  rw [Quiver.FreeGroupoid.lift_unique φ (quotFunctor ⋙ F₁) hφ,
    Quiver.FreeGroupoid.lift_unique φ (quotFunctor ⋙ F₂) rfl]

/-- Restrict a functor `universalGradingGroupoid C ⥤ G` to a `GroupoidGrading C G`. -/
def gradingOfFunctor (F : universalGradingGroupoid C ⥤ G) : GroupoidGrading C G where
  obj I := F.obj (mkObj I)
  deg S := F.map (degree S)
  deg_comp f hf := by
    rw [degree_comp f hf]
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map]

/-- The universal property of `universalGradingGroupoid C`: groupoid gradings of `C` by `G`
correspond bijectively to functors `universalGradingGroupoid C ⥤ G`. -/
def liftEquiv : GroupoidGrading C G ≃ (universalGradingGroupoid C ⥤ G) where
  toFun := lift
  invFun := gradingOfFunctor
  left_inv γ := by
    rcases γ with ⟨obj, deg, deg_comp⟩
    dsimp only [gradingOfFunctor, lift_mkObj]
    congr
    funext S
    exact freeLift_map_freeDeg ⟨obj, deg, deg_comp⟩ S
  right_inv F := functor_ext (fun _ ↦ by simp [gradingOfFunctor]) fun S ↦ by
    simp [gradingOfFunctor]

@[simp]
theorem liftEquiv_apply (γ : GroupoidGrading C G) :
    liftEquiv γ = lift γ := by
  rfl

@[simp]
theorem liftEquiv_symm_apply_obj (F : universalGradingGroupoid C ⥤ G) (I : UnitSimpleClasses C) :
    (liftEquiv.symm F).obj I = F.obj (mkObj I) := by
  rfl

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

/-- The groupoid grading of `C` valued in `universalGradingGroupoid D` induced by a monoidal
equivalence `e : C ≌ D`. -/
def gradingOfEquivalence (e : C ≌ D) [e.functor.Monoidal] :
    GroupoidGrading C (universalGradingGroupoid D) where
  obj I := mkObj (UnitSimpleClasses.equiv e I)
  deg S := eqToHom (by simp) ≫ degree (SimpleClasses.equiv e S) ≫ eqToHom (by simp)
  deg_comp {S T U} f hf := by
    have : e.functor.PreservesZeroMorphisms :=
      e.functor.preservesZeroMorphisms_of_isLeftAdjoint
    let dU := SimpleClasses.equivApplyReprIso e U
    let dST := (SimpleClasses.equivApplyReprIso e S ⊗ᵢ SimpleClasses.equivApplyReprIso e T) ≪≫
      Functor.Monoidal.μIso e.functor S.repr T.repr
    let g := dU.hom ≫ e.functor.map f ≫ dST.inv
    have hg : g ≠ 0 := fun h ↦ hf <| e.functor.map_injective <| by
      have h0 := dU.inv ≫= h =≫ dST.hom
      rw [e.functor.map_zero]
      simpa [g, Category.assoc] using h0
    simp [degree_comp g hg, Category.assoc]

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

theorem mapEquivalence_comp_symm (e : C ≌ D) [e.functor.Monoidal] :
    letI := e.inverseMonoidal
    mapEquivalence e ⋙ mapEquivalence e.symm = 𝟭 (universalGradingGroupoid C) := by
  let _ := e.inverseMonoidal
  have hobj : ∀ I : UnitSimpleClasses C,
      (mapEquivalence e ⋙ mapEquivalence e.symm).obj (mkObj I) =
        (𝟭 (universalGradingGroupoid C)).obj (mkObj I) := fun I ↦ by
    simp only [Functor.comp_obj, Functor.id_obj, mapEquivalence_mkObj,
      ← UnitSimpleClasses.equiv_symm e]
    exact congrArg mkObj ((UnitSimpleClasses.equiv e).symm_apply_apply I)
  refine functor_ext hobj fun S ↦ ?_
  have hS : SimpleClasses.equiv e.symm (SimpleClasses.equiv e S) = S :=
    (SimpleClasses.eq_iff_nonempty_iso _ _).2
      ⟨SimpleClasses.equivApplyReprIso e.symm _ ≪≫
        e.inverse.mapIso (SimpleClasses.equivApplyReprIso e S) ≪≫
        (e.unitIso.app S.repr).symm⟩
  simp [eqToHom_map, degree_congr hS, Category.assoc]

theorem symm_mapEquivalence_comp (e : C ≌ D) [e.functor.Monoidal] :
    letI := e.inverseMonoidal
    mapEquivalence e.symm ⋙ mapEquivalence e = 𝟭 (universalGradingGroupoid D) := by
  let _ := e.inverseMonoidal
  have hobj : ∀ J : UnitSimpleClasses D,
      (mapEquivalence e.symm ⋙ mapEquivalence e).obj (mkObj J) =
        (𝟭 (universalGradingGroupoid D)).obj (mkObj J) := fun J ↦ by
    simp only [Functor.comp_obj, Functor.id_obj, mapEquivalence_mkObj,
      ← UnitSimpleClasses.equiv_symm e]
    exact congrArg mkObj ((UnitSimpleClasses.equiv e).apply_symm_apply J)
  refine functor_ext hobj fun T ↦ ?_
  have hT : SimpleClasses.equiv e (SimpleClasses.equiv e.symm T) = T :=
    (SimpleClasses.eq_iff_nonempty_iso _ _).2
      ⟨SimpleClasses.equivApplyReprIso e _ ≪≫
        e.functor.mapIso (SimpleClasses.equivApplyReprIso e.symm T) ≪≫
        e.counitIso.app T.repr⟩
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

end Equivalence

private theorem quotFunctor_obj_of (I : UnitSimpleClasses C) :
    (CategoryTheory.Quotient.functor (Rel C)).obj
      ((Quiver.FreeGroupoid.of (GeneratingQuiver C)).obj ⟨I⟩) = mkObj I :=
  rfl

private theorem quotFunctor_map_of (S : SimpleClasses C) :
    (CategoryTheory.Quotient.functor (Rel C)).map
      ((Quiver.FreeGroupoid.of (GeneratingQuiver C)).map (GeneratingEdge.mk S)) ≍
        degree S :=
  HEq.rfl

private theorem quotFunctor_map_inv_of (S : SimpleClasses C) :
    (CategoryTheory.Quotient.functor (Rel C)).map
      (inv ((Quiver.FreeGroupoid.of (GeneratingQuiver C)).map (GeneratingEdge.mk S))) ≍
        inv (degree S) := by
  rw [CategoryTheory.Functor.map_inv]
  rfl

section Rigid

variable [RigidCategory C]

/-- Dual simple classes have inverse degrees in `universalGradingGroupoid C`. -/
@[simp]
theorem degree_dual (S : SimpleClasses C) :
    degree S.dual = eqToHom (by simp) ≫ inv (degree S) ≫ eqToHom (by simp) := by
  obtain ⟨I, f, _, hf⟩ :=
    exists_unitSimpleClasses_comp_ne_zero (coevaluation_ne_zero (Y := S.reprᘁ)
      (Simple.not_isZero S.repr))
  let t := whiskerLeftIso S.repr (SimpleClasses.dualReprIso S).symm
  have hg : (f ≫ η_ S.repr S.reprᘁ) ≫ t.hom ≠ 0 := fun h ↦ hf <| by
    rw [← Category.comp_id (f ≫ η_ S.repr S.reprᘁ), ← t.hom_inv_id, ← Category.assoc, h, zero_comp]
  have hcomp := degree_comp ((f ≫ η_ S.repr S.reprᘁ) ≫ t.hom) hg
  rw [degree_unitSummand] at hcomp
  have hinv : eqToHom (by simp) ≫ degree S.dual =
      inv (degree S) ≫ eqToHom (by simp) := by
    rw [IsIso.eq_inv_comp]
    simpa [Category.assoc] using
      eqToHom (congrArg mkObj (leftUnitClass_eq_of_hom_ne_zero hg)).symm ≫= hcomp.symm =≫
        eqToHom (congrArg mkObj (rightUnitClass_eq_of_hom_ne_zero hg))
  simpa [Category.assoc] using
    eqToHom (congrArg mkObj (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hg)).symm ≫= hinv

@[simp]
theorem degreeOf_rightDual (X : C) [Simple X] :
    degreeOf Xᘁ = eqToHom (by simp) ≫ inv (degreeOf X) ≫ eqToHom (by simp) := by
  dsimp only [degreeOf]
  rw [degree_congr (SimpleClasses.dual_classOf X).symm]
  simp [Category.assoc]

/-- In a rigid finite semisimple monoidal category, every morphism in
`universalGradingGroupoid C` is the degree of some simple isomorphism class. -/
theorem exists_degree_eq {x y : universalGradingGroupoid C} (g : x ⟶ y) :
    ∃ (S : SimpleClasses C) (hL : mkObj (leftUnitClass S.repr) = x)
      (hR : mkObj (rightUnitClass S.repr) = y),
      g = eqToHom hL.symm ≫ degree S ≫ eqToHom hR := by
  refine CategoryTheory.Quotient.induction (r := Rel C)
    (P := fun {x y} g ↦ ∃ (S : SimpleClasses C)
      (hL : mkObj (leftUnitClass S.repr) = x) (hR : mkObj (rightUnitClass S.repr) = y),
      g = eqToHom hL.symm ≫ degree S ≫ eqToHom hR) (fun p ↦ ?_) g
  induction p with
  | of_map e =>
    rcases e with ⟨S⟩
    exact ⟨S, (quotFunctor_obj_of _).symm, (quotFunctor_obj_of _).symm,
      (conj_eqToHom_iff_heq' _ _ _ _).2 (quotFunctor_map_of S)⟩
  | inv_of_map e =>
    rcases e with ⟨S⟩
    refine ⟨S.dual,
      (congrArg mkObj (leftUnitClass_dual_repr S)).trans (quotFunctor_obj_of _).symm,
      (congrArg mkObj (rightUnitClass_dual_repr S)).trans (quotFunctor_obj_of _).symm, ?_⟩
    rw [degree_dual]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    exact (conj_eqToHom_iff_heq' _ _ _ _).2 (quotFunctor_map_inv_of S)
  | id u =>
    rcases u with ⟨I⟩
    exact ⟨I.val,
      (congrArg mkObj (leftUnitClass_unitRepr I)).trans (quotFunctor_obj_of _).symm,
      (congrArg mkObj (rightUnitClass_unitRepr I)).trans (quotFunctor_obj_of _).symm,
      by simp⟩
  | comp p₁ p₂ ih₁ ih₂ =>
    obtain ⟨S, hSL, hSR, hp₁⟩ := ih₁
    obtain ⟨T, hTL, hTR, hp₂⟩ := ih₂
    have hmid : rightUnitClass S.repr = leftUnitClass T.repr :=
      mkObj.injective (hSR.trans hTL.symm)
    have hnz : ¬ IsZero (S.repr ⊗ T.repr) :=
      (not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass S.repr T.repr).2 hmid
    obtain ⟨W, hW, f, hf⟩ := exists_simple_hom_ne_zero hnz
    let _ := hW
    let dW := SimpleClasses.classOfReprIso W
    have hf' : dW.hom ≫ f ≠ 0 := fun h ↦ hf <| by
      rw [← dW.inv_hom_id_assoc f, h, comp_zero]
    refine ⟨SimpleClasses.classOf W,
      (congrArg mkObj (leftUnitClass_eq_of_hom_ne_zero hf')).trans hSL,
      (congrArg mkObj (rightUnitClass_eq_of_hom_ne_zero hf')).trans hTR, ?_⟩
    rw [CategoryTheory.Functor.map_comp, hp₁, hp₂, degree_comp (dW.hom ≫ f) hf']
    simp [Category.assoc]

/-- Every morphism `mkObj I ⟶ mkObj J` in `universalGradingGroupoid C` comes from a simple class
`S` with `leftUnitClass S.repr = I` and `rightUnitClass S.repr = J`. -/
theorem exists_simple_degree_eq {I J : UnitSimpleClasses C} (g : mkObj I ⟶ mkObj J) :
    ∃ (S : SimpleClasses C) (hL : leftUnitClass S.repr = I) (hR : rightUnitClass S.repr = J),
      g = eqToHom (congrArg mkObj hL).symm ≫ degree S ≫ eqToHom (congrArg mkObj hR) := by
  obtain ⟨S, hL, hR, hg⟩ := exists_degree_eq g
  exact ⟨S, mkObj.injective hL, mkObj.injective hR, hg⟩

/-- In a rigid finite semisimple monoidal category, there is a morphism `mkObj I ⟶ mkObj J` in
`universalGradingGroupoid C` if and only if some simple class has left unit support `I` and right
unit support `J`. -/
theorem nonempty_hom_mkObj_iff (I J : UnitSimpleClasses C) :
    Nonempty (mkObj I ⟶ mkObj J) ↔
      ∃ S : SimpleClasses C, leftUnitClass S.repr = I ∧ rightUnitClass S.repr = J := by
  refine ⟨fun ⟨g⟩ ↦ ?_, fun ⟨S, hL, hR⟩ ↦
    ⟨eqToHom (congrArg mkObj hL).symm ≫ degree S ≫ eqToHom (congrArg mkObj hR)⟩⟩
  obtain ⟨S, hL, hR, _⟩ := exists_simple_degree_eq g
  exact ⟨S, hL, hR⟩

/-- In a multifusion category (finitely many simple classes), every hom-set of
`universalGradingGroupoid C` is finite. -/
instance [Finite (SimpleClasses C)] (x y : universalGradingGroupoid C) : Finite (x ⟶ y) := by
  refine Finite.of_surjective
    (fun p : {S : SimpleClasses C //
        mkObj (leftUnitClass S.repr) = x ∧ mkObj (rightUnitClass S.repr) = y} ↦
      eqToHom p.property.left.symm ≫ degree p.val ≫ eqToHom p.property.right)
    fun g ↦ ?_
  obtain ⟨S, hL, hR, hg⟩ := exists_degree_eq g
  exact ⟨⟨S, hL, hR⟩, hg.symm⟩

end Rigid

section SingleObjComparison

/-- For any group `G`, functors `universalGradingGroupoid C ⥤ SingleObj G` correspond bijectively
to group homomorphisms `universalGradingGroup C →* Gᵐᵒᵖ` (the opposite group accounts for
`SingleObj`'s reversed composition `f ≫ g = g * f`). Neither `[Simple (𝟙_ C)]` nor
`[RigidCategory C]` is required. -/
def singleObjFunctorEquiv (G : Type w) [Group G] :
    (universalGradingGroupoid C ⥤ SingleObj G) ≃ (universalGradingGroup C →* Gᵐᵒᵖ) where
  toFun F :=
    universalGradingGroup.lift (fun S ↦ MulOpposite.op (F.map (degree S))) fun S T U f hf ↦ by
      rw [degree_comp f hf]
      simp only [CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl, SingleObj.id_as_one,
        SingleObj.comp_as_mul, one_mul, mul_one, ← MulOpposite.op_mul]
  invFun χ :=
    lift
      { obj := fun _ ↦ SingleObj.star G
        deg := fun S ↦ MulOpposite.unop (χ (universalGradingGroup.degree S))
        deg_comp := fun {S T U} f hf ↦ by
          rw [universalGradingGroup.degree_mul S T U f hf, map_mul]
          simp only [eqToHom_refl, SingleObj.id_as_one, SingleObj.comp_as_mul, one_mul, mul_one,
            MulOpposite.unop_mul] }
  left_inv F := functor_ext (fun _ ↦ rfl) fun S ↦ by
    simp only [lift_degree, eqToHom_refl, Category.id_comp, Category.comp_id,
      universalGradingGroup.lift_degree, MulOpposite.unop_op]
  right_inv χ := universalGradingGroup.hom_ext fun S ↦ by
    simp only [universalGradingGroup.lift_degree, lift_degree, eqToHom_refl, Category.id_comp,
      Category.comp_id, MulOpposite.op_unop]

/-- For an abelian group `A`, `A`-valued groupoid characters
`universalGradingGroupoid C ⥤ SingleObj A` are canonically isomorphic as a group to characters
`universalGradingGroup C →* A` of the universal grading group. Neither `[Simple (𝟙_ C)]` nor
`[RigidCategory C]` is required. -/
def singleObjFunctorMulEquiv (A : Type w) [CommGroup A] :
    (universalGradingGroupoid C ⥤ SingleObj A) ≃* (universalGradingGroup C →* A) where
  toFun F :=
    universalGradingGroup.lift (fun S ↦ F.map (degree S)) fun S T U f hf ↦ by
      rw [degree_comp f hf]
      simp only [CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl, SingleObj.id_as_one,
        SingleObj.comp_as_mul, one_mul, mul_one]
      exact mul_comm (F.map (degree T) : A) (F.map (degree S) : A)
  invFun χ :=
    lift
      { obj := fun _ ↦ SingleObj.star A
        deg := fun S ↦ χ (universalGradingGroup.degree S)
        deg_comp := fun {S T U} f hf ↦ by
          rw [universalGradingGroup.degree_mul S T U f hf, map_mul]
          simp only [eqToHom_refl, SingleObj.id_as_one, SingleObj.comp_as_mul, one_mul, mul_one]
          exact mul_comm (χ (universalGradingGroup.degree S) : A)
            (χ (universalGradingGroup.degree T) : A) }
  left_inv F := functor_ext (fun _ ↦ rfl) fun S ↦ by
    simp only [lift_degree, eqToHom_refl, Category.id_comp, Category.comp_id,
      universalGradingGroup.lift_degree]
  right_inv χ := universalGradingGroup.hom_ext fun S ↦ by
    simp only [universalGradingGroup.lift_degree, lift_degree, eqToHom_refl, Category.id_comp,
      Category.comp_id]
  map_mul' F₁ F₂ := universalGradingGroup.hom_ext fun S ↦ by
    simp only [MonoidHom.mul_apply, universalGradingGroup.lift_degree, SingleObj.functor_mul_map]

@[simp]
theorem singleObjFunctorMulEquiv_apply_degree (A : Type w) [CommGroup A]
    (F : universalGradingGroupoid C ⥤ SingleObj A) (S : SimpleClasses C) :
    singleObjFunctorMulEquiv A F (universalGradingGroup.degree S) = F.map (degree S) := by
  simp only [singleObjFunctorMulEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    universalGradingGroup.lift_degree]

theorem singleObjFunctorMulEquiv_apply_degree_classOf (A : Type w) [CommGroup A]
    (F : universalGradingGroupoid C ⥤ SingleObj A) (X : C) [Simple X] :
    singleObjFunctorMulEquiv A F (universalGradingGroup.degree (SimpleClasses.classOf X)) =
      F.map (degreeOf X) := by
  rw [singleObjFunctorMulEquiv_apply_degree]
  simp only [degreeOf, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl,
    Category.id_comp, Category.comp_id]

@[simp]
theorem singleObjFunctorMulEquiv_symm_map_degree (A : Type w) [CommGroup A]
    (χ : universalGradingGroup C →* A) (S : SimpleClasses C) :
    ((singleObjFunctorMulEquiv A).symm χ).map (degree S) = χ (universalGradingGroup.degree S) := by
  simp only [singleObjFunctorMulEquiv, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
    lift_degree, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
theorem singleObjFunctorMulEquiv_symm_map_degreeOf (A : Type w) [CommGroup A]
    (χ : universalGradingGroup C →* A) (X : C) [Simple X] :
    ((singleObjFunctorMulEquiv A).symm χ).map (degreeOf X) =
      χ (universalGradingGroup.degree (SimpleClasses.classOf X)) := by
  simp only [degreeOf, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl,
    Category.id_comp, Category.comp_id, singleObjFunctorMulEquiv_symm_map_degree]

end SingleObjComparison

section SimpleUnit

variable [Simple (𝟙_ C)]

instance instUnique : Unique (universalGradingGroupoid C) where
  default := mkObj UnitSimpleClasses.unit
  uniq x := by
    obtain ⟨I, rfl⟩ := mkObj.surjective x
    exact congrArg mkObj (Subsingleton.elim I UnitSimpleClasses.unit)

@[simp]
theorem default_eq_mkObj_unit :
    (default : universalGradingGroupoid C) = mkObj UnitSimpleClasses.unit :=
  (rfl)

private def toSingleObjGradingGroup :
    universalGradingGroupoid C ⥤ SingleObj (universalGradingGroup C)ᵐᵒᵖ :=
  lift
    { obj := fun _ ↦ SingleObj.star (universalGradingGroup C)ᵐᵒᵖ
      deg := fun S ↦ MulOpposite.op (universalGradingGroup.degree S)
      deg_comp := fun {S T U} f hf ↦ by
        rw [universalGradingGroup.degree_mul S T U f hf]
        simp only [eqToHom_refl, SingleObj.id_as_one, SingleObj.comp_as_mul, one_mul, mul_one,
          MulOpposite.op_mul] }

private def fromSingleObjGradingGroupHom :
    universalGradingGroup C →*
      ((default : universalGradingGroupoid C) ⟶ default) :=
  universalGradingGroup.lift
    (fun S ↦ eqToHom (Subsingleton.elim _ _) ≫ degree S ≫ eqToHom (Subsingleton.elim _ _))
    fun S T U f hf ↦ by
      rw [degree_comp f hf]
      simp [CategoryTheory.Groupoid.vertexGroup_mul, Category.assoc]

private def fromSingleObjGradingGroup :
    SingleObj (universalGradingGroup C)ᵐᵒᵖ ⥤ universalGradingGroupoid C where
  obj _ := default
  map m := fromSingleObjGradingGroupHom (MulOpposite.unop m)
  map_id _ := fromSingleObjGradingGroupHom.map_one
  map_comp m₁ m₂ := fromSingleObjGradingGroupHom.map_mul (MulOpposite.unop m₁) (MulOpposite.unop m₂)

private theorem toSingleObj_comp_fromSingleObj :
    toSingleObjGradingGroup (C := C) ⋙ fromSingleObjGradingGroup (C := C) =
      𝟭 (universalGradingGroupoid C) := by
  refine functor_ext (fun _ ↦ Subsingleton.elim _ _) fun S ↦ ?_
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map,
    toSingleObjGradingGroup, lift_degree, eqToHom_refl, Category.id_comp, Category.comp_id,
    fromSingleObjGradingGroup, MulOpposite.unop_op, fromSingleObjGradingGroupHom,
    universalGradingGroup.lift_degree]

private theorem fromSingleObj_comp_toSingleObj :
    fromSingleObjGradingGroup (C := C) ⋙ toSingleObjGradingGroup (C := C) =
      𝟭 (SingleObj (universalGradingGroup C)ᵐᵒᵖ) := by
  refine SingleObj.functor_ext fun m ↦ MulOpposite.unop_injective ?_
  let ψ : universalGradingGroup C →* universalGradingGroup C :=
    { toFun := fun x ↦
        MulOpposite.unop ((toSingleObjGradingGroup (C := C)).map (fromSingleObjGradingGroupHom x))
      map_one' := by
        rw [map_one, CategoryTheory.Groupoid.vertexGroup_one, CategoryTheory.Functor.map_id]
        rfl
      map_mul' := fun x y ↦ by
        rw [map_mul, CategoryTheory.Groupoid.vertexGroup_mul, CategoryTheory.Functor.map_comp]
        rfl }
  have hψ : ψ = MonoidHom.id (universalGradingGroup C) := by
    ext S
    simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.id_apply,
      fromSingleObjGradingGroupHom, universalGradingGroup.lift_degree,
      CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl, Category.id_comp,
      Category.comp_id, toSingleObjGradingGroup, lift_degree, MulOpposite.unop_op]
  exact DFunLike.congr_fun hψ (MulOpposite.unop m)

/-- When `𝟙_ C` is simple, `universalGradingGroupoid C` is equivalent (in fact, isomorphic) to
`SingleObj (universalGradingGroup C)ᵐᵒᵖ`. -/
def singleObjEquivalence :
    universalGradingGroupoid C ≌ SingleObj (universalGradingGroup C)ᵐᵒᵖ where
  functor := toSingleObjGradingGroup
  inverse := fromSingleObjGradingGroup
  unitIso := eqToIso toSingleObj_comp_fromSingleObj.symm
  counitIso := eqToIso fromSingleObj_comp_toSingleObj
  functor_unitIso_comp _ := by simp [eqToHom_map]

/-- When `𝟙_ C` is simple, the vertex group of `universalGradingGroupoid C` at its unique object is
canonically isomorphic to `universalGradingGroup C`. -/
def vertexGroupMulEquiv :
    ((default : universalGradingGroupoid C) ⟶ default) ≃* universalGradingGroup C where
  toFun g := MulOpposite.unop ((toSingleObjGradingGroup (C := C)).map g)
  invFun := fromSingleObjGradingGroupHom
  left_inv g :=
    eq_of_heq (CategoryTheory.Functor.hcongr_hom (toSingleObj_comp_fromSingleObj (C := C)) g)
  right_inv x := by
    let m : SingleObj.star (universalGradingGroup C)ᵐᵒᵖ ⟶
        SingleObj.star (universalGradingGroup C)ᵐᵒᵖ := MulOpposite.op x
    simpa [fromSingleObjGradingGroup, m] using
      congrArg MulOpposite.unop
        (CategoryTheory.Functor.congr_hom (fromSingleObj_comp_toSingleObj (C := C)) m)
  map_mul' g₁ g₂ := by
    rw [CategoryTheory.Groupoid.vertexGroup_mul, CategoryTheory.Functor.map_comp]
    rfl

@[simp]
theorem vertexGroupMulEquiv_degree (S : SimpleClasses C) :
    vertexGroupMulEquiv
        (eqToHom (Subsingleton.elim _ _) ≫ degree S ≫ eqToHom (Subsingleton.elim _ _)) =
      universalGradingGroup.degree S := by
  simp only [vertexGroupMulEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl, Category.id_comp,
    Category.comp_id, toSingleObjGradingGroup, lift_degree, MulOpposite.unop_op]

@[simp]
theorem vertexGroupMulEquiv_symm_degree (S : SimpleClasses C) :
    vertexGroupMulEquiv.symm (universalGradingGroup.degree S) =
      eqToHom (Subsingleton.elim _ _) ≫ degree S ≫ eqToHom (Subsingleton.elim _ _) := by
  simp only [vertexGroupMulEquiv, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
    fromSingleObjGradingGroupHom, universalGradingGroup.lift_degree]

end SimpleUnit

end Basic

end universalGradingGroupoid

end TauCeti
