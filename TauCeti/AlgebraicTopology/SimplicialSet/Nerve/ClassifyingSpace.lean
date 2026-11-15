/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.ULift
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.FundamentalGroupoid

/-!
# Classifying space of a category and of a functor

The classifying space `TauCeti.CategoryTheory.classifyingSpace C` of a category `C : Type u` with
`[Category.{v} C]` is the geometric realization `|nerve C| : TopCat.{max u v}`, and a functor
`F : C ⥤ D` induces `TauCeti.CategoryTheory.classifyingSpaceMap F`, assembling into
`TauCeti.CategoryTheory.classifyingSpaceFunctor : Cat.{v, u} ⥤ TopCat.{max u v}`.

Each object `X : C` gives `classifyingSpace.vertex X` and each morphism `f : X ⟶ Y` gives a path
`classifyingSpace.edgePath f`, satisfying `classifyingSpace.edgePath_id` and
`classifyingSpace.homotopic_edgePath_comp` and inducing `classifyingSpace.toFundamentalGroupoid C`.
Universe changes via `CategoryTheory.nerve.asSmallIso` yield `classifyingSpace.asSmallHomeomorph`
and the cross-universe continuous map `classifyingSpace.mapOfFunctor`. We also establish
faithfulness (`classifyingSpace.mapOfFunctor_injective`), non-fullness
(`TauCeti.CategoryTheory.not_full_classifyingSpaceFunctor`), and identifications for empty,
discrete, contractible linear-order, `Fin 2`, and constant-functor examples.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Mathematics 341, Springer, 1973, §1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, AMS, 2013, Chapter IV, §3.
-/

public section

open CategoryTheory Limits Opposite Simplicial Convexity

universe w u₁ v₁ u₂ v₂ u₃ v₃ v u

namespace TauCeti.CategoryTheory

/-- The classifying space `BC = |nerve C|` of a category `C`, defined as the geometric realization
of its nerve. -/
@[expose, implicit_reducible]
noncomputable def classifyingSpace (C : Type u) [Category.{v} C] : TopCat.{max u v} :=
  SSet.toTop.obj (nerve C)

lemma classifyingSpace_def (C : Type u) [Category.{v} C] :
    classifyingSpace C = SSet.toTop.obj (nerve C) := (rfl)

/-- The continuous map `BF : BC ⟶ BD` induced on classifying spaces by a functor `F : C ⥤ D`. -/
noncomputable def classifyingSpaceMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : classifyingSpace C ⟶ classifyingSpace D :=
  SSet.toTop.map (nerveMap F)

lemma classifyingSpaceMap_def {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    classifyingSpaceMap F = SSet.toTop.map (nerveMap F) := (rfl)

@[simp] lemma classifyingSpaceMap_toTopObjMk {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ} (s : (nerve C) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    classifyingSpaceMap F (SSet.toTopObjMk s w) = SSet.toTopObjMk ((nerveMap F).app (op ⦋n⦌) s) w :=
  SSet.toTop_map_toTopObjMk (nerveMap F) s w

@[simp] lemma classifyingSpaceMap_id (C : Type u) [Category.{v} C] :
    classifyingSpaceMap (𝟭 C) = 𝟙 (classifyingSpace C) := by
  have hid : nerveMap (𝟭 C) = 𝟙 (nerve C) := nerveFunctor.map_id (Cat.of C)
  rw [classifyingSpaceMap, hid, SSet.toTop.map_id]; rfl

@[simp, reassoc]
lemma classifyingSpaceMap_comp {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    classifyingSpaceMap (F ⋙ G) = classifyingSpaceMap F ≫ classifyingSpaceMap G := by
  have hcomp : nerveMap (F ⋙ G) = nerveMap F ≫ nerveMap G :=
    nerveFunctor.map_comp (X := Cat.of C) (Y := Cat.of D) (Z := Cat.of E) F.toCatHom G.toCatHom
  rw [classifyingSpaceMap, hcomp, SSet.toTop.map_comp]; rfl

/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}`, defined as
`nerveFunctor ⋙ SSet.toTop`. -/
@[expose]
noncomputable def classifyingSpaceFunctor : Cat.{v, u} ⥤ TopCat.{max u v} :=
  nerveFunctor.{v, u} ⋙ SSet.toTop

lemma classifyingSpaceFunctor_def :
    classifyingSpaceFunctor.{v, u} = nerveFunctor.{v, u} ⋙ SSet.toTop := (rfl)

@[simp] lemma classifyingSpaceFunctor_obj (C : Cat.{v, u}) :
    classifyingSpaceFunctor.obj C = classifyingSpace C := (rfl)

@[simp] lemma classifyingSpaceFunctor_map {C D : Cat.{v, u}} (F : C ⟶ D) :
    classifyingSpaceFunctor.map F = classifyingSpaceMap F.toFunctor := (rfl)

namespace classifyingSpace

section Vertices

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The canonical vertex `[X]` of `classifyingSpace C` associated to an object `X : C`. -/
noncomputable def vertex (X : C) : classifyingSpace C :=
  SSet.toTopPoint (X := nerve C) (nerveEquiv.symm X)

lemma vertex_eq_toTopPoint (X : C) :
    vertex X = SSet.toTopPoint (nerve.objEquiv.symm (nerveEquiv.symm X)) :=
  congrArg SSet.toTopPoint (nerve.objEquiv_symm_nerveEquiv_symm X).symm

lemma vertex_eq_toTopObjMk (X : C) (w : StdSimplex ℝ (Fin 1)) :
    vertex X = SSet.toTopObjMk (nerve.objEquiv.symm (nerveEquiv.symm X)) w :=
  (vertex_eq_toTopPoint X).trans (SSet.toTopPoint_eq_toTopObjMk _ w)

@[simp] lemma _root_.TauCeti.CategoryTheory.classifyingSpaceMap_vertex (F : C ⥤ D) (X : C) :
    classifyingSpaceMap F (vertex X) = vertex (F.obj X) := by
  rw [vertex_eq_toTopPoint, classifyingSpaceMap_def, SSet.toTop_map_toTopPoint,
    nerve.nerveMap_app_objEquiv_symm, nerveEquiv_symm_eq_mk₀,
    Functor.mapComposableArrows_obj_mk₀, ← nerveEquiv_symm_eq_mk₀, ← vertex_eq_toTopPoint]

/-- Distinct objects of `C` give distinct vertices of `classifyingSpace C`. -/
theorem vertex_injective (C : Type u) [Category.{v} C] :
    Function.Injective (vertex (C := C)) :=
  (SSet.toTopPoint_injective (nerve C)).comp nerveEquiv.symm.injective

@[simp] lemma vertex_inj {X Y : C} : vertex X = vertex Y ↔ X = Y := (vertex_injective C).eq_iff

/-- Every point of `classifyingSpace C` can be joined by a path to some `vertex X`. -/
theorem exists_joined_vertex (p : classifyingSpace C) : ∃ X : C, Joined (vertex X) p := by
  obtain ⟨s, hs⟩ := SSet.exists_joined_toTopPoint (X := nerve C) p
  refine ⟨nerveEquiv (nerve.objEquiv s), ?_⟩
  rwa [vertex_eq_toTopPoint, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end Vertices

section UniverseChange

/-- Lifting `C` to `AsSmall.{w} C` produces a homeomorphic classifying space. -/
noncomputable def asSmallHomeomorph (C : Type u) [Category.{v} C] :
    classifyingSpace C ≃ₜ classifyingSpace (AsSmall.{w} C) :=
  ((nerve C).toTopUliftHomeomorph.{w}).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.asSmallIso.{w} C).symm))

@[simp] lemma asSmallHomeomorph_toTopObjMk {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve C) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    asSmallHomeomorph.{w} C (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk
        (nerve.objEquiv.symm ((AsSmall.up.mapComposableArrows n).obj (nerve.objEquiv s))) w₀ := by
  simp only [asSmallHomeomorph, Homeomorph.trans_apply, TopCat.homeoOfIso_apply,
    Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv]
  rw [SSet.toTopUliftHomeomorph_toTopObjMk, SSet.toTop_map_toTopObjMk, nerve.asSmallIso_inv_app,
    Equiv.symm_apply_apply]

@[simp] lemma asSmallHomeomorph_symm_toTopObjMk {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve (AsSmall.{w} C)) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    (asSmallHomeomorph.{w} C).symm (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk
        (nerve.objEquiv.symm ((AsSmall.down.mapComposableArrows n).obj (nerve.objEquiv s))) w₀ := by
  simp only [asSmallHomeomorph, Homeomorph.symm_trans_apply, TopCat.homeoOfIso_symm_apply,
    Functor.mapIso_symm, Iso.symm_inv, Functor.mapIso_hom]
  rw [SSet.toTop_map_toTopObjMk, nerve.asSmallIso_hom_app,
    SSet.toTopUliftHomeomorph_symm_toTopObjMk, Equiv.symm_apply_apply]

@[simp] lemma asSmallHomeomorph_vertex {C : Type u} [Category.{v} C] (X : C) :
    asSmallHomeomorph.{w} C (vertex X) = vertex (AsSmall.up.obj X) := by
  rw [vertex_eq_toTopObjMk X default, asSmallHomeomorph_toTopObjMk, Equiv.apply_symm_apply,
    nerveEquiv_symm_eq_mk₀, Functor.mapComposableArrows_obj_mk₀, ← nerveEquiv_symm_eq_mk₀,
    ← vertex_eq_toTopObjMk]

@[simp] lemma asSmallHomeomorph_symm_vertex {C : Type u} [Category.{v} C] (X : AsSmall.{w} C) :
    (asSmallHomeomorph.{w} C).symm (vertex X) = vertex (AsSmall.down.obj X) := by
  rw [vertex_eq_toTopObjMk X default, asSmallHomeomorph_symm_toTopObjMk, Equiv.apply_symm_apply,
    nerveEquiv_symm_eq_mk₀, Functor.mapComposableArrows_obj_mk₀, ← nerveEquiv_symm_eq_mk₀,
    ← vertex_eq_toTopObjMk]

private lemma asSmall_up_comp_down_comp_up_comp_down {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) :
    (AsSmall.up ⋙
      (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up :
        AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D)) ⋙
      AsSmall.down = F :=
  CategoryTheory.Functor.ext (fun X ↦ (rfl : F.obj X = F.obj X))
    fun _ _ f ↦ (by simp : F.map f = 𝟙 _ ≫ F.map f ≫ 𝟙 _)

/-- Continuous map `C(classifyingSpace C, classifyingSpace D)` induced by a functor `F : C ⥤ D`
across arbitrary object and morphism universes. -/
noncomputable def mapOfFunctor {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) : C(classifyingSpace C, classifyingSpace D) :=
  ((asSmallHomeomorph.{max u₁ v₁} D).symm :
      C(classifyingSpace (AsSmall.{max u₁ v₁} D), classifyingSpace D)).comp
    ((classifyingSpaceMap
        (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up :
          AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D)).hom.comp
      (asSmallHomeomorph.{max u₂ v₂} C :
        C(classifyingSpace C, classifyingSpace (AsSmall.{max u₂ v₂} C))))

@[simp] lemma mapOfFunctor_toTopObjMk {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {n : ℕ} (s : (nerve C) _⦋n⦌)
    (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    mapOfFunctor F (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk (nerve.objEquiv.symm ((F.mapComposableArrows n).obj (nerve.objEquiv s)))
        w₀ := by
  simp [mapOfFunctor, ← Functor.comp_mapComposableArrows_obj,
    asSmall_up_comp_down_comp_up_comp_down]

@[simp] lemma mapOfFunctor_vertex {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (X : C) :
    mapOfFunctor F (vertex X) = vertex (F.obj X) := by
  rw [vertex_eq_toTopObjMk X default, mapOfFunctor_toTopObjMk, Equiv.apply_symm_apply,
    nerveEquiv_symm_eq_mk₀, Functor.mapComposableArrows_obj_mk₀, ← nerveEquiv_symm_eq_mk₀,
    ← vertex_eq_toTopObjMk]

@[simp] lemma mapOfFunctor_id (C : Type u₁) [Category.{v₁} C] :
    mapOfFunctor (𝟭 C) = ContinuousMap.id (classifyingSpace C) := by
  ext p; obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p; simp

@[simp] lemma mapOfFunctor_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) :
    mapOfFunctor (F ⋙ G) = (mapOfFunctor G).comp (mapOfFunctor F) := by
  ext p; obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p; simp

/-- For `C` and `D` in the same universes, `mapOfFunctor F` agrees with
`(classifyingSpaceMap F).hom`. -/
lemma mapOfFunctor_eq_classifyingSpaceMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : mapOfFunctor F = (classifyingSpaceMap F).hom := by
  ext p; obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p
  simp [nerve.nerveMap_app_eq_objEquiv_symm]

/-- A constant functor `(Functor.const C).obj Y` across arbitrary universes induces the constant
continuous map at `vertex Y`. -/
@[simp] lemma mapOfFunctor_const (C : Type u₁) [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (Y : D) :
    mapOfFunctor ((Functor.const C).obj Y) =
      ContinuousMap.const (classifyingSpace C) (vertex Y) := by
  ext p
  obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p
  have hconst : (((Functor.const C).obj Y).mapComposableArrows n).obj (nerve.objEquiv s) =
      nerve.objEquiv ((nerve D).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
        (nerve.objEquiv.symm (nerveEquiv.symm Y))) :=
    ComposableArrows.ext_of_totalArrow fun _ _ _ ↦ by
      simp [nerveEquiv_symm_eq_mk₀, ComposableArrows.totalArrow_def, ComposableArrows.mk₀,
        ComposableArrows.whiskerLeft]
  rw [mapOfFunctor_toTopObjMk, hconst, Equiv.symm_apply_apply, SSet.toTopObjMk_map,
    SSet.toTopObjMk_zero, ← vertex_eq_toTopPoint, ContinuousMap.const_apply]

/-- A constant functor `(Functor.const C).obj Y` realizes to the constant map at `vertex Y`. -/
@[simp] lemma _root_.TauCeti.CategoryTheory.classifyingSpaceMap_const (C D : Type u)
    [Category.{v} C] [Category.{v} D] (Y : D) :
    classifyingSpaceMap ((Functor.const C).obj Y) =
      TopCat.const (X := classifyingSpace C) (vertex Y) :=
  TopCat.ext fun p ↦ by
    have h := congrArg (· p) (mapOfFunctor_const C Y)
    rwa [mapOfFunctor_eq_classifyingSpaceMap] at h

/-- `mapOfFunctor` is injective on functors across arbitrary object and morphism universes. -/
theorem mapOfFunctor_injective {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] :
    Function.Injective (mapOfFunctor : (C ⥤ D) → C(classifyingSpace C, classifyingSpace D)) := by
  intro F G h
  have hmap : classifyingSpaceMap
      (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up :
        AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D) =
      classifyingSpaceMap (AsSmall.down (C := C) ⋙ G ⋙ AsSmall.up) := by
    ext q
    obtain ⟨p, rfl⟩ := (asSmallHomeomorph.{max u₂ v₂} C).surjective q
    exact (asSmallHomeomorph.{max u₁ v₁} D).symm.injective
      (by simpa [mapOfFunctor] using congrArg (· p) h)
  simpa only [asSmall_up_comp_down_comp_up_comp_down] using
    congrArg (fun H ↦ (AsSmall.up ⋙ H) ⋙ AsSmall.down)
      (TauCeti.nerveMap_injective (SSet.toTop.map_injective hmap))

/-- Strictly mutually inverse functors `F : C ⥤ D` and `G : D ⥤ C` induce a homeomorphism on
classifying spaces. -/
noncomputable def homeomorphOfStrictIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C)
    (hFG : F ⋙ G = 𝟭 C) (hGF : G ⋙ F = 𝟭 D) :
    classifyingSpace C ≃ₜ classifyingSpace D where
  toFun := mapOfFunctor F
  invFun := mapOfFunctor G
  left_inv p := congrArg (· p) ((mapOfFunctor_comp F G).symm.trans (by rw [hFG, mapOfFunctor_id]))
  right_inv q := congrArg (· q) ((mapOfFunctor_comp G F).symm.trans (by rw [hGF, mapOfFunctor_id]))
  continuous_toFun := (mapOfFunctor F).continuous
  continuous_invFun := (mapOfFunctor G).continuous

@[simp] lemma homeomorphOfStrictIso_apply {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C) (hFG : F ⋙ G = 𝟭 C)
    (hGF : G ⋙ F = 𝟭 D) (p : classifyingSpace C) :
    homeomorphOfStrictIso F G hFG hGF p = mapOfFunctor F p := (rfl)

@[simp] lemma homeomorphOfStrictIso_symm_apply {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C)
    (hFG : F ⋙ G = 𝟭 C) (hGF : G ⋙ F = 𝟭 D) (q : classifyingSpace D) :
    (homeomorphOfStrictIso F G hFG hGF).symm q = mapOfFunctor G q := (rfl)

end UniverseChange

section EdgesAndFundamentalGroupoid

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The edge path in `classifyingSpace C` from `vertex X` to `vertex Y` associated to `f : X ⟶ Y`.
-/
noncomputable def edgePath {X Y : C} (f : X ⟶ Y) : Path (vertex X) (vertex Y) :=
  (nerve.edgeMk f).toTopPath

lemma edgePath_apply {X Y : C} (f : X ⟶ Y) (t : unitInterval) :
    edgePath f t =
      SSet.toTopObjMk (nerve.objEquiv.symm (ComposableArrows.mk₁ f))
        (StdSimplex.homeomorphI.symm t) :=
  ((nerve.edgeMk f).toTopPath_apply t).trans
    (congrArg (SSet.toTopObjMk · _) (nerve.objEquiv_symm_eq _).symm)

/-- The edge path of `𝟙 X` is the constant path at `vertex X`. -/
@[simp] lemma edgePath_id (X : C) : edgePath (𝟙 X) = Path.refl (vertex X) := by
  ext t
  refine (congrArg (fun e : (nerve C).Edge _ _ ↦ e.toTopPath t) (nerve.edgeMk_id X)).trans ?_
  have hid : (SSet.Edge.id (X := nerve C) (nerveEquiv.symm X)).toTopPath t =
      (SSet.Edge.id (nerve.objEquiv.symm (nerveEquiv.symm X))).toTopPath t :=
    congrArg (fun x : (nerve C) _⦋0⦌ ↦ (SSet.Edge.id x).toTopPath t)
      (nerve.objEquiv_symm_nerveEquiv_symm X).symm
  rw [hid, SSet.Edge.toTopPath_id, ← vertex_eq_toTopPoint]

/-- Pushing `edgePath f` forward along `mapOfFunctor F` gives `edgePath (F.map f)` up to
`Path.cast`. -/
lemma edgePath_mapOfFunctor {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    edgePath (F.map f) =
      ((edgePath f).map (mapOfFunctor F).continuous).cast
        (mapOfFunctor_vertex F X).symm (mapOfFunctor_vertex F Y).symm := by
  ext t
  rw [edgePath_apply, Path.cast_coe, Path.map_coe, Function.comp_apply, edgePath_apply,
    mapOfFunctor_toTopObjMk, Equiv.apply_symm_apply, Functor.mapComposableArrows_obj_mk₁]

/-- Pushing `edgePath f` forward along `classifyingSpaceMap F` gives `edgePath (F.map f)`. -/
lemma edgePath_map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    edgePath (F.map f) =
      ((edgePath f).map (classifyingSpaceMap F).hom.continuous).cast
        (classifyingSpaceMap_vertex F X).symm (classifyingSpaceMap_vertex F Y).symm := by
  ext t
  simpa [mapOfFunctor_eq_classifyingSpaceMap] using congrArg (· t) (edgePath_mapOfFunctor F f)

/-- For `f : X ⟶ Y` and `g : Y ⟶ Z`, `(edgePath f).trans (edgePath g)` is homotopic rel endpoints
to `edgePath (f ≫ g)`. -/
theorem homotopic_edgePath_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((edgePath f).trans (edgePath g)).Homotopic (edgePath (f ≫ g)) :=
  ((nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl).some.homotopic_toTopPath

/-- The canonical functor `C ⥤ FundamentalGroupoid (classifyingSpace C)` sending `X` to `vertex X`
and `f : X ⟶ Y` to `Path.Homotopic.Quotient.mk (edgePath f)`. -/
@[expose, implicit_reducible, simps]
noncomputable def toFundamentalGroupoid (C : Type u) [Category.{v} C] :
    C ⥤ FundamentalGroupoid (classifyingSpace C) where
  obj X := .mk (vertex X)
  map f := FundamentalGroupoid.fromPath (.mk (edgePath f))
  map_id X := by simp [FundamentalGroupoid.id_eq_path_refl]
  map_comp f g := _root_.Quotient.sound (homotopic_edgePath_comp f g).symm

/-- Naturality isomorphism comparing `toFundamentalGroupoid` along `F : C ⥤ D` across arbitrary
universes with `FundamentalGroupoid.map (mapOfFunctor F)`. -/
noncomputable def toFundamentalGroupoidMapOfFunctorNatIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) :
    F ⋙ toFundamentalGroupoid D ≅
      toFundamentalGroupoid C ⋙ FundamentalGroupoid.map (mapOfFunctor F) :=
  let hobj (X : C) : (F ⋙ toFundamentalGroupoid D).obj X =
      (toFundamentalGroupoid C ⋙ FundamentalGroupoid.map (mapOfFunctor F)).obj X :=
    FundamentalGroupoid.ext (mapOfFunctor_vertex F X).symm
  NatIso.ofComponents (fun X ↦ eqToIso (hobj X)) fun {X Y} f ↦ by
    rw [← cancel_mono (eqToIso (hobj Y)).inv, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      eqToIso.hom, eqToIso.inv]
    dsimp only [Functor.comp_map]
    rw [toFundamentalGroupoid_map, toFundamentalGroupoid_map, Category.assoc,
      FundamentalGroupoid.conj_eqToHom_map_fromPath (mapOfFunctor F) (edgePath f)
        (mapOfFunctor_vertex F X).symm (mapOfFunctor_vertex F Y).symm]
    exact _root_.Quotient.sound (by rw [edgePath_mapOfFunctor])

@[simp] lemma toFundamentalGroupoidMapOfFunctorNatIso_hom_app {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (X : C) :
    (toFundamentalGroupoidMapOfFunctorNatIso F).hom.app X =
      eqToHom (show (F ⋙ toFundamentalGroupoid D).obj X =
          (toFundamentalGroupoid C ⋙ FundamentalGroupoid.map (mapOfFunctor F)).obj X
        from congrArg FundamentalGroupoid.mk (mapOfFunctor_vertex F X).symm) := (rfl)

@[simp] lemma toFundamentalGroupoidMapOfFunctorNatIso_inv_app {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (X : C) :
    (toFundamentalGroupoidMapOfFunctorNatIso F).inv.app X =
      eqToHom (show (toFundamentalGroupoid C ⋙ FundamentalGroupoid.map (mapOfFunctor F)).obj X =
          (F ⋙ toFundamentalGroupoid D).obj X
        from congrArg FundamentalGroupoid.mk (mapOfFunctor_vertex F X)) := (rfl)

/-- Naturality isomorphism comparing `toFundamentalGroupoid` along `F : C ⥤ D` with
`FundamentalGroupoid.map (classifyingSpaceMap F).hom`. -/
noncomputable def toFundamentalGroupoidNatIso (F : C ⥤ D) :
    F ⋙ toFundamentalGroupoid D ≅
      toFundamentalGroupoid C ⋙ FundamentalGroupoid.map (classifyingSpaceMap F).hom :=
  toFundamentalGroupoidMapOfFunctorNatIso F ≪≫
    Functor.isoWhiskerLeft (toFundamentalGroupoid C)
      (eqToIso (congrArg FundamentalGroupoid.map (mapOfFunctor_eq_classifyingSpaceMap F)))

@[simp] lemma toFundamentalGroupoidNatIso_hom_app (F : C ⥤ D) (X : C) :
    (toFundamentalGroupoidNatIso F).hom.app X =
      eqToHom (show (F ⋙ toFundamentalGroupoid D).obj X =
          (toFundamentalGroupoid C ⋙
            FundamentalGroupoid.map (classifyingSpaceMap F).hom).obj X
        from congrArg FundamentalGroupoid.mk (classifyingSpaceMap_vertex F X).symm) := by
  simp [toFundamentalGroupoidNatIso]

@[simp] lemma toFundamentalGroupoidNatIso_inv_app (F : C ⥤ D) (X : C) :
    (toFundamentalGroupoidNatIso F).inv.app X =
      eqToHom (show (toFundamentalGroupoid C ⋙
          FundamentalGroupoid.map (classifyingSpaceMap F).hom).obj X =
          (F ⋙ toFundamentalGroupoid D).obj X
        from congrArg FundamentalGroupoid.mk (classifyingSpaceMap_vertex F X)) := by
  simp [toFundamentalGroupoidNatIso]

end EdgesAndFundamentalGroupoid

section Examples

/-- The classifying space `classifyingSpace C` is nonempty if and only if `C` is nonempty. -/
@[simp] lemma nonempty_iff (C : Type u) [Category.{v} C] :
    Nonempty (classifyingSpace C) ↔ Nonempty C :=
  (SSet.nonempty_toTop_iff (nerve C)).trans nerveEquiv.nonempty_congr

/-- The classifying space `classifyingSpace C` is empty if and only if `C` is empty. -/
@[simp] lemma isEmpty_iff (C : Type u) [Category.{v} C] :
    IsEmpty (classifyingSpace C) ↔ IsEmpty C := by
  rw [← not_nonempty_iff, nonempty_iff, not_nonempty_iff]

instance instIsEmpty (C : Type u) [Category.{v} C] [IsEmpty C] : IsEmpty (classifyingSpace C) :=
  (isEmpty_iff C).2 ‹_›

instance instNonempty (C : Type u) [Category.{v} C] [Nonempty C] : Nonempty (classifyingSpace C) :=
  (nonempty_iff C).2 ‹_›

/-- For `[IsDiscrete C]`, `classifyingSpace C` is isomorphic in `TopCat` to discrete `ULift.{v} C`.
-/
noncomputable def isDiscreteIso (C : Type u) [Category.{v} C] [IsDiscrete C] :
    classifyingSpace C ≅ TopCat.discrete.obj (ULift.{v} C) :=
  SSet.toTop.mapIso (nerve.isDiscreteIso C) ≪≫ SSet.toTopConstIso (ULift.{v} C)

@[simp] lemma isDiscreteIso_hom_vertex {C : Type u} [Category.{v} C] [IsDiscrete C] (X : C) :
    (isDiscreteIso C).hom (vertex X) = ULift.up X := by
  have h1 : (SSet.toTop.map (nerve.isDiscreteIso C).hom) (vertex X) =
      SSet.toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{v} C)) (ULift.up X) := by
    rw [vertex_eq_toTopPoint, SSet.toTop_map_toTopPoint, nerve.isDiscreteIso_hom_app,
      Equiv.apply_symm_apply, nerveEquiv_symm_obj]
  exact (ConcreteCategory.comp_apply _ _ (vertex X)).trans
    ((congrArg (SSet.toTopConstIso (ULift.{v} C)).hom h1).trans
      (SSet.toTopConstIso_hom_toTopPoint (ULift.{v} C) (ULift.up X)))

@[simp] lemma isDiscreteIso_inv_apply {C : Type u} [Category.{v} C] [IsDiscrete C]
    (x : ULift.{v} C) : (isDiscreteIso C).inv x = vertex x.down := by
  have h0 : (Functor.const (Fin 1)).obj x.down = nerveEquiv.symm x.down :=
    ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)
  refine (ConcreteCategory.comp_apply (SSet.toTopConstIso (ULift.{v} C)).inv
    (SSet.toTop.map (nerve.isDiscreteIso C).inv) x).trans ?_
  rw [SSet.toTopConstIso_inv_apply, SSet.toTop_map_toTopPoint, nerve.isDiscreteIso_inv_app, h0,
    ← vertex_eq_toTopPoint]

/-- For `[IsDiscrete C]`, `classifyingSpace C` is homeomorphic to discrete `C`. -/
noncomputable def isDiscreteHomeomorph (C : Type u) [Category.{v} C] [IsDiscrete C] :
    classifyingSpace C ≃ₜ TopCat.discrete.obj C :=
  (TopCat.homeoOfIso (isDiscreteIso C)).trans
    { toEquiv := Equiv.ulift, continuous_toFun := continuous_bot,
      continuous_invFun := continuous_bot }

@[simp] lemma isDiscreteHomeomorph_vertex {C : Type u} [Category.{v} C] [IsDiscrete C] (X : C) :
    isDiscreteHomeomorph C (vertex X) = X := by
  simp [isDiscreteHomeomorph]; rfl

@[simp] lemma isDiscreteHomeomorph_symm_apply {C : Type u} [Category.{v} C] [IsDiscrete C]
    (X : TopCat.discrete.obj C) : (isDiscreteHomeomorph C).symm X = vertex (C := C) X :=
  (isDiscreteHomeomorph C).injective
    ((Homeomorph.apply_symm_apply _ _).trans (isDiscreteHomeomorph_vertex (C := C) X).symm)

instance instDiscreteTopology (C : Type u) [Category.{v} C] [IsDiscrete C] :
    DiscreteTopology (classifyingSpace C) :=
  (isDiscreteHomeomorph C).isEmbedding.discreteTopology

instance instSubsingleton (C : Type u) [Category.{v} C] [Subsingleton C] [IsDiscrete C] :
    Subsingleton (classifyingSpace C) := by
  have : Subsingleton (TopCat.discrete.obj C) := ‹Subsingleton C›
  exact (isDiscreteHomeomorph C).toEquiv.subsingleton

/-- The classifying space of a discrete category with a unique object has unique point
`vertex default`. -/
noncomputable instance instUnique (C : Type u) [Category.{v} C] [Unique C] [IsDiscrete C] :
    Unique (classifyingSpace C) where
  default := vertex default
  uniq _ := Subsingleton.elim _ _

@[simp] lemma vertex_default_eq_default (C : Type u) [Category.{v} C] [Unique C] [IsDiscrete C] :
    vertex (default : C) = default := (rfl)

/-- `classifyingSpace (Discrete S)` is isomorphic in `TopCat` to discrete `S`. -/
noncomputable def discreteIso (S : Type u) :
    classifyingSpace (Discrete S) ≅ TopCat.discrete.obj S :=
  isDiscreteIso (Discrete S) ≪≫ TopCat.discrete.mapIso (Equiv.ulift.trans discreteEquiv).toIso

@[simp] lemma discreteIso_hom_vertex (S : Type u) (s : S) :
    (discreteIso S).hom (vertex (Discrete.mk s)) = s :=
  (ConcreteCategory.comp_apply _ _ _).trans
    (congrArg (TopCat.discrete.map (Equiv.ulift.trans discreteEquiv).toIso.hom)
      (isDiscreteIso_hom_vertex (X := Discrete.mk s)))

@[simp] lemma discreteIso_inv_apply (S : Type u) (s : S) :
    (discreteIso S).inv s = vertex (Discrete.mk s) :=
  (ConcreteCategory.comp_apply
    (TopCat.discrete.mapIso (Equiv.ulift.trans discreteEquiv).toIso).inv
    (isDiscreteIso (Discrete S)).inv s).trans
    (isDiscreteIso_inv_apply (ULift.up (Discrete.mk s)))

/-- Homeomorphism between `classifyingSpace (Discrete S)` and discrete `S`. -/
noncomputable def discreteHomeomorph (S : Type u) :
    classifyingSpace (Discrete S) ≃ₜ TopCat.discrete.obj S :=
  TopCat.homeoOfIso (discreteIso S)

@[simp] lemma discreteHomeomorph_vertex (S : Type u) (s : S) :
    discreteHomeomorph S (vertex (Discrete.mk s)) = s :=
  discreteIso_hom_vertex S s

@[simp] lemma discreteHomeomorph_symm_apply (S : Type u) (s : TopCat.discrete.obj S) :
    (discreteHomeomorph S).symm s = vertex (Discrete.mk s) :=
  discreteIso_inv_apply S s

/-- A preorder order-isomorphic to `Fin (n + 1)` has classifying space homeomorphic to
`StdSimplex ℝ (Fin (n + 1))`. -/
noncomputable def preorderHomeomorphStdSimplex {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) : classifyingSpace α ≃ₜ StdSimplex ℝ (Fin (n + 1)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.stdSimplex.isoOfRepresentableBy (nerve.representableBy α e)).symm)).trans
    ⦋n⦌.toTopHomeo.{u}

@[simp] lemma preorderHomeomorphStdSimplex_toTopObjMk {n m : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (s : (nerve α) _⦋m⦌) (w : StdSimplex ℝ (Fin (m + 1))) :
    preorderHomeomorphStdSimplex e (SSet.toTopObjMk s w) =
      w.map fun i ↦ e ((nerve.objEquiv s).obj i) := by
  let θ : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.Hom.mk
    ⟨fun i ↦ e ((nerve.objEquiv s).obj i),
      fun _ _ hij ↦ e.monotone (leOfHom ((nerve.objEquiv s).map (homOfLE hij)))⟩
  have hθ : (nerve.representableBy α e).homEquiv θ = s :=
    nerve.objEquiv.injective <| ComposableArrows.ext
      (fun i ↦ by
        rw [nerve.objEquiv_eq]
        dsimp [nerve.representableBy, SimplexCategory.homEquivFunctor,
          SimplexCategory.homEquivOrderHom, θ]
        exact e.symm_apply_apply _)
      (fun _ _ ↦ Subsingleton.elim _ _)
  have hinv : (SSet.stdSimplex.isoOfRepresentableBy (nerve.representableBy α e)).inv.app (op ⦋m⦌)
      s = SSet.stdSimplex.objEquiv.{u}.symm θ := by
    simp [SSet.stdSimplex.isoOfRepresentableBy, ← hθ]
  have hyon : SSet.yonedaEquiv.symm (SSet.stdSimplex.objEquiv.{u}.symm θ) =
      SSet.stdSimplex.map θ :=
    SSet.yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_map])
  rw [preorderHomeomorphStdSimplex, Homeomorph.trans_apply, TopCat.homeoOfIso_apply,
    Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, SSet.toTop_map_toTopObjMk, hinv,
    SSet.toTopObjMk_eq_toTop_map, hyon, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply]
  rfl

lemma preorderHomeomorphStdSimplex_symm_eq_toTopObjMk {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (w : StdSimplex ℝ (Fin (n + 1))) :
    (preorderHomeomorphStdSimplex e).symm w =
      SSet.toTopObjMk (nerve.objEquiv.symm e.symm.monotone.functor) w := by
  apply (preorderHomeomorphStdSimplex e).injective
  rw [Homeomorph.apply_symm_apply, preorderHomeomorphStdSimplex_toTopObjMk, Equiv.apply_symm_apply]
  simpa [Function.id_def] using (StdSimplex.map_id w).symm

@[simp] lemma preorderHomeomorphStdSimplex_vertex {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (a : α) :
    preorderHomeomorphStdSimplex e (vertex a) = StdSimplex.single (e a) := by
  rw [vertex_eq_toTopObjMk a (StdSimplex.single 0), preorderHomeomorphStdSimplex_toTopObjMk,
    Equiv.apply_symm_apply, StdSimplex.map_single, nerveEquiv_symm_obj]

@[simp] lemma preorderHomeomorphStdSimplex_symm_single {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (i : Fin (n + 1)) :
    (preorderHomeomorphStdSimplex e).symm (StdSimplex.single i) = vertex (e.symm i) :=
  (preorderHomeomorphStdSimplex e).injective (by simp)

/-- The classifying space of a preorder order-isomorphic to `Fin (n + 1)` is contractible. -/
lemma contractibleSpace_of_orderIso_fin {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) : ContractibleSpace (classifyingSpace α) :=
  (preorderHomeomorphStdSimplex e).contractibleSpace

instance (n : ℕ) [NeZero n] : ContractibleSpace (classifyingSpace (Fin n)) := by
  obtain _ | n := n
  · exact absurd rfl (NeZero.ne 0)
  · exact contractibleSpace_of_orderIso_fin (OrderIso.refl (Fin (n + 1)))

/-- The classifying space of `Fin 2` is homeomorphic to `unitInterval`, sending `vertex 0` to `0`
and `vertex 1` to `1`. -/
noncomputable def finTwoHomeomorphI : classifyingSpace (Fin 2) ≃ₜ unitInterval :=
  (preorderHomeomorphStdSimplex (OrderIso.refl (Fin 2))).trans StdSimplex.homeomorphI

@[simp] lemma finTwoHomeomorphI_toTopObjMk {m : ℕ} (s : (nerve (Fin 2)) _⦋m⦌)
    (w : StdSimplex ℝ (Fin (m + 1))) :
    finTwoHomeomorphI (SSet.toTopObjMk s w) =
      StdSimplex.homeomorphI (w.map ((nerve.objEquiv s).obj)) := by
  simp [finTwoHomeomorphI]

@[simp] lemma finTwoHomeomorphI_vertex_zero : finTwoHomeomorphI (vertex (0 : Fin 2)) = 0 := by
  simp [finTwoHomeomorphI]

@[simp] lemma finTwoHomeomorphI_vertex_one : finTwoHomeomorphI (vertex (1 : Fin 2)) = 1 := by
  simp [finTwoHomeomorphI]

@[simp] lemma finTwoHomeomorphI_symm_zero : finTwoHomeomorphI.symm 0 = vertex (0 : Fin 2) :=
  finTwoHomeomorphI.injective (by simp)

@[simp] lemma finTwoHomeomorphI_symm_one : finTwoHomeomorphI.symm 1 = vertex (1 : Fin 2) :=
  finTwoHomeomorphI.injective (by simp)

@[simp] lemma finTwoHomeomorphI_edgePath_apply (f : (0 : Fin 2) ⟶ 1) (t : unitInterval) :
    finTwoHomeomorphI (edgePath f t) = t := by
  have hid : (ComposableArrows.mk₁ f).obj = (id : Fin 2 → Fin 2) := by funext i; fin_cases i <;> rfl
  rw [edgePath_apply, finTwoHomeomorphI_toTopObjMk, Equiv.apply_symm_apply, hid,
    StdSimplex.map_id, Homeomorph.apply_symm_apply]

lemma finTwoHomeomorphI_symm_apply (t : unitInterval) :
    finTwoHomeomorphI.symm t = edgePath (homOfLE (zero_le_one' (Fin 2))) t :=
  finTwoHomeomorphI.injective (by simp)

lemma coe_finTwoHomeomorphI_symm :
    ⇑finTwoHomeomorphI.symm = edgePath (homOfLE (zero_le_one' (Fin 2))) :=
  funext finTwoHomeomorphI_symm_apply

/-- Reflection of `classifyingSpace (Fin 2)` swapping `vertex 0` and `vertex 1`. -/
noncomputable def finTwoReflect : classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2) :=
  (TopCat.isoOfHomeo
    ((finTwoHomeomorphI.trans unitInterval.symmHomeomorph).trans finTwoHomeomorphI.symm)).hom

lemma finTwoReflect_apply (p : classifyingSpace (Fin 2)) :
    finTwoReflect p = finTwoHomeomorphI.symm (unitInterval.symm (finTwoHomeomorphI p)) := by
  simp [finTwoReflect]

@[simp] lemma finTwoHomeomorphI_finTwoReflect (p : classifyingSpace (Fin 2)) :
    finTwoHomeomorphI (finTwoReflect p) = unitInterval.symm (finTwoHomeomorphI p) := by
  rw [finTwoReflect_apply, Homeomorph.apply_symm_apply]

@[simp] lemma finTwoReflect_vertex_zero : finTwoReflect (vertex (0 : Fin 2)) = vertex 1 := by
  simp [finTwoReflect_apply]

@[simp] lemma finTwoReflect_vertex_one : finTwoReflect (vertex (1 : Fin 2)) = vertex 0 := by
  simp [finTwoReflect_apply]

/-- `finTwoReflect` is not `classifyingSpaceMap F` for any `F : Fin 2 ⥤ Fin 2`. -/
theorem not_exists_classifyingSpaceMap_eq_finTwoReflect :
    ¬ ∃ F : Fin 2 ⥤ Fin 2, classifyingSpaceMap F = finTwoReflect := by
  rintro ⟨F, hF⟩
  have h0 : F.obj 0 = 1 :=
    vertex_inj.1 (by simpa using ConcreteCategory.congr_hom hF (vertex (0 : Fin 2)))
  have h1 : F.obj 1 = 0 :=
    vertex_inj.1 (by simpa using ConcreteCategory.congr_hom hF (vertex (1 : Fin 2)))
  have hle : F.obj 0 ≤ F.obj 1 := leOfHom (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)))
  rw [h0, h1] at hle
  exact absurd hle (by decide)

end Examples

end classifyingSpace

/-- `classifyingSpaceMap` is injective on functors. -/
theorem classifyingSpaceMap_injective {C D : Type u} [Category.{v} C] [Category.{v} D] :
    Function.Injective
      (classifyingSpaceMap : (C ⥤ D) → (classifyingSpace C ⟶ classifyingSpace D)) := fun _ _ h ↦
  classifyingSpace.mapOfFunctor_injective
    (by simp [classifyingSpace.mapOfFunctor_eq_classifyingSpaceMap, h])

/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` is faithful. -/
instance : classifyingSpaceFunctor.{v, u}.Faithful :=
  inferInstanceAs (nerveFunctor.{v, u} ⋙ SSet.toTop).Faithful

/-- Whenever `C` has `Y ≠ X`, `classifyingSpaceMap (𝟭 C)` differs from the constant map at `X`. -/
lemma classifyingSpaceMap_id_ne_const {C : Type u} [Category.{v} C] {X Y : C} (hne : Y ≠ X) :
    classifyingSpaceMap (𝟭 C) ≠ classifyingSpaceMap ((Functor.const C).obj X) := fun h ↦ by
  have hy := ConcreteCategory.congr_hom h (classifyingSpace.vertex Y)
  rw [classifyingSpaceMap_vertex, classifyingSpaceMap_const, Functor.id_obj, TopCat.const_apply,
    classifyingSpace.vertex_inj] at hy
  exact hne hy

attribute [local instance] uliftCategory in
/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` is not full in any universes
`v, u`. -/
theorem not_full_classifyingSpaceFunctor : ¬ classifyingSpaceFunctor.{v, u}.Full := by
  intro hFull
  let C₀ : Type u := ULift.{u} (ULiftHom.{v} (Fin 2))
  let toFin : C₀ ⥤ Fin 2 := _root_.CategoryTheory.ULift.downFunctor ⋙ ULiftHom.down
  let fromFin : Fin 2 ⥤ C₀ := ULiftHom.up ⋙ _root_.CategoryTheory.ULift.upFunctor
  have hTF : toFin ⋙ fromFin = 𝟭 C₀ :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ ULift.ext (Subsingleton.elim _ _))
  have hFT : fromFin ⋙ toFin = 𝟭 (Fin 2) :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  let e : classifyingSpace C₀ ≃ₜ classifyingSpace (Fin 2) :=
    classifyingSpace.homeomorphOfStrictIso toFin fromFin hTF hFT
  let reflMor : classifyingSpace C₀ ⟶ classifyingSpace C₀ :=
    TopCat.ofHom ((e.symm : C(classifyingSpace (Fin 2), classifyingSpace C₀)).comp
      (classifyingSpace.finTwoReflect.hom.comp
        (e : C(classifyingSpace C₀, classifyingSpace (Fin 2)))))
  obtain ⟨G, hG⟩ := classifyingSpaceFunctor.map_surjective (X := Cat.of C₀) (Y := Cat.of C₀)
    reflMor
  refine classifyingSpace.not_exists_classifyingSpaceMap_eq_finTwoReflect
    ⟨fromFin ⋙ G.toFunctor ⋙ toFin, TopCat.ext fun p ↦ ?_⟩
  have he (q : classifyingSpace C₀) : classifyingSpace.mapOfFunctor toFin q = e q := rfl
  have he_symm (x : classifyingSpace (Fin 2)) :
      classifyingSpace.mapOfFunctor fromFin x = e.symm x := rfl
  have hG' : (classifyingSpaceMap G.toFunctor).hom = reflMor.hom :=
    congrArg ConcreteCategory.hom hG
  refine (congrArg (· p)
    (classifyingSpace.mapOfFunctor_eq_classifyingSpaceMap
      (fromFin ⋙ G.toFunctor ⋙ toFin)).symm).trans ?_
  rw [classifyingSpace.mapOfFunctor_comp, classifyingSpace.mapOfFunctor_comp,
    ContinuousMap.comp_apply, ContinuousMap.comp_apply, he_symm, he,
    classifyingSpace.mapOfFunctor_eq_classifyingSpaceMap G.toFunctor, hG']
  simp [reflMor]

end TauCeti.CategoryTheory
