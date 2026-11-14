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
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.InducedCategory

/-!
# Classifying space of a category and of a functor

The classifying space `TauCeti.classifyingSpace C` of a category `C : Type u` with
`[Category.{v} C]` is the geometric realization `|nerve C| : TopCat.{max u v}` of its nerve, and a
functor `F : C ⥤ D` between categories in the same object and morphism universes induces
`TauCeti.classifyingSpaceMap F : classifyingSpace C ⟶ classifyingSpace D`, assembling into
`TauCeti.classifyingSpaceFunctor : Cat.{v, u} ⥤ TopCat.{max u v}`.

Each object `X : C` determines a canonical vertex `classifyingSpace.vertex X : classifyingSpace C`,
and each morphism `f : X ⟶ Y` determines a path `classifyingSpace.edgePath f` from `vertex X` to
`vertex Y`. Identity morphisms give constant paths (`classifyingSpace.edgePath_id`), composable
pairs `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy
`((edgePath f).trans (edgePath g)).Homotopic (edgePath (f ≫ g))` via the `2`-simplex
`ComposableArrows.mk₂ f g` (`classifyingSpace.homotopic_edgePath_comp`), and these assemble into
`classifyingSpace.toFundamentalGroupoid C : C ⥤ FundamentalGroupoid (classifyingSpace C)`.

To compare categories across different universes (such as `Functor.Elements.π F : F.Elements ⥤ C`
for `F : C ⥤ Type w`), `CategoryTheory.nerve.asSmallIso` identifies `nerve (AsSmall.{w} C)` with
`SSet.uliftFunctor.obj (nerve C)`, giving `classifyingSpace.asSmallHomeomorph` and the fully
universe-polymorphic continuous map
`classifyingSpace.mapOfFunctor : C(classifyingSpace C, classifyingSpace D)`.

We also record the concrete identifications and properties of classifying spaces:
* Faithfulness of `classifyingSpaceFunctor`, injectivity of `vertex`, and failure of fullness
  (`classifyingSpace.not_full_classifyingSpaceFunctor`, witnessed by interval reflection on
  `Fin 2`).
* Finite nonempty linear orders (`classifyingSpace.preorderHomeomorphStdSimplex`,
  `classifyingSpace.finTwoHomeomorphI`), empty categories, single-object single-morphism categories
  (`classifyingSpace.instUnique`), discrete categories (`classifyingSpace.discreteIso`,
  `classifyingSpace.discreteHomeomorph`), constant functors (`classifyingSpaceMap_const`), and
  endpoint inclusions/projections on `Fin 2`.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Mathematics 341, Springer, 1973, §1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145, AMS, 2013, Chapter IV, §3.
-/

public section

open CategoryTheory Limits Opposite Simplicial Convexity

universe w u₁ v₁ u₂ v₂ u₃ v₃ v u

namespace CategoryTheory.nerve

/-- Object `X : C` viewed as a `0`-simplex of `nerve C`. -/
@[expose]
def mk₀ {C : Type u} [Category.{v} C] (X : C) : (nerve C) _⦋0⦌ :=
  ComposableArrows.mk₀ X

@[simp]
lemma nerveMap_app_nerve_mk₀ {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (X : C) :
    (nerveMap F).app (op ⦋0⦌) (mk₀ X) = mk₀ (F.obj X) :=
  nerveMap_app_mk₀ F X

/-- Pushforward of an `n`-simplex of `nerve C` along an arbitrary functor `F : C ⥤ D` (possibly
changing universes). -/
@[expose]
def mapSimplex {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {n : ℕ} (s : (nerve C) _⦋n⦌) : (nerve D) _⦋n⦌ :=
  (F.mapComposableArrows n).obj s

@[simp]
lemma mapSimplex_mk₀ {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (X : C) :
    mapSimplex F (mk₀ X) = mk₀ (F.obj X) :=
  ComposableArrows.ext₀ rfl

@[simp]
lemma mapSimplex_id {C : Type u₁} [Category.{v₁} C] {n : ℕ} (s : (nerve C) _⦋n⦌) :
    mapSimplex (𝟭 C) s = s := by
  let s' : ComposableArrows C n := s
  change ((𝟭 C).mapComposableArrows n).obj s' = s'
  exact Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl

@[simp]
lemma mapSimplex_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) {n : ℕ} (s : (nerve C) _⦋n⦌) :
    mapSimplex (F ⋙ G) s = mapSimplex G (mapSimplex F s) := by
  let s' : ComposableArrows C n := s
  change ((F ⋙ G).mapComposableArrows n).obj s' =
    (G.mapComposableArrows n).obj ((F.mapComposableArrows n).obj s')
  exact Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl

lemma nerveMap_app_eq_mapSimplex {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ} (s : (nerve C) _⦋n⦌) :
    (nerveMap F).app (op ⦋n⦌) s = mapSimplex F s :=
  (rfl)

/-- The nerve of `AsSmall.{w} C` is naturally isomorphic to the universe lift of `nerve C`. -/
def asSmallIso (C : Type u) [Category.{v} C] :
    nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) where
  hom :=
    { app m := ↾fun s ↦ ULift.up ((AsSmall.down.mapComposableArrows m.unop.len).obj s)
      naturality _ _ _ := rfl }
  inv :=
    { app m := ↾fun s ↦ (AsSmall.up.mapComposableArrows m.unop.len).obj s.down
      naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

@[simp]
lemma asSmallIso_hom_app {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve (AsSmall.{w} C)) _⦋n⦌) :
    (asSmallIso.{w} C).hom.app (op ⦋n⦌) s =
      (nerve C).uliftFunctorObjEquiv.{w} (op ⦋n⦌) (mapSimplex AsSmall.down s) :=
  (rfl)

@[simp]
lemma asSmallIso_inv_app {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (SSet.uliftFunctor.{w, max u v}.obj (nerve C)) _⦋n⦌) :
    (asSmallIso.{w} C).inv.app (op ⦋n⦌) s =
      mapSimplex AsSmall.up (((nerve C).uliftFunctorObjEquiv.{w} (op ⦋n⦌)).symm s) :=
  (rfl)

/-- The nerve of a discrete category `Discrete S` is isomorphic to the constant simplicial set on
`S`. -/
def discreteIso (S : Type u) :
    nerve (Discrete S) ≅ (Functor.const SimplexCategoryᵒᵖ).obj S where
  hom :=
    { app m := ↾fun F ↦ (F.obj 0).as
      naturality m₁ m₂ θ := ConcreteCategory.hom_ext _ _ fun F ↦ by
        dsimp [nerve, Functor.const]
        exact (Discrete.eq_of_hom (F.map (homOfLE (Fin.zero_le _)))).symm }
  inv :=
    { app m := ↾fun s ↦ (Functor.const (Fin (m.unop.len + 1))).obj (Discrete.mk s)
      naturality _ _ _ := rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext ⟨⟨n⟩⟩
    refine ConcreteCategory.hom_ext _ _ fun F ↦ ?_
    let F' : ComposableArrows (Discrete S) n := F
    change (Functor.const (Fin (n + 1))).obj (Discrete.mk (F'.obj 0).as) = F'
    exact Functor.ext
      (fun i ↦ Discrete.ext (Discrete.eq_of_hom (F'.map (homOfLE (Fin.zero_le i)))))
      (fun _ _ _ ↦ Subsingleton.elim _ _)
  inv_hom_id := rfl

@[simp]
lemma discreteIso_hom_app_mk₀ (S : Type u) (s : S) :
    ConcreteCategory.hom (X := (nerve (Discrete S)).obj (op ⦋0⦌)) (Y := S)
      ((discreteIso S).hom.app (op ⦋0⦌)) (mk₀ (Discrete.mk s)) = s :=
  (rfl)

end CategoryTheory.nerve

namespace TauCeti

/-- `nerveMap` is injective on functors: `0`- and `1`-simplices of the nerve recover the action of a
functor on objects and morphisms. -/
theorem nerveMap_injective {C D : Type u} [Category.{v} C] [Category.{v} D] :
    Function.Injective (nerveMap : (C ⥤ D) → (nerve C ⟶ nerve D)) := by
  intro F G h
  have h₁ {X Y : C} (f : X ⟶ Y) : Arrow.mk (F.map f) = Arrow.mk (G.map f) := by
    rw [← ComposableArrows.mk₁_eq_mk₁_iff, ← nerveMap_app_mk₁, ← nerveMap_app_mk₁, h]
  refine CategoryTheory.Functor.ext (fun X ↦ congr($(h₁ (𝟙 X)).left)) fun X Y f ↦ ?_
  obtain ⟨_, _, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 (h₁ f)
  exact hf

/-- The classifying space `BC = |nerve C|` of a category `C`, defined as the geometric realization
of its nerve. -/
@[expose, implicit_reducible]
noncomputable def classifyingSpace (C : Type u) [Category.{v} C] : TopCat.{max u v} :=
  SSet.toTop.obj (nerve C)

lemma classifyingSpace_def (C : Type u) [Category.{v} C] :
    classifyingSpace C = SSet.toTop.obj (nerve C) :=
  (rfl)

/-- The continuous map `BF : BC ⟶ BD` induced on classifying spaces by a functor `F : C ⥤ D`. -/
@[expose, implicit_reducible]
noncomputable def classifyingSpaceMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : classifyingSpace C ⟶ classifyingSpace D :=
  SSet.toTop.map (nerveMap F)

lemma classifyingSpaceMap_def {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    classifyingSpaceMap F = SSet.toTop.map (nerveMap F) :=
  (rfl)

@[simp]
lemma classifyingSpaceMap_id (C : Type u) [Category.{v} C] :
    classifyingSpaceMap (𝟭 C) = 𝟙 (classifyingSpace C) := by
  have hid : nerveMap (𝟭 C) = 𝟙 (nerve C) := nerveFunctor.map_id (Cat.of C)
  rw [classifyingSpaceMap, hid, SSet.toTop.map_id]
  rfl

@[simp, reassoc]
lemma classifyingSpaceMap_comp {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    classifyingSpaceMap (F ⋙ G) = classifyingSpaceMap F ≫ classifyingSpaceMap G := by
  have hcomp : nerveMap (F ⋙ G) = nerveMap F ≫ nerveMap G :=
    nerveFunctor.map_comp (X := Cat.of C) (Y := Cat.of D) (Z := Cat.of E) F.toCatHom G.toCatHom
  rw [classifyingSpaceMap, hcomp, SSet.toTop.map_comp]
  rfl

/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}`, defined as
`nerveFunctor ⋙ SSet.toTop`. -/
@[expose, implicit_reducible]
noncomputable def classifyingSpaceFunctor : Cat.{v, u} ⥤ TopCat.{max u v} :=
  nerveFunctor.{v, u} ⋙ SSet.toTop

lemma classifyingSpaceFunctor_def :
    classifyingSpaceFunctor.{v, u} = nerveFunctor.{v, u} ⋙ SSet.toTop :=
  (rfl)

@[simp]
lemma classifyingSpaceFunctor_obj (C : Cat.{v, u}) :
    classifyingSpaceFunctor.obj C = classifyingSpace C :=
  (rfl)

@[simp]
lemma classifyingSpaceFunctor_map {C D : Cat.{v, u}} (F : C ⟶ D) :
    classifyingSpaceFunctor.map F = classifyingSpaceMap F.toFunctor :=
  (rfl)

/-- `classifyingSpaceMap` is injective on functors. -/
theorem classifyingSpaceMap_injective {C D : Type u} [Category.{v} C] [Category.{v} D] :
    Function.Injective
      (classifyingSpaceMap : (C ⥤ D) → (classifyingSpace C ⟶ classifyingSpace D)) :=
  SSet.toTop.map_injective.comp nerveMap_injective

/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` is faithful. -/
instance : classifyingSpaceFunctor.{v, u}.Faithful where
  map_injective h := Cat.Hom.ext (classifyingSpaceMap_injective h)

namespace classifyingSpace

section VerticesAndEdges

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/-- The canonical vertex `[X]` of `classifyingSpace C` associated to an object `X : C`. -/
noncomputable def vertex (X : C) : classifyingSpace C :=
  SSet.toTopPoint (nerve.mk₀ X)

lemma vertex_eq_toTopPoint (X : C) :
    vertex X = SSet.toTopPoint (nerve.mk₀ X) :=
  (rfl)

lemma vertex_eq_toTopObjMk (X : C) (w : StdSimplex ℝ (Fin 1)) :
    vertex X = SSet.toTopObjMk (nerve.mk₀ X) w :=
  SSet.toTopPoint_eq_toTopObjMk (nerve.mk₀ X) w

/-- Explicit expression of `vertex X` via the adjunction unit `nerve C ⟶ Sing (classifyingSpace C)`,
matching the singular `0`-simplex evaluation on `nerve.mk₀ X`. -/
lemma vertex_eq_toSSetObjEquiv (X : C) :
    vertex X = TopCat.toSSetObjEquiv (classifyingSpace C) (op ⦋0⦌)
      (((sSetTopAdj.unit.app (nerve C)).app (op ⦋0⦌)) (nerve.mk₀ X)) default :=
  (vertex_eq_toTopObjMk X default).trans (SSet.toTopObjMk_def _ _)

@[simp]
lemma _root_.TauCeti.classifyingSpaceMap_vertex (F : C ⥤ D) (X : C) :
    classifyingSpaceMap F (vertex X) = vertex (F.obj X) := by
  rw [classifyingSpaceMap, vertex, SSet.toTop_map_toTopPoint, nerve.nerveMap_app_nerve_mk₀, vertex]

/-- A constant functor `(Functor.const C).obj Y` realizes to the constant map at `vertex Y`. -/
@[simp]
lemma _root_.TauCeti.classifyingSpaceMap_const (C D : Type u) [Category.{v} C] [Category.{v} D]
    (Y : D) :
    classifyingSpaceMap ((Functor.const C).obj Y) =
      TopCat.const (X := classifyingSpace C) (vertex Y) :=
  SSet.toTop_hom_ext fun n s w ↦ by
    let lhs : ComposableArrows D n := (((Functor.const C).obj Y).mapComposableArrows n).obj s
    let rhs : ComposableArrows D n := (ComposableArrows.mk₀ Y).whiskerLeft
      (SimplexCategory.toCat.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).toFunctor
    have hlr : lhs = rhs :=
      CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ f ↦ by
        refine ((Category.id_comp _).trans ((Category.comp_id _).trans ?_)).symm
        change rhs.map f = 𝟙 Y
        exact (ComposableArrows.mk₀ Y).map_id 0
    have hs : (nerveMap ((Functor.const C).obj Y)).app (op ⦋n⦌) s =
        (nerve D).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op (nerve.mk₀ Y) := hlr
    rw [classifyingSpaceMap, SSet.toTop_map_toTopObjMk, hs, SSet.toTopObjMk_map,
      SSet.toTopObjMk_zero, TopCat.const_apply, vertex]

/-- Distinct objects of `C` give distinct vertices of `classifyingSpace C`. -/
theorem vertex_injective (C : Type u) [Category.{v} C] :
    Function.Injective (vertex (C := C)) :=
  (SSet.toTopPoint_injective (nerve C)).comp nerveEquiv.symm.injective

@[simp]
lemma vertex_inj {X Y : C} : vertex X = vertex Y ↔ X = Y :=
  (vertex_injective C).eq_iff

/-- Every point of `classifyingSpace C` can be joined by a path to the vertex of some object of `C`.
-/
theorem exists_joined_vertex (p : classifyingSpace C) :
    ∃ X : C, Joined (vertex X) p := by
  obtain ⟨s, hs⟩ := SSet.exists_joined_toTopPoint (X := nerve C) p
  have hs' : nerve.mk₀ (nerveEquiv s) = s := nerveEquiv.left_inv s
  exact ⟨nerveEquiv s, by rwa [vertex, hs']⟩

/-- The edge path in `classifyingSpace C` from `vertex X` to `vertex Y` associated to a morphism
`f : X ⟶ Y`. -/
noncomputable def edgePath {X Y : C} (f : X ⟶ Y) : Path (vertex X) (vertex Y) :=
  (nerve.edgeMk f).toTopPath

lemma edgePath_apply {X Y : C} (f : X ⟶ Y) (t : unitInterval) :
    edgePath f t =
      SSet.toTopObjMk (X := nerve C) (ComposableArrows.mk₁ f) (StdSimplex.homeomorphI.symm t) :=
  (nerve.edgeMk f).toTopPath_apply t

/-- The edge path of an identity morphism `𝟙 X` is the constant path at `vertex X`. -/
@[simp]
lemma edgePath_id (X : C) : edgePath (𝟙 X) = Path.refl (vertex X) := by
  ext t
  exact (congrArg (fun e : (nerve C).Edge (nerve.mk₀ X) (nerve.mk₀ X) ↦ e.toTopPath t)
    (nerve.edgeMk_id X)).trans
    (congrArg (fun p : Path (vertex X) (vertex X) ↦ p t) (SSet.Edge.toTopPath_id (nerve.mk₀ X)))

lemma homotopic_edgePath_id (X : C) : (edgePath (𝟙 X)).Homotopic (Path.refl (vertex X)) := by
  rw [edgePath_id]

/-- Pushing `edgePath f` forward along `classifyingSpaceMap F` gives `edgePath (F.map f)` after
identifying endpoints via `classifyingSpaceMap_vertex`. -/
lemma edgePath_map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    edgePath (F.map f) =
      ((edgePath f).map (classifyingSpaceMap F).hom.continuous).cast
        (classifyingSpaceMap_vertex F X).symm (classifyingSpaceMap_vertex F Y).symm := by
  ext t
  rw [edgePath_apply, Path.cast_coe, Path.map_coe, Function.comp_apply, edgePath_apply]
  exact ((SSet.toTop_map_toTopObjMk (nerveMap F) _ _).trans
    (congrArg (SSet.toTopObjMk · _) (nerveMap_app_mk₁ F f))).symm

/-- For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, the concatenation of `edgePath f` and
`edgePath g` is homotopic rel endpoints to `edgePath (f ≫ g)`, witnessed by the `2`-simplex
`ComposableArrows.mk₂ f g`. -/
theorem homotopic_edgePath_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((edgePath f).trans (edgePath g)).Homotopic (edgePath (f ≫ g)) :=
  ((nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl).some.homotopic_toTopPath

/-- The canonical functor `C ⥤ FundamentalGroupoid (classifyingSpace C)` sending `X` to `vertex X`
and `f : X ⟶ Y` to the path homotopy class `Path.Homotopic.Quotient.mk (edgePath f)`. -/
@[expose, simps]
noncomputable def toFundamentalGroupoid (C : Type u) [Category.{v} C] :
    C ⥤ FundamentalGroupoid (classifyingSpace C) where
  obj X := .mk (vertex X)
  map f := FundamentalGroupoid.fromPath (.mk (edgePath f))
  map_id X := by simp [FundamentalGroupoid.id_eq_path_refl]
  map_comp f g := _root_.Quotient.sound (homotopic_edgePath_comp f g).symm

/-- Naturality isomorphism comparing `toFundamentalGroupoid` along a functor `F : C ⥤ D` with the
topological fundamental groupoid map of `classifyingSpaceMap F`. -/
noncomputable def toFundamentalGroupoidNatIso (F : C ⥤ D) :
    F ⋙ toFundamentalGroupoid D ≅
      toFundamentalGroupoid C ⋙ FundamentalGroupoid.map (classifyingSpaceMap F).hom := by
  have hobj (X : C) :
      (F ⋙ toFundamentalGroupoid D).obj X =
        (toFundamentalGroupoid C ⋙ FundamentalGroupoid.map (classifyingSpaceMap F).hom).obj X :=
    congrArg FundamentalGroupoid.mk (classifyingSpaceMap_vertex F X).symm
  refine NatIso.ofComponents (fun X ↦ eqToIso (hobj X)) fun {X Y} f ↦ ?_
  rw [← cancel_mono (eqToIso (hobj Y)).inv, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.assoc]
  change FundamentalGroupoid.fromPath (.mk (edgePath (F.map f))) =
    eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMap_vertex F X).symm) ≫
      Path.Homotopic.Quotient.map (.mk (edgePath f)) (classifyingSpaceMap F).hom ≫
      eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMap_vertex F Y))
  rw [FundamentalGroupoid.conj_eqToHom (classifyingSpaceMap_vertex F X).symm
      (classifyingSpaceMap_vertex F Y).symm,
    ← Path.Homotopic.Quotient.mk_map]
  exact _root_.Quotient.sound (by rw [edgePath_map])

end VerticesAndEdges

section UniverseChange

/-- Lifting `C` to `AsSmall.{w} C` produces a homeomorphic classifying space. -/
noncomputable def asSmallHomeomorph (C : Type u) [Category.{v} C] :
    classifyingSpace C ≃ₜ classifyingSpace (AsSmall.{w} C) :=
  ((nerve C).toTopUliftHomeomorph.{w}).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.asSmallIso.{w} C).symm))

@[simp]
lemma asSmallHomeomorph_toTopObjMk {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve C) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    asSmallHomeomorph.{w} C (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk (nerve.mapSimplex AsSmall.up s) w₀ := by
  change SSet.toTop.map (nerve.asSmallIso.{w} C).inv
    ((nerve C).toTopUliftHomeomorph.{w} (SSet.toTopObjMk s w₀)) = _
  rw [SSet.toTopUliftHomeomorph_toTopObjMk, SSet.toTop_map_toTopObjMk,
    nerve.asSmallIso_inv_app, Equiv.symm_apply_apply]

@[simp]
lemma asSmallHomeomorph_symm_toTopObjMk {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve (AsSmall.{w} C)) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    (asSmallHomeomorph.{w} C).symm (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk (nerve.mapSimplex AsSmall.down s) w₀ := by
  change ((nerve C).toTopUliftHomeomorph.{w}).symm
    (SSet.toTop.map (nerve.asSmallIso.{w} C).hom (SSet.toTopObjMk s w₀)) = _
  rw [SSet.toTop_map_toTopObjMk, SSet.toTopUliftHomeomorph_symm_toTopObjMk,
    nerve.asSmallIso_hom_app, Equiv.symm_apply_apply]

@[simp]
lemma asSmallHomeomorph_vertex {C : Type u} [Category.{v} C] (X : C) :
    asSmallHomeomorph.{w} C (vertex X) = vertex (AsSmall.up.obj X) := by
  rw [vertex_eq_toTopObjMk X default, asSmallHomeomorph_toTopObjMk, nerve.mapSimplex_mk₀]
  exact (vertex_eq_toTopObjMk (AsSmall.up.obj X) default).symm

@[simp]
lemma asSmallHomeomorph_symm_vertex {C : Type u} [Category.{v} C] (X : AsSmall.{w} C) :
    (asSmallHomeomorph.{w} C).symm (vertex X) = vertex (AsSmall.down.obj X) := by
  rw [vertex_eq_toTopObjMk X default, asSmallHomeomorph_symm_toTopObjMk, nerve.mapSimplex_mk₀]
  exact (vertex_eq_toTopObjMk (AsSmall.down.obj X) default).symm

/-- Continuous map `C(classifyingSpace C, classifyingSpace D)` induced by an arbitrary functor
`F : C ⥤ D` across possibly distinct object and morphism universes `(u₁, v₁)` and `(u₂, v₂)` (such
as `Functor.Elements.π F : F.Elements ⥤ C` when `F : C ⥤ Type w`). -/
noncomputable def mapOfFunctor {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) : C(classifyingSpace C, classifyingSpace D) :=
  ((asSmallHomeomorph.{max u₁ v₁} D).symm :
      C(classifyingSpace (AsSmall.{max u₁ v₁} D), classifyingSpace D)).comp
    ((classifyingSpaceMap
        (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up :
          AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D)).hom.comp
      (asSmallHomeomorph.{max u₂ v₂} C :
        C(classifyingSpace C, classifyingSpace (AsSmall.{max u₂ v₂} C))))

@[simp]
lemma mapOfFunctor_toTopObjMk {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {n : ℕ} (s : (nerve C) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    mapOfFunctor F (SSet.toTopObjMk s w₀) =
      SSet.toTopObjMk (nerve.mapSimplex F s) w₀ := by
  change (asSmallHomeomorph.{max u₁ v₁} D).symm
    (classifyingSpaceMap
      (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up :
        AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D)
      (asSmallHomeomorph.{max u₂ v₂} C (SSet.toTopObjMk s w₀))) = _
  rw [asSmallHomeomorph_toTopObjMk, classifyingSpaceMap, SSet.toTop_map_toTopObjMk,
    nerve.nerveMap_app_eq_mapSimplex, asSmallHomeomorph_symm_toTopObjMk,
    ← nerve.mapSimplex_comp, ← nerve.mapSimplex_comp]
  rfl

@[simp]
lemma mapOfFunctor_vertex {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (X : C) :
    mapOfFunctor F (vertex X) = vertex (F.obj X) := by
  rw [vertex_eq_toTopObjMk X default, mapOfFunctor_toTopObjMk, nerve.mapSimplex_mk₀]
  exact (vertex_eq_toTopObjMk (F.obj X) default).symm

@[simp]
lemma mapOfFunctor_id (C : Type u₁) [Category.{v₁} C] :
    mapOfFunctor (𝟭 C) = ContinuousMap.id (classifyingSpace C) := by
  ext p
  obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p
  rw [mapOfFunctor_toTopObjMk, nerve.mapSimplex_id, ContinuousMap.id_apply]

@[simp]
lemma mapOfFunctor_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) :
    mapOfFunctor (F ⋙ G) = (mapOfFunctor G).comp (mapOfFunctor F) := by
  ext p
  obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p
  rw [ContinuousMap.comp_apply, mapOfFunctor_toTopObjMk, mapOfFunctor_toTopObjMk,
    mapOfFunctor_toTopObjMk, nerve.mapSimplex_comp]

/-- When `C` and `D` share object and morphism universes, `mapOfFunctor F` agrees with the
underlying continuous map of `classifyingSpaceMap F`. -/
lemma mapOfFunctor_eq_classifyingSpaceMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    mapOfFunctor F = (classifyingSpaceMap F).hom := by
  ext p
  obtain ⟨n, s, w₀, rfl⟩ := SSet.exists_toTopObjMk p
  change mapOfFunctor F (SSet.toTopObjMk s w₀) = classifyingSpaceMap F (SSet.toTopObjMk s w₀)
  rw [mapOfFunctor_toTopObjMk, classifyingSpaceMap, SSet.toTop_map_toTopObjMk,
    nerve.nerveMap_app_eq_mapSimplex]

/-- Any pair of strictly mutually inverse functors `F : C ⥤ D` and `G : D ⥤ C` (such as universe
lifts via `ULift`, `ULiftHom`, or `AsSmall`) induces a homeomorphism on classifying spaces. -/
noncomputable def homeomorphOfStrictIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G : D ⥤ C)
    (hFG : F ⋙ G = 𝟭 C) (hGF : G ⋙ F = 𝟭 D) :
    classifyingSpace C ≃ₜ classifyingSpace D where
  toFun := mapOfFunctor F
  invFun := mapOfFunctor G
  left_inv p :=
    congrArg (· p) ((mapOfFunctor_comp F G).symm.trans (by rw [hFG, mapOfFunctor_id]))
  right_inv q :=
    congrArg (· q) ((mapOfFunctor_comp G F).symm.trans (by rw [hGF, mapOfFunctor_id]))
  continuous_toFun := (mapOfFunctor F).continuous
  continuous_invFun := (mapOfFunctor G).continuous

@[simp]
lemma homeomorphOfStrictIso_vertex {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (G : D ⥤ C) (hFG : F ⋙ G = 𝟭 C) (hGF : G ⋙ F = 𝟭 D) (X : C) :
    homeomorphOfStrictIso F G hFG hGF (vertex X) = vertex (F.obj X) :=
  mapOfFunctor_vertex F X

end UniverseChange

section ExamplesAndChecks

/-- The classifying space `classifyingSpace C` is nonempty if and only if `C` is nonempty. -/
@[simp]
lemma nonempty_iff (C : Type u) [Category.{v} C] :
    Nonempty (classifyingSpace C) ↔ Nonempty C :=
  (SSet.nonempty_toTop_iff (nerve C)).trans nerveEquiv.nonempty_congr

/-- The classifying space `classifyingSpace C` is empty if and only if `C` is empty. -/
@[simp]
lemma isEmpty_iff (C : Type u) [Category.{v} C] :
    IsEmpty (classifyingSpace C) ↔ IsEmpty C := by
  rw [← not_nonempty_iff, nonempty_iff, not_nonempty_iff]

instance instIsEmpty (C : Type u) [Category.{v} C] [IsEmpty C] : IsEmpty (classifyingSpace C) :=
  (isEmpty_iff C).2 ‹_›

instance instNonempty (C : Type u) [Category.{v} C] [Nonempty C] : Nonempty (classifyingSpace C) :=
  (nonempty_iff C).2 ‹_›

/-- The classifying space of a category with one object and one morphism is a single point, with
its unique point equal to the canonical vertex. -/
noncomputable instance instUnique (C : Type u) [Category.{v} C] [Unique C]
    [Subsingleton ((default : C) ⟶ default)] :
    Unique (classifyingSpace C) := by
  have hhom (x y : C) : Subsingleton (x ⟶ y) := by
    rw [Subsingleton.elim x default, Subsingleton.elim y default]
    infer_instance
  let termIso : nerve C ≅ (Δ[0] : SSet.{max u v}) :=
    IsTerminal.uniqueUpToIso
      (IsTerminal.ofUniqueHom
        (fun X ↦ { app m := ↾fun _ ↦ (Functor.const (Fin (m.unop.len + 1))).obj default })
        fun X m ↦ by
          apply NatTrans.ext; funext ⟨⟨n⟩⟩
          refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
          let f₁ : Fin (n + 1) ⥤ C := m.app (op ⦋n⦌) x
          change f₁ = (Functor.const (Fin (n + 1))).obj default
          exact CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _) fun _ _ _ ↦
            (hhom _ _).elim _ _)
      SSet.stdSimplex.isTerminalObj₀
  exact (TopCat.homeoOfIso (SSet.toTop.mapIso termIso)).unique

@[simp]
lemma vertex_default_eq_default (C : Type u) [Category.{v} C] [Unique C]
    [Subsingleton ((default : C) ⟶ default)] :
    vertex (default : C) = default :=
  Subsingleton.elim _ _

/-- Inclusion of an object `x : D` from a one-object, one-morphism category `P` followed by the
constant projection `D ⥤ P` realizes to the identity on `classifyingSpace P`. -/
lemma classifyingSpaceMap_const_comp_const_unique {P D : Type u} [Category.{v} P] [Category.{v} D]
    [Unique P] [Subsingleton ((default : P) ⟶ default)] (x : D) (p : P) :
    classifyingSpaceMap ((Functor.const P).obj x) ≫ classifyingSpaceMap ((Functor.const D).obj p) =
      𝟙 (classifyingSpace P) := by
  ext q
  exact Subsingleton.elim _ _

/-- Constant projection `C ⥤ D` followed by constant inclusion `D ⥤ E` at `z` realizes to the
constant map at `vertex z`. -/
lemma classifyingSpaceMap_const_comp_const {C D E : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] (y : D) (z : E) :
    classifyingSpaceMap ((Functor.const C).obj y) ≫ classifyingSpaceMap ((Functor.const D).obj z) =
      TopCat.const (X := classifyingSpace C) (vertex z) := by
  ext q
  simp

/-- For any type `S`, `classifyingSpace (Discrete S)` is isomorphic in `TopCat` to the discrete
topological space on `S`. -/
noncomputable def discreteIso (S : Type u) :
    classifyingSpace (Discrete S) ≅ TopCat.discrete.obj S :=
  SSet.toTop.mapIso (nerve.discreteIso S) ≪≫ SSet.toTopConstIso S

/-- Homeomorphism between `classifyingSpace (Discrete S)` and `S` equipped with the discrete
topology. -/
noncomputable def discreteHomeomorph (S : Type u) :
    classifyingSpace (Discrete S) ≃ₜ TopCat.discrete.obj S :=
  TopCat.homeoOfIso (discreteIso S)

@[simp]
lemma discreteHomeomorph_vertex (S : Type u) (s : S) :
    discreteHomeomorph S (vertex (Discrete.mk s)) = s := by
  change (SSet.toTopConstIso S).hom
    (SSet.toTop.map (nerve.discreteIso S).hom (SSet.toTopPoint (nerve.mk₀ (Discrete.mk s)))) = s
  rw [SSet.toTop_map_toTopPoint]
  exact SSet.toTopConstIso_hom_toTopPoint S s

@[simp]
lemma discreteHomeomorph_symm_apply (S : Type u) (s : TopCat.discrete.obj S) :
    (discreteHomeomorph S).symm s = vertex (Discrete.mk s) := by
  apply (discreteHomeomorph S).injective
  rw [Homeomorph.apply_symm_apply]
  exact (discreteHomeomorph_vertex S s).symm

/-- The two objects of `Discrete Bool` give distinct vertices of `classifyingSpace (Discrete Bool)`.
-/
lemma vertex_discrete_false_ne_true :
    vertex (Discrete.mk false) ≠ vertex (Discrete.mk true) :=
  vertex_inj.not.2 (by decide)

/-- A preorder order-isomorphic to `Fin (n + 1)` has classifying space homeomorphic to the standard
topological `n`-simplex `StdSimplex ℝ (Fin (n + 1))`. -/
noncomputable def preorderHomeomorphStdSimplex {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) :
    classifyingSpace α ≃ₜ StdSimplex ℝ (Fin (n + 1)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.stdSimplex.isoOfRepresentableBy (nerve.representableBy α e)).symm)).trans
    ⦋n⦌.toTopHomeo.{u}

@[simp]
lemma preorderHomeomorphStdSimplex_vertex {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (a : α) :
    preorderHomeomorphStdSimplex e (vertex a) = StdSimplex.single (e a) := by
  have hinv : (SSet.stdSimplex.isoOfRepresentableBy (nerve.representableBy α e)).inv.app (op ⦋0⦌)
      (nerve.mk₀ a) = SSet.stdSimplex.objEquiv.{u}.symm (SimplexCategory.const ⦋0⦌ ⦋n⦌ (e a)) := by
    apply (SSet.stdSimplex.objEquiv.{u}.trans (nerve.representableBy α e).homEquiv).injective
    refine (Equiv.apply_symm_apply
      (SSet.stdSimplex.objEquiv.{u}.trans (nerve.representableBy α e).homEquiv)
      (nerve.mk₀ a)).trans ?_
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, nerve.representableBy]
    let x₀ : Fin 1 ⥤ α := nerve.mk₀ a
    change x₀ = (SimplexCategory.homEquivFunctor (SimplexCategory.const ⦋0⦌ ⦋n⦌ (e a))) ⋙
      e.symm.monotone.functor
    exact CategoryTheory.Functor.ext
      (fun i ↦ by
        fin_cases i
        change a = e.symm ((SimplexCategory.const ⦋0⦌ ⦋n⦌ (e a)).toOrderHom 0); simp)
      (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hyon : SSet.yonedaEquiv.symm
      (SSet.stdSimplex.objEquiv.{u}.symm (SimplexCategory.const ⦋0⦌ ⦋n⦌ (e a))) =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (e a)) :=
    SSet.yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_map])
  change ⦋n⦌.toTopHomeo.{u}
    (SSet.toTop.map (SSet.stdSimplex.isoOfRepresentableBy (nerve.representableBy α e)).inv
      (SSet.toTopPoint (nerve.mk₀ a))) = StdSimplex.single (e a)
  rw [SSet.toTop_map_toTopPoint, hinv,
    SSet.toTopPoint_eq_toTopObjMk _ (StdSimplex.single 0), SSet.toTopObjMk_eq_toTop_map, hyon,
    SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply,
    StdSimplex.map_single]
  rfl

/-- The classifying space of a preorder order-isomorphic to `Fin (n + 1)` is contractible. -/
lemma contractibleSpace_of_orderIso_fin {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) :
    ContractibleSpace (classifyingSpace α) :=
  (preorderHomeomorphStdSimplex e).contractibleSpace

instance : ContractibleSpace (classifyingSpace (Fin 2)) :=
  contractibleSpace_of_orderIso_fin (OrderIso.refl (Fin 2))

/-- The classifying space of the ordinal `Fin 2 = {0 < 1}` is homeomorphic to the unit interval `I`,
sending `vertex 0` to `0` and `vertex 1` to `1`. -/
noncomputable def finTwoHomeomorphI : classifyingSpace (Fin 2) ≃ₜ unitInterval :=
  (preorderHomeomorphStdSimplex (OrderIso.refl (Fin 2))).trans StdSimplex.homeomorphI

@[simp]
lemma finTwoHomeomorphI_vertex_zero : finTwoHomeomorphI (vertex (0 : Fin 2)) = 0 := by
  simp [finTwoHomeomorphI]

@[simp]
lemma finTwoHomeomorphI_vertex_one : finTwoHomeomorphI (vertex (1 : Fin 2)) = 1 := by
  simp [finTwoHomeomorphI]

/-- Although `classifyingSpace (Fin 2)` is contractible, its two endpoint vertices `0` and `1` are
distinct. -/
lemma vertex_finTwo_zero_ne_one : vertex (0 : Fin 2) ≠ vertex (1 : Fin 2) :=
  vertex_inj.not.2 (by decide)

/-- Whenever `C` has another object `Y ≠ X`, the realized identity of `C` differs from the realized
constant endofunctor at `X`, as detected at `vertex Y`. -/
lemma classifyingSpaceMap_id_ne_const {C : Type u} [Category.{v} C] {X Y : C} (hne : Y ≠ X) :
    classifyingSpaceMap (𝟭 C) ≠ classifyingSpaceMap ((Functor.const C).obj X) := fun h ↦ by
  have hy := ConcreteCategory.congr_hom h (vertex Y)
  rw [classifyingSpaceMap_vertex, classifyingSpaceMap_const, Functor.id_obj, TopCat.const_apply,
    vertex_inj] at hy
  exact hne hy

/-- For either endpoint `i : Fin 2`, the realized identity of `Fin 2` differs from the realized
constant endofunctor at `i`, as detected at the opposite vertex `i.rev`. -/
lemma classifyingSpaceMap_id_ne_const_finTwo (i : Fin 2) :
    classifyingSpaceMap (𝟭 (Fin 2)) ≠ classifyingSpaceMap ((Functor.const (Fin 2)).obj i) :=
  classifyingSpaceMap_id_ne_const (Y := i.rev) (by fin_cases i <;> decide)

/-- Endpoint inclusion `Discrete PUnit ⥤ Fin 2` followed by the terminal functor
`Fin 2 ⥤ Discrete PUnit` realizes to the identity on `classifyingSpace (Discrete PUnit)`. -/
lemma classifyingSpaceMap_punit_finTwo_comp_terminal (i : Fin 2) :
    classifyingSpaceMap ((Functor.const (Discrete PUnit.{1})).obj i) ≫
        classifyingSpaceMap ((Functor.const (Fin 2)).obj (Discrete.mk PUnit.unit)) =
      𝟙 (classifyingSpace (Discrete PUnit.{1})) :=
  classifyingSpaceMap_const_comp_const_unique i (Discrete.mk PUnit.unit)

/-- Terminal projection `Fin 2 ⥤ Discrete PUnit` followed by endpoint inclusion
`Discrete PUnit ⥤ Fin 2` at `i` realizes to the constant map at `vertex i` on
`classifyingSpace (Fin 2)`. -/
lemma classifyingSpaceMap_finTwo_terminal_comp_punit (i : Fin 2) :
    classifyingSpaceMap ((Functor.const (Fin 2)).obj (Discrete.mk PUnit.unit)) ≫
        classifyingSpaceMap ((Functor.const (Discrete PUnit.{1})).obj i) =
      TopCat.const (vertex i) :=
  classifyingSpaceMap_const_comp_const _ i

/-- Reflection of the interval `classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2)` swapping
`vertex 0` and `vertex 1`. -/
noncomputable def finTwoReflect : classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2) :=
  (TopCat.isoOfHomeo
    ((finTwoHomeomorphI.trans unitInterval.symmHomeomorph).trans finTwoHomeomorphI.symm)).hom

@[simp]
lemma finTwoReflect_vertex_zero : finTwoReflect (vertex (0 : Fin 2)) = vertex 1 := by
  change finTwoHomeomorphI.symm (unitInterval.symmHomeomorph (finTwoHomeomorphI (vertex 0))) = _
  rw [finTwoHomeomorphI_vertex_zero, unitInterval.symmHomeomorph_apply, unitInterval.symm_zero,
    ← finTwoHomeomorphI_vertex_one, Homeomorph.symm_apply_apply]

@[simp]
lemma finTwoReflect_vertex_one : finTwoReflect (vertex (1 : Fin 2)) = vertex 0 := by
  change finTwoHomeomorphI.symm (unitInterval.symmHomeomorph (finTwoHomeomorphI (vertex 1))) = _
  rw [finTwoHomeomorphI_vertex_one, unitInterval.symmHomeomorph_apply, unitInterval.symm_one,
    ← finTwoHomeomorphI_vertex_zero, Homeomorph.symm_apply_apply]

/-- The interval reflection `finTwoReflect` is not `classifyingSpaceMap F` for any functor
`F : Fin 2 ⥤ Fin 2`. -/
theorem not_exists_classifyingSpaceMap_eq_finTwoReflect :
    ¬ ∃ F : Fin 2 ⥤ Fin 2, classifyingSpaceMap F = finTwoReflect := by
  rintro ⟨F, hF⟩
  have h0 : F.obj 0 = 1 := vertex_inj.1 (by
    simpa using ConcreteCategory.congr_hom hF (vertex (0 : Fin 2)))
  have h1 : F.obj 1 = 0 := vertex_inj.1 (by
    simpa using ConcreteCategory.congr_hom hF (vertex (1 : Fin 2)))
  have hle : F.obj 0 ≤ F.obj 1 := leOfHom (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)))
  rw [h0, h1] at hle
  exact absurd hle (by decide)

/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` is not full (in any universes
`v, u`), as witnessed by lifting the interval reflection on `Fin 2` into `Cat.{v, u}`. -/
theorem not_full_classifyingSpaceFunctor : ¬ classifyingSpaceFunctor.{v, u}.Full := by
  intro hFull
  let C₀ := ULiftHom.{v} (InducedCategory (Fin 2) (ULift.down : ULift.{u} (Fin 2) → Fin 2))
  let toFin : C₀ ⥤ Fin 2 := ULiftHom.down ⋙ inducedFunctor ULift.down
  let fromFin : Fin 2 ⥤ C₀ :=
    { obj i := ULiftHom.objUp (ULift.up i)
      map f := ⟨(inducedFunctor ULift.down).preimage f⟩ }
  have hTF : toFin ⋙ fromFin = 𝟭 C₀ :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦
      ULift.ext (InducedCategory.hom_ext (Subsingleton.elim _ _))
  have hFT : fromFin ⋙ toFin = 𝟭 (Fin 2) :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  let e : classifyingSpace C₀ ≃ₜ classifyingSpace (Fin 2) :=
    homeomorphOfStrictIso toFin fromFin hTF hFT
  let reflHomeo : classifyingSpace C₀ ≃ₜ classifyingSpace C₀ :=
    ((e.trans finTwoHomeomorphI).trans unitInterval.symmHomeomorph).trans
      (e.trans finTwoHomeomorphI).symm
  have := hFull
  obtain ⟨G, hG⟩ := classifyingSpaceFunctor.map_surjective (X := Cat.of C₀) (Y := Cat.of C₀)
    (TopCat.isoOfHomeo reflHomeo).hom
  refine not_exists_classifyingSpaceMap_eq_finTwoReflect ⟨fromFin ⋙ G.toFunctor ⋙ toFin, ?_⟩
  apply TopCat.ext
  intro p
  have hp : mapOfFunctor (fromFin ⋙ G.toFunctor ⋙ toFin) p = finTwoReflect p := by
    rw [mapOfFunctor_comp, mapOfFunctor_comp]
    simp only [ContinuousMap.comp_apply, mapOfFunctor_eq_classifyingSpaceMap G.toFunctor]
    change e (classifyingSpaceFunctor.map G (e.symm p)) = finTwoReflect p
    rw [hG]
    change e (e.symm (finTwoHomeomorphI.symm
      (unitInterval.symmHomeomorph (finTwoHomeomorphI (e (e.symm p)))))) = finTwoReflect p
    rw [e.apply_symm_apply, e.apply_symm_apply]; rfl
  exact (congrArg (· p)
    (mapOfFunctor_eq_classifyingSpaceMap (fromFin ⋙ G.toFunctor ⋙ toFin)).symm).trans hp

end ExamplesAndChecks

end classifyingSpace

end TauCeti
