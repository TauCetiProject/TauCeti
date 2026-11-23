/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Op
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Prism

/-!
# Classifying spaces of categories

The classifying space `CategoryTheory.classifyingSpace C` of a category `C` is the geometric
realization `|nerve C|` of its nerve. It translates categories, functors, and natural
transformations into topological spaces, continuous maps, and homotopies, carrying objects,
morphisms, discrete categories, finite ordinals, opposite categories, adjunctions, equivalences,
skeletons, initial/terminal objects, and connected components to points, edge paths, the
fundamental groupoid, standard simplices, barycentric reversal, homotopy equivalences,
contractibility, and path components.

Because `SSet.toTop : SSet.{u} ⥤ TopCat.{u}` operates in a fixed universe, the bundled functor
`classifyingSpaceFunctor : Cat.{v, u} ⥤ TopCat.{max u v}`, `classifyingSpaceMap`, and
`NatTrans.classifyingSpaceHomotopy` apply to categories sharing a universe pair `(u, v)`.
Cross-universe functors and natural transformations—such as passing to a skeleton, a small model of
an essentially small category, or a cross-universe adjunction or equivalence—are supported uniformly
by `Functor.toClassifyingSpaceContinuousMap` and `NatTrans.toClassifyingSpaceHomotopy` via
`AsSmall` and `asSmallHomeomorph`, together with agreement lemmas when universes coincide.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341, Springer, 1973, §1.
* C. A. Weibel, *An Introduction to Algebraic K-Theory*, AMS, 2013, Chapter IV, §§3.1–3.3.
-/

public section

open CategoryTheory.MonoidalCategory Opposite Simplicial Convexity
universe w v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

section Basic
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
/-- The classifying space `BC` of a category `C`, defined as `|nerve C|`. -/
@[expose, implicit_reducible]
noncomputable def classifyingSpace (C : Type u) [Category.{v} C] : TopCat.{max u v} := |nerve C|
lemma classifyingSpace_def (C : Type u) [Category.{v} C] : classifyingSpace C = |nerve C| := (rfl)
/-- A functor `F : C ⥤ D` in the same universes induces a morphism on classifying spaces. -/
noncomputable def classifyingSpaceMap (F : C ⥤ D) : classifyingSpace C ⟶ classifyingSpace D :=
  SSet.toTop.map (nerveMap F)
lemma classifyingSpaceMap_def (F : C ⥤ D) :
    classifyingSpaceMap F = SSet.toTop.map (nerveMap F) := (rfl)
@[simp] lemma classifyingSpaceMap_toTopObjMk (F : C ⥤ D) {n : ℕ} (σ : ComposableArrows C n)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    classifyingSpaceMap F (SSet.toTopObjMk (X := nerve C) σ w) =
      SSet.toTopObjMk (X := nerve D) ((F.mapComposableArrows n).obj σ) w :=
  SSet.toTop_map_toTopObjMk (nerveMap F) σ w
@[simp] lemma classifyingSpaceMap_id (C : Type u) [Category.{v} C] :
    classifyingSpaceMap (𝟭 C) = 𝟙 (classifyingSpace C) := by
  rw [classifyingSpaceMap_def, nerveMap_id, CategoryTheory.Functor.map_id]
  -- `classifyingSpace C` is definitionally `|nerve C|`.
  rfl
@[simp, reassoc] lemma classifyingSpaceMap_comp (F : C ⥤ D) (G : D ⥤ E) :
    classifyingSpaceMap (F ⋙ G) = classifyingSpaceMap F ≫ classifyingSpaceMap G := by
  simp only [classifyingSpaceMap_def, nerveMap_comp, CategoryTheory.Functor.map_comp]
/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` (`nerveFunctor ⋙ SSet.toTop`). -/
@[expose] noncomputable def classifyingSpaceFunctor : Cat.{v, u} ⥤ TopCat.{max u v} :=
  nerveFunctor ⋙ SSet.toTop
lemma classifyingSpaceFunctor_def :
    classifyingSpaceFunctor.{v, u} = nerveFunctor ⋙ SSet.toTop := (rfl)
@[simp] lemma classifyingSpaceFunctor_obj (C : Cat.{v, u}) :
    classifyingSpaceFunctor.obj C = classifyingSpace C := (rfl)
@[simp] lemma classifyingSpaceFunctor_map {C D : Cat.{v, u}} (F : C ⟶ D) :
    classifyingSpaceFunctor.map F = classifyingSpaceMap F.toFunctor := (rfl)
end Basic

namespace classifyingSpace
section VerticesAndEdges
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
/-- The vertex of `classifyingSpace C` corresponding to an object `c : C`. -/
noncomputable def vertex (c : C) : classifyingSpace C :=
  SSet.toTopPoint (X := nerve C) (nerveEquiv.symm c)
lemma vertex_def (c : C) : vertex c = SSet.toTopPoint (X := nerve C) (nerveEquiv.symm c) := (rfl)
@[simp] lemma toTopObjMk_single {n : ℕ} (σ : (nerve C) _⦋n⦌) (i : Fin (n + 1)) :
    SSet.toTopObjMk (X := nerve C) σ (StdSimplex.single i) = vertex (σ.obj i) := by
  rw [SSet.toTopObjMk_single, vertex_def]
  exact congrArg (SSet.toTopPoint (X := nerve C)) (ComposableArrows.ext₀ rfl)
private lemma vertex_eq_toTopObjMk (c : C) :
    vertex c = SSet.toTopObjMk (X := nerve C) (nerveEquiv.symm c) (StdSimplex.single 0) :=
  (toTopObjMk_single (σ := nerveEquiv.symm c) 0).symm
/-- Distinct objects of `C` determine distinct vertices of `classifyingSpace C`. -/
theorem vertex_injective : Function.Injective (vertex (C := C)) :=
  (SSet.toTopPoint_injective (nerve C)).comp nerveEquiv.symm.injective
@[simp] lemma vertex_inj {x y : C} : vertex x = vertex y ↔ x = y := vertex_injective.eq_iff
@[simp] lemma classifyingSpaceMap_vertex (F : C ⥤ D) (c : C) :
    classifyingSpaceMap F (vertex c) = vertex (F.obj c) :=
  (SSet.toTop_map_toTopPoint (nerveMap F) (nerveEquiv.symm c : (nerve C) _⦋0⦌)).trans
    (congrArg (SSet.toTopPoint (X := nerve D)) (nerveMap_app_mk₀ F c))
lemma classifyingSpaceMap_const_apply (C : Type u) [Category.{v} C] {D : Type u}
    [Category.{v} D] (d : D) (z : classifyingSpace C) :
    classifyingSpaceMap ((Functor.const C).obj d) z = vertex d := by
  rw [classifyingSpaceMap_def, nerveMap_const, vertex_def]; exact SSet.toTop_map_const_apply _ z
lemma classifyingSpaceMap_const (C : Type u) [Category.{v} C] {D : Type u} [Category.{v} D]
    (d : D) : classifyingSpaceMap ((Functor.const C).obj d) = TopCat.const (vertex d) := by
  rw [classifyingSpaceMap_def, nerveMap_const, vertex_def]; exact SSet.toTop_map_const _
@[simp] lemma classifyingSpaceMap_const_hom (C : Type u) [Category.{v} C] {D : Type u}
    [Category.{v} D] (d : D) :
    (classifyingSpaceMap ((Functor.const C).obj d)).hom =
      ContinuousMap.const (classifyingSpace C) (vertex d) := by
  rw [classifyingSpaceMap_def, nerveMap_const, vertex_def]; exact SSet.toTop_map_const_hom _
lemma exists_joined_vertex (z : classifyingSpace C) : ∃ c : C, Joined (vertex c) z := by
  obtain ⟨x, hx⟩ := SSet.exists_joined_toTopPoint (X := nerve C) z
  exact ⟨nerveEquiv x, by rw [vertex_def, Equiv.symm_apply_apply nerveEquiv x]; exact hx.symm⟩
/-- The path in `classifyingSpace C` from `vertex x` to `vertex y` traced by `f : x ⟶ y`. -/
noncomputable def edgePath {x y : C} (f : x ⟶ y) : _root_.Path (vertex x) (vertex y) :=
  (nerve.edgeMk f).toTopPath
lemma edgePath_apply {x y : C} (f : x ⟶ y) (t : unitInterval) : edgePath f t =
    SSet.toTopObjMk (X := nerve C) (nerve.edgeMk f).edge (StdSimplex.homeomorphI.symm t) :=
  (nerve.edgeMk f).toTopPath_apply t
@[simp] lemma edgePath_id (x : C) : edgePath (𝟙 x) = _root_.Path.refl (vertex x) := by
  rw [edgePath, nerve.edgeMk_id]; exact SSet.Edge.toTopPath_id (X := nerve C) (nerveEquiv.symm x)
/-- For composable morphisms `f : x ⟶ y` and `g : y ⟶ z`, `edgePath (f ≫ g)` is path-homotopic to
`(edgePath f).trans (edgePath g)`. -/
theorem edgePath_comp_homotopic {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    (edgePath (f ≫ g)).Homotopic ((edgePath f).trans (edgePath g)) :=
  (((nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl).some).toTopPath_homotopic
@[simp] lemma classifyingSpaceMap_edgePath_apply (F : C ⥤ D) {x y : C} (f : x ⟶ y)
    (t : unitInterval) : classifyingSpaceMap F (edgePath f t) = edgePath (F.map f) t := by
  rw [classifyingSpaceMap_def, edgePath_apply, SSet.toTop_map_toTopObjMk, edgePath_apply]
  exact congrArg (SSet.toTopObjMk (X := nerve D) · _) (nerveMap_app_mk₁ F f)
lemma classifyingSpaceMap_edgePath (F : C ⥤ D) {x y : C} (f : x ⟶ y) :
    (edgePath f).map (classifyingSpaceMap F).hom.continuous =
      (edgePath (F.map f)).cast (classifyingSpaceMap_vertex F x)
        (classifyingSpaceMap_vertex F y) :=
  _root_.Path.ext (funext (classifyingSpaceMap_edgePath_apply F f))
/-- The canonical functor `C ⥤ FundamentalGroupoid (classifyingSpace C)` sending `c` to `vertex c`
and `f : x ⟶ y` to the path-homotopy class of `edgePath f`. -/
@[expose] noncomputable def toFundamentalGroupoid (C : Type u) [Category.{v} C] :
    C ⥤ FundamentalGroupoid (classifyingSpace C) where
  obj c := FundamentalGroupoid.mk (vertex c)
  map f := FundamentalGroupoid.fromPath (.mk (edgePath f))
  map_id _ := by
    rw [edgePath_id, FundamentalGroupoid.id_eq_path_refl]
    -- `FundamentalGroupoid.fromPath` on a path-homotopy class is definitionally that class.
    rfl
  map_comp f g := by
    rw [FundamentalGroupoid.comp_eq, ← Path.Homotopic.Quotient.mk_trans]
    exact (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).2 (edgePath_comp_homotopic f g)
@[simp] lemma toFundamentalGroupoid_obj (c : C) :
    (toFundamentalGroupoid C).obj c = FundamentalGroupoid.mk (vertex c) := (rfl)
@[simp] lemma toFundamentalGroupoid_map {x y : C} (f : x ⟶ y) :
    (toFundamentalGroupoid C).map f = FundamentalGroupoid.fromPath (.mk (edgePath f)) := (rfl)
end VerticesAndEdges

section AsSmall
variable (C : Type u) [Category.{v} C]
/-- The classifying space of `AsSmall.{w} C` is canonically homeomorphic to `classifyingSpace C`. -/
noncomputable def asSmallHomeomorph : classifyingSpace (AsSmall.{w} C) ≃ₜ classifyingSpace C :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.asSmallIso.{w} C))).trans
    (SSet.toTopUliftHomeomorph.{w, max u v} (nerve C))
@[simp] lemma asSmallHomeomorph_toTopObjMk {n : ℕ} (σ : ComposableArrows (AsSmall.{w} C) n)
    (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    asSmallHomeomorph.{w} C (SSet.toTopObjMk (X := nerve (AsSmall.{w} C)) σ w₀) =
      SSet.toTopObjMk (X := nerve C) ((AsSmall.down.mapComposableArrows n).obj σ) w₀ :=
  ((congrArg (SSet.toTopUliftHomeomorph.{w, max u v} (nerve C))
    (SSet.toTop_map_toTopObjMk (nerve.asSmallIso.{w} C).hom σ w₀)).trans
    (SSet.toTopUliftHomeomorph_toTopObjMk (nerve C) _ w₀)).trans
    (congrArg (SSet.toTopObjMk (X := nerve C) · w₀) (nerve.asSmallIso_hom_app_down (n := op ⦋n⦌) σ))
@[simp] lemma asSmallHomeomorph_symm_toTopObjMk {n : ℕ} (σ : ComposableArrows C n)
    (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    (asSmallHomeomorph.{w} C).symm (SSet.toTopObjMk (X := nerve C) σ w₀) =
      SSet.toTopObjMk (X := nerve (AsSmall.{w} C)) ((AsSmall.up.mapComposableArrows n).obj σ) w₀ :=
  (asSmallHomeomorph.{w} C).injective <| by
    rw [Homeomorph.apply_symm_apply, asSmallHomeomorph_toTopObjMk,
      Functor.mapComposableArrows_obj, Functor.mapComposableArrows_obj,
      CategoryTheory.Functor.assoc, AsSmall.up_comp_down.{w} C, CategoryTheory.Functor.comp_id]
@[simp] lemma asSmallHomeomorph_vertex (c : AsSmall.{w} C) :
    asSmallHomeomorph.{w} C (vertex c) = vertex (AsSmall.down.obj c) :=
  (congrArg (asSmallHomeomorph.{w} C) (vertex_eq_toTopObjMk c)).trans <|
    (asSmallHomeomorph_toTopObjMk C (nerveEquiv.symm c) _).trans <|
      (congrArg (SSet.toTopObjMk (X := nerve C) · _)
        (ComposableArrows.ext₀ rfl)).trans (SSet.toTopObjMk_eq_toTopPoint _ _)
@[simp] lemma asSmallHomeomorph_symm_vertex (c : C) :
    (asSmallHomeomorph.{w} C).symm (vertex c) = vertex (AsSmall.up.obj c) :=
  (asSmallHomeomorph.{w} C).injective (by simp)
end AsSmall
end classifyingSpace

namespace Functor
section CrossUniverse
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
/-- A functor `F : C ⥤ D` across arbitrary universes induces a continuous map
`C(classifyingSpace C, classifyingSpace D)` via `AsSmall` and `asSmallHomeomorph`. -/
noncomputable def toClassifyingSpaceContinuousMap (F : C ⥤ D) :
    C(classifyingSpace C, classifyingSpace D) :=
  ((classifyingSpace.asSmallHomeomorph.{max u₁ v₁} D : C(_, _)).comp
    (classifyingSpaceMap (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up (C := D) :
      AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D)).hom).comp
    ((classifyingSpace.asSmallHomeomorph.{max u₂ v₂} C).symm : C(_, _))
@[simp] lemma toClassifyingSpaceContinuousMap_toTopObjMk (F : C ⥤ D) {n : ℕ}
    (σ : ComposableArrows C n) (w : StdSimplex ℝ (Fin (n + 1))) :
    F.toClassifyingSpaceContinuousMap (SSet.toTopObjMk (X := nerve C) σ w) =
      SSet.toTopObjMk (X := nerve D) ((F.mapComposableArrows n).obj σ) w := by
  dsimp only [toClassifyingSpaceContinuousMap, ContinuousMap.comp_apply]
  refine (congrArg (fun z ↦ (classifyingSpace.asSmallHomeomorph.{max u₁ v₁} D)
      (classifyingSpaceMap (AsSmall.down ⋙ F ⋙ AsSmall.up) z))
      (classifyingSpace.asSmallHomeomorph_symm_toTopObjMk C σ w)).trans <|
    (congrArg (classifyingSpace.asSmallHomeomorph.{max u₁ v₁} D)
      (classifyingSpaceMap_toTopObjMk (AsSmall.down ⋙ F ⋙ AsSmall.up) _ w)).trans <|
    (classifyingSpace.asSmallHomeomorph_toTopObjMk D _ w).trans <|
    congrArg (SSet.toTopObjMk (X := nerve D) · w) ?_
  rw [Functor.mapComposableArrows_obj, Functor.mapComposableArrows_obj,
    Functor.mapComposableArrows_obj, Functor.mapComposableArrows_obj,
    CategoryTheory.Functor.assoc, CategoryTheory.Functor.assoc, CategoryTheory.Functor.assoc,
    CategoryTheory.Functor.assoc, AsSmall.up_comp_down, CategoryTheory.Functor.comp_id,
    ← CategoryTheory.Functor.assoc AsSmall.up AsSmall.down F, AsSmall.up_comp_down,
    CategoryTheory.Functor.id_comp]
@[simp] lemma toClassifyingSpaceContinuousMap_vertex (F : C ⥤ D) (c : C) :
    F.toClassifyingSpaceContinuousMap (classifyingSpace.vertex c) =
      classifyingSpace.vertex (F.obj c) := by simp [toClassifyingSpaceContinuousMap]
@[simp] lemma toClassifyingSpaceContinuousMap_edgePath_apply (F : C ⥤ D) {x y : C} (f : x ⟶ y)
    (t : unitInterval) :
    F.toClassifyingSpaceContinuousMap (classifyingSpace.edgePath f t) =
      classifyingSpace.edgePath (F.map f) t := by
  rw [classifyingSpace.edgePath_apply, nerve.edgeMk_edge,
    toClassifyingSpaceContinuousMap_toTopObjMk, Functor.mapComposableArrows_obj_mk₁,
    classifyingSpace.edgePath_apply, nerve.edgeMk_edge]
lemma toClassifyingSpaceContinuousMap_edgePath (F : C ⥤ D) {x y : C} (f : x ⟶ y) :
    (classifyingSpace.edgePath f).map F.toClassifyingSpaceContinuousMap.continuous =
      (classifyingSpace.edgePath (F.map f)).cast
        (F.toClassifyingSpaceContinuousMap_vertex x)
        (F.toClassifyingSpaceContinuousMap_vertex y) :=
  _root_.Path.ext (funext (F.toClassifyingSpaceContinuousMap_edgePath_apply f))
@[simp] lemma toClassifyingSpaceContinuousMap_id (C : Type u₁) [Category.{v₁} C] :
    (𝟭 C).toClassifyingSpaceContinuousMap = ContinuousMap.id (classifyingSpace C) := by
  ext z; obtain ⟨n, (σ : ComposableArrows C n), w, rfl⟩ := SSet.exists_toTopObjMk (X := nerve C) z
  simp only [toClassifyingSpaceContinuousMap_toTopObjMk, ContinuousMap.id_apply]
  exact congrArg (SSet.toTopObjMk (X := nerve C) · w) (CategoryTheory.Functor.comp_id σ)
@[simp] lemma toClassifyingSpaceContinuousMap_comp (F : C ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).toClassifyingSpaceContinuousMap =
      G.toClassifyingSpaceContinuousMap.comp F.toClassifyingSpaceContinuousMap := by
  ext z; obtain ⟨n, (σ : ComposableArrows C n), w, rfl⟩ := SSet.exists_toTopObjMk (X := nerve C) z
  simp only [toClassifyingSpaceContinuousMap_toTopObjMk, ContinuousMap.comp_apply]
  exact congrArg (SSet.toTopObjMk (X := nerve E) · w) (CategoryTheory.Functor.assoc σ F G).symm
@[simp] lemma toClassifyingSpaceContinuousMap_const (d : D) :
    ((Functor.const C).obj d).toClassifyingSpaceContinuousMap =
      ContinuousMap.const (classifyingSpace C) (classifyingSpace.vertex d) := by
  have h : (AsSmall.down (C := C) ⋙ (Functor.const C).obj d ⋙ AsSmall.up (C := D) :
      AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D) = (Functor.const _).obj (AsSmall.up.obj d) :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
      simp only [Functor.comp_map, Functor.const_obj_map, eqToHom_refl, Category.id_comp,
        Category.comp_id]; exact CategoryTheory.Functor.map_id _ d
  ext z; simp [toClassifyingSpaceContinuousMap, h]
/-- Distinct functors `F, G : C ⥤ D` across arbitrary universes induce distinct continuous maps on
classifying spaces. -/
theorem toClassifyingSpaceContinuousMap_injective :
    Function.Injective (toClassifyingSpaceContinuousMap (C := C) (D := D)) := by
  intro F G h
  have h_obj (c : C) : F.obj c = G.obj c := classifyingSpace.vertex_injective <| by
    simpa using DFunLike.congr_fun h (classifyingSpace.vertex c)
  refine CategoryTheory.Functor.ext h_obj fun x y f ↦ ?_
  have hmk : ComposableArrows.mk₁ (F.map f) = ComposableArrows.mk₁ (G.map f) :=
    SSet.toTopObjMk_one_injective (nerve D) <| funext fun w ↦ by
      have hw := DFunLike.congr_fun h (SSet.toTopObjMk (X := nerve C) (ComposableArrows.mk₁ f) w)
      rwa [toClassifyingSpaceContinuousMap_toTopObjMk, toClassifyingSpaceContinuousMap_toTopObjMk,
        Functor.mapComposableArrows_obj_mk₁, Functor.mapComposableArrows_obj_mk₁] at hw
  rw [← ComposableArrows.mk₁_eqToHom_comp (h_obj x),
    ← ComposableArrows.mk₁_comp_eqToHom _ (h_obj y).symm, Category.assoc] at hmk
  exact (Arrow.mk_inj _ _).1 (ComposableArrows.arrowEquiv.symm.injective hmk)
end CrossUniverse

lemma toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap {C D : Type u} [Category.{v} C]
    [Category.{v} D] (F : C ⥤ D) :
    F.toClassifyingSpaceContinuousMap = (classifyingSpaceMap F).hom := by
  ext z; obtain ⟨n, (σ : ComposableArrows C n), w, rfl⟩ := SSet.exists_toTopObjMk (X := nerve C) z
  simp
lemma toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap_apply {C D : Type u} [Category.{v} C]
    [Category.{v} D] (F : C ⥤ D) (z : classifyingSpace C) :
    F.toClassifyingSpaceContinuousMap z = classifyingSpaceMap F z :=
  DFunLike.congr_fun (toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap F) z
end Functor

/-- Distinct functors `F, G : C ⥤ D` induce distinct maps on classifying spaces. -/
theorem classifyingSpaceMap_injective {C D : Type u} [Category.{v} C] [Category.{v} D] :
    Function.Injective (classifyingSpaceMap (C := C) (D := D)) := fun F G h ↦
  Functor.toClassifyingSpaceContinuousMap_injective <| by
    simp [Functor.toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap, h]
instance instFaithfulClassifyingSpaceFunctor : classifyingSpaceFunctor.{v, u}.Faithful where
  map_injective h := Cat.Hom.ext (classifyingSpaceMap_injective h)

namespace classifyingSpace

/-- Naturality of `toFundamentalGroupoid` with respect to functors across arbitrary universes. -/
theorem toFundamentalGroupoid_comp_map {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) :
    toFundamentalGroupoid C ⋙ FundamentalGroupoid.map F.toClassifyingSpaceContinuousMap =
      F ⋙ toFundamentalGroupoid D := by
  let g := F.toClassifyingSpaceContinuousMap
  have hmap {x₀ x₁ : classifyingSpace C} {y₀ y₁ : classifyingSpace D} (p : _root_.Path x₀ x₁)
      (q : _root_.Path y₀ y₁) (hx : g x₀ = y₀) (hy : g x₁ = y₁) (hpq : ∀ t, g (p t) = q t) :
      (FundamentalGroupoid.map g).map (FundamentalGroupoid.fromPath (.mk p)) =
        eqToHom (congrArg FundamentalGroupoid.mk hx) ≫ FundamentalGroupoid.fromPath (.mk q) ≫
          eqToHom (congrArg FundamentalGroupoid.mk hy).symm := by
    subst hx hy; simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact congrArg (FundamentalGroupoid.fromPath ∘ Path.Homotopic.Quotient.mk)
      (_root_.Path.ext (funext hpq))
  exact CategoryTheory.Functor.ext
    (fun c ↦ congrArg FundamentalGroupoid.mk (F.toClassifyingSpaceContinuousMap_vertex c))
    fun _ _ f ↦ hmap (edgePath f) (edgePath (F.map f))
      (F.toClassifyingSpaceContinuousMap_vertex _) (F.toClassifyingSpaceContinuousMap_vertex _)
      (F.toClassifyingSpaceContinuousMap_edgePath_apply f)

section BasicTypes
variable (C : Type u) [Category.{v} C]
instance [IsEmpty C] : IsEmpty (classifyingSpace C) :=
  (SSet.isEmpty_toTop_iff (nerve C)).2 (nerveEquiv (C := C)).isEmpty
@[simp] theorem isEmpty_iff : IsEmpty (classifyingSpace C) ↔ IsEmpty C :=
  (SSet.isEmpty_toTop_iff (nerve C)).trans nerveEquiv.isEmpty_congr
@[simp] theorem nonempty_iff : Nonempty (classifyingSpace C) ↔ Nonempty C :=
  (SSet.nonempty_toTop_iff (nerve C)).trans (nerve.nonempty_iff C)
instance [Nonempty C] : Nonempty (classifyingSpace C) := (nonempty_iff C).2 ‹_›
instance [Subsingleton C] [Quiver.IsThin C] : Subsingleton (classifyingSpace C) :=
  inferInstanceAs (Subsingleton |nerve C|)
noncomputable instance [Unique C] [Quiver.IsThin C] : Unique (classifyingSpace C) where
  default := vertex default
  uniq _ := Subsingleton.elim _ _
@[simp] lemma default_eq_vertex [Unique C] [Quiver.IsThin C] :
    (default : classifyingSpace C) = vertex default := (rfl)
end BasicTypes

/-- `classifyingSpace (Discrete ι)` is homeomorphic to `TopCat.discrete.obj ι`. -/
noncomputable def discreteHomeomorph (ι : Type u) :
    classifyingSpace (Discrete ι) ≃ₜ TopCat.discrete.obj ι :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.discreteIso ι) ≪≫ SSet.constCompToTopIso.app ι)
@[simp] lemma discreteHomeomorph_vertex (ι : Type u) (i : Discrete ι) :
    discreteHomeomorph ι (vertex i) = (i.as : TopCat.discrete.obj ι) :=
  (congrArg (SSet.constCompToTopIso.hom.app ι)
    ((SSet.toTop_map_toTopPoint (nerve.discreteIso ι).hom
        (nerveEquiv.symm i : (nerve (Discrete ι)) _⦋0⦌)).trans
      (congrArg _ (nerve.discreteIso_hom_app_nerveEquiv_symm i)))).trans
    (SSet.constCompToTopIso_hom_app_toTopPoint ι i.as)
@[simp] lemma discreteHomeomorph_symm_apply (ι : Type u) (i : TopCat.discrete.obj ι) :
    (discreteHomeomorph ι).symm i = vertex ⟨i⟩ := (discreteHomeomorph ι).injective (by simp)

/-- `classifyingSpace (Fin (n + 1))` is homeomorphic to `StdSimplex ℝ (Fin (n + 1))`. -/
noncomputable def finSuccHomeomorphStdSimplex (n : ℕ) :
    classifyingSpace (Fin (n + 1)) ≃ₜ StdSimplex ℝ (Fin (n + 1)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.finSuccIsoStdSimplex n))).trans ⦋n⦌.toTopHomeo
@[simp] lemma finSuccHomeomorphStdSimplex_toTopObjMk (n : ℕ) {d : ℕ}
    (σ : (nerve (Fin (n + 1))) _⦋d⦌) (w : StdSimplex ℝ (Fin (d + 1))) :
    finSuccHomeomorphStdSimplex n (SSet.toTopObjMk (X := nerve (Fin (n + 1))) σ w) =
      StdSimplex.map (fun i ↦ σ.obj i) w := by
  simp only [finSuccHomeomorphStdSimplex, Homeomorph.trans_apply, TopCat.homeoOfIso_apply,
    Functor.mapIso_hom, SSet.toTop_map_toTopObjMk]
  let φ : ⦋d⦌ ⟶ ⦋n⦌ := SSet.stdSimplex.objEquiv ((nerve.finSuccIsoStdSimplex n).hom.app (op ⦋d⦌) σ)
  have hσ : (nerve.finSuccIsoStdSimplex n).hom.app (op ⦋d⦌) σ =
      Δ[n].map φ.op (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) := by ext k : 3; rfl
  rw [hσ, SSet.toTopObjMk_map, ← SSet.toTop_map_yonedaEquiv_symm_toTopHomeo_symm,
    SSet.yonedaEquiv_symm_stdSimplex_id ⦋n⦌, CategoryTheory.Functor.map_id,
    CategoryTheory.id_apply, Homeomorph.apply_symm_apply]
  exact congrArg (StdSimplex.map · w) (funext fun i ↦ nerve.finSuccIsoStdSimplex_hom_app_apply σ i)
@[simp] lemma finSuccHomeomorphStdSimplex_vertex (n : ℕ) (i : Fin (n + 1)) :
    finSuccHomeomorphStdSimplex n (vertex i) = StdSimplex.single i :=
  (congrArg (finSuccHomeomorphStdSimplex n) (vertex_eq_toTopObjMk i)).trans <|
    (finSuccHomeomorphStdSimplex_toTopObjMk n
      (nerveEquiv.symm i : (nerve (Fin (n + 1))) _⦋0⦌) _).trans (StdSimplex.map_single 0 _)
private lemma finSuccIsoStdSimplex_inv_app_id_obj (n : ℕ) :
    (fun i : Fin (n + 1) ↦ ((nerve.finSuccIsoStdSimplex n).inv.app (op ⦋n⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))).obj i) = id :=
  funext fun i ↦ nerve.finSuccIsoStdSimplex_inv_app_obj _ i
lemma finSuccHomeomorphStdSimplex_symm_apply (n : ℕ) (w : StdSimplex ℝ (Fin (n + 1))) :
    (finSuccHomeomorphStdSimplex n).symm w = SSet.toTopObjMk (X := nerve (Fin (n + 1)))
      ((nerve.finSuccIsoStdSimplex n).inv.app (op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))
      w :=
  (finSuccHomeomorphStdSimplex n).injective <| by
    rw [Homeomorph.apply_symm_apply, finSuccHomeomorphStdSimplex_toTopObjMk,
      finSuccIsoStdSimplex_inv_app_id_obj, StdSimplex.map_id]
@[simp] lemma finSuccHomeomorphStdSimplex_symm_single (n : ℕ) (i : Fin (n + 1)) :
    (finSuccHomeomorphStdSimplex n).symm (StdSimplex.single i) = vertex i :=
  (finSuccHomeomorphStdSimplex n).injective (by simp)

/-- The classifying space of `Fin 2` is homeomorphic to `unitInterval`. -/
noncomputable def finTwoHomeomorphI : classifyingSpace (Fin 2) ≃ₜ unitInterval :=
  (finSuccHomeomorphStdSimplex 1).trans StdSimplex.homeomorphI
@[simp] lemma finTwoHomeomorphI_vertex_zero : finTwoHomeomorphI (vertex (0 : Fin 2)) = 0 := by
  ext; simp [finTwoHomeomorphI]
@[simp] lemma finTwoHomeomorphI_vertex_one : finTwoHomeomorphI (vertex (1 : Fin 2)) = 1 := by
  ext; simp [finTwoHomeomorphI]
private lemma edgeMk_finTwo_obj_eq_id :
    (fun i : Fin 2 ↦ (nerve.edgeMk (homOfLE (by decide : (0 : Fin 2) ≤ 1))).edge.obj i) = id :=
  funext fun i ↦ by fin_cases i <;> rfl
@[simp] lemma finTwoHomeomorphI_edgePath_apply (t : unitInterval) :
    finTwoHomeomorphI (edgePath (homOfLE (by decide : (0 : Fin 2) ≤ 1)) t) = t := by
  rw [finTwoHomeomorphI, Homeomorph.trans_apply, edgePath_apply,
    finSuccHomeomorphStdSimplex_toTopObjMk, edgeMk_finTwo_obj_eq_id, StdSimplex.map_id,
    Homeomorph.apply_symm_apply]
lemma finTwoHomeomorphI_symm_apply (t : unitInterval) :
    finTwoHomeomorphI.symm t = edgePath (homOfLE (by decide : (0 : Fin 2) ≤ 1)) t :=
  finTwoHomeomorphI.injective (by simp)
@[simp] lemma finTwoHomeomorphI_symm_zero : finTwoHomeomorphI.symm 0 = vertex (0 : Fin 2) :=
  finTwoHomeomorphI.injective (by simp)
@[simp] lemma finTwoHomeomorphI_symm_one : finTwoHomeomorphI.symm 1 = vertex (1 : Fin 2) :=
  finTwoHomeomorphI.injective (by simp)

/-- There exists a morphism `classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2)` outside the
range of `classifyingSpaceMap`. -/
theorem exists_hom_fin_two_notMem_range_classifyingSpaceMap :
    ∃ f : classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2),
      f ∉ Set.range (classifyingSpaceMap (C := Fin 2) (D := Fin 2)) := by
  -- Transport `t ↦ 1 - t` across `finTwoHomeomorphI`; it swaps `vertex 0` and `vertex 1`, whereas
  -- every functor `Fin 2 ⥤ Fin 2` is order-preserving.
  let f : classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2) := TopCat.ofHom
    ⟨fun z ↦ finTwoHomeomorphI.symm (unitInterval.symm (finTwoHomeomorphI z)), by fun_prop⟩
  refine ⟨f, fun ⟨F, hF⟩ ↦ ?_⟩
  have hf (b : Fin 2) : F.obj b = 1 - b := vertex_injective <| by
    rw [← classifyingSpaceMap_vertex, hF]
    fin_cases b <;> apply finTwoHomeomorphI.injective <;> simp [f]
  have hle := leOfHom (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)))
  rw [hf 0, hf 1] at hle; exact absurd hle (by decide)
end classifyingSpace

section NonFullness
attribute [local instance] uliftCategory
/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` is not full. -/
theorem not_full_classifyingSpaceFunctor : ¬ classifyingSpaceFunctor.{v, u}.Full := by
  intro hfull
  obtain ⟨f, hf⟩ := classifyingSpace.exists_hom_fin_two_notMem_range_classifyingSpaceMap
  let C := ULift.{u} (ULiftHom.{v} (Fin 2))
  let eUp : Fin 2 ⥤ C := ULiftHom.up ⋙ ULift.upFunctor
  let eDown : C ⥤ Fin 2 := ULift.downFunctor ⋙ ULiftHom.down
  have hcomp : eUp ⋙ eDown = 𝟭 (Fin 2) :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ Subsingleton.elim _ _
  let f' : classifyingSpace C ⟶ classifyingSpace C := TopCat.ofHom
    (eUp.toClassifyingSpaceContinuousMap.comp (f.hom.comp eDown.toClassifyingSpaceContinuousMap))
  obtain ⟨G, hG⟩ := hfull.map_surjective (X := Cat.of C) (Y := Cat.of C) f'
  rw [classifyingSpaceFunctor_map] at hG
  refine hf ⟨eUp ⋙ G.toFunctor ⋙ eDown, TopCat.ext fun z ↦ ?_⟩
  have hid (w) : eDown.toClassifyingSpaceContinuousMap (eUp.toClassifyingSpaceContinuousMap w) =
      w := by rw [← ContinuousMap.comp_apply, ← Functor.toClassifyingSpaceContinuousMap_comp, hcomp]
              simp
  rw [← Functor.toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap_apply]
  simp only [Functor.toClassifyingSpaceContinuousMap_comp, ContinuousMap.comp_apply,
    G.toFunctor.toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap_apply]
  rw [ConcreteCategory.congr_hom hG (eUp.toClassifyingSpaceContinuousMap z)]; simp [f', hid]
end NonFullness

/-! ### Opposite categories -/

namespace classifyingSpace
section Opposite
variable (C : Type u) [Category.{v} C]
/-- Isomorphism `classifyingSpace Cᵒᵖ ≅ classifyingSpace C` from `nerve.opIso` and
`SSet.opFunctorCompToTopIso`. -/
noncomputable def opIso : classifyingSpace Cᵒᵖ ≅ classifyingSpace C :=
  SSet.toTop.mapIso (nerve.opIso C) ≪≫ SSet.opFunctorCompToTopIso.app (nerve C)
/-- Homeomorphism `classifyingSpace Cᵒᵖ ≃ₜ classifyingSpace C` reversing barycentric coordinates. -/
noncomputable def opHomeomorph : classifyingSpace Cᵒᵖ ≃ₜ classifyingSpace C :=
  TopCat.homeoOfIso (opIso C)
lemma homeoOfIso_opIso : TopCat.homeoOfIso (opIso C) = opHomeomorph C := (rfl)
lemma opIso_hom_naturality {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    classifyingSpaceMap F.op ≫ (opIso D).hom = (opIso C).hom ≫ classifyingSpaceMap F := by
  rw [classifyingSpaceMap_def, classifyingSpaceMap_def, opIso, opIso, Iso.trans_hom, Iso.trans_hom,
    Functor.mapIso_hom, Functor.mapIso_hom, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    nerve.opIso_hom_naturality, CategoryTheory.Functor.map_comp, Category.assoc]
  exact congrArg (SSet.toTop.map (nerve.opIso C).hom ≫ ·)
    (SSet.opFunctorCompToTopIso.hom.naturality (nerveMap F))
@[simp] lemma opHomeomorph_toTopObjMk {n : ℕ} (σ : (nerve Cᵒᵖ) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    opHomeomorph C (SSet.toTopObjMk (X := nerve Cᵒᵖ) σ w) = SSet.toTopObjMk (X := nerve C)
      ((nerve C).opObjEquiv ((nerve.opIso C).hom.app (op ⦋n⦌) σ)) (StdSimplex.map Fin.rev w) :=
  (congrArg (SSet.opFunctorCompToTopIso.hom.app (nerve C))
    (SSet.toTop_map_toTopObjMk (nerve.opIso C).hom σ w)).trans
    (SSet.opFunctorCompToTopIso_hom_app_toTopObjMk (nerve C) _ w)
@[simp] lemma opHomeomorph_symm_toTopObjMk {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (opHomeomorph C).symm (SSet.toTopObjMk (X := nerve C) σ w) = SSet.toTopObjMk (X := nerve Cᵒᵖ)
      ((nerve.opIso C).inv.app (op ⦋n⦌) ((nerve C).opObjEquiv.symm σ)) (StdSimplex.map Fin.rev w) :=
  (congrArg (SSet.toTop.map (nerve.opIso C).inv)
    (SSet.opFunctorCompToTopIso_inv_app_toTopObjMk (nerve C) σ w)).trans
    (SSet.toTop_map_toTopObjMk (nerve.opIso C).inv _ _)
@[simp] lemma opHomeomorph_vertex (x : Cᵒᵖ) : opHomeomorph C (vertex x) = vertex x.unop :=
  (congrArg (opHomeomorph C) (vertex_eq_toTopObjMk x)).trans <|
    (opHomeomorph_toTopObjMk C (nerveEquiv.symm x : (nerve Cᵒᵖ) _⦋0⦌) _).trans <|
      (congrArg (SSet.toTopObjMk (X := nerve C) · _)
        ((congrArg (nerve C).opObjEquiv (nerve.opIso_hom_app_nerveEquiv_symm C x)).trans
          (Equiv.apply_symm_apply _ _))).trans (SSet.toTopObjMk_eq_toTopPoint _ _)
@[simp] lemma opHomeomorph_symm_vertex (x : C) : (opHomeomorph C).symm (vertex x) = vertex (op x) :=
  (opHomeomorph C).injective (by simp)
@[simp] lemma opHomeomorph_edgePath_apply {x y : C} (f : x ⟶ y) (t : unitInterval) :
    opHomeomorph C (edgePath f.op t) = (edgePath f).symm t := by
  have hop : opHomeomorph C (edgePath f.op t) =
      SSet.toTopOpHomeomorph (nerve C) (SSet.toTop.map (nerve.opIso C).hom (edgePath f.op t)) := by
    rw [SSet.toTopOpHomeomorph_apply]
    -- `opHomeomorph C` is `TopCat.homeoOfIso (opIso C)`, whose `hom` factors through
    -- `nerve.opIso C` and `SSet.opFunctorCompToTopIso.hom.app (nerve C)`.
    rfl
  have hedge : ((nerve.edgeMk f.op).map (nerve.opIso C).hom).toTopPath t =
      (SSet.Edge.opEquiv (nerve.edgeMk f)).toTopPath t :=
    (SSet.Edge.toTopPath_apply _ t).trans <|
      (congrArg (SSet.toTopObjMk (X := (nerve C).op) · (StdSimplex.homeomorphI.symm t)) <|
        (SSet.Edge.map_edge (nerve.edgeMk f.op) (nerve.opIso C).hom).trans <|
          (congrArg ((nerve.opIso C).hom.app (op ⦋1⦌)) (nerve.edgeMk_edge f.op)).trans <|
            (nerve.opIso_hom_app_mk₁ C f).trans <|
              ((congrArg (SSet.opObjEquiv (X := nerve C) (n := op ⦋1⦌)).symm
                (nerve.edgeMk_edge f)).symm.trans
                (SSet.Edge.opEquiv_edge (nerve.edgeMk f)).symm)).trans
        (SSet.Edge.toTopPath_apply _ t).symm
  exact hop.trans <|
    (congrArg (SSet.toTopOpHomeomorph (nerve C))
      ((SSet.Edge.toTop_map_toTopPath_apply (nerve.opIso C).hom (nerve.edgeMk f.op) t).trans
        hedge)).trans
      (SSet.toTopOpHomeomorph_opEquiv_toTopPath_apply (nerve.edgeMk f) t)
lemma opHomeomorph_edgePath {x y : C} (f : x ⟶ y) :
    (edgePath f.op).map (opHomeomorph C).continuous =
      (edgePath f).symm.cast (opHomeomorph_vertex C (op y))
        (opHomeomorph_vertex C (op x)) :=
  _root_.Path.ext (funext (opHomeomorph_edgePath_apply C f))
lemma opHomeomorph_naturality_apply {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (z : classifyingSpace Cᵒᵖ) :
    opHomeomorph D (classifyingSpaceMap F.op z) = classifyingSpaceMap F (opHomeomorph C z) :=
  ConcreteCategory.congr_hom (opIso_hom_naturality F) z
lemma opHomeomorph_toClassifyingSpaceContinuousMap_apply {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (z : classifyingSpace Cᵒᵖ) :
    opHomeomorph D (F.op.toClassifyingSpaceContinuousMap z) =
      F.toClassifyingSpaceContinuousMap (opHomeomorph C z) := by
  obtain ⟨n, (σ : ComposableArrows Cᵒᵖ n), w, rfl⟩ := SSet.exists_toTopObjMk (X := nerve Cᵒᵖ) z
  rw [Functor.toClassifyingSpaceContinuousMap_toTopObjMk,
    opHomeomorph_toTopObjMk D ((F.op.mapComposableArrows n).obj σ) w,
    opHomeomorph_toTopObjMk C σ w,
    Functor.toClassifyingSpaceContinuousMap_toTopObjMk F
      ((nerve C).opObjEquiv ((nerve.opIso C).hom.app (op ⦋n⦌) σ))]
  refine congrArg (SSet.toTopObjMk (X := nerve D) · _) <|
    CategoryTheory.Functor.ext
      (fun i ↦ (nerve.opIso_hom_app_obj D ((F.op.mapComposableArrows n).obj σ) i).trans
        (congrArg F.obj (nerve.opIso_hom_app_obj C σ i)).symm)
      fun i j g ↦ ?_
  obtain ⟨h, rfl⟩ : ∃ h : i ≤ j, g = homOfLE h := ⟨leOfHom g, Subsingleton.elim _ _⟩
  refine (nerve.opIso_hom_app_map D ((F.op.mapComposableArrows n).obj σ) h).trans ?_
  have hC : ((F.mapComposableArrows n).obj
      (SSet.opObjEquiv ((nerve.opIso C).hom.app (op ⦋n⦌) σ))).map (homOfLE h) =
      F.map (((nerve C).opObjEquiv ((nerve.opIso C).hom.app (op ⦋n⦌) σ)).map (homOfLE h)) := rfl
  rw [hC, nerve.opIso_hom_app_map C σ h]
  simp [eqToHom_map]
end Opposite

/-! ### Path components and categorical connected components -/

section PathComponents
variable (C : Type u) [Category.{v} C]
/-- The path components `ZerothHomotopy (classifyingSpace C)` correspond canonically to
`ConnectedComponents C`. -/
noncomputable def zerothHomotopyEquivConnectedComponents :
    ZerothHomotopy (classifyingSpace C) ≃ ConnectedComponents C :=
  (SSet.π₀EquivZerothHomotopy (nerve C)).symm.trans (nerve.π₀EquivConnectedComponents C)
@[simp] lemma zerothHomotopyEquivConnectedComponents_mk_vertex (c : C) :
    zerothHomotopyEquivConnectedComponents C (ZerothHomotopy.mk (vertex c)) =
      ConnectedComponents.mk c := by
  rw [vertex_def, ← SSet.π₀EquivZerothHomotopy_mk (X := nerve C) (nerveEquiv.symm c)]
  simp [zerothHomotopyEquivConnectedComponents]
@[simp] lemma zerothHomotopyEquivConnectedComponents_symm_mk (c : C) :
    (zerothHomotopyEquivConnectedComponents C).symm (ConnectedComponents.mk c) =
      ZerothHomotopy.mk (vertex c) :=
  (zerothHomotopyEquivConnectedComponents C).injective (by simp)
/-- `classifyingSpace C` is path-connected if and only if `C` is a connected category. -/
@[simp] theorem pathConnectedSpace_iff :
    PathConnectedSpace (classifyingSpace C) ↔ CategoryTheory.IsConnected C :=
  (SSet.pathConnectedSpace_toTop_iff (nerve C)).trans (nerve.isConnected_iff C)
instance [CategoryTheory.IsConnected C] : PathConnectedSpace (classifyingSpace C) :=
  (pathConnectedSpace_iff C).2 ‹_›
end PathComponents

@[simp] lemma zerothHomotopyEquivConnectedComponents_mk_toClassifyingSpaceContinuousMap
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    (z : classifyingSpace C) :
    zerothHomotopyEquivConnectedComponents D
        (ZerothHomotopy.mk (F.toClassifyingSpaceContinuousMap z)) =
      F.mapConnectedComponents
        (zerothHomotopyEquivConnectedComponents C (ZerothHomotopy.mk z)) := by
  obtain ⟨c, hc⟩ := exists_joined_vertex z
  rw [(ZerothHomotopy.sound hc.somePath).symm,
    (ZerothHomotopy.sound (hc.somePath.map F.toClassifyingSpaceContinuousMap.continuous)).symm]
  simp
@[simp] lemma zerothHomotopyEquivConnectedComponents_mk_classifyingSpaceMap {C D : Type u}
    [Category.{v} C] [Category.{v} D] (F : C ⥤ D) (z : classifyingSpace C) :
    zerothHomotopyEquivConnectedComponents D (ZerothHomotopy.mk (classifyingSpaceMap F z)) =
      F.mapConnectedComponents
        (zerothHomotopyEquivConnectedComponents C (ZerothHomotopy.mk z)) := by
  rw [← F.toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap_apply z]; simp
end classifyingSpace

/-! ### Homotopies from natural transformations and zigzags -/

namespace NatTrans
section SameUniverse
variable {B C D E : Type u} [Category.{v} B] [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁)
/-- A natural transformation `η : F₀ ⟶ F₁` between functors in the same universes induces a homotopy
from `(classifyingSpaceMap F₀).hom` to `(classifyingSpaceMap F₁).hom`. -/
noncomputable def classifyingSpaceHomotopy :
    ContinuousMap.Homotopy (classifyingSpaceMap F₀).hom (classifyingSpaceMap F₁).hom where
  toContinuousMap := η.nerveHomotopy.toTop.toContinuousMap
  map_zero_left := η.nerveHomotopy.toTop.map_zero_left
  map_one_left := η.nerveHomotopy.toTop.map_one_left
lemma classifyingSpaceHomotopy_def :
    η.classifyingSpaceHomotopy.toContinuousMap = η.nerveHomotopy.toTop.toContinuousMap := (rfl)
lemma classifyingSpaceHomotopy_apply (t : unitInterval) (z : classifyingSpace C) :
    η.classifyingSpaceHomotopy (t, z) = η.nerveHomotopy.toTop (t, z) := (rfl)
@[simp] lemma classifyingSpaceHomotopy_vertex (t : unitInterval) (c : C) :
    η.classifyingSpaceHomotopy (t, classifyingSpace.vertex c) =
      classifyingSpace.edgePath (η.app c) t :=
  (SSet.Homotopy.toTop_toTopPoint η.nerveHomotopy t
    (nerveEquiv.symm c : (nerve C) _⦋0⦌)).trans <|
    (congrArg (SSet.toTopObjMk (X := nerve D) · (StdSimplex.homeomorphI.symm t))
      ((nerveHomotopy_h_verticalEdge η c).trans (nerve.edgeMk_edge (η.app c)).symm)).trans
      (classifyingSpace.edgePath_apply (η.app c) t).symm
@[simp] lemma whiskerLeft_classifyingSpaceHomotopy_apply (K : B ⥤ C) (t : unitInterval)
    (z : classifyingSpace B) :
    (Functor.whiskerLeft K η).classifyingSpaceHomotopy (t, z) =
      η.classifyingSpaceHomotopy (t, classifyingSpaceMap K z) := by
  rw [classifyingSpaceHomotopy_apply, SSet.Homotopy.toTop_apply_of_h
    (H₁ := η.nerveHomotopy.precomp (nerveMap K))
    ((whiskerLeft_nerveHomotopy_h K η).trans (SSet.Homotopy.precomp_h _ _).symm),
    SSet.Homotopy.toTop_precomp_apply]
  rfl
@[simp] lemma whiskerRight_classifyingSpaceHomotopy_apply (G : D ⥤ E) (t : unitInterval)
    (z : classifyingSpace C) :
    (Functor.whiskerRight η G).classifyingSpaceHomotopy (t, z) =
      classifyingSpaceMap G (η.classifyingSpaceHomotopy (t, z)) := by
  rw [classifyingSpaceHomotopy_apply, SSet.Homotopy.toTop_apply_of_h
    (H₁ := η.nerveHomotopy.postcomp (nerveMap G))
    ((whiskerRight_nerveHomotopy_h η G).trans (SSet.Homotopy.postcomp_h _ _).symm),
    SSet.Homotopy.toTop_postcomp_apply]
  rfl
private lemma classifyingSpaceHomotopy_toTopObjMk_of_prism {p n : ℕ} (σ : ComposableArrows C p)
    (s : StdSimplex ℝ (Fin (p + 1))) (t : unitInterval) (α : ⦋n⦌ ⟶ ⦋p⦌) (β : ⦋n⦌ ⟶ ⦋1⦌)
    (w : StdSimplex ℝ (Fin (n + 1)))
    (hprism : SSet.prodStdSimplex₁.prism.{max u v} p (s, t) =
      SSet.toTopObjMk (X := (Δ[p] ⊗ Δ[1] : SSet.{max u v}))
        (SSet.stdSimplex.objEquiv.symm α, SSet.stdSimplex.objEquiv.symm β) w) :
    η.classifyingSpaceHomotopy (t, SSet.toTopObjMk (X := nerve C) σ s) =
      SSet.toTopObjMk (X := nerve D)
        (η.mapNerveCylinderObj (σ.whiskerLeft (SimplexCategory.toCat.map α).toFunctor) β) w := by
  rw [classifyingSpaceHomotopy_apply, SSet.Homotopy.toTop_apply,
    SSet.toTopCylinder_toTopObjMk_of_prism (X := nerve C) σ s t hprism]
  let p₀ : (nerve C ⊗ Δ[1] : SSet.{max u v}) _⦋n⦌ :=
    ((nerve C).map α.op σ, SSet.stdSimplex.objEquiv.symm β)
  exact (SSet.toTop_map_toTopObjMk η.nerveHomotopy.h p₀ w).trans
    (congrArg (SSet.toTopObjMk (X := nerve D) · w)
      ((nerveHomotopy_h_app η (op ⦋n⦌) p₀).trans (congrArg _ (Equiv.apply_symm_apply _ _))))
end SameUniverse

section CrossUniverse
variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C]
  {D : Type u₃} [Category.{v₃} D]
/-- A natural transformation `η : F₀ ⟶ F₁` across arbitrary universes induces a homotopy from
`F₀.toClassifyingSpaceContinuousMap` to `F₁.toClassifyingSpaceContinuousMap`. -/
noncomputable def toClassifyingSpaceHomotopy {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    ContinuousMap.Homotopy F₀.toClassifyingSpaceContinuousMap
      F₁.toClassifyingSpaceContinuousMap where
  toFun p := classifyingSpace.asSmallHomeomorph.{max u₂ v₂} D
    ((Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₃ v₃} C ⥤ C)
      (Functor.whiskerRight η (AsSmall.up : D ⥤ AsSmall.{max u₂ v₂} D))).classifyingSpaceHomotopy
      (p.1, (classifyingSpace.asSmallHomeomorph.{max u₃ v₃} C).symm p.2))
  continuous_toFun := by fun_prop
  map_zero_left _ := by simp [Functor.toClassifyingSpaceContinuousMap]
  map_one_left _ := by simp [Functor.toClassifyingSpaceContinuousMap]
lemma toClassifyingSpaceHomotopy_apply {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (t : unitInterval)
    (z : classifyingSpace C) :
    η.toClassifyingSpaceHomotopy (t, z) = classifyingSpace.asSmallHomeomorph.{max u₂ v₂} D
      ((Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₃ v₃} C ⥤ C)
        (Functor.whiskerRight η (AsSmall.up : D ⥤ AsSmall.{max u₂ v₂} D))).classifyingSpaceHomotopy
        (t, (classifyingSpace.asSmallHomeomorph.{max u₃ v₃} C).symm z)) := (rfl)
@[simp] lemma toClassifyingSpaceHomotopy_vertex {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (t : unitInterval)
    (c : C) :
    η.toClassifyingSpaceHomotopy (t, classifyingSpace.vertex c) =
      classifyingSpace.edgePath (η.app c) t := by
  rw [toClassifyingSpaceHomotopy_apply, classifyingSpace.asSmallHomeomorph_symm_vertex,
    classifyingSpaceHomotopy_vertex, classifyingSpace.edgePath_apply, nerve.edgeMk_edge,
    classifyingSpace.asSmallHomeomorph_toTopObjMk, Functor.mapComposableArrows_obj_mk₁,
    classifyingSpace.edgePath_apply, nerve.edgeMk_edge]
  -- `AsSmall.down.map (AsSmall.up.map (η.app (AsSmall.down.obj (AsSmall.up.obj c))))` is
  -- definitionally `η.app c`.
  rfl
private lemma toClassifyingSpaceHomotopy_toTopObjMk_of_prism {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁)
    {p n : ℕ} (σ : ComposableArrows C p) (s : StdSimplex ℝ (Fin (p + 1))) (t : unitInterval)
    (α : ⦋n⦌ ⟶ ⦋p⦌) (β : ⦋n⦌ ⟶ ⦋1⦌) (w : StdSimplex ℝ (Fin (n + 1)))
    (hprism : SSet.prodStdSimplex₁.prism.{max (max u₂ v₂) (max u₃ v₃)} p (s, t) =
      SSet.toTopObjMk (X := (Δ[p] ⊗ Δ[1] : SSet.{max (max u₂ v₂) (max u₃ v₃)}))
        (SSet.stdSimplex.objEquiv.symm α, SSet.stdSimplex.objEquiv.symm β) w) :
    η.toClassifyingSpaceHomotopy (t, SSet.toTopObjMk (X := nerve C) σ s) =
      SSet.toTopObjMk (X := nerve D)
        (η.mapNerveCylinderObj (σ.whiskerLeft (SimplexCategory.toCat.map α).toFunctor) β) w := by
  rw [toClassifyingSpaceHomotopy_apply, classifyingSpace.asSmallHomeomorph_symm_toTopObjMk,
    classifyingSpaceHomotopy_toTopObjMk_of_prism _ _ s t α β w hprism,
    classifyingSpace.asSmallHomeomorph_toTopObjMk,
    whiskerLeft_mapNerveCylinderObj, whiskerRight_mapNerveCylinderObj]
  simp only [Functor.mapComposableArrows_obj, ComposableArrows.whiskerLeft]
  exact congrArg (fun τ ↦ SSet.toTopObjMk (X := nerve D) (η.mapNerveCylinderObj τ β) w) <|
    (CategoryTheory.Functor.assoc _ (σ ⋙ AsSmall.up) AsSmall.down).trans <|
      congrArg ((SimplexCategory.toCat.map α).toFunctor ⋙ ·) <|
        (CategoryTheory.Functor.assoc σ AsSmall.up AsSmall.down).trans <|
          (congrArg (σ ⋙ ·) (AsSmall.up_comp_down C)).trans (CategoryTheory.Functor.comp_id σ)
@[simp] lemma whiskerLeft_toClassifyingSpaceHomotopy_apply (K : B ⥤ C) {F₀ F₁ : C ⥤ D}
    (η : F₀ ⟶ F₁) (t : unitInterval) (z : classifyingSpace B) :
    (Functor.whiskerLeft K η).toClassifyingSpaceHomotopy (t, z) =
      η.toClassifyingSpaceHomotopy (t, K.toClassifyingSpaceContinuousMap z) := by
  obtain ⟨p, (σ : ComposableArrows B p), s, rfl⟩ := SSet.exists_toTopObjMk (X := nerve B) z
  obtain ⟨n, α, β, w, h₁, h₂⟩ := SSet.prodStdSimplex₁.exists_prism_eq_toTopObjMk.{
    max (max u₁ v₁) (max u₃ v₃), max (max u₂ v₂) (max u₃ v₃)} p s t
  rw [Functor.toClassifyingSpaceContinuousMap_toTopObjMk,
    toClassifyingSpaceHomotopy_toTopObjMk_of_prism _ σ s t α β w h₁,
    toClassifyingSpaceHomotopy_toTopObjMk_of_prism _ _ s t α β w h₂,
    whiskerLeft_mapNerveCylinderObj]
  exact congrArg (fun τ ↦ SSet.toTopObjMk (X := nerve D) (η.mapNerveCylinderObj τ β) w)
    (CategoryTheory.Functor.assoc _ σ K)
@[simp] lemma whiskerRight_toClassifyingSpaceHomotopy_apply {F₀ F₁ : B ⥤ C} (η : F₀ ⟶ F₁)
    (G : C ⥤ D) (t : unitInterval) (z : classifyingSpace B) :
    (Functor.whiskerRight η G).toClassifyingSpaceHomotopy (t, z) =
      G.toClassifyingSpaceContinuousMap (η.toClassifyingSpaceHomotopy (t, z)) := by
  obtain ⟨p, (σ : ComposableArrows B p), s, rfl⟩ := SSet.exists_toTopObjMk (X := nerve B) z
  obtain ⟨n, α, β, w, h₁, h₂⟩ := SSet.prodStdSimplex₁.exists_prism_eq_toTopObjMk.{
    max (max u₁ v₁) (max u₃ v₃), max (max u₁ v₁) (max u₂ v₂)} p s t
  rw [toClassifyingSpaceHomotopy_toTopObjMk_of_prism _ σ s t α β w h₁,
    toClassifyingSpaceHomotopy_toTopObjMk_of_prism _ σ s t α β w h₂,
    Functor.toClassifyingSpaceContinuousMap_toTopObjMk, whiskerRight_mapNerveCylinderObj]
end CrossUniverse

lemma toClassifyingSpaceHomotopy_eq_classifyingSpaceHomotopy_apply {C D : Type u} [Category.{v} C]
    [Category.{v} D] {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (t : unitInterval) (z : classifyingSpace C) :
    η.toClassifyingSpaceHomotopy (t, z) = η.classifyingSpaceHomotopy (t, z) := by
  obtain ⟨p, (σ : ComposableArrows C p), s, rfl⟩ := SSet.exists_toTopObjMk (X := nerve C) z
  obtain ⟨n, α, β, w, h₁, h₂⟩ :=
    SSet.prodStdSimplex₁.exists_prism_eq_toTopObjMk.{max u v, max u v} p s t
  rw [toClassifyingSpaceHomotopy_toTopObjMk_of_prism η σ s t α β w h₁,
    classifyingSpaceHomotopy_toTopObjMk_of_prism η σ s t α β w h₂]
end NatTrans

namespace Zigzag
/-- A zigzag of natural transformations across arbitrary universes induces a homotopy between the
induced maps on classifying spaces. -/
theorem homotopic_toClassifyingSpaceContinuousMap {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F₀ F₁ : C ⥤ D} (h : Zigzag F₀ F₁) :
    F₀.toClassifyingSpaceContinuousMap.Homotopic F₁.toClassifyingSpaceContinuousMap := by
  induction h with
  | refl => exact .refl _
  | tail _ hzag ih =>
    exact hzag.rec (fun ⟨η⟩ ↦ ih.trans ⟨η.toClassifyingSpaceHomotopy⟩)
      fun ⟨η⟩ ↦ ih.trans ⟨η.toClassifyingSpaceHomotopy.symm⟩
/-- A zigzag of natural transformations between functors in the same universes induces a homotopy
between `(classifyingSpaceMap F₀).hom` and `(classifyingSpaceMap F₁).hom`. -/
theorem homotopic_classifyingSpaceMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F₀ F₁ : C ⥤ D} (h : Zigzag F₀ F₁) :
    (classifyingSpaceMap F₀).hom.Homotopic (classifyingSpaceMap F₁).hom := by
  rw [← Functor.toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap F₀,
    ← Functor.toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap F₁]
  exact h.homotopic_toClassifyingSpaceContinuousMap
end Zigzag

/-! ### Adjunctions, equivalences, skeletons, small models, and contractibility -/

namespace Adjunction
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C}
/-- An adjunction `L ⊣ R` across arbitrary universes induces a homotopy equivalence
`classifyingSpace C ≃ₕ classifyingSpace D`. -/
noncomputable def classifyingSpaceHomotopyEquiv (adj : L ⊣ R) :
    ContinuousMap.HomotopyEquiv (classifyingSpace C) (classifyingSpace D) where
  toFun := L.toClassifyingSpaceContinuousMap
  invFun := R.toClassifyingSpaceContinuousMap
  left_inv := by
    rw [← Functor.toClassifyingSpaceContinuousMap_comp,
      ← Functor.toClassifyingSpaceContinuousMap_id]
    exact ⟨adj.unit.toClassifyingSpaceHomotopy.symm⟩
  right_inv := by
    rw [← Functor.toClassifyingSpaceContinuousMap_comp,
      ← Functor.toClassifyingSpaceContinuousMap_id]
    exact ⟨adj.counit.toClassifyingSpaceHomotopy⟩
@[simp] lemma classifyingSpaceHomotopyEquiv_toFun (adj : L ⊣ R) :
    adj.classifyingSpaceHomotopyEquiv.toFun = L.toClassifyingSpaceContinuousMap := (rfl)
@[simp] lemma classifyingSpaceHomotopyEquiv_invFun (adj : L ⊣ R) :
    adj.classifyingSpaceHomotopyEquiv.invFun = R.toClassifyingSpaceContinuousMap := (rfl)
end Adjunction

namespace Equivalence
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
/-- An equivalence of categories `C ≌ D` across arbitrary universes induces a homotopy equivalence
`classifyingSpace C ≃ₕ classifyingSpace D`. -/
noncomputable def classifyingSpaceHomotopyEquiv (e : C ≌ D) :
    ContinuousMap.HomotopyEquiv (classifyingSpace C) (classifyingSpace D) :=
  e.toAdjunction.classifyingSpaceHomotopyEquiv
@[simp] lemma classifyingSpaceHomotopyEquiv_toFun (e : C ≌ D) :
    e.classifyingSpaceHomotopyEquiv.toFun = e.functor.toClassifyingSpaceContinuousMap := (rfl)
@[simp] lemma classifyingSpaceHomotopyEquiv_invFun (e : C ≌ D) :
    e.classifyingSpaceHomotopyEquiv.invFun = e.inverse.toClassifyingSpaceContinuousMap := (rfl)
end Equivalence

namespace classifyingSpace
variable (C : Type u) [Category.{v} C]
/-- Passing to a skeleton `Skeleton C` preserves the homotopy type of `classifyingSpace C`. -/
noncomputable def skeletonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (classifyingSpace (Skeleton C)) (classifyingSpace C) :=
  (skeletonEquivalence C).classifyingSpaceHomotopyEquiv
@[simp] lemma skeletonHomotopyEquiv_toFun : (skeletonHomotopyEquiv C).toFun =
    (skeletonEquivalence C).functor.toClassifyingSpaceContinuousMap := (rfl)
@[simp] lemma skeletonHomotopyEquiv_invFun : (skeletonHomotopyEquiv C).invFun =
    (skeletonEquivalence C).inverse.toClassifyingSpaceContinuousMap := (rfl)
/-- An essentially `w`-small category `C` has classifying space homotopy equivalent to that of its
small model `SmallModel.{w} C`. -/
noncomputable def smallModelHomotopyEquiv [EssentiallySmall.{w} C] :
    ContinuousMap.HomotopyEquiv (classifyingSpace (SmallModel.{w} C)) (classifyingSpace C) :=
  (equivSmallModel.{w} C).symm.classifyingSpaceHomotopyEquiv
@[simp] lemma smallModelHomotopyEquiv_toFun [EssentiallySmall.{w} C] :
    (smallModelHomotopyEquiv.{w} C).toFun =
      (equivSmallModel.{w} C).inverse.toClassifyingSpaceContinuousMap := (rfl)
@[simp] lemma smallModelHomotopyEquiv_invFun [EssentiallySmall.{w} C] :
    (smallModelHomotopyEquiv.{w} C).invFun =
      (equivSmallModel.{w} C).functor.toClassifyingSpaceContinuousMap := (rfl)
end classifyingSpace

namespace Limits
variable {C : Type u} [Category.{v} C]
/-- If `C` has a chosen initial object `x`, `classifyingSpace C` is contractible. -/
theorem IsInitial.contractibleSpace_classifyingSpace {x : C} (hx : IsInitial x) :
    ContractibleSpace (classifyingSpace C) :=
  SSet.contractibleSpace_toTop_of_homotopy hx.nerveHomotopy
/-- If `C` has a chosen terminal object `x`, `classifyingSpace C` is contractible. -/
theorem IsTerminal.contractibleSpace_classifyingSpace {x : C} (hx : IsTerminal x) :
    ContractibleSpace (classifyingSpace C) :=
  SSet.contractibleSpace_toTop_of_homotopy_id_const hx.nerveHomotopy
instance instContractibleSpaceClassifyingSpaceOfHasInitial (C : Type u) [Category.{v} C]
    [HasInitial C] : ContractibleSpace (classifyingSpace C) :=
  initialIsInitial.contractibleSpace_classifyingSpace
instance instContractibleSpaceClassifyingSpaceOfHasTerminal (C : Type u) [Category.{v} C]
    [HasTerminal C] : ContractibleSpace (classifyingSpace C) :=
  terminalIsTerminal.contractibleSpace_classifyingSpace
end Limits
end CategoryTheory
