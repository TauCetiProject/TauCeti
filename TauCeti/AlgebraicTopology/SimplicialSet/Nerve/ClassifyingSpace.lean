/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Op
public import TauCeti.AlgebraicTopology.SimplicialSet.PrismRealization
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Basic

/-!
# Classifying spaces of categories

The classifying space `CategoryTheory.classifyingSpace C` of a category `C` is `|nerve C|`. Objects,
morphisms, and composable pairs give vertices, edge paths, and homotopies assembling into
`classifyingSpace.toFundamentalGroupoid : C ⥤ FundamentalGroupoid (classifyingSpace C)`. We build
`classifyingSpaceFunctor : Cat ⥤ TopCat`, `Functor.toClassifyingSpaceContinuousMap`, and
`NatTrans.toClassifyingSpaceHomotopy` across arbitrary universes via `asSmallHomeomorph`, and derive
homotopy invariance under adjunctions/equivalences, contractibility from initial/terminal objects,
`classifyingSpace.opHomeomorph`, and `classifyingSpace.zerothHomotopyEquivConnectedComponents`.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341, Springer, 1973, §1.
* C. A. Weibel, *An Introduction to Algebraic K-Theory*, AMS, 2013, Chapter IV, §§3.1–3.3.
-/

public section

open Opposite Simplicial Convexity

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

/-- The classifying space `BC` of a category `C`, defined as `|nerve C|`. -/
@[expose, implicit_reducible]
noncomputable def classifyingSpace (C : Type u) [Category.{v} C] : TopCat.{max u v} := |nerve C|

/-- Definitional equality `classifyingSpace C = |nerve C|`. -/
lemma classifyingSpace_def (C : Type u) [Category.{v} C] : classifyingSpace C = |nerve C| := rfl

/-- A functor `F : C ⥤ D` in the same universes induces a morphism on classifying spaces. -/
@[expose, implicit_reducible]
noncomputable def classifyingSpaceMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : classifyingSpace C ⟶ classifyingSpace D :=
  SSet.toTop.map (nerveMap F)

@[simp]
lemma classifyingSpaceMap_id (C : Type u) [Category.{v} C] :
    classifyingSpaceMap (𝟭 C) = 𝟙 (classifyingSpace C) := by
  rw [classifyingSpaceMap, nerveMap_id, CategoryTheory.Functor.map_id]; rfl

@[simp, reassoc]
lemma classifyingSpaceMap_comp {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    classifyingSpaceMap (F ⋙ G) = classifyingSpaceMap F ≫ classifyingSpaceMap G := by
  rw [classifyingSpaceMap, nerveMap_comp, CategoryTheory.Functor.map_comp]; rfl

/-- The classifying space functor `Cat.{v, u} ⥤ TopCat.{max u v}` (`nerveFunctor ⋙ SSet.toTop`). -/
@[expose]
noncomputable def classifyingSpaceFunctor : Cat.{v, u} ⥤ TopCat.{max u v} :=
  nerveFunctor ⋙ SSet.toTop

@[simp]
lemma classifyingSpaceFunctor_obj (C : Cat.{v, u}) :
    classifyingSpaceFunctor.obj C = classifyingSpace C := (rfl)

@[simp]
lemma classifyingSpaceFunctor_map {C D : Cat.{v, u}} (F : C ⟶ D) :
    classifyingSpaceFunctor.map F = classifyingSpaceMap F.toFunctor := (rfl)

namespace classifyingSpace

private def vertexSimplex {C : Type u} [Category.{v} C] (c : C) : (nerve C) _⦋0⦌ :=
  nerveEquiv.symm c

section VerticesAndEdges

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The vertex of `classifyingSpace C` corresponding to an object `c : C`. -/
noncomputable def vertex (c : C) : classifyingSpace C :=
  SSet.toTopPoint (X := nerve C) (nerveEquiv.symm c)

private lemma vertex_eq (c : C) : vertex c = SSet.toTopPoint (vertexSimplex c) := rfl

/-- Distinct objects of `C` determine distinct vertices of `classifyingSpace C`. -/
theorem vertex_injective : Function.Injective (vertex (C := C)) :=
  (SSet.toTopPoint_injective (nerve C)).comp nerveEquiv.symm.injective

@[simp]
lemma vertex_inj {x y : C} : vertex x = vertex y ↔ x = y := vertex_injective.eq_iff

@[simp]
lemma classifyingSpaceMap_vertex (F : C ⥤ D) (c : C) :
    classifyingSpaceMap F (vertex c) = vertex (F.obj c) := by
  rw [classifyingSpaceMap, vertex_eq, SSet.toTop_map_toTopPoint, vertex_eq]
  exact congrArg (SSet.toTopPoint (X := nerve D)) (nerveMap_app_zero_nerveEquiv_symm F c)

@[simp]
lemma classifyingSpaceMap_const (C : Type u) [Category.{v} C] {D : Type u} [Category.{v} D]
    (d : D) (z : classifyingSpace C) :
    classifyingSpaceMap ((Functor.const C).obj d) z = vertex d := by
  rw [classifyingSpaceMap, nerveMap_const, vertex_eq]
  exact SSet.toTop_map_const (vertexSimplex d) z

/-- Every point of `classifyingSpace C` is path-connected to the vertex of some object of `C`. -/
lemma exists_joined_vertex (z : classifyingSpace C) : ∃ c : C, Joined (vertex c) z := by
  obtain ⟨x, hx⟩ := SSet.exists_joined_toTopPoint (X := nerve C) z
  exact ⟨nerveEquiv x, by rw [vertex, Equiv.symm_apply_apply nerveEquiv x]; exact hx.symm⟩

/-- The path in `classifyingSpace C` from `vertex x` to `vertex y` traced by `f : x ⟶ y`. -/
noncomputable def edgePath {x y : C} (f : x ⟶ y) : _root_.Path (vertex x) (vertex y) :=
  (nerve.edgeMk f).toTopPath

@[simp]
lemma edgePath_apply {x y : C} (f : x ⟶ y) (t : unitInterval) :
    edgePath f t = SSet.toTopObjMk (nerve.edgeMk f).edge (StdSimplex.homeomorphI.symm t) :=
  (nerve.edgeMk f).toTopPath_apply t

/-- The identity morphism `𝟙 x` traces the constant path at `vertex x`. -/
@[simp]
lemma edgePath_id (x : C) : edgePath (𝟙 x) = _root_.Path.refl (vertex x) := by
  rw [edgePath, nerve.edgeMk_id]; exact SSet.Edge.toTopPath_id (vertexSimplex x)

/-- For composable `f : x ⟶ y` and `g : y ⟶ z`, the `2`-simplex `(f, g)` of `nerve C` furnishes a
path homotopy from `edgePath (f ≫ g)` to `(edgePath f).trans (edgePath g)`. -/
theorem edgePath_comp_homotopic {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    (edgePath (f ≫ g)).Homotopic ((edgePath f).trans (edgePath g)) :=
  (((nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl).some).toTopPath_homotopic

lemma classifyingSpaceMap_edgePath_apply (F : C ⥤ D) {x y : C} (f : x ⟶ y) (t : unitInterval) :
    classifyingSpaceMap F (edgePath f t) = edgePath (F.map f) t := by
  rw [classifyingSpaceMap, edgePath_apply, SSet.toTop_map_toTopObjMk, edgePath_apply]
  exact congrArg (SSet.toTopObjMk (X := nerve D) · _) (nerveMap_app_one_edgeMk F f)

/-- The canonical functor `C ⥤ FundamentalGroupoid (classifyingSpace C)` sending `c` to `vertex c`
and `f : x ⟶ y` to the path-homotopy class of `edgePath f`. -/
@[expose]
noncomputable def toFundamentalGroupoid (C : Type u) [Category.{v} C] :
    C ⥤ FundamentalGroupoid (classifyingSpace C) where
  obj c := FundamentalGroupoid.mk (vertex c)
  map f := FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (edgePath f))
  map_id _ := by rw [edgePath_id, FundamentalGroupoid.id_eq_path_refl]; rfl
  map_comp f g := by
    rw [FundamentalGroupoid.comp_eq, ← Path.Homotopic.Quotient.mk_trans]
    exact (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).2 (edgePath_comp_homotopic f g)

@[simp]
lemma toFundamentalGroupoid_obj (c : C) :
    (toFundamentalGroupoid C).obj c = FundamentalGroupoid.mk (vertex c) := (rfl)

@[simp]
lemma toFundamentalGroupoid_map {x y : C} (f : x ⟶ y) :
    (toFundamentalGroupoid C).map f =
      FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (edgePath f)) := (rfl)

end VerticesAndEdges

end classifyingSpace

/-- Distinct functors `F, G : C ⥤ D` induce distinct maps on classifying spaces. -/
theorem classifyingSpaceMap_injective {C D : Type u} [Category.{v} C] [Category.{v} D] :
    Function.Injective (classifyingSpaceMap (C := C) (D := D)) := by
  intro F G h
  have h_obj (c : C) : F.obj c = G.obj c := classifyingSpace.vertex_injective <| by
    simpa using ConcreteCategory.congr_hom h (classifyingSpace.vertex c)
  refine CategoryTheory.Functor.ext h_obj fun x y f ↦ ?_
  have hmk : ComposableArrows.mk₁ (F.map f) = ComposableArrows.mk₁ (G.map f) :=
    SSet.toTopObjMk_one_injective (nerve D) <| funext fun w ↦ by
      have hw := ConcreteCategory.congr_hom h
        (SSet.toTopObjMk (X := nerve C) (nerve.edgeMk f).edge w)
      rwa [classifyingSpaceMap, SSet.toTop_map_toTopObjMk, classifyingSpaceMap,
        SSet.toTop_map_toTopObjMk, nerveMap_app_one_edgeMk, nerveMap_app_one_edgeMk] at hw
  rw [← ComposableArrows.mk₁_eqToHom_comp (h_obj x),
    ← ComposableArrows.mk₁_comp_eqToHom _ (h_obj y).symm, Category.assoc] at hmk
  exact (Arrow.mk_inj _ _).1 (ComposableArrows.arrowEquiv.symm.injective hmk)

instance instFaithfulClassifyingSpaceFunctor : classifyingSpaceFunctor.{v, u}.Faithful where
  map_injective h := Cat.Hom.ext (classifyingSpaceMap_injective h)

namespace classifyingSpace

/-- The classifying space of `AsSmall.{w} C` is canonically homeomorphic to `classifyingSpace C`. -/
noncomputable def asSmallHomeomorph (C : Type u) [Category.{v} C] :
    classifyingSpace (AsSmall.{w} C) ≃ₜ classifyingSpace C :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.asSmallIso.{w} C))).trans
    (SSet.toTopUliftHomeomorph.{w, max u v} (nerve C))

@[simp]
lemma asSmallHomeomorph_toTopObjMk (C : Type u) [Category.{v} C] {n : ℕ}
    (σ : (nerve (AsSmall.{w} C)) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    asSmallHomeomorph.{w} C (SSet.toTopObjMk (X := nerve (AsSmall.{w} C)) σ w₀) =
      SSet.toTopObjMk (X := nerve C) (AsSmall.down.mapNerveObj σ) w₀ := by
  simp [asSmallHomeomorph, SSet.toTopUliftHomeomorph_toTopObjMk (nerve C)]

@[simp]
lemma asSmallHomeomorph_symm_toTopObjMk (C : Type u) [Category.{v} C] {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (w₀ : StdSimplex ℝ (Fin (n + 1))) :
    (asSmallHomeomorph.{w} C).symm (SSet.toTopObjMk (X := nerve C) σ w₀) =
      SSet.toTopObjMk (X := nerve (AsSmall.{w} C)) (AsSmall.up.mapNerveObj σ) w₀ := by
  apply (asSmallHomeomorph.{w} C).injective
  rw [Homeomorph.apply_symm_apply, asSmallHomeomorph_toTopObjMk]
  exact congrArg (SSet.toTopObjMk (X := nerve C) · w₀)
    (CategoryTheory.Functor.ext (fun _ ↦ rfl)
      fun _ _ _ ↦ ((Category.id_comp _).trans (Category.comp_id _)).symm)

@[simp]
lemma asSmallHomeomorph_vertex (C : Type u) [Category.{v} C] (c : AsSmall.{w} C) :
    asSmallHomeomorph.{w} C (vertex c) = vertex (AsSmall.down.obj c) := by
  rw [vertex_eq, ← SSet.toTopObjMk_eq_toTopPoint (vertexSimplex c) (StdSimplex.single 0),
    asSmallHomeomorph_toTopObjMk, SSet.toTopObjMk_eq_toTopPoint, vertex_eq]
  exact congrArg (SSet.toTopPoint (X := nerve C)) (ComposableArrows.ext₀ rfl)

@[simp]
lemma asSmallHomeomorph_symm_vertex (C : Type u) [Category.{v} C] (c : C) :
    (asSmallHomeomorph.{w} C).symm (vertex c) = vertex (AsSmall.up.obj c) :=
  (asSmallHomeomorph.{w} C).injective (by simp)

end classifyingSpace

namespace Functor

/-- A functor `F : C ⥤ D` across arbitrary universes induces a continuous map
`C(classifyingSpace C, classifyingSpace D)` via `AsSmall` and `asSmallHomeomorph`. -/
noncomputable def toClassifyingSpaceContinuousMap
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) :
    C(classifyingSpace C, classifyingSpace D) :=
  ((classifyingSpace.asSmallHomeomorph.{max u₁ v₁} D : C(_, _)).comp
    (classifyingSpaceMap (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up (C := D) :
      AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D)).hom).comp
    ((classifyingSpace.asSmallHomeomorph.{max u₂ v₂} C).symm : C(_, _))

@[simp]
lemma toClassifyingSpaceContinuousMap_toTopObjMk
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    F.toClassifyingSpaceContinuousMap (SSet.toTopObjMk (X := nerve C) σ w) =
      SSet.toTopObjMk (X := nerve D) (F.mapNerveObj σ) w := by
  simp only [toClassifyingSpaceContinuousMap, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass,
    classifyingSpace.asSmallHomeomorph_symm_toTopObjMk, classifyingSpaceMap]
  refine ((congrArg (classifyingSpace.asSmallHomeomorph.{max u₁ v₁} D)
    (SSet.toTop_map_toTopObjMk (nerveMap (AsSmall.down ⋙ F ⋙ AsSmall.up)) _ w)).trans
    (classifyingSpace.asSmallHomeomorph_toTopObjMk D _ w)).trans
    (congrArg (SSet.toTopObjMk (X := nerve D) · w)
      (CategoryTheory.Functor.ext (fun _ ↦ rfl)
        fun _ _ _ ↦ ((Category.id_comp _).trans (Category.comp_id _)).symm))

@[simp]
lemma toClassifyingSpaceContinuousMap_vertex
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (c : C) :
    F.toClassifyingSpaceContinuousMap (classifyingSpace.vertex c) =
      classifyingSpace.vertex (F.obj c) := by simp [toClassifyingSpaceContinuousMap]

lemma toClassifyingSpaceContinuousMap_edgePath_apply
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {x y : C} (f : x ⟶ y) (t : unitInterval) :
    F.toClassifyingSpaceContinuousMap (classifyingSpace.edgePath f t) =
      classifyingSpace.edgePath (F.map f) t := by
  rw [classifyingSpace.edgePath_apply, toClassifyingSpaceContinuousMap_toTopObjMk,
    classifyingSpace.edgePath_apply]
  exact congrArg (SSet.toTopObjMk (X := nerve D) · _) (F.mapNerveObj_edgeMk f)

@[simp]
lemma toClassifyingSpaceContinuousMap_id (C : Type u₁) [Category.{v₁} C] :
    (𝟭 C).toClassifyingSpaceContinuousMap = ContinuousMap.id (classifyingSpace C) := by
  ext z; obtain ⟨n, σ, w, rfl⟩ := SSet.exists_toTopObjMk (X := nerve C) z
  rw [toClassifyingSpaceContinuousMap_toTopObjMk, id_mapNerveObj, ContinuousMap.id_apply]

@[simp]
lemma toClassifyingSpaceContinuousMap_comp {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).toClassifyingSpaceContinuousMap =
      G.toClassifyingSpaceContinuousMap.comp F.toClassifyingSpaceContinuousMap := by
  ext z; obtain ⟨n, σ, w, rfl⟩ := SSet.exists_toTopObjMk (X := nerve C) z
  simp only [ContinuousMap.comp_apply, toClassifyingSpaceContinuousMap_toTopObjMk, comp_mapNerveObj]

/-- When `C` and `D` share the same universes, `F.toClassifyingSpaceContinuousMap` agrees with
`(classifyingSpaceMap F).hom`. -/
lemma toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap
    {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    F.toClassifyingSpaceContinuousMap = (classifyingSpaceMap F).hom := by
  ext z; obtain ⟨n, σ, w, rfl⟩ := SSet.exists_toTopObjMk (X := nerve C) z
  exact (toClassifyingSpaceContinuousMap_toTopObjMk F σ w).trans
    (SSet.toTop_map_toTopObjMk (nerveMap F) σ w).symm

end Functor

namespace classifyingSpace

/-- Naturality of `toFundamentalGroupoid` with respect to functors across arbitrary universes. -/
theorem toFundamentalGroupoid_comp_map
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) :
    toFundamentalGroupoid C ⋙ FundamentalGroupoid.map F.toClassifyingSpaceContinuousMap =
      F ⋙ toFundamentalGroupoid D := by
  let g := F.toClassifyingSpaceContinuousMap
  have hmap {x₀ x₁ : classifyingSpace C} {y₀ y₁ : classifyingSpace D}
      (p : _root_.Path x₀ x₁) (q : _root_.Path y₀ y₁)
      (hx : g x₀ = y₀) (hy : g x₁ = y₁) (hpq : ∀ t, g (p t) = q t) :
      (FundamentalGroupoid.map g).map
          (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p)) =
        eqToHom (congrArg FundamentalGroupoid.mk hx) ≫
          FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk q) ≫
          eqToHom (congrArg FundamentalGroupoid.mk hy).symm := by
    subst hx hy; simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact congrArg (FundamentalGroupoid.fromPath ∘ Path.Homotopic.Quotient.mk)
      (_root_.Path.ext (funext hpq))
  exact CategoryTheory.Functor.ext
    (fun c ↦ congrArg FundamentalGroupoid.mk (F.toClassifyingSpaceContinuousMap_vertex c))
    fun _ _ f ↦ hmap (edgePath f) (edgePath (F.map f))
      (F.toClassifyingSpaceContinuousMap_vertex _) (F.toClassifyingSpaceContinuousMap_vertex _)
      (F.toClassifyingSpaceContinuousMap_edgePath_apply f)

instance (C : Type u) [Category.{v} C] [IsEmpty C] : IsEmpty (classifyingSpace C) :=
  (SSet.isEmpty_toTop_iff (nerve C)).2 (nerveEquiv (C := C)).isEmpty

@[simp]
theorem isEmpty_iff (C : Type u) [Category.{v} C] : IsEmpty (classifyingSpace C) ↔ IsEmpty C :=
  (SSet.isEmpty_toTop_iff (nerve C)).trans nerveEquiv.isEmpty_congr

/-- If `C` has a unique object with trivial endomorphism monoid, `classifyingSpace C` has a unique
point, namely `vertex default`. -/
@[instance_reducible]
noncomputable def uniqueOfUnique (C : Type u) [Category.{v} C] [Unique C]
    [Subsingleton (End (default : C))] : Unique (classifyingSpace C) where
  default := vertex default
  uniq z := by
    obtain ⟨n, σ, w, rfl⟩ := SSet.exists_toTopObjMk (X := nerve C) z
    have hσ : σ = (nerve C).map (⦋n⦌.const ⦋0⦌ 0).op (vertexSimplex default) := by
      refine CategoryTheory.Functor.ext (fun i ↦ Unique.eq_default (σ.obj i)) fun _ _ g ↦ ?_
      have hmap {a b : C} (u : a ⟶ b) (ha : a = default) (hb : b = default) :
          u = eqToHom ha ≫ 𝟙 (default : C) ≫ eqToHom hb.symm := by
        subst ha hb; simp only [eqToHom_refl, Category.comp_id]
        exact (End.homEquiv (X := (default : C))).symm.injective (Subsingleton.elim _ _)
      exact hmap (σ.map g) (Unique.eq_default _) (Unique.eq_default _)
    rw [hσ, SSet.toTopObjMk_map, SSet.toTopObjMk_eq_toTopPoint]; rfl

@[simp]
lemma uniqueOfUnique_default (C : Type u) [Category.{v} C] [Unique C]
    [Subsingleton (End (default : C))] :
    (uniqueOfUnique C).default = vertex default := (rfl)

/-- `classifyingSpace (Discrete ι)` is homeomorphic to `TopCat.discrete.obj ι`. -/
noncomputable def discreteHomeomorph (ι : Type u) :
    classifyingSpace (Discrete ι) ≃ₜ TopCat.discrete.obj ι :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.discreteIso ι) ≪≫ SSet.constCompToTopIso.app ι)

@[simp]
lemma discreteHomeomorph_vertex (ι : Type u) (i : Discrete ι) :
    discreteHomeomorph ι (vertex i) = (show TopCat.discrete.obj ι from i.as) := by
  simp only [discreteHomeomorph, TopCat.homeoOfIso_apply, Iso.trans_hom, Functor.mapIso_hom,
    ConcreteCategory.comp_apply, vertex_eq]
  change (SSet.constCompToTopIso.hom.app ι)
    (SSet.toTop.map (nerve.discreteIso ι).hom (SSet.toTopPoint (vertexSimplex i))) = _
  have hd : (nerve.discreteIso ι).hom.app (op ⦋0⦌) (vertexSimplex i) = i.as :=
    nerve.discreteIso_hom_app_nerveEquiv_symm ι i
  rw [SSet.toTop_map_toTopPoint, hd, SSet.constCompToTopIso_hom_app_toTopPoint]

@[simp]
lemma discreteHomeomorph_symm_apply (ι : Type u) (i : TopCat.discrete.obj ι) :
    (discreteHomeomorph ι).symm i = vertex ⟨i⟩ :=
  (discreteHomeomorph ι).injective (by simp)

/-- The two vertices of `classifyingSpace (Discrete Bool)` are distinct. -/
lemma vertex_mk_true_ne_vertex_mk_false : vertex (⟨true⟩ : Discrete Bool) ≠ vertex ⟨false⟩ :=
  fun h ↦ Bool.noConfusion (Discrete.ext_iff.1 (vertex_injective h))

/-- Isomorphism `nerve (Fin (n + 1)) ≅ Δ[n]` in `SSet.{0}`. -/
def nerveFinSuccIsoStdSimplex (n : ℕ) : nerve (Fin (n + 1)) ≅ (Δ[n] : SSet.{0}) :=
  ⟨nerveMap ULift.upFunctor, nerveMap ULift.downFunctor,
    by rw [← nerveMap_comp]; exact nerveMap_id _,
    by rw [← nerveMap_comp]; exact nerveMap_id _⟩ ≪≫ (SSet.stdSimplex.isoNerve.{0} n).symm

/-- `classifyingSpace (Fin (n + 1))` is homeomorphic to `StdSimplex ℝ (Fin (n + 1))`. -/
noncomputable def finSuccHomeomorphStdSimplex (n : ℕ) :
    classifyingSpace (Fin (n + 1)) ≃ₜ StdSimplex ℝ (Fin (n + 1)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (nerveFinSuccIsoStdSimplex n))).trans ⦋n⦌.toTopHomeo

@[simp]
lemma finSuccHomeomorphStdSimplex_vertex (n : ℕ) (i : Fin (n + 1)) :
    finSuccHomeomorphStdSimplex n (vertex i) = StdSimplex.single i := by
  simp only [finSuccHomeomorphStdSimplex, Homeomorph.trans_apply, TopCat.homeoOfIso_apply,
    Functor.mapIso_hom, vertex_eq, SSet.toTop_map_toTopPoint]
  have hv : (nerveFinSuccIsoStdSimplex n).hom.app (op ⦋0⦌) (vertexSimplex i) =
      Δ[n].map (⦋0⦌.const ⦋n⦌ i).op (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) := by
    ext k : 3; fin_cases k; rfl
  rw [hv, ← SSet.toTopObjMk_eq_toTopPoint _ (StdSimplex.single 0), SSet.toTopObjMk_map,
    ← SSet.toTop_map_yonedaEquiv_symm_toTopHomeo_symm,
    show SSet.yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌) : (Δ[n] : SSet.{0}) _⦋n⦌) =
      𝟙 Δ[n] from SSet.yonedaEquiv.injective (by simp),
    CategoryTheory.Functor.map_id, CategoryTheory.id_apply, Homeomorph.apply_symm_apply,
    StdSimplex.map_single]; rfl

/-- The classifying space of `Fin 2` is homeomorphic to `unitInterval`. -/
noncomputable def finTwoHomeomorphI : classifyingSpace (Fin 2) ≃ₜ unitInterval :=
  (finSuccHomeomorphStdSimplex 1).trans StdSimplex.homeomorphI

@[simp]
lemma finTwoHomeomorphI_vertex_zero : finTwoHomeomorphI (vertex (0 : Fin 2)) = 0 := by
  rw [finTwoHomeomorphI, Homeomorph.trans_apply, finSuccHomeomorphStdSimplex_vertex]; ext; simp

@[simp]
lemma finTwoHomeomorphI_vertex_one : finTwoHomeomorphI (vertex (1 : Fin 2)) = 1 := by
  rw [finTwoHomeomorphI, Homeomorph.trans_apply, finSuccHomeomorphStdSimplex_vertex]; ext; simp

/-- On `Fin 2`, `classifyingSpaceMap (𝟭 (Fin 2))` differs from either constant map. -/
lemma classifyingSpaceMap_id_ne_const_fin_two (b : Fin 2) :
    classifyingSpaceMap (𝟭 (Fin 2)) ≠ classifyingSpaceMap ((Functor.const (Fin 2)).obj b) := by
  intro h
  have hb := vertex_injective <| by simpa using ConcreteCategory.congr_hom h (vertex (1 - b))
  fin_cases b <;> exact absurd hb (by decide)

/-- Composing the endpoint inclusion `Discrete PUnit ⥤ Fin 2` at `b` with `Fin 2 ⥤ Discrete PUnit`
realizes to `𝟙 _` in one order and to the constant map at `vertex b` in the other. -/
lemma classifyingSpaceMap_fin_two_endpoint_retraction (b : Fin 2) :
    classifyingSpaceMap (((Functor.const (Discrete PUnit.{1})).obj b) ⋙
        ((Functor.const (Fin 2)).obj ⟨PUnit.unit⟩)) =
      𝟙 (classifyingSpace (Discrete PUnit.{1})) ∧
    classifyingSpaceMap (((Functor.const (Fin 2)).obj ⟨PUnit.unit⟩) ⋙
        ((Functor.const (Discrete PUnit.{1})).obj b)) =
      classifyingSpaceMap ((Functor.const (Fin 2)).obj b) :=
  ⟨by rw [show _ ⋙ _ = 𝟭 _ from CategoryTheory.Functor.ext (fun ⟨⟨⟩⟩ ↦ rfl)
        fun ⟨⟨⟩⟩ ⟨⟨⟩⟩ _ ↦ Subsingleton.elim _ _, classifyingSpaceMap_id], rfl⟩

/-- Reflection of `classifyingSpace (Fin 2)` via `t ↦ 1 - t` swaps `vertex 0` and `vertex 1`, hence
lies outside the range of `classifyingSpaceMap`. -/
theorem exists_hom_fin_two_notMem_range_classifyingSpaceMap :
    ∃ f : classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2),
      f ∉ Set.range (classifyingSpaceMap (C := Fin 2) (D := Fin 2)) := by
  let symmI : C(unitInterval, unitInterval) := ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  let f : classifyingSpace (Fin 2) ⟶ classifyingSpace (Fin 2) := TopCat.ofHom
    ((finTwoHomeomorphI.symm : C(unitInterval, classifyingSpace (Fin 2))).comp
      (symmI.comp (finTwoHomeomorphI : C(classifyingSpace (Fin 2), unitInterval))))
  refine ⟨f, fun ⟨F, hF⟩ ↦ ?_⟩
  have hf (b : Fin 2) : F.obj b = 1 - b := vertex_injective <| by
    rw [← classifyingSpaceMap_vertex, hF]
    change finTwoHomeomorphI.symm (symmI (finTwoHomeomorphI (vertex b))) = _
    revert b; refine Fin.forall_fin_two.2 ⟨?_, ?_⟩ <;> apply finTwoHomeomorphI.injective <;>
      simp [symmI]
  have hle := leOfHom (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)))
  rw [hf 0, hf 1] at hle; exact absurd hle (by decide)

end classifyingSpace

/-- The classifying space functor `Cat.{0, 0} ⥤ TopCat.{0}` is not full. -/
theorem not_full_classifyingSpaceFunctor : ¬ Nonempty classifyingSpaceFunctor.{0, 0}.Full := by
  rintro ⟨hfull⟩
  obtain ⟨f, hf⟩ := classifyingSpace.exists_hom_fin_two_notMem_range_classifyingSpaceMap
  obtain ⟨F, hF⟩ := hfull.map_surjective (X := Cat.of (Fin 2)) (Y := Cat.of (Fin 2)) f
  exact hf ⟨F.toFunctor, hF⟩

/-! ### Opposite categories -/

namespace classifyingSpace

section Opposite

variable (C : Type u) [Category.{v} C]

/-- Isomorphism `classifyingSpace Cᵒᵖ ≅ classifyingSpace C` from `nerve.opIso` and `toTopOpIso`. -/
noncomputable def opIso : classifyingSpace Cᵒᵖ ≅ classifyingSpace C :=
  SSet.toTop.mapIso (nerve.opIso C) ≪≫ SSet.toTopOpIso.app (nerve C)

/-- Homeomorphism `classifyingSpace Cᵒᵖ ≃ₜ classifyingSpace C` reversing barycentric coordinates. -/
noncomputable def opHomeomorph : classifyingSpace Cᵒᵖ ≃ₜ classifyingSpace C :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (nerve.opIso C))).trans (nerve C).toTopOpHomeomorph

@[simp]
lemma opHomeomorph_vertex (x : Cᵒᵖ) : opHomeomorph C (vertex x) = vertex x.unop := by
  simp only [opHomeomorph, Homeomorph.trans_apply, TopCat.homeoOfIso_apply, Functor.mapIso_hom,
    vertex_eq, SSet.toTop_map_toTopPoint]
  rw [show (nerve.opIso C).hom.app (op ⦋0⦌) (vertexSimplex x) =
      (SSet.opObjEquiv (X := nerve C) (n := op ⦋0⦌)).symm (vertexSimplex x.unop) from
      nerve.opIso_hom_app_nerveEquiv_symm C x,
    SSet.toTopOpHomeomorph_toTopPoint, Equiv.apply_symm_apply]

@[simp]
lemma opHomeomorph_symm_vertex (x : C) : (opHomeomorph C).symm (vertex x) = vertex (op x) :=
  (opHomeomorph C).injective (by simp)

/-- Under `opHomeomorph C`, `edgePath f.op` traces `(edgePath f).symm`. -/
lemma opHomeomorph_edgePath_apply {x y : C} (f : x ⟶ y) (t : unitInterval) :
    opHomeomorph C (edgePath f.op t) = (edgePath f).symm t := by
  let ef : (nerve C).Edge (vertexSimplex x) (vertexSimplex y) := nerve.edgeMk f
  let eop : (nerve Cᵒᵖ) _⦋1⦌ := (nerve.edgeMk f.op).edge
  have hedge : (nerve.opIso C).hom.app (op ⦋1⦌) eop = (SSet.Edge.opEquiv ef).edge :=
    (nerve C).opObjEquiv.injective <| (congrArg (nerve C).opObjEquiv (SSet.Edge.opEquiv_edge ef)
      |>.trans (Equiv.apply_symm_apply _ _)).symm ▸
      ComposableArrows.ext₁ (nerve.opIso_hom_app_obj C eop 0)
        (nerve.opIso_hom_app_obj C eop 1) (nerve.opIso_hom_app_map C eop (by decide))
  rw [edgePath_apply, show (nerve.edgeMk f.op).edge = eop from rfl]
  simp only [opHomeomorph, Homeomorph.trans_apply, TopCat.homeoOfIso_apply, Functor.mapIso_hom,
    SSet.toTop_map_toTopObjMk, hedge]
  rw [← SSet.Edge.toTopPath_apply, SSet.toTopOpHomeomorph_opEquiv_toTopPath_apply]; rfl

end Opposite

end classifyingSpace

/-! ### Homotopies from natural transformations and zigzags -/

namespace NatTrans

/-- A natural transformation `η : F₀ ⟶ F₁` between functors in the same universes induces a homotopy
from `(classifyingSpaceMap F₀).hom` to `(classifyingSpaceMap F₁).hom`. -/
noncomputable def classifyingSpaceHomotopy {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    ContinuousMap.Homotopy (classifyingSpaceMap F₀).hom (classifyingSpaceMap F₁).hom :=
  η.nerveHomotopy.toTop

/-- Over `classifyingSpace.vertex c`, `η.classifyingSpaceHomotopy` traces `edgePath (η.app c)`. -/
@[simp]
lemma classifyingSpaceHomotopy_vertex {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (t : unitInterval) (c : C) :
    η.classifyingSpaceHomotopy (t, classifyingSpace.vertex c) =
      classifyingSpace.edgePath (η.app c) t := by
  rw [classifyingSpaceHomotopy, classifyingSpace.vertex_eq,
    ← SSet.toTopObjMk_eq_toTopPoint (classifyingSpace.vertexSimplex c) (StdSimplex.single 0),
    SSet.Homotopy.toTop_toTopObjMk_zero, classifyingSpace.edgePath_apply]
  exact congrArg (SSet.toTopObjMk (X := nerve D) · _) (η.nerveHomotopy_h_verticalEdge c)

/-- A natural transformation `η : F₀ ⟶ F₁` across arbitrary universes induces a homotopy from
`F₀.toClassifyingSpaceContinuousMap` to `F₁.toClassifyingSpaceContinuousMap`. -/
noncomputable def toClassifyingSpaceHomotopy {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    ContinuousMap.Homotopy F₀.toClassifyingSpaceContinuousMap
      F₁.toClassifyingSpaceContinuousMap where
  toFun p := classifyingSpace.asSmallHomeomorph.{max u₁ v₁} D
    ((Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₂ v₂} C ⥤ C)
      (Functor.whiskerRight η (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁} D))).classifyingSpaceHomotopy
      (p.1, (classifyingSpace.asSmallHomeomorph.{max u₂ v₂} C).symm p.2))
  continuous_toFun := by fun_prop
  map_zero_left _ := by simp [Functor.toClassifyingSpaceContinuousMap]
  map_one_left _ := by simp [Functor.toClassifyingSpaceContinuousMap]

@[simp]
lemma toClassifyingSpaceHomotopy_vertex {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (t : unitInterval) (c : C) :
    η.toClassifyingSpaceHomotopy (t, classifyingSpace.vertex c) =
      classifyingSpace.edgePath (η.app c) t := by
  change classifyingSpace.asSmallHomeomorph.{max u₁ v₁} D
    ((Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₂ v₂} C ⥤ C)
      (Functor.whiskerRight η (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁} D))).classifyingSpaceHomotopy
      (t, (classifyingSpace.asSmallHomeomorph.{max u₂ v₂} C).symm (classifyingSpace.vertex c))) = _
  rw [classifyingSpace.asSmallHomeomorph_symm_vertex, classifyingSpaceHomotopy_vertex,
    classifyingSpace.edgePath_apply, classifyingSpace.asSmallHomeomorph_toTopObjMk,
    classifyingSpace.edgePath_apply]
  exact congrArg (SSet.toTopObjMk (X := nerve D) · _) (AsSmall.down.mapNerveObj_edgeMk _)

end NatTrans

namespace Zigzag

/-- A zigzag of natural transformations across arbitrary universes induces a homotopy between the
induced maps on classifying spaces. -/
theorem homotopic_toClassifyingSpaceContinuousMap {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F₀ F₁ : C ⥤ D} (h : Zigzag F₀ F₁) :
    F₀.toClassifyingSpaceContinuousMap.Homotopic F₁.toClassifyingSpaceContinuousMap := by
  induction h with
  | refl => exact ContinuousMap.Homotopic.refl _
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

/-! ### Adjunctions, equivalences, skeletons, and small models -/

namespace Adjunction

/-- An adjunction `L ⊣ R` between categories in the same universes induces a homotopy equivalence
`classifyingSpace C ≃ₕ classifyingSpace D`. -/
noncomputable def classifyingSpaceHomotopyEquiv {C D : Type u} [Category.{v} C] [Category.{v} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    ContinuousMap.HomotopyEquiv (classifyingSpace C) (classifyingSpace D) where
  toFun := (classifyingSpaceMap L).hom
  invFun := (classifyingSpaceMap R).hom
  left_inv := by
    have hu := adj.unit.classifyingSpaceHomotopy.symm
    rw [classifyingSpaceMap_comp, classifyingSpaceMap_id] at hu; exact ⟨hu⟩
  right_inv := by
    have hc := adj.counit.classifyingSpaceHomotopy
    rw [classifyingSpaceMap_comp, classifyingSpaceMap_id] at hc; exact ⟨hc⟩

@[simp]
lemma classifyingSpaceHomotopyEquiv_toFun {C D : Type u} [Category.{v} C] [Category.{v} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    adj.classifyingSpaceHomotopyEquiv.toFun = (classifyingSpaceMap L).hom := (rfl)

@[simp]
lemma classifyingSpaceHomotopyEquiv_invFun {C D : Type u} [Category.{v} C] [Category.{v} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    adj.classifyingSpaceHomotopyEquiv.invFun = (classifyingSpaceMap R).hom := (rfl)

/-- An adjunction `L ⊣ R` across arbitrary universes induces a homotopy equivalence
`classifyingSpace C ≃ₕ classifyingSpace D`. -/
noncomputable def toClassifyingSpaceHomotopyEquiv {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    ContinuousMap.HomotopyEquiv (classifyingSpace C) (classifyingSpace D) where
  toFun := L.toClassifyingSpaceContinuousMap
  invFun := R.toClassifyingSpaceContinuousMap
  left_inv := by
    have hu := adj.unit.toClassifyingSpaceHomotopy.symm
    rw [Functor.toClassifyingSpaceContinuousMap_comp,
      Functor.toClassifyingSpaceContinuousMap_id] at hu; exact ⟨hu⟩
  right_inv := by
    have hc := adj.counit.toClassifyingSpaceHomotopy
    rw [Functor.toClassifyingSpaceContinuousMap_comp,
      Functor.toClassifyingSpaceContinuousMap_id] at hc; exact ⟨hc⟩

@[simp]
lemma toClassifyingSpaceHomotopyEquiv_toFun {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    adj.toClassifyingSpaceHomotopyEquiv.toFun = L.toClassifyingSpaceContinuousMap := (rfl)

@[simp]
lemma toClassifyingSpaceHomotopyEquiv_invFun {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    adj.toClassifyingSpaceHomotopyEquiv.invFun = R.toClassifyingSpaceContinuousMap := (rfl)

end Adjunction

namespace Equivalence

/-- An equivalence of categories `C ≌ D` across arbitrary universes induces a homotopy equivalence
`classifyingSpace C ≃ₕ classifyingSpace D`. -/
noncomputable def classifyingSpaceHomotopyEquiv
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (e : C ≌ D) :
    ContinuousMap.HomotopyEquiv (classifyingSpace C) (classifyingSpace D) :=
  e.toAdjunction.toClassifyingSpaceHomotopyEquiv

@[simp]
lemma classifyingSpaceHomotopyEquiv_toFun
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (e : C ≌ D) :
    e.classifyingSpaceHomotopyEquiv.toFun = e.functor.toClassifyingSpaceContinuousMap := (rfl)

@[simp]
lemma classifyingSpaceHomotopyEquiv_invFun
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (e : C ≌ D) :
    e.classifyingSpaceHomotopyEquiv.invFun = e.inverse.toClassifyingSpaceContinuousMap := (rfl)

end Equivalence

namespace classifyingSpace

/-- Passing to a skeleton `Skeleton C` preserves the homotopy type of `classifyingSpace C`. -/
noncomputable def skeletonHomotopyEquiv (C : Type u) [Category.{v} C] :
    ContinuousMap.HomotopyEquiv (classifyingSpace (Skeleton C)) (classifyingSpace C) :=
  (skeletonEquivalence C).classifyingSpaceHomotopyEquiv

/-- An essentially `w`-small category `C` has classifying space homotopy equivalent to that of its
small model `SmallModel.{w} C`. -/
noncomputable def smallModelHomotopyEquiv (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] :
    ContinuousMap.HomotopyEquiv (classifyingSpace (SmallModel.{w} C)) (classifyingSpace C) :=
  (equivSmallModel.{w} C).symm.classifyingSpaceHomotopyEquiv

end classifyingSpace

/-! ### Contractibility from initial and terminal objects -/

namespace Limits

private lemma contractibleSpace_of_topHomotopy {C : Type u} [Category.{v} C] (x : C)
    (H : ContinuousMap.Homotopy (SSet.toTop.map (𝟙 (nerve C))).hom
      (SSet.toTop.map (SSet.const (classifyingSpace.vertexSimplex x))).hom) :
    ContractibleSpace (classifyingSpace C) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨classifyingSpace.vertex x, ?_⟩
  have h := H
  have hconst : (SSet.toTop.map (SSet.const (classifyingSpace.vertexSimplex x) :
      nerve C ⟶ nerve C)).hom =
      ContinuousMap.const (classifyingSpace C) (classifyingSpace.vertex x) :=
    ContinuousMap.ext (SSet.toTop_map_const _)
  have hid : (SSet.toTop.map (𝟙 (nerve C))).hom = ContinuousMap.id (classifyingSpace C) := by
    rw [CategoryTheory.Functor.map_id]; rfl
  rw [hconst, hid] at h; exact ⟨h⟩

/-- If `C` has a chosen initial object `x`, `classifyingSpace C` is contractible. -/
theorem IsInitial.contractibleSpace_classifyingSpace {C : Type u} [Category.{v} C] {x : C}
    (hx : IsInitial x) : ContractibleSpace (classifyingSpace C) :=
  contractibleSpace_of_topHomotopy x hx.nerveHomotopy.toTop.symm

/-- If `C` has a chosen terminal object `x`, `classifyingSpace C` is contractible. -/
theorem IsTerminal.contractibleSpace_classifyingSpace {C : Type u} [Category.{v} C] {x : C}
    (hx : IsTerminal x) : ContractibleSpace (classifyingSpace C) :=
  contractibleSpace_of_topHomotopy x hx.nerveHomotopy.toTop

instance instContractibleSpaceClassifyingSpaceOfHasInitial (C : Type u) [Category.{v} C]
    [HasInitial C] : ContractibleSpace (classifyingSpace C) :=
  initialIsInitial.contractibleSpace_classifyingSpace

instance instContractibleSpaceClassifyingSpaceOfHasTerminal (C : Type u) [Category.{v} C]
    [HasTerminal C] : ContractibleSpace (classifyingSpace C) :=
  terminalIsTerminal.contractibleSpace_classifyingSpace

end Limits

namespace classifyingSpace

instance (n : ℕ) : ContractibleSpace (classifyingSpace (Fin (n + 1))) :=
  (Limits.IsInitial.ofUniqueHom (fun y : Fin (n + 1) ↦ homOfLE (Fin.zero_le y))
    (fun _ _ ↦ Subsingleton.elim _ _)).contractibleSpace_classifyingSpace

/-- The classifying space of an empty category is not contractible. -/
theorem not_contractibleSpace_of_isEmpty (C : Type u) [Category.{v} C] [IsEmpty C] :
    ¬ ContractibleSpace (classifyingSpace C) := fun _ ↦
  let ⟨e⟩ := ContractibleSpace.hequiv_unit (classifyingSpace C)
  IsEmpty.false (e.invFun ())

/-! ### Path components and categorical connected components -/

/-- The path components `ZerothHomotopy (classifyingSpace C)` correspond canonically to
`ConnectedComponents C`. -/
noncomputable def zerothHomotopyEquivConnectedComponents (C : Type u) [Category.{v} C] :
    ZerothHomotopy (classifyingSpace C) ≃ ConnectedComponents C :=
  (SSet.π₀EquivZerothHomotopy (nerve C)).symm.trans (nerve.π₀EquivConnectedComponents C)

@[simp]
lemma zerothHomotopyEquivConnectedComponents_mk_vertex (C : Type u) [Category.{v} C] (c : C) :
    zerothHomotopyEquivConnectedComponents C (ZerothHomotopy.mk (vertex c)) =
      ConnectedComponents.mk c := by
  rw [zerothHomotopyEquivConnectedComponents, Equiv.trans_apply,
    show ((nerve C).π₀EquivZerothHomotopy).symm (ZerothHomotopy.mk (vertex c)) =
      SSet.π₀.mk (vertexSimplex c) from
      (nerve C).π₀EquivZerothHomotopy.injective
        (by rw [Equiv.apply_symm_apply, SSet.π₀EquivZerothHomotopy_mk, vertex_eq])]
  exact nerve.π₀EquivConnectedComponents_mk_nerveEquiv_symm C c

@[simp]
lemma zerothHomotopyEquivConnectedComponents_symm_mk (C : Type u) [Category.{v} C] (c : C) :
    (zerothHomotopyEquivConnectedComponents C).symm (ConnectedComponents.mk c) =
      ZerothHomotopy.mk (vertex c) :=
  (zerothHomotopyEquivConnectedComponents C).injective (by simp)

/-- Naturality of `zerothHomotopyEquivConnectedComponents` across arbitrary universes. -/
@[simp]
lemma zerothHomotopyEquivConnectedComponents_mk_toClassifyingSpaceContinuousMap
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (z : classifyingSpace C) :
    zerothHomotopyEquivConnectedComponents D
        (ZerothHomotopy.mk (F.toClassifyingSpaceContinuousMap z)) =
      F.mapConnectedComponents
        (zerothHomotopyEquivConnectedComponents C (ZerothHomotopy.mk z)) := by
  obtain ⟨c, hc⟩ := exists_joined_vertex z
  rw [(ZerothHomotopy.sound hc.somePath).symm,
    (ZerothHomotopy.sound (hc.somePath.map F.toClassifyingSpaceContinuousMap.continuous)).symm,
    F.toClassifyingSpaceContinuousMap_vertex, zerothHomotopyEquivConnectedComponents_mk_vertex,
    zerothHomotopyEquivConnectedComponents_mk_vertex, Functor.mapConnectedComponents_mk]

@[simp]
lemma zerothHomotopyEquivConnectedComponents_mk_classifyingSpaceMap
    {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) (z : classifyingSpace C) :
    zerothHomotopyEquivConnectedComponents D (ZerothHomotopy.mk (classifyingSpaceMap F z)) =
      F.mapConnectedComponents
        (zerothHomotopyEquivConnectedComponents C (ZerothHomotopy.mk z)) := by
  rw [show classifyingSpaceMap F z = F.toClassifyingSpaceContinuousMap z from
    (congrFun (congrArg DFunLike.coe F.toClassifyingSpaceContinuousMap_eq_classifyingSpaceMap)
      z).symm,
    zerothHomotopyEquivConnectedComponents_mk_toClassifyingSpaceContinuousMap]

/-- `classifyingSpace C` is path-connected if and only if `C` is a connected category. -/
theorem pathConnectedSpace_iff (C : Type u) [Category.{v} C] :
    PathConnectedSpace (classifyingSpace C) ↔ CategoryTheory.IsConnected C := by
  rw [pathConnectedSpace_iff_zerothHomotopy, and_comm, ← unique_iff_subsingleton_and_nonempty,
    ← nonempty_unique_connectedComponents_iff]
  exact ⟨fun ⟨h⟩ ↦ ⟨by haveI := h; exact (zerothHomotopyEquivConnectedComponents C).symm.unique⟩,
    fun ⟨h⟩ ↦ ⟨by haveI := h; exact (zerothHomotopyEquivConnectedComponents C).unique⟩⟩

/-- In `Limits.WalkingCospan`, there is no morphism in either direction between `WalkingCospan.left`
and `WalkingCospan.right`, yet their vertices in `classifyingSpace Limits.WalkingCospan` are joined
by a path through `WalkingCospan.one`. -/
lemma walkingCospan_isEmpty_hom_and_joined_vertices :
    IsEmpty (Limits.WalkingCospan.left ⟶ Limits.WalkingCospan.right) ∧
    IsEmpty (Limits.WalkingCospan.right ⟶ Limits.WalkingCospan.left) ∧
    Joined (vertex Limits.WalkingCospan.left) (vertex Limits.WalkingCospan.right) :=
  ⟨⟨nofun⟩, ⟨nofun⟩,
    ⟨(edgePath Limits.WalkingCospan.Hom.inl).trans (edgePath Limits.WalkingCospan.Hom.inr).symm⟩⟩

end classifyingSpace

end CategoryTheory
