/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Edge

/-!
# The classifying space of a small category

The classifying space `BC` of a category `C` is the geometric realization of its nerve,
`TauCeti.CategoryTheory.classifyingSpace C = |nerve C|`, and a functor `F : C ⥤ D` induces the
realization `BF = |nerveMap F|` (`CategoryTheory.Functor.classifyingSpaceMap`). Both are
abbreviations, so that the API of geometric realizations of simplicial sets applies to them
directly; together they form the functor `nerveFunctor ⋙ SSet.toTop`
(`TauCeti.CategoryTheory.classifyingSpaceFunctor`). If the objects of `C` live in `Type u` and its
morphisms in `Type v`, then `BC` lives in `TopCat.{max u v}`; categories in other universes are
compared after an explicit `ULift` or `AsSmall`.

An object `X` gives a vertex `[X]` of `BC` (`TauCeti.CategoryTheory.classifyingSpace.vertex`), and
an arrow `f : X ⟶ Y` an edge path from `[X]` to `[Y]`
(`TauCeti.CategoryTheory.classifyingSpace.edge`), the path traced by the `1`-simplex `f` of the
nerve. These satisfy:

* `edge (𝟙 X)` is the constant path (`TauCeti.CategoryTheory.classifyingSpace.edge_id`);
* `edge f` followed by `edge g` is homotopic rel endpoints to `edge (f ≫ g)`, through the realized
  `2`-simplex `(f, g)` of the nerve
  (`TauCeti.CategoryTheory.classifyingSpace.edge_trans_homotopic`);
* `BF [X] = [F X]`, and `BF` carries `edge f` to `edge (F.map f)`
  (`CategoryTheory.Functor.classifyingSpaceMap_vertex`,
  `TauCeti.CategoryTheory.classifyingSpace.map_edge`).

Hence vertices and edge classes form a functor `C ⥤ πₓ BC` to the fundamental groupoid
(`TauCeti.CategoryTheory.classifyingSpace.toFundamentalGroupoid`). Every point of `BC` is joined by
a path to a vertex (`TauCeti.CategoryTheory.classifyingSpace.exists_joined_vertex`); in particular
the classifying space of an empty category is empty, while that of a category with at most one
object and at most one arrow between any two objects has at most one point.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 89.
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, Characterization 3.1,
  Recipe 3.1.1 and Definition 3.1.4.
-/

public section

open CategoryTheory Simplicial

universe v u

namespace TauCeti.CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The classifying space `BC` of a category `C`: the geometric realization `|nerve C|` of its
nerve. -/
noncomputable abbrev classifyingSpace : TopCat.{max u v} :=
  SSet.toTop.obj (nerve C)

/-- The classifying-space functor `Cat ⥤ TopCat`: the nerve followed by geometric realization. -/
noncomputable abbrev classifyingSpaceFunctor : Cat.{v, u} ⥤ TopCat.{max u v} :=
  nerveFunctor ⋙ SSet.toTop

end TauCeti.CategoryTheory

namespace CategoryTheory.Functor

open TauCeti.CategoryTheory

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/-- The map `BF : BC ⟶ BD` of classifying spaces induced by a functor `F : C ⥤ D`: the geometric
realization of the map of nerves `nerveMap F`. -/
noncomputable abbrev classifyingSpaceMap (F : C ⥤ D) : classifyingSpace C ⟶ classifyingSpace D :=
  SSet.toTop.map (nerveMap F)

/-- The identity functor induces the identity of the classifying space. -/
@[simp]
lemma classifyingSpaceMap_id : (𝟭 C).classifyingSpaceMap = 𝟙 (classifyingSpace C) :=
  -- `nerveMap (𝟭 C)` is the identity of `nerve C` by definition: it composes strings with `𝟭 C`.
  SSet.toTop.map_id (nerve C)

/-- The classifying space of a composite of functors is the composite of their classifying
spaces. -/
@[simp]
lemma classifyingSpaceMap_comp (F : C ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).classifyingSpaceMap = F.classifyingSpaceMap ≫ G.classifyingSpaceMap :=
  -- `nerveMap (F ⋙ G)` is `nerveMap F ≫ nerveMap G` by definition: both compose strings with `F`
  -- and then with `G`.
  SSet.toTop.map_comp (nerveMap F) (nerveMap G)

end CategoryTheory.Functor

namespace TauCeti.CategoryTheory

/-- The classifying-space functor sends a functor to its classifying-space map. -/
lemma classifyingSpaceFunctor_map {C D : Cat.{v, u}} (F : C ⟶ D) :
    classifyingSpaceFunctor.map F = F.toFunctor.classifyingSpaceMap :=
  rfl

namespace classifyingSpace

variable {C : Type u} [Category.{v} C]

/-- The vertex `[X]` of the classifying space given by an object `X`: the point of the
`0`-simplex `X` of the nerve. -/
noncomputable abbrev vertex (X : C) : classifyingSpace C :=
  SSet.toTopPoint (nerveEquiv.symm X)

/-- The edge path from `[X]` to `[Y]` in the classifying space given by an arrow `f : X ⟶ Y`: the
path traced by the `1`-simplex `f` of the nerve. -/
noncomputable def edge {X Y : C} (f : X ⟶ Y) : Path (vertex X) (vertex Y) :=
  (nerve.edgeMk f).toTopPath

/-- The edge path of an arrow is the path traced by the corresponding edge of the nerve. -/
lemma edge_eq_toTopPath {X Y : C} (f : X ⟶ Y) : edge f = (nerve.edgeMk f).toTopPath :=
  (rfl)

/-- The edge path of an identity arrow is the constant path. -/
@[simp]
lemma edge_id (X : C) : edge (𝟙 X) = Path.refl (vertex X) := by
  rw [edge_eq_toTopPath, nerve.edgeMk_id]
  exact SSet.Edge.toTopPath_id _

/-- The edge path of `f` followed by the edge path of `g` is homotopic rel endpoints to the edge
path of `f ≫ g`. -/
theorem edge_trans_homotopic {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((edge f).trans (edge g)).Homotopic (edge (f ≫ g)) :=
  SSet.Edge.CompStruct.toTopPath_trans_homotopic
    ((nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl).some

/-- Every point of the classifying space is joined by a path to the vertex of an object. -/
lemma exists_joined_vertex (p : classifyingSpace C) : ∃ X : C, Joined (vertex X) p := by
  obtain ⟨x, hx⟩ := SSet.exists_joined_toTopPoint p
  exact ⟨nerveEquiv x, (nerveEquiv.symm_apply_apply x).symm ▸ hx⟩

/-- The classifying space of an empty category is empty. -/
instance [IsEmpty C] : IsEmpty (classifyingSpace C) :=
  ⟨fun p ↦ IsEmpty.false (exists_joined_vertex p).choose⟩

/-- The classifying space of a nonempty category is nonempty: its nerve has a vertex. -/
instance [Nonempty C] : Nonempty (classifyingSpace C) :=
  have : Nonempty (nerve C _⦋0⦌) := ⟨nerveEquiv.symm (Classical.arbitrary C)⟩
  SSet.nonempty_toTop

/-- The classifying space of a category with at most one object and at most one arrow between any
two objects, such as the category with one object and one morphism, has at most one point. -/
instance [Subsingleton C] [Quiver.IsThin C] : Subsingleton (classifyingSpace C) :=
  SSet.subsingleton_toTop fun _ ↦ ⟨fun _ _ ↦ nerve.ext_of_isThin (funext fun _ ↦
    Subsingleton.elim _ _)⟩

end classifyingSpace

end TauCeti.CategoryTheory

namespace CategoryTheory.Functor

open TauCeti.CategoryTheory classifyingSpace

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The classifying space of a functor `F` sends the vertex `[X]` to the vertex `[F X]`. -/
@[simp]
lemma classifyingSpaceMap_vertex (F : C ⥤ D) (X : C) :
    F.classifyingSpaceMap (vertex X) = vertex (F.obj X) :=
  (SSet.toTop_map_toTopPoint (nerveMap F) (nerveEquiv.symm X)).trans
    (congrArg SSet.toTopPoint (nerveMap_app_nerveEquiv_symm F X))

end CategoryTheory.Functor

namespace TauCeti.CategoryTheory.classifyingSpace

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The classifying space of a functor `F` carries the edge path of an arrow `f` to the edge path
of `F.map f`, after identifying the images of the endpoints with the vertices of their images
(`CategoryTheory.Functor.classifyingSpaceMap_vertex`). -/
lemma map_edge (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (edge f).map F.classifyingSpaceMap.hom.continuous =
      (edge (F.map f)).cast (F.classifyingSpaceMap_vertex X) (F.classifyingSpaceMap_vertex Y) := by
  ext t
  rw [edge_eq_toTopPath, edge_eq_toTopPath, (nerve.edgeMk f).map_toTopPath (nerveMap F),
    Path.cast_coe, Path.cast_coe]
  apply SSet.Edge.toTopPath_apply_eq_of_edge_eq
  exact nerveMap_app_mk₁ F f

variable (C) in
/-- The functor from a category to the fundamental groupoid of its classifying space, sending an
object to its vertex and an arrow to the homotopy class of its edge path. -/
@[expose, simps]
noncomputable def toFundamentalGroupoid : C ⥤ FundamentalGroupoid (classifyingSpace C) where
  obj X := .mk (vertex X)
  map f := FundamentalGroupoid.fromPath (.mk (edge f))
  map_id X := by
    rw [edge_id]
    exact (FundamentalGroupoid.id_eq_path_refl _).symm
  map_comp f g := by
    rw [FundamentalGroupoid.comp_eq, ← Path.Homotopic.Quotient.mk_trans]
    exact Quotient.sound (edge_trans_homotopic f g).symm

end TauCeti.CategoryTheory.classifyingSpace
