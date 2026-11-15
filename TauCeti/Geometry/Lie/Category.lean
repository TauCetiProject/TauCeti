/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import TauCeti.Algebra.Category.LieAlgCat.Basic
public import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Faithfulness
import TauCeti.Geometry.Lie.Interior

/-!
# The Lie functor as a categorical functor

`TauCeti.LieGroupCat` is the category of finite-dimensional smooth real Lie groups and smooth
homomorphisms. Each object carries its own vector-space model and model with corners, so the
category includes morphisms between groups of different dimensions.

Differentiation gives `TauCeti.LieGroupCat.lieFunctor` into the category of finite-dimensional
real Lie algebras. Its map on morphisms is `lieMap`, the differential at the identity.
It is injective on morphisms
out of preconnected objects. Its restrictions to preconnected and simply connected groups are
faithful.

## Main definitions and results

* `TauCeti.LieGroupCat` and `TauCeti.LieGroupCat.of`: bundled groups and their constructor.
* `TauCeti.LieGroupCat.Hom.hom`, `TauCeti.LieGroupCat.ofHom`: conversions between categorical
  morphisms and smooth homomorphisms, with `hom_id`, `hom_comp`, `hom_ofHom`, `ofHom_hom` and
  `hom_ext`, and `ofHom_id` and `ofHom_comp` for conversion of identities and composites.
* `TauCeti.LieGroupCat.lieAlgebra`: the finite-dimensional Lie algebra of a bundled group.
* `TauCeti.LieGroupCat.isoMk`: construct an isomorphism from inverse smooth homomorphisms,
  with `isoMk_hom_hom` and `isoMk_inv_hom`.
* `TauCeti.LieGroupCat.lieFunctor`: differentiation as a categorical functor.
* `TauCeti.LieGroupCat.lieFunctor_obj`: its finite-dimensional Lie algebra object.
* `TauCeti.LieGroupCat.lieFunctor_map_hom_hom`: its underlying Lie homomorphism.
* `TauCeti.LieGroupCat.lieFunctor_map_injective`: faithfulness on preconnected sources.
* `TauCeti.LieGroupCat.isPreconnected` and `TauCeti.LieGroupCat.preconnectedLieFunctor`: the
  preconnected object property and the faithful restriction of differentiation to it.
* `TauCeti.LieGroupCat.isSimplyConnected`: the simply connected object property, whose full
  subcategory is the source of `simplyConnectedLieFunctor`.
* `TauCeti.LieGroupCat.isSimplyConnected_le_isPreconnected`: the inclusion of object properties.
* `TauCeti.LieGroupCat.simplyConnectedLieFunctor`: the faithful restriction of `lieFunctor` to
  simply connected groups.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Theorem 3.41 (uniqueness) and Corollary 3.44.
* Mathlib's `ModelWithCorners.MfldCat`, for the concrete-category setup.
-/

public section

noncomputable section

open CategoryTheory Topology
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

/-- Finite-dimensional smooth real Lie groups, with a model chosen for each object. -/
structure LieGroupCat where
  /-- The underlying type of the group. -/
  carrier : Type u
  /-- The vector-space model. -/
  model : Type v
  /-- The topological model for charts. -/
  chartDomain : Type w
  /-- The normed additive group of the vector-space model. -/
  [normedAddCommGroup : NormedAddCommGroup model]
  /-- Real scalar multiplication on the model. -/
  [normedSpace : NormedSpace ℝ model]
  /-- Finite dimensionality of the model. -/
  [finiteDimensional : FiniteDimensional ℝ model]
  /-- The topology of the chart model. -/
  [topologicalSpaceChartDomain : TopologicalSpace chartDomain]
  /-- The model with corners. -/
  modelWithCorners : ModelWithCorners ℝ model chartDomain
  /-- The topology of the group. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The charts on the group. -/
  [chartedSpace : ChartedSpace chartDomain carrier]
  /-- The group operations. -/
  [group : Group carrier]
  /-- Smoothness of the group operations. -/
  [lieGroup : LieGroup modelWithCorners ∞ carrier]

attribute [instance] LieGroupCat.normedAddCommGroup LieGroupCat.normedSpace
  LieGroupCat.finiteDimensional LieGroupCat.topologicalSpaceChartDomain
  LieGroupCat.topologicalSpace LieGroupCat.chartedSpace LieGroupCat.group LieGroupCat.lieGroup

instance : CoeSort (LieGroupCat.{u, v, w}) (Type u) := ⟨LieGroupCat.carrier⟩

namespace LieGroupCat

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- Bundled Lie groups are Hausdorff. -/
instance (G : LieGroupCat.{u, v, w}) : T2Space G :=
  G.modelWithCorners.t2Space_of_lieGroup ∞

/-- Bundle a finite-dimensional smooth real Lie group. -/
abbrev of {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (G : Type u) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] :
    LieGroupCat.{u, v, w} where
  carrier := G
  model := E
  chartDomain := H
  modelWithCorners := I

/-- A smooth homomorphism between bundled Lie groups. -/
@[ext]
structure Hom (G K : LieGroupCat.{u, v, w}) where
  /-- The underlying smooth homomorphism. Use `Hom.hom` to access it. -/
  hom' : ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K

instance : Category (LieGroupCat.{u, v, w}) where
  Hom G K := Hom G K
  id _ := ⟨ContMDiffMonoidMorphism.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
  id_comp f := Hom.ext (ContMDiffMonoidMorphism.comp_id f.hom')
  comp_id f := Hom.ext (ContMDiffMonoidMorphism.id_comp f.hom')
  assoc f g h := Hom.ext (ContMDiffMonoidMorphism.comp_assoc h.hom' g.hom' f.hom').symm

instance : ConcreteCategory (LieGroupCat.{u, v, w})
    (fun G K ↦ ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K) where
  hom := Hom.hom'
  ofHom := Hom.mk
  id_apply := by
    intro G x
    exact congrFun (ContMDiffMonoidMorphism.coe_id (I := G.modelWithCorners) (n := ∞)
      (G := G)) x
  comp_apply := by
    intro G K L f g x
    exact congrFun (ContMDiffMonoidMorphism.coe_comp g.hom' f.hom') x

variable {G K L : LieGroupCat.{u, v, w}}

/-- The smooth homomorphism underlying a categorical morphism. -/
abbrev Hom.hom (f : G ⟶ K) :
    ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K :=
  ConcreteCategory.hom f

/-- Regard a smooth homomorphism as a categorical morphism. -/
abbrev ofHom (f : ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K) :
    G ⟶ K := ConcreteCategory.ofHom f

/-- The identity morphism has the identity smooth homomorphism. -/
@[simp]
theorem hom_id : (𝟙 G : G ⟶ G).hom = ContMDiffMonoidMorphism.id := rfl

/-- The underlying smooth homomorphism of a composite is the composite of the underlying maps. -/
@[simp]
theorem hom_comp (f : G ⟶ K) (g : K ⟶ L) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Constructing a categorical morphism preserves its underlying smooth homomorphism. -/
@[simp]
theorem hom_ofHom (f : ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K) :
    (ofHom f).hom = f := rfl

/-- A categorical morphism is recovered from its underlying smooth homomorphism. -/
@[simp]
theorem ofHom_hom (f : G ⟶ K) : ofHom f.hom = f := rfl

/-- Converting the identity smooth homomorphism gives the identity categorical morphism. -/
@[simp]
theorem ofHom_id : ofHom (ContMDiffMonoidMorphism.id
    (I := G.modelWithCorners) (n := ∞) (G := G)) = 𝟙 G := rfl

/-- Converting a composite smooth homomorphism gives the composite categorical morphism. -/
@[simp]
theorem ofHom_comp
    (f : ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K)
    (g : ContMDiffMonoidMorphism K.modelWithCorners L.modelWithCorners ∞ K L) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/-- Categorical morphisms are equal if their underlying smooth homomorphisms agree. -/
@[ext]
theorem hom_ext {f g : G ⟶ K} (h : f.hom = g.hom) : f = g := ConcreteCategory.ext h

private theorem ofHom_comp_eq_id_of_leftInverse
    (f : ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K)
    (g : ContMDiffMonoidMorphism K.modelWithCorners G.modelWithCorners ∞ K G)
    (hgf : Function.LeftInverse g f) : ofHom f ≫ ofHom g = 𝟙 G := by
  apply hom_ext
  apply DFunLike.ext
  intro x
  simpa only [hom_comp, hom_ofHom, hom_id, ContMDiffMonoidMorphism.coe_comp,
    Function.comp_apply, ContMDiffMonoidMorphism.coe_id, id_eq] using hgf x

/-- Mutually inverse smooth homomorphisms give an isomorphism of Lie group objects. -/
def isoMk (f : ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K)
    (g : ContMDiffMonoidMorphism K.modelWithCorners G.modelWithCorners ∞ K G)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) : G ≅ K where
  hom := ofHom f
  inv := ofHom g
  hom_inv_id := ofHom_comp_eq_id_of_leftInverse f g hgf
  inv_hom_id := ofHom_comp_eq_id_of_leftInverse g f hfg

/-- The forward smooth homomorphism of `isoMk` is the specified forward map. -/
@[simp]
theorem isoMk_hom_hom
    (f : ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K)
    (g : ContMDiffMonoidMorphism K.modelWithCorners G.modelWithCorners ∞ K G)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) :
    (isoMk f g hgf hfg).hom.hom = f := by simp only [isoMk, hom_ofHom]

/-- The inverse smooth homomorphism of `isoMk` is the specified inverse map. -/
@[simp]
theorem isoMk_inv_hom
    (f : ContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners ∞ G K)
    (g : ContMDiffMonoidMorphism K.modelWithCorners G.modelWithCorners ∞ K G)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) :
    (isoMk f g hgf hfg).inv.hom = g := by simp only [isoMk, hom_ofHom]

/-- The Lie algebra of left-invariant derivations of a Lie group,
bundled as a finite-dimensional real Lie algebra. -/
noncomputable abbrev lieAlgebra (G : LieGroupCat.{u, v, w}) : FGLieAlgCat ℝ := by
  let _ := finiteDimensional_leftInvariantDerivation
    (I := G.modelWithCorners) (G := G) BoundarylessManifold.isInteriorPoint
  exact FGLieAlgCat.of ℝ (LeftInvariantDerivation G.modelWithCorners G)

/-- Send a finite-dimensional Lie group to its Lie algebra of left-invariant derivations,
and a smooth homomorphism `f` to its differential `lieMap f.hom`. -/
-- Expose the object component so imported statements identify its underlying carrier without
-- transporting Lie homomorphisms along an equality of types.
@[expose]
noncomputable def lieFunctor : LieGroupCat.{u, v, w} ⥤ FGLieAlgCat.{u} ℝ where
  obj := lieAlgebra
  map f := ObjectProperty.homMk (LieAlgCat.ofHom (_root_.lieMap f.hom))
  map_id G := by
    apply ObjectProperty.hom_ext
    apply LieAlgCat.hom_ext
    simpa only [ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.id_hom,
      LieAlgCat.hom_ofHom, LieAlgCat.hom_id, hom_id] using
      _root_.lieMap_id (I := G.modelWithCorners) (G := G)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply LieAlgCat.hom_ext
    simpa only [ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
      LieAlgCat.hom_ofHom, LieAlgCat.hom_comp, hom_comp] using
      _root_.lieMap_comp f.hom g.hom

/-- The Lie functor sends a group to its finite-dimensional Lie algebra. -/
@[simp]
theorem lieFunctor_obj (G : LieGroupCat.{u, v, w}) : lieFunctor.obj G = lieAlgebra G := rfl

/-- The underlying map of the Lie functor is the Lie map of the underlying smooth homomorphism. -/
@[simp]
theorem lieFunctor_map_hom_hom (f : G ⟶ K) : (lieFunctor.map f).hom.hom = _root_.lieMap f.hom := rfl

/-- The Lie functor is injective on homomorphisms out of a preconnected group. -/
@[grind inj]
theorem lieFunctor_map_injective [PreconnectedSpace G] :
    Function.Injective (lieFunctor.map : (G ⟶ K) → (lieFunctor.obj G ⟶ lieFunctor.obj K)) := by
  intro f g h
  apply hom_ext
  apply _root_.lieMap_injective (I := G.modelWithCorners) (I' := K.modelWithCorners)
  -- Match the left-invariant-derivation carriers through the characteristic equations.
  exact (lieFunctor_map_hom_hom f).symm.trans
    ((congrArg (fun f ↦ f.hom.hom) h).trans (lieFunctor_map_hom_hom g))

/-- The object property of being preconnected. -/
abbrev isPreconnected : ObjectProperty (LieGroupCat.{u, v, w}) :=
  fun G ↦ PreconnectedSpace G

/-- Differentiation restricted to preconnected Lie groups. -/
noncomputable abbrev preconnectedLieFunctor :
    isPreconnected.{u, v, w}.FullSubcategory ⥤ FGLieAlgCat.{u} ℝ :=
  isPreconnected.ι ⋙ lieFunctor

/-- Differentiation is faithful on preconnected Lie groups. -/
instance : preconnectedLieFunctor.Faithful where
  map_injective {G K} f g h := by
    let _ : PreconnectedSpace G.obj := G.property
    apply ObjectProperty.hom_ext
    apply lieFunctor_map_injective
    simpa only [preconnectedLieFunctor, Functor.comp_map, ObjectProperty.ι_map] using h

/-- The object property of being simply connected. -/
abbrev isSimplyConnected : ObjectProperty (LieGroupCat.{u, v, w}) :=
  fun G ↦ SimplyConnectedSpace G

/-- Every simply connected Lie group is preconnected. -/
theorem isSimplyConnected_le_isPreconnected :
    isSimplyConnected.{u, v, w} ≤ isPreconnected := by
  intro G hG
  let _ : SimplyConnectedSpace G := hG
  infer_instance

/-- Differentiation restricted to simply connected Lie groups. -/
noncomputable abbrev simplyConnectedLieFunctor :
    isSimplyConnected.{u, v, w}.FullSubcategory ⥤ FGLieAlgCat.{u} ℝ :=
  ObjectProperty.ιOfLE isSimplyConnected_le_isPreconnected ⋙ preconnectedLieFunctor

/-- Differentiation is faithful on simply connected Lie groups. -/
instance : simplyConnectedLieFunctor.Faithful := inferInstance

end LieGroupCat

end TauCeti
