/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Lie.Category
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.KernelMap
public import TauCeti.Geometry.Manifold.Algebra.Pi
import TauCeti.Geometry.Lie.AutomaticSmoothness
import TauCeti.Geometry.Lie.Tangent.LeftInvariantDerivation

/-!
# Tori are equivalent to their exponential lattices

A torus here is a compact connected commutative finite-dimensional real Lie group, an object of
the full subcategory `TauCeti.LieGroupCat.isTorus` of `TauCeti.LieGroupCat`. Sending a torus `T` to
the kernel of its exponential `exp : 𝔱 → T`, a full lattice in `𝔱`, and a smooth homomorphism to
the restriction of its Lie map, gives the functor `TauCeti.lieExpKerFunctor` to the finitely
generated free `ℤ`-modules (`TauCeti.isFreeFiniteIntModule`). It is fully faithful
(`TauCeti.lieExpKerFunctorFullyFaithful`): every additive map of exponential kernels is the
restriction of the Lie map of exactly one continuous homomorphism
(`TauCeti.existsUnique_continuousMonoidHom_lieMap_ker`), which is smooth by automatic smoothness
(`ContinuousMonoidHom.toContMDiffMonoidMorphism`). It is essentially surjective: `ℤⁿ` is the
exponential lattice of the product `(S¹)ⁿ` of circles (`TauCeti.standardTorus`), whose lattice has
rank `n`, the dimension (`TauCeti.finrank_lieExpKerFunctor_obj_standardTorus`). So it is an
equivalence of categories (`TauCeti.lieExpKerEquivalence`). The circle goes to `2πℤ ≅ ℤ`, and
`z ↦ z²` to multiplication by `2`.

Connectedness is needed: `ℤ/2` and the trivial group both have kernel `0`. Compactness is needed:
`ℝ` has kernel `0`, and every `t ↦ ct` restricts to the zero map. Essential surjectivity uses the
tori `(S¹)ⁿ`, whose models live in the lowest universe, so the equivalence is stated there.

## Main definitions

* `TauCeti.LieGroupCat.isTorus`: the compact connected commutative Lie groups.
* `TauCeti.isFreeFiniteIntModule`: the finitely generated free `ℤ`-modules.
* `TauCeti.lieExpKerFunctor`: the exponential lattice functor.
* `TauCeti.lieExpKerFunctorFullyFaithful`: its full faithfulness.
* `TauCeti.standardTorus`: the torus `(S¹)ⁿ`.
* `TauCeti.lieExpKerEquivalence`: the equivalence of tori with finitely generated free
  `ℤ`-modules.

## Main results

* `TauCeti.LieGroupCat.isTorus_iff`, `TauCeti.LieGroupCat.isTorus_of`,
  `TauCeti.isFreeFiniteIntModule_iff`: membership in the two subcategories.
* `TauCeti.lieExpKerFunctor_obj_obj`, `TauCeti.standardTorus_obj`: the objects.
* `TauCeti.coe_lieExpKerFunctor_map_hom_hom_apply`: the functor acts on morphisms by the Lie map.
* `TauCeti.finrank_lieExpKerFunctor_obj_standardTorus`: the lattice of `(S¹)ⁿ` has rank `n`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser (2002), Cor. 1.103(c)
  and Prop. 4.58.
-/

public section

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

namespace LieGroupCat

attribute [local instance] ContMDiffMul.boundarylessManifold

/-- The compact connected commutative Lie groups, the tori. -/
def isTorus : ObjectProperty LieGroupCat.{u, v, w} :=
  fun G ↦ CompactSpace G ∧ ConnectedSpace G ∧ IsMulCommutative G

theorem isTorus_iff {G : LieGroupCat.{u, v, w}} :
    isTorus G ↔ CompactSpace G ∧ ConnectedSpace G ∧ IsMulCommutative G :=
  Iff.rfl

/-- A compact connected commutative Lie group is a torus. -/
theorem isTorus_of {G : LieGroupCat.{u, v, w}} [CompactSpace G] [ConnectedSpace G]
    [IsMulCommutative G] : isTorus G :=
  isTorus_iff.2 ⟨‹_›, ‹_›, ‹_›⟩

instance (G : isTorus.{u, v, w}.FullSubcategory) : CompactSpace G.obj :=
  (isTorus_iff.1 G.property).1
instance (G : isTorus.{u, v, w}.FullSubcategory) : ConnectedSpace G.obj :=
  (isTorus_iff.1 G.property).2.1
instance (G : isTorus.{u, v, w}.FullSubcategory) : IsMulCommutative G.obj :=
  (isTorus_iff.1 G.property).2.2

end LieGroupCat

/-- The finitely generated free `ℤ`-modules. -/
def isFreeFiniteIntModule : ObjectProperty (ModuleCat.{u} ℤ) :=
  fun M ↦ Module.Free ℤ M ∧ Module.Finite ℤ M

theorem isFreeFiniteIntModule_iff {M : ModuleCat.{u} ℤ} :
    isFreeFiniteIntModule M ↔ Module.Free ℤ M ∧ Module.Finite ℤ M :=
  Iff.rfl

instance (M : isFreeFiniteIntModule.{u}.FullSubcategory) : Module.Free ℤ M.obj :=
  (isFreeFiniteIntModule_iff.1 M.property).1
instance (M : isFreeFiniteIntModule.{u}.FullSubcategory) : Module.Finite ℤ M.obj :=
  (isFreeFiniteIntModule_iff.1 M.property).2

open LieGroupCat ContinuousMonoidHom

attribute [local instance] ContMDiffMul.boundarylessManifold

theorem isFreeFiniteIntModule_ker (G : isTorus.{u, v, w}.FullSubcategory) :
    isFreeFiniteIntModule
      (ModuleCat.of ℤ (lieExpAddMonoidHom (I := G.obj.modelWithCorners) (G := G.obj)).ker) :=
  isFreeFiniteIntModule_iff.2 ⟨inferInstance, inferInstance⟩

/-- **The exponential lattice functor.** It sends a torus `T` to the kernel of its exponential,
a finitely generated free `ℤ`-module, and a smooth homomorphism to the restriction of its Lie
map. -/
-- Exposed: `coe_lieExpKerFunctor_map_hom_hom_apply` types its argument through
-- `lieExpKerFunctor_obj_obj`, which holds by unfolding.
@[expose] def lieExpKerFunctor :
    isTorus.{u, v, w}.FullSubcategory ⥤ isFreeFiniteIntModule.FullSubcategory where
  obj G := ⟨_, isFreeFiniteIntModule_ker G⟩
  map {G K} f := ObjectProperty.homMk (ModuleCat.ofHom
    (lieMapKer (I := G.obj.modelWithCorners) (I' := K.obj.modelWithCorners)
      (Hom.toContinuousMonoidHom f.hom)).toIntLinearMap)
  map_id G := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun X ↦ Subtype.ext ?_
    simp
  map_comp {G K L} f g := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, Hom.toContinuousMonoidHom_comp]
    rw [lieMapKer_comp (I := G.obj.modelWithCorners) (I' := K.obj.modelWithCorners)
      (I'' := L.obj.modelWithCorners)]
    -- `AddMonoidHom.toIntLinearMap` of a composite is the composite of the `ℤ`-linear maps, by
    -- definition; Mathlib has no lemma for it.
    rfl

theorem lieExpKerFunctor_obj_obj (G : isTorus.{u, v, w}.FullSubcategory) :
    (lieExpKerFunctor.obj G).obj =
      ModuleCat.of ℤ (lieExpAddMonoidHom (I := G.obj.modelWithCorners) (G := G.obj)).ker :=
  (rfl)

@[simp]
theorem coe_lieExpKerFunctor_map_hom_hom_apply {G K : isTorus.{u, v, w}.FullSubcategory}
    (f : G ⟶ K) (X : (lieExpAddMonoidHom (I := G.obj.modelWithCorners) (G := G.obj)).ker) :
    ((lieExpKerFunctor.map f).hom.hom X).val =
      lieMap (I := G.obj.modelWithCorners) (I' := K.obj.modelWithCorners)
        (Hom.toContinuousMonoidHom f.hom) X := by
  simp only [lieExpKerFunctor, ObjectProperty.homMk_hom, ModuleCat.hom_ofHom]
  exact coe_lieMapKer_apply _ X

/-- The continuous homomorphism whose Lie map restricts to a given map of exponential kernels
(`existsUnique_continuousMonoidHom_lieMap_ker`). -/
private def lieExpKerPreimage {G K : isTorus.{u, v, w}.FullSubcategory}
    (g : lieExpKerFunctor.obj G ⟶ lieExpKerFunctor.obj K) : G.obj →ₜ* K.obj :=
  (existsUnique_continuousMonoidHom_lieMap_ker (I := G.obj.modelWithCorners)
    (I' := K.obj.modelWithCorners) g.hom.hom.toAddMonoidHom).exists.choose

private theorem lieMap_lieExpKerPreimage {G K : isTorus.{u, v, w}.FullSubcategory}
    (g : lieExpKerFunctor.obj G ⟶ lieExpKerFunctor.obj K)
    (X : (lieExpAddMonoidHom (I := G.obj.modelWithCorners) (G := G.obj)).ker) :
    lieMap (I := G.obj.modelWithCorners) (I' := K.obj.modelWithCorners) (lieExpKerPreimage g) X =
      (g.hom.hom X).val :=
  (existsUnique_continuousMonoidHom_lieMap_ker (I := G.obj.modelWithCorners)
    (I' := K.obj.modelWithCorners) g.hom.hom.toAddMonoidHom).exists.choose_spec X

/-- **The exponential lattice functor is fully faithful**: a smooth homomorphism of tori is
determined by its restriction to the exponential lattices, and every additive map of the lattices
is such a restriction. -/
def lieExpKerFunctorFullyFaithful : lieExpKerFunctor.{u, v, w}.FullyFaithful where
  preimage {G K} g := ObjectProperty.homMk (ofHom
    ((lieExpKerPreimage g).toContMDiffMonoidMorphism G.obj.modelWithCorners K.obj.modelWithCorners))
  map_preimage {G K} g := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun X ↦ Subtype.ext ?_
    refine (coe_lieExpKerFunctor_map_hom_hom_apply _ X).trans ?_
    rw [ObjectProperty.homMk_hom, Hom.toContinuousMonoidHom_ofHom_toContMDiffMonoidMorphism]
    exact lieMap_lieExpKerPreimage g X
  preimage_map {G K} f := by
    apply ObjectProperty.hom_ext
    apply hom_ext
    refine DFunLike.ext _ _ fun x ↦ ?_
    have h := (existsUnique_continuousMonoidHom_lieMap_ker (I := G.obj.modelWithCorners)
      (I' := K.obj.modelWithCorners) (lieExpKerFunctor.map f).hom.hom.toAddMonoidHom).unique
      (lieMap_lieExpKerPreimage (lieExpKerFunctor.map f))
      (fun X ↦ (coe_lieExpKerFunctor_map_hom_hom_apply f X).symm)
    rw [ObjectProperty.homMk_hom, hom_ofHom, ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
    exact (DFunLike.congr_fun h x).trans (congrFun (Hom.coe_toContinuousMonoidHom f.hom) x)

instance : lieExpKerFunctor.{u, v, w}.Full := lieExpKerFunctorFullyFaithful.full

instance : lieExpKerFunctor.{u, v, w}.Faithful := lieExpKerFunctorFullyFaithful.faithful

/-- The `n`-dimensional torus `(S¹)ⁿ`, as a compact connected commutative Lie group. -/
@[expose] def standardTorus (n : ℕ) : isTorus.{0, 0, 0}.FullSubcategory :=
  ⟨LieGroupCat.of (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1) (Fin n → Circle), isTorus_of⟩

theorem standardTorus_obj (n : ℕ) :
    (standardTorus n).obj =
      LieGroupCat.of (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1) (Fin n → Circle) :=
  (rfl)

/-- The exponential lattice of `(S¹)ⁿ` has rank `n`. -/
theorem finrank_lieExpKerFunctor_obj_standardTorus (n : ℕ) :
    Module.finrank ℤ (lieExpKerFunctor.obj (standardTorus n)).obj = n := by
  let T := (standardTorus n).obj
  let K := (lieExpAddMonoidHom (I := T.modelWithCorners) (G := T)).ker
  have h : Module.finrank ℤ K = n := by
    rw [← K.toIntSubmoduleEquiv.finrank_eq, finrank_lieExpLattice,
      finrank_leftInvariantDerivation_eq_modelVectorSpace BoundarylessManifold.isInteriorPoint]
    -- The model vector space of `standardTorus n` is the product of `n` copies of that of `𝓡 1`
    -- (`standardTorus_obj`).
    exact (Module.finrank_pi_fintype (R := ℝ)
      (M := fun _ : Fin n ↦ EuclideanSpace ℝ (Fin 1))).trans (by simp)
  -- The carrier of `lieExpKerFunctor.obj (standardTorus n)` is `ker(exp)`
  -- (`lieExpKerFunctor_obj_obj`).
  exact h

instance : lieExpKerFunctor.{0, 0, 0}.EssSurj where
  mem_essImage M := by
    let n := Module.finrank ℤ M.obj
    let e : (lieExpKerFunctor.obj (standardTorus n)).obj ≃ₗ[ℤ] M.obj :=
      (Module.finBasisOfFinrankEq ℤ _ (finrank_lieExpKerFunctor_obj_standardTorus n)).equiv
        (Module.finBasisOfFinrankEq ℤ M.obj rfl) (Equiv.refl _)
    exact ⟨standardTorus n, ⟨isFreeFiniteIntModule.fullyFaithfulι.preimageIso e.toModuleIso⟩⟩

/-- **Tori are equivalent to their exponential lattices** (Knapp, Cor. 1.103(c)): `T ↦ ker(exp_T)`
is an equivalence from compact connected commutative Lie groups to finitely generated free
`ℤ`-modules. -/
instance : lieExpKerFunctor.{0, 0, 0}.IsEquivalence where

/-- **Tori are equivalent to their exponential lattices**, as an equivalence of categories from
compact connected commutative Lie groups to finitely generated free `ℤ`-modules. -/
def lieExpKerEquivalence :
    isTorus.{0, 0, 0}.FullSubcategory ≌ isFreeFiniteIntModule.{0}.FullSubcategory :=
  lieExpKerFunctor.asEquivalence

end TauCeti
