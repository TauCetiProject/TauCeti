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

/-- The underlying continuous homomorphism of a smooth homomorphism of bundled Lie groups. -/
@[expose] def Hom.toContinuousMonoidHom {G K : LieGroupCat.{u, v, w}} (f : G ⟶ K) : G →ₜ* K :=
  ⟨f.hom.toMonoidHom, f.hom.contMDiff_toFun.continuous⟩

@[simp]
theorem Hom.toContinuousMonoidHom_id (G : LieGroupCat.{u, v, w}) :
    Hom.toContinuousMonoidHom (𝟙 G) = ContinuousMonoidHom.id G :=
  ContinuousMonoidHom.ext fun x ↦
    congrFun (ContMDiffMonoidMorphism.coe_id (I := G.modelWithCorners) (n := ∞) (G := G)) x

@[simp]
theorem Hom.toContinuousMonoidHom_comp {G K L : LieGroupCat.{u, v, w}} (f : G ⟶ K) (g : K ⟶ L) :
    Hom.toContinuousMonoidHom (f ≫ g) =
      (Hom.toContinuousMonoidHom g).comp (Hom.toContinuousMonoidHom f) :=
  ContinuousMonoidHom.ext fun x ↦ congrFun (ContMDiffMonoidMorphism.coe_comp g.hom f.hom) x

@[simp]
theorem Hom.coe_toContinuousMonoidHom {G K : LieGroupCat.{u, v, w}} (f : G ⟶ K) :
    ⇑(Hom.toContinuousMonoidHom f) = f.hom :=
  rfl

@[simp]
theorem Hom.toContinuousMonoidHom_ofHom_toContMDiffMonoidMorphism {G K : LieGroupCat.{u, v, w}}
    (f : G →ₜ* K) :
    Hom.toContinuousMonoidHom
      (ofHom (f.toContMDiffMonoidMorphism G.modelWithCorners K.modelWithCorners)) = f :=
  ContinuousMonoidHom.ext fun x ↦ congrFun (ContinuousMonoidHom.coe_toContMDiffMonoidMorphism
    (I := G.modelWithCorners) (I' := K.modelWithCorners) f) x

/-- The compact connected commutative Lie groups, the tori. -/
@[expose] def isTorus : ObjectProperty LieGroupCat.{u, v, w} :=
  fun G ↦ CompactSpace G ∧ ConnectedSpace G ∧ IsMulCommutative G

instance (G : isTorus.{u, v, w}.FullSubcategory) : CompactSpace G.obj := G.property.1
instance (G : isTorus.{u, v, w}.FullSubcategory) : ConnectedSpace G.obj := G.property.2.1
instance (G : isTorus.{u, v, w}.FullSubcategory) : IsMulCommutative G.obj := G.property.2.2
instance (G : isTorus.{u, v, w}.FullSubcategory) : IsTopologicalGroup G.obj :=
  topologicalGroup_of_lieGroup G.obj.modelWithCorners ∞

end LieGroupCat

/-- The finitely generated free `ℤ`-modules. -/
@[expose] def isFreeFiniteIntModule : ObjectProperty (ModuleCat.{u} ℤ) :=
  fun M ↦ Module.Free ℤ M ∧ Module.Finite ℤ M

open LieGroupCat ContinuousMonoidHom

attribute [local instance] ContMDiffMul.boundarylessManifold

/-- The kernel of the exponential of a Lie group is its exponential lattice, as a `ℤ`-module. -/
private def lieExpLatticeEquivKer (G : LieGroupCat.{u, v, w}) [IsMulCommutative G] :
    lieExpLattice (I := G.modelWithCorners) (G := G) ≃ₗ[ℤ]
      (lieExpAddMonoidHom (I := G.modelWithCorners) (G := G)).ker where
  toFun X := ⟨X.val, X.property⟩
  invFun X := ⟨X.val, X.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := Subtype.ext (by simp)
  left_inv _ := rfl
  right_inv _ := rfl

theorem isFreeFiniteIntModule_ker (G : isTorus.{u, v, w}.FullSubcategory) :
    isFreeFiniteIntModule
      (ModuleCat.of ℤ (lieExpAddMonoidHom (I := G.obj.modelWithCorners) (G := G.obj)).ker) :=
  ⟨Module.Free.of_equiv (lieExpLatticeEquivKer G.obj),
    Module.Finite.equiv (lieExpLatticeEquivKer G.obj)⟩

/-- **The exponential lattice functor.** It sends a torus `T` to the kernel of its exponential,
a finitely generated free `ℤ`-module, and a smooth homomorphism to the restriction of its Lie
map. -/
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
    refine LinearMap.ext fun X ↦ Subtype.ext ?_
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      AddMonoidHom.coe_toIntLinearMap, coe_lieMapKer_apply, Hom.toContinuousMonoidHom_comp]
    rw [ContinuousMonoidHom.lieMap_comp (I := G.obj.modelWithCorners)
      (I' := K.obj.modelWithCorners) (I'' := L.obj.modelWithCorners), LieHom.comp_apply]

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
    exact DFunLike.congr_fun h x

instance : lieExpKerFunctor.{u, v, w}.Full := lieExpKerFunctorFullyFaithful.full

instance : lieExpKerFunctor.{u, v, w}.Faithful := lieExpKerFunctorFullyFaithful.faithful

/-- The `n`-dimensional torus `(S¹)ⁿ`, as a compact connected commutative Lie group. -/
@[expose] def standardTorus (n : ℕ) : isTorus.{0, 0, 0}.FullSubcategory :=
  ⟨LieGroupCat.of (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1) (Fin n → Circle),
    show CompactSpace (Fin n → Circle) ∧ ConnectedSpace (Fin n → Circle) ∧
      IsMulCommutative (Fin n → Circle) from ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The exponential lattice of `(S¹)ⁿ` has rank `n`. -/
theorem finrank_lieExpKerFunctor_obj_standardTorus (n : ℕ) :
    Module.finrank ℤ (lieExpKerFunctor.obj (standardTorus n)).obj = n := by
  let T := (standardTorus n).obj
  -- The object of `lieExpKerFunctor` is `ModuleCat.of ℤ ker(exp)`, whose carrier is `ker(exp)`.
  change Module.finrank ℤ (lieExpAddMonoidHom (I := T.modelWithCorners) (G := T)).ker = n
  rw [← (lieExpLatticeEquivKer T).finrank_eq, finrank_lieExpLattice,
    finrank_leftInvariantDerivation_eq_modelVectorSpace BoundarylessManifold.isInteriorPoint]
  -- The model vector space of `standardTorus n` is the product of `n` copies of that of `𝓡 1`.
  change Module.finrank ℝ (Fin n → EuclideanSpace ℝ (Fin 1)) = n
  rw [Module.finrank_pi_fintype]
  simp

instance : lieExpKerFunctor.{0, 0, 0}.EssSurj where
  mem_essImage M := by
    have := M.property.1
    have := M.property.2
    let n := Module.finrank ℤ M.obj
    have := (lieExpKerFunctor.obj (standardTorus n)).property.1
    have := (lieExpKerFunctor.obj (standardTorus n)).property.2
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
