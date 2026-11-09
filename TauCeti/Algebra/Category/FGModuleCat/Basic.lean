/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.CategoryTheory.ObjectProperty

/-!
# Finitely generated modules

This file provides general results about Mathlib's category of finitely generated modules.
Additivity of finite-free rank on biproducts makes dimension a split-additive invariant, which
feeds the Grothendieck-group computation for finite-dimensional vector spaces.

## Main results

* `FGModuleCat.hom_hom_ofHom`: the linear map underlying `FGModuleCat.ofHom f` is `f`, the
  analogue of Mathlib's `ModuleCat.hom_ofHom`.
* `FGModuleCat.forget₂_obj`, `FGModuleCat.forget₂_map`: the forgetful functor to `ModuleCat R`
  takes underlying modules and morphisms.
* `FGModuleCat.hom_hom_add`, `FGModuleCat.hom_hom_smul`: morphisms of finitely generated modules
  add and scale pointwise, the companions of Mathlib's `FGModuleCat.hom_hom_comp` and
  `FGModuleCat.hom_hom_id`.
* `FGModuleCat.braiding_hom_hom_hom`: the braiding of finitely generated modules is the swap
  `TensorProduct.comm` of the tensor product.
* `FGModuleCat.whiskerRight_hom_hom`: right whiskering of finitely generated modules is
  `LinearMap.rTensor`.
* `FGModuleCat.biprodIsoProd`: the biproduct of two finitely generated modules is their product,
  the analogue of Mathlib's `ModuleCat.biprodIsoProd`, with its projection lemmas
  `FGModuleCat.biprodIsoProd_inv_comp_fst` and `FGModuleCat.biprodIsoProd_inv_comp_snd`.
* `FGModuleCat.finrank_biprod`: rank is additive on biproducts of finite free modules.
* `TauCeti.FGModuleCat.homLinearEquivOfIsScalarTower`: for an algebra `R` over a field `k`,
  morphisms into `FGModuleCat.of R M` are the `R`-linear maps into `M`, `k`-linearly for the
  original `k`-action on `M` rather than the category's restricted scalar action.
* `FGModuleCat.tensorUnitHomLinearEquiv`: morphisms `𝟙_ (FGModuleCat R) ⟶ W` identify `R`-linearly
  with `W` by evaluation at `1`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- The linear map underlying `FGModuleCat.ofHom f` is `f`. -/
@[simp]
theorem _root_.FGModuleCat.hom_hom_ofHom {R : Type u} [Ring R] {V W : Type v} [AddCommGroup V]
    [Module R V] [Module.Finite R V] [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : V →ₗ[R] W) : (FGModuleCat.ofHom f).hom.hom = f :=
  (rfl)

/-- The forgetful functor from finitely generated modules sends an object to its underlying
module: it is the inclusion of a full subcategory. -/
@[simp]
theorem _root_.FGModuleCat.forget₂_obj {R : Type u} [Ring R] (X : FGModuleCat.{v} R) :
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).obj X = X.obj :=
  rfl

/-- The forgetful functor from finitely generated modules sends a morphism to its underlying
morphism of modules. -/
@[simp]
theorem _root_.FGModuleCat.forget₂_map {R : Type u} [Ring R] {X Y : FGModuleCat.{v} R}
    (f : X ⟶ Y) : (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map f = f.hom :=
  rfl

/-- The linear map underlying a sum of morphisms of finitely generated modules is the sum of the
linear maps underlying them: addition of morphisms in a full subcategory of `ModuleCat R` is the
addition of the underlying linear maps. -/
@[simp]
theorem _root_.FGModuleCat.hom_hom_add {R : Type u} [Ring R] {V W : FGModuleCat.{v} R}
    (f g : V ⟶ W) : (f + g).hom.hom = f.hom.hom + g.hom.hom :=
  (rfl)

/-- The linear map underlying a scalar multiple of a morphism of finitely generated modules over a
commutative ring is the scalar multiple of the underlying linear map. -/
@[simp]
theorem _root_.FGModuleCat.hom_hom_smul {R : Type u} [CommRing R] {V W : FGModuleCat.{v} R}
    (r : R) (f : V ⟶ W) : (r • f).hom.hom = r • f.hom.hom :=
  (rfl)

open MonoidalCategory in
/-- The linear map underlying the braiding of finitely generated modules over a commutative ring
is the swap of the factors of the tensor product. -/
@[simp]
theorem _root_.FGModuleCat.braiding_hom_hom_hom {R : Type u} [CommRing R]
    (V W : FGModuleCat.{u} R) :
    (β_ V W).hom.hom.hom = (TensorProduct.comm R V W).toLinearMap :=
  (rfl)

open MonoidalCategory in
/-- The linear map underlying the right whiskering `f ▷ U` of finitely generated modules over a
commutative ring is `LinearMap.rTensor U f`. Not a simp lemma: simp first unfolds `f ▷ U` to the
whiskering in `ModuleCat` via `ObjectProperty.whiskerRight_def`, and Mathlib's
`ModuleCat.hom_whiskerRight` is likewise not a simp lemma. -/
theorem _root_.FGModuleCat.whiskerRight_hom_hom {R : Type u} [CommRing R]
    {V W : FGModuleCat.{u} R} (f : V ⟶ W) (U : FGModuleCat.{u} R) :
    (f ▷ U).hom.hom = f.hom.hom.rTensor U :=
  (rfl)

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The biproduct of two finitely generated modules is their product, the analogue of Mathlib's
`ModuleCat.biprodIsoProd`. -/
noncomputable def _root_.FGModuleCat.biprodIsoProd {R : Type u} [Ring R]
    (X Y : FGModuleCat.{v} R) : (X ⊞ Y : FGModuleCat.{v} R) ≅ FGModuleCat.of R (X × Y) :=
  letI F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  letI : PreservesBinaryBiproduct X Y F := preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  F.preimageIso (F.mapBiprod X Y ≪≫ ModuleCat.biprodIsoProd X.obj Y.obj)

/-- The inverse of `FGModuleCat.biprodIsoProd` followed by the first biproduct projection is the
first product projection. -/
@[simp, elementwise]
theorem _root_.FGModuleCat.biprodIsoProd_inv_comp_fst {R : Type u} [Ring R]
    (X Y : FGModuleCat.{v} R) :
    (FGModuleCat.biprodIsoProd X Y).inv ≫ biprod.fst = FGModuleCat.ofHom (LinearMap.fst R X Y) := by
  have : PreservesBinaryBiproduct X Y (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  apply (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map_injective
  have h : ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapBiprod X Y).inv ≫
      (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map biprod.fst = biprod.fst := by
    rw [Iso.inv_comp_eq, Functor.mapBiprod_hom, biprod.lift_fst]
  rw [Functor.map_comp, FGModuleCat.biprodIsoProd, Functor.preimageIso_inv, Functor.map_preimage,
    Iso.trans_inv, Category.assoc, h]
  -- The forgetful functor sends `X` to `X.obj` and `FGModuleCat.ofHom f` to `ModuleCat.ofHom f`
  -- definitionally, so Mathlib's projection lemma closes the goal up to that unfolding.
  exact ModuleCat.biprodIsoProd_inv_comp_fst _ _

/-- The inverse of `FGModuleCat.biprodIsoProd` followed by the second biproduct projection is the
second product projection. -/
@[simp, elementwise]
theorem _root_.FGModuleCat.biprodIsoProd_inv_comp_snd {R : Type u} [Ring R]
    (X Y : FGModuleCat.{v} R) :
    (FGModuleCat.biprodIsoProd X Y).inv ≫ biprod.snd = FGModuleCat.ofHom (LinearMap.snd R X Y) := by
  have : PreservesBinaryBiproduct X Y (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  apply (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map_injective
  have h : ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapBiprod X Y).inv ≫
      (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map biprod.snd = biprod.snd := by
    rw [Iso.inv_comp_eq, Functor.mapBiprod_hom, biprod.lift_snd]
  rw [Functor.map_comp, FGModuleCat.biprodIsoProd, Functor.preimageIso_inv, Functor.map_preimage,
    Iso.trans_inv, Category.assoc, h]
  -- As for `biprodIsoProd_inv_comp_fst`.
  exact ModuleCat.biprodIsoProd_inv_comp_snd _ _

/-- The rank of a biproduct of finite free modules is the sum of their ranks. -/
@[simp]
theorem _root_.FGModuleCat.finrank_biprod (R : Type u) [Ring R] [StrongRankCondition R]
    (X Y : FGModuleCat.{v} R) [Module.Free R X] [Module.Free R Y] :
    Module.finrank R ((X ⊞ Y : FGModuleCat.{v} R) : Type v) =
      Module.finrank R X + Module.finrank R Y :=
  (FGModuleCat.isoToLinearEquiv (FGModuleCat.biprodIsoProd X Y)).finrank_eq.trans
    Module.finrank_prod


namespace FGModuleCat

variable (k : Type w) [Field k] {R : Type u} [Ring R] [Algebra k R] {M : Type v}
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module k M] [IsScalarTower k R M]

/-- Category morphisms into `M` identify with linear maps into `M`, respecting its original
`k`-action rather than the category's restricted scalar action. -/
noncomputable def homLinearEquivOfIsScalarTower (N : FGModuleCat.{v} R) :
    (N ⟶ FGModuleCat.of R M) ≃ₗ[k] (N →ₗ[R] M) where
  toFun f := f.hom.hom
  invFun f := FGModuleCat.ofHom f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro x
    -- `ModuleCat.linearOverField` acts on morphisms through `ModuleCat.moduleOfAlgebraModule`,
    -- so `(c • f) x` unfolds by definition to `algebraMap k R c • f x`.
    exact algebraMap_smul R c (f.hom.hom x)

/-- The comparison preserves the underlying linear map. -/
@[simp]
theorem homLinearEquivOfIsScalarTower_apply (N : FGModuleCat.{v} R)
    (f : N ⟶ FGModuleCat.of R M) :
    homLinearEquivOfIsScalarTower k N f = f.hom.hom := (rfl)

/-- The inverse comparison bundles a linear map as a category morphism. -/
@[simp]
theorem homLinearEquivOfIsScalarTower_symm_apply (N : FGModuleCat.{v} R)
    (f : N →ₗ[R] M) :
    (homLinearEquivOfIsScalarTower k N).symm f = FGModuleCat.ofHom f := (rfl)

end FGModuleCat

/-! ### Closure properties of `ModuleCat.isFG` -/

variable (R : Type u) [Ring R]

instance : (ModuleCat.isFG.{v} R).IsClosedUnderIsomorphisms where
  of_iso {M N} e h := by
    have : Module.Finite R M := (ModuleCat.isFG_iff M).mp h
    exact (ModuleCat.isFG_iff N).mpr (Module.Finite.equiv e.toLinearEquiv)

instance : (ModuleCat.isFG.{v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    (ModuleCat.isFG_iff _).mpr inferInstance⟩

instance : (ModuleCat.isFG.{v} R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    have : Module.Finite R M := (ModuleCat.isFG_iff M).mp hM
    have : Module.Finite R N := (ModuleCat.isFG_iff N).mp hN
    exact (ModuleCat.isFG_iff _).mpr
      (Module.Finite.equiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm)

end TauCeti

namespace FGModuleCat

open CategoryTheory MonoidalCategory

universe u

variable {R : Type u} [CommRing R]

/-- Morphisms out of the monoidal unit `𝟙_ (FGModuleCat R)` identify `R`-linearly with the elements
of the target module by evaluation at `1 : R`. -/
def tensorUnitHomLinearEquiv (W : FGModuleCat.{u} R) :
    (𝟙_ (FGModuleCat.{u} R) ⟶ W) ≃ₗ[R] W :=
  InducedCategory.homLinearEquiv ≪≫ₗ ModuleCat.homLinearEquiv ≪≫ₗ
    LinearMap.ringLmapEquivSelf R R W

/-- `tensorUnitHomLinearEquiv` evaluates a morphism out of `𝟙_ (FGModuleCat R)` at `1 : R`. -/
@[simp]
theorem tensorUnitHomLinearEquiv_apply (W : FGModuleCat.{u} R) (f : 𝟙_ (FGModuleCat.{u} R) ⟶ W) :
    tensorUnitHomLinearEquiv W f = f.hom.hom (1 : R) :=
  (rfl)

/-- The inverse of `tensorUnitHomLinearEquiv` sends `w : W` to `LinearMap.toSpanSingleton R W w`. -/
@[simp]
theorem tensorUnitHomLinearEquiv_symm_apply_hom_hom (W : FGModuleCat.{u} R) (w : W) :
    ((tensorUnitHomLinearEquiv W).symm w).hom.hom = LinearMap.toSpanSingleton R W w :=
  (rfl)

/-- Postcomposition on `𝟙_ (FGModuleCat R) ⟶ W` corresponds under `tensorUnitHomLinearEquiv` to the
underlying linear map. -/
theorem conj_tensorUnitHomLinearEquiv_rightComp {W : FGModuleCat.{u} R} (f : W ⟶ W) :
    (tensorUnitHomLinearEquiv W).conj (Linear.rightComp R (𝟙_ (FGModuleCat.{u} R)) f) =
      f.hom.hom := by
  ext w
  simp only [LinearEquiv.conj_apply_apply, Linear.rightComp_apply,
    tensorUnitHomLinearEquiv_apply, hom_hom_comp, LinearMap.comp_apply,
    tensorUnitHomLinearEquiv_symm_apply_hom_hom]
  exact congrArg f.hom.hom (LinearMap.toSpanSingleton_apply_one R W w)

end FGModuleCat
