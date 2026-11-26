/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank

/-!
# Symmetric monoidal structure on invertible sheaves

The object property `SheafOfModules.isInvertible X` on `X.Modules` contains the monoidal unit
`𝒪_X` and is closed under the monoidal tensor product, because `M ⊗ N` in `X.Modules` is
canonically isomorphic to `SheafOfModules.tensorProduct X.sheaf M N`, which preserves
invertibility. Consequently, the full subcategory `InvertibleSheaf X` inherits the symmetric
monoidal structure of `X.Modules`, and its inclusions `InvertibleSheaf.toFiniteLocallyFree X` into
`FiniteLocallyFreeSheaf X` and `InvertibleSheaf.toQuasicoherent X` into `QuasicoherentSheaf X` are
braided monoidal.

The explicit line-bundle operations `InvertibleSheaf.tensorProduct` and `InvertibleSheaf.trivial`
are canonically isomorphic to the inherited monoidal tensor product and unit
(`InvertibleSheaf.tensorProductIsoTensor` and `InvertibleSheaf.trivialIsoTensorUnit`). Passing to
isomorphism classes therefore identifies the monoidal `Skeleton` of `InvertibleSheaf X` with
`LineBundleClass X` by a multiplicative equivalence `LineBundleClass.skeletonMulEquiv`.

## Main declarations

* `TauCeti.AlgebraicGeometry.SheafOfModules.isMonoidal_isInvertible`: `isInvertible X` is a
  monoidal object property on `X.Modules`, giving `InvertibleSheaf X` its inherited symmetric
  monoidal category structure;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.toFiniteLocallyFreeMonoidal` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.toFiniteLocallyFreeBraided`: the inclusion into
  finite locally free sheaves is braided monoidal;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.isInvertible_le_isQuasicoherent`,
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.toQuasicoherent` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.toQuasicoherentBraided`: invertible sheaves are
  quasicoherent, and the inclusion into quasicoherent sheaves is braided monoidal;
* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorPow_obj`: monoidal tensor powers of invertible
  sheaves are invertible, and computed on underlying sheaves;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorProductIsoTensor` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.trivialIsoTensorUnit`: comparisons between the
  explicit line-bundle operations and the inherited monoidal operations, the first natural in
  both factors (`InvertibleSheaf.tensorProductCongr_hom_comp_tensorProductIsoTensor_hom`);
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.pullbackToFiniteLocallyFreeTensorIso`: the pullback
  of the vector bundle underlying `M ⊗ N` is the pullback of the line bundle
  `InvertibleSheaf.tensorProduct M N`;
* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorObj`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorUnit`, and
  `TauCeti.AlgebraicGeometry.LineBundleClass.skeletonMulEquiv`: compatibility of `LineBundleClass`
  with the monoidal structure on `Skeleton (InvertibleSheaf X)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 6
* [The Stacks Project, Tag 01CR](https://stacks.math.columbia.edu/tag/01CR)
* [The Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

/-- Invertibility is a monoidal property of `𝒪_X`-modules: the structure sheaf is invertible, and
the tensor product of two invertible sheaves in `X.Modules` is invertible. -/
instance isMonoidal_isInvertible (X : Scheme.{u}) : (isInvertible X).IsMonoidal where
  prop_unit := isInvertible_tensorUnit X
  prop_tensor M N hM hN := by
    let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := hM
    let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) N := hN
    have hprod : isInvertible X (SheafOfModules.tensorProduct X.sheaf M N) :=
      TauCeti.SheafOfModules.IsInvertible.tensorProduct (R := X.sheaf) (M := M) (N := N)
    exact (isInvertible X).prop_of_iso
      (SheafOfModules.tensorProductIso X.sheaf M N ≪≫ (M.tensorUnderlyingIso N).symm) hprod

/-- The monoidal tensor product of two invertible sheaves is invertible. -/
instance isInvertible_tensorObj {X : Scheme.{u}} (M N : X.Modules)
    [isInvertible X M] [isInvertible X N] : isInvertible X (M ⊗ N) :=
  ObjectProperty.prop_tensor ‹_› ‹_›

/-- The monoidal tensor powers of an invertible sheaf are invertible. -/
instance isInvertible_tensorPow {X : Scheme.{u}} (M : X.Modules) [isInvertible X M] (n : ℕ) :
    isInvertible X (TauCeti.tensorPow M n) := by
  induction n with
  | zero => exact isInvertible_tensorUnit X
  | succ n ih => exact ObjectProperty.prop_tensor ‹_› ih

end SheafOfModules

namespace InvertibleSheaf

variable {X : Scheme.{u}}

-- As in `FiniteLocallyFree.lean`, `SheafOfModules.isInvertible X` and
-- `Scheme.Modules.isFiniteLocallyFree X` are phrased on definitionally equal module-sheaf
-- categories (`X.Modules` vs `SheafOfModules X.ringCatSheaf`), so the `ιOfLE` monoidal and
-- braided instances are registered explicitly.
/-- The inclusion of invertible sheaves into finite locally free sheaves is strong monoidal. -/
instance toFiniteLocallyFreeMonoidal (X : Scheme.{u}) : (toFiniteLocallyFree X).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

/-- The inclusion of invertible sheaves into finite locally free sheaves is braided monoidal. -/
instance toFiniteLocallyFreeBraided (X : Scheme.{u}) : (toFiniteLocallyFree X).Braided where

/-- Invertible sheaves are quasicoherent. -/
lemma isInvertible_le_isQuasicoherent (X : Scheme.{u}) :
    SheafOfModules.isInvertible X ≤ _root_.SheafOfModules.isQuasicoherent X.ringCatSheaf :=
  fun _ _ ↦ SheafOfModules.isQuasicoherent_of_isInvertible

/-- The fully faithful inclusion of line bundles into quasicoherent sheaves. -/
abbrev toQuasicoherent (X : Scheme.{u}) : InvertibleSheaf X ⥤ QuasicoherentSheaf X :=
  ObjectProperty.ιOfLE (isInvertible_le_isQuasicoherent X)

-- Quasi-coherence is a monoidal property for the category structure of `X.Modules`, which
-- instance search does not find through `QuasicoherentSheaf X`, so it is passed explicitly.
/-- The inclusion of line bundles into quasicoherent sheaves is braided monoidal. -/
instance toQuasicoherentBraided (X : Scheme.{u}) : (toQuasicoherent X).Braided :=
  @ObjectProperty.instBraidedFullSubcategoryιOfLE X.Modules _ _ _ _ _ _
    (Scheme.Modules.isMonoidal_isQuasicoherent X) (isInvertible_le_isQuasicoherent X)

/-- `InvertibleSheaf.tensorProduct L K` is canonically isomorphic to the inherited monoidal tensor
product `L ⊗ K` in `InvertibleSheaf X`. -/
def tensorProductIsoTensor (L K : InvertibleSheaf X) : tensorProduct L K ≅ L ⊗ K :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X) (tensorProductObjIso L K)

/-- On underlying sheaves, `tensorProductIsoTensor L K` is `tensorProductObjIso L K`. -/
@[simp]
theorem tensorProductIsoTensor_hom_hom (L K : InvertibleSheaf X) :
    (tensorProductIsoTensor L K).hom.hom = (tensorProductObjIso L K).hom :=
  (rfl)

/-- On underlying sheaves, the inverse of `tensorProductIsoTensor L K` is
`(tensorProductObjIso L K).inv`. -/
@[simp]
theorem tensorProductIsoTensor_inv_hom (L K : InvertibleSheaf X) :
    (tensorProductIsoTensor L K).inv.hom = (tensorProductObjIso L K).inv :=
  (rfl)

/-- `tensorProductIsoTensor` is natural with respect to isomorphisms in both factors, transported
through the explicit tensor product by `tensorProductCongrLeft` and `tensorProductCongrRight`. -/
@[reassoc]
theorem tensorProductCongr_hom_comp_tensorProductIsoTensor_hom {L L' K K' : InvertibleSheaf X}
    (e : L ≅ L') (e' : K ≅ K') :
    (tensorProductCongrLeft (K := K) e).hom ≫ (tensorProductCongrRight (L := L') e').hom ≫
        (tensorProductIsoTensor L' K').hom =
      (tensorProductIsoTensor L K).hom ≫ (e.hom ⊗ₘ e'.hom) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, tensorProductIsoTensor_hom_hom,
    tensorProductCongrRight_hom_hom_comp_tensorProductObjIso_hom,
    tensorProductCongrLeft_hom_hom_comp_tensorProductObjIso_hom_assoc]
  -- The tensor product of morphisms of line bundles is computed on underlying sheaves.
  exact congrArg _ (tensorHom_def _ _).symm

/-- `InvertibleSheaf.trivial X` is canonically isomorphic to the monoidal unit
`𝟙_ (InvertibleSheaf X)`. -/
def trivialIsoTensorUnit (X : Scheme.{u}) : trivial X ≅ 𝟙_ (InvertibleSheaf X) :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X) (trivialObjIsoUnit X)

/-- On underlying sheaves, `trivialIsoTensorUnit X` is `trivialObjIsoUnit X`. -/
@[simp]
theorem trivialIsoTensorUnit_hom_hom (X : Scheme.{u}) :
    (trivialIsoTensorUnit X).hom.hom = (trivialObjIsoUnit X).hom :=
  (rfl)

/-- On underlying sheaves, the inverse of `trivialIsoTensorUnit X` is
`(trivialObjIsoUnit X).inv`. -/
@[simp]
theorem trivialIsoTensorUnit_inv_hom (X : Scheme.{u}) :
    (trivialIsoTensorUnit X).inv.hom = (trivialObjIsoUnit X).inv :=
  (rfl)

/-- Pulling back the vector bundle `M ⊗ N` underlying a tensor product of line bundles along
`f : Y ⟶ X` gives the sheaf underlying the pullback of the line bundle `M.tensorProduct N`. -/
def pullbackToFiniteLocallyFreeTensorIso {Y : Scheme.{u}} (f : Y ⟶ X) (M N : InvertibleSheaf X) :
    ((FiniteLocallyFreeSheaf.pullback f).obj
        ((toFiniteLocallyFree X).obj M ⊗ (toFiniteLocallyFree X).obj N)).obj ≅
      ((pullback f).obj (M.tensorProduct N)).obj :=
  (Scheme.Modules.isFiniteLocallyFree Y).ι.mapIso ((FiniteLocallyFreeSheaf.pullback f).mapIso
      (Functor.Monoidal.μIso (toFiniteLocallyFree X) M N ≪≫
        (toFiniteLocallyFree X).mapIso (tensorProductIsoTensor M N).symm)) ≪≫
    eqToIso (pullback_toFiniteLocallyFree_obj_obj f _)

/-- The underlying sheaf of the monoidal tensor power `L^{⊗n}` in `InvertibleSheaf X` is the
monoidal tensor power of the underlying sheaf of `L`. -/
@[simp]
theorem tensorPow_obj (L : InvertibleSheaf X) (n : ℕ) :
    (TauCeti.tensorPow L n).obj = TauCeti.tensorPow L.obj n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [TauCeti.tensorPow_succ, TauCeti.tensorPow_succ, ← ih]; rfl

end InvertibleSheaf

namespace LineBundleClass

variable {X : Scheme.{u}}

/-- The class of the monoidal tensor product `L ⊗ K` in `InvertibleSheaf X` is `mk L * mk K`. -/
@[simp]
theorem mk_tensorObj (L K : InvertibleSheaf X) : mk (L ⊗ K) = mk L * mk K := by
  rw [← mk_tensorProduct, mk_eq_mk_iff]
  exact ⟨(InvertibleSheaf.tensorProductObjIso L K).symm⟩

/-- The class of the monoidal unit `𝟙_ (InvertibleSheaf X)` is `1`. -/
@[simp]
theorem mk_tensorUnit (X : Scheme.{u}) : mk (𝟙_ (InvertibleSheaf X)) = 1 :=
  mk_eq_one_iff.mpr ⟨Iso.refl _⟩

/-- The multiplicative equivalence identifying the monoidal `Skeleton` of `InvertibleSheaf X` with
`LineBundleClass X`. -/
def skeletonMulEquiv (X : Scheme.{u}) :
    Skeleton (InvertibleSheaf X) ≃* LineBundleClass X where
  toFun := (SheafOfModules.isInvertible X).skeletonLift mk
    (fun _ _ h ↦ mk_eq_mk_iff.mpr h)
  invFun := lift toSkeleton
    (fun _ _ ⟨e⟩ ↦ toSkeleton_eq_toSkeleton_iff.mpr
      ⟨ObjectProperty.isoMk (SheafOfModules.isInvertible X) e⟩)
  left_inv x := by
    obtain ⟨L, rfl⟩ : ∃ L, toSkeleton L = x := Quotient.inductionOn x fun L ↦ ⟨L, rfl⟩
    rw [ObjectProperty.skeletonLift_toSkeleton, lift_mk]
  right_inv a := by
    obtain ⟨L, rfl⟩ := mk_surjective a
    rw [lift_mk, ObjectProperty.skeletonLift_toSkeleton]
  map_mul' x y := by
    obtain ⟨L, rfl⟩ : ∃ L, toSkeleton L = x := Quotient.inductionOn x fun L ↦ ⟨L, rfl⟩
    obtain ⟨K, rfl⟩ : ∃ K, toSkeleton K = y := Quotient.inductionOn y fun K ↦ ⟨K, rfl⟩
    rw [← Skeleton.toSkeleton_tensorObj, ObjectProperty.skeletonLift_toSkeleton,
      ObjectProperty.skeletonLift_toSkeleton, ObjectProperty.skeletonLift_toSkeleton,
      mk_tensorObj]

/-- `skeletonMulEquiv X` sends `toSkeleton L` to `mk L`. -/
@[simp]
theorem skeletonMulEquiv_toSkeleton (L : InvertibleSheaf X) :
    skeletonMulEquiv X (toSkeleton L) = mk L :=
  ObjectProperty.skeletonLift_toSkeleton _ L

/-- The inverse of `skeletonMulEquiv X` sends `mk L` to `toSkeleton L`. -/
@[simp]
theorem skeletonMulEquiv_symm_mk (L : InvertibleSheaf X) :
    (skeletonMulEquiv X).symm (mk L) = toSkeleton L :=
  lift_mk L

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
