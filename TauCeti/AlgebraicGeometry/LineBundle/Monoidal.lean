/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Symmetric monoidal structure on invertible sheaves

The object property `SheafOfModules.isInvertible X` on `X.Modules` contains the monoidal unit
`𝒪_X` and is closed under the monoidal tensor product, because `M ⊗ N` in `X.Modules` is
canonically isomorphic to `SheafOfModules.tensorProduct X.sheaf M N`, which preserves
invertibility. Consequently, the full subcategory `InvertibleSheaf X` inherits the symmetric
monoidal structure of `X.Modules`, and its inclusion `InvertibleSheaf.toFiniteLocallyFree X` into
`FiniteLocallyFreeSheaf X` is braided monoidal.

The explicit line-bundle operations `InvertibleSheaf.tensorProduct` and `InvertibleSheaf.trivial`
are canonically isomorphic to the inherited monoidal tensor product and unit
(`InvertibleSheaf.tensorProductIsoTensor` and `InvertibleSheaf.trivialIsoTensorUnit`). Passing to
isomorphism classes therefore identifies the monoidal `Skeleton` of `InvertibleSheaf X` with
`LineBundleClass X` by a multiplicative equivalence `LineBundleClass.skeletonMulEquiv`.

Pullback of line bundles along any morphism of schemes is strong symmetric monoidal: its inverse
comparisons are the structure-sheaf identification `f^* 𝒪_Y ≅ 𝒪_X` and the oplax tensor comparison
`f^*(L ⊗ K) ⟶ f^*L ⊗ f^*K` of module pullback, which is invertible because line bundles are
quasicoherent. The identity and composition comparisons `InvertibleSheaf.pullbackId` and
`InvertibleSheaf.pullbackComp` are monoidal natural isomorphisms, by the corresponding identities
`Scheme.Modules.pullback_id_δ`, `Scheme.Modules.pullbackObjUnitIso_id`,
`Scheme.Modules.inv_δ_comp_pullbackComp_hom_app` and `Scheme.Modules.pullbackObjUnitIso_inv_comp`
of module pullback. This lets pullback act on monoidal constructions with line bundles, such as
tensor powers, by specified isomorphisms rather than merely up to isomorphism.

## Main declarations

* `TauCeti.AlgebraicGeometry.SheafOfModules.isMonoidal_isInvertible`: `isInvertible X` is a
  monoidal object property on `X.Modules`, giving `InvertibleSheaf X` its inherited symmetric
  monoidal category structure;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.toFiniteLocallyFreeMonoidal` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.toFiniteLocallyFreeBraided`: the inclusion into
  finite locally free sheaves is braided monoidal;
* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorPow_obj`: monoidal tensor powers of invertible
  sheaves are invertible, and computed on underlying sheaves;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorProductIsoTensor` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.trivialIsoTensorUnit`: comparisons between the
  explicit line-bundle operations and the inherited monoidal operations;
* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorObj`,
  `TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorUnit`, and
  `TauCeti.AlgebraicGeometry.LineBundleClass.skeletonMulEquiv`: compatibility of `LineBundleClass`
  with the monoidal structure on `Skeleton (InvertibleSheaf X)`;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.pullbackMonoidal` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.pullbackBraided`: pullback of line bundles is strong
  symmetric monoidal, with comparisons computed by `InvertibleSheaf.pullback_η_hom`,
  `InvertibleSheaf.pullback_δ_hom`, `InvertibleSheaf.pullback_ε_hom` and
  `InvertibleSheaf.pullback_μ_hom`;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.isMonoidal_pullbackId_hom` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.isMonoidal_pullbackComp_hom`: the identity and
  composition comparisons of pullback are monoidal.

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

/-- The underlying sheaf of the monoidal tensor power `L^{⊗n}` in `InvertibleSheaf X` is the
monoidal tensor power of the underlying sheaf of `L`. -/
@[simp]
theorem tensorPow_obj (L : InvertibleSheaf X) (n : ℕ) :
    (TauCeti.tensorPow L n).obj = TauCeti.tensorPow L.obj n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [TauCeti.tensorPow_succ, TauCeti.tensorPow_succ, ← ih]; rfl

end InvertibleSheaf

namespace InvertibleSheaf

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {X Y Z : Scheme.{u}}

/-- **Pullback of line bundles is strong monoidal.** Its inverse comparisons are those of the
oplax monoidal module pullback `Scheme.Modules.pullbackOplaxMonoidal`: the structure-sheaf
identification `f^* 𝒪_Y ≅ 𝒪_X` and the tensor comparison `f^*(L ⊗ K) ⟶ f^*L ⊗ f^*K`, which is
invertible because line bundles are quasicoherent. -/
instance pullbackMonoidal (f : X ⟶ Y) : (pullback f).Monoidal :=
  letI : (pullback f).OplaxMonoidal :=
    { η := ObjectProperty.homMk (η (Scheme.Modules.pullback f))
      δ L K := ObjectProperty.homMk (δ (Scheme.Modules.pullback f) L.obj K.obj)
      δ_natural_left φ K := ObjectProperty.hom_ext _
        (δ_natural_left (Scheme.Modules.pullback f) φ.hom K.obj)
      δ_natural_right L φ := ObjectProperty.hom_ext _
        (δ_natural_right (Scheme.Modules.pullback f) L.obj φ.hom)
      oplax_associativity L K M := ObjectProperty.hom_ext _
        (Functor.OplaxMonoidal.associativity (Scheme.Modules.pullback f) L.obj K.obj M.obj)
      oplax_left_unitality L := ObjectProperty.hom_ext _
        (Functor.OplaxMonoidal.left_unitality (Scheme.Modules.pullback f) L.obj)
      oplax_right_unitality L := ObjectProperty.hom_ext _
        (Functor.OplaxMonoidal.right_unitality (Scheme.Modules.pullback f) L.obj) }
  have : IsIso (η (Scheme.Modules.pullback f)) := by
    rw [Scheme.Modules.pullback_η]
    infer_instance
  have : IsIso (η (pullback f)) := (ObjectProperty.isIso_hom_iff _).mp
    (inferInstanceAs (IsIso (η (Scheme.Modules.pullback f))))
  have (L K : InvertibleSheaf Y) : IsIso (δ (pullback f) L K) :=
    (ObjectProperty.isIso_hom_iff _).mp
      (inferInstanceAs (IsIso (δ (Scheme.Modules.pullback f) L.obj K.obj)))
  Functor.Monoidal.ofOplaxMonoidal _

/-- On underlying sheaves, the inverse unit comparison of line-bundle pullback is the
structure-sheaf identification `f^* 𝒪_Y ≅ 𝒪_X`. -/
@[simp]
theorem pullback_η_hom (f : X ⟶ Y) :
    (η (pullback f)).hom = (Scheme.Modules.pullbackObjUnitIso f).hom :=
  Scheme.Modules.pullback_η f

/-- On underlying sheaves, the inverse tensor comparison of line-bundle pullback is the tensor
comparison of module pullback. -/
@[simp]
theorem pullback_δ_hom (f : X ⟶ Y) (L K : InvertibleSheaf Y) :
    (δ (pullback f) L K).hom = δ (Scheme.Modules.pullback f) L.obj K.obj :=
  (rfl)

/-- On underlying sheaves, the unit comparison of line-bundle pullback is the inverse of the
structure-sheaf identification `f^* 𝒪_Y ≅ 𝒪_X`. -/
@[simp]
theorem pullback_ε_hom (f : X ⟶ Y) :
    (ε (pullback f)).hom = (Scheme.Modules.pullbackObjUnitIso f).inv := by
  refine (Iso.inv_ext ?_).symm
  rw [← Scheme.Modules.pullback_η]
  exact congrArg (·.hom) (Functor.Monoidal.η_ε (pullback f))

/-- On underlying sheaves, the tensor comparison of line-bundle pullback is the inverse of the
tensor comparison of module pullback. -/
@[simp]
theorem pullback_μ_hom (f : X ⟶ Y) (L K : InvertibleSheaf Y) :
    (μ (pullback f) L K).hom = inv (δ (Scheme.Modules.pullback f) L.obj K.obj) :=
  IsIso.eq_inv_of_hom_inv_id (f := δ (Scheme.Modules.pullback f) L.obj K.obj)
    (congrArg (·.hom) (Functor.Monoidal.δ_μ (pullback f) L K))

/-- The inverse tensor comparison of line-bundle pullback is compatible with the symmetry. -/
@[reassoc]
theorem pullback_map_braiding_hom_comp_δ (f : X ⟶ Y) (L K : InvertibleSheaf Y) :
    (pullback f).map (β_ L K).hom ≫ δ (pullback f) K L =
      δ (pullback f) L K ≫ (β_ ((pullback f).obj L) ((pullback f).obj K)).hom :=
  ObjectProperty.hom_ext _ (Scheme.Modules.pullback_map_braiding_hom_comp_δ f L.obj K.obj)

/-- Pullback of line bundles is braided (hence symmetric) monoidal. -/
instance pullbackBraided (f : X ⟶ Y) : (pullback f).Braided where
  braided L K := by
    rw [← cancel_epi (δ (pullback f) L K), Functor.Monoidal.δ_μ_assoc,
      ← cancel_mono (δ (pullback f) K L), Category.assoc, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id, pullback_map_braiding_hom_comp_δ]

-- `pullback f` is a lift of module pullback, so its underlying objects are those of module
-- pullback on the nose. The public `pullback_map`, `pullbackId_hom_app_hom` and
-- `pullbackComp_hom_app_hom` keep the resulting identity transports `eqToHom`, which `simp`
-- cannot remove when they stand alone; these restatements drop them, so that the module
-- identities apply directly.
private lemma pullback_map_hom (f : X ⟶ Y) {L K : InvertibleSheaf Y} (φ : L ⟶ K) :
    ((pullback f).map φ).hom = (Scheme.Modules.pullback f).map φ.hom :=
  (rfl)

private lemma pullbackId_hom_app_hom_eq (L : InvertibleSheaf X) :
    ((pullbackId X).hom.app L).hom = (Scheme.Modules.pullbackId X).hom.app L.obj :=
  (pullbackId_hom_app_hom X L).trans (Category.id_comp _)

private lemma pullbackComp_hom_app_hom_eq (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    ((pullbackComp f g).hom.app L).hom = (Scheme.Modules.pullbackComp f g).hom.app L.obj :=
  (pullbackComp_hom_app_hom f g L).trans ((Category.id_comp _).trans (Category.comp_id _))

/-- The identity comparison `pullback (𝟙 X) ≅ 𝟭` of line bundles is monoidal. -/
instance isMonoidal_pullbackId_hom (X : Scheme.{u}) : NatTrans.IsMonoidal (pullbackId X).hom where
  unit := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, pullback_ε_hom, pullbackId_hom_app_hom_eq,
      Functor.LaxMonoidal.id_ε, ObjectProperty.FullSubcategory.id_hom,
      ObjectProperty.tensorUnit_obj]
    exact (Iso.inv_comp_eq_id _).2 (Scheme.Modules.pullbackObjUnitIso_id X).symm
  tensor L K := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, pullback_μ_hom, pullbackId_hom_app_hom_eq,
      ObjectProperty.tensorHom_def, ObjectProperty.homMk_hom, ObjectProperty.tensorObj_obj,
      Functor.LaxMonoidal.id_μ, Category.comp_id]
    exact (IsIso.inv_comp_eq (δ (Scheme.Modules.pullback (𝟙 X)) L.obj K.obj)).2
      (Scheme.Modules.pullback_id_δ X L.obj K.obj).symm

/-- The composition comparison `pullback g ⋙ pullback f ≅ pullback (f ≫ g)` of line bundles is
monoidal. -/
instance isMonoidal_pullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (pullbackComp f g).hom where
  unit := by
    apply ObjectProperty.hom_ext
    simp only [Functor.LaxMonoidal.comp_ε, ObjectProperty.FullSubcategory.comp_hom,
      pullback_map_hom, pullback_ε_hom, pullbackComp_hom_app_hom_eq, ObjectProperty.tensorUnit_obj,
      Category.assoc]
    exact Scheme.Modules.pullbackObjUnitIso_inv_comp f g
  tensor L K := by
    apply ObjectProperty.hom_ext
    simp only [Functor.LaxMonoidal.comp_μ, ObjectProperty.FullSubcategory.comp_hom,
      pullback_map_hom, pullback_μ_hom, pullbackComp_hom_app_hom_eq, ObjectProperty.tensorHom_def,
      ObjectProperty.homMk_hom, ObjectProperty.tensorObj_obj, Category.assoc]
    exact Scheme.Modules.inv_δ_comp_pullbackComp_hom_app f g L.obj K.obj

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
