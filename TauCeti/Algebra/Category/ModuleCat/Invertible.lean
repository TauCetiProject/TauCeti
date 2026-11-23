/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Monoidal
public import TauCeti.CategoryTheory.Skeletal

/-!
# The category of invertible modules over a commutative ring

For a commutative ring `R`, the invertible `R`-modules (`Module.Invertible R M`) form a full
subcategory `(invertibleModules R).FullSubcategory` of `ModuleCat.{u} R`. Because `R` itself is
invertible and tensor products of invertible modules are invertible, this full subcategory inherits
the symmetric monoidal structure of `ModuleCat.{u} R`, and its inclusion into the category of
finite projective `R`-modules is braided monoidal.

Linear dualization restricts to a contravariant endofunctor on invertible modules, with double-dual
identification `InvertibleModules.evalIso` and contraction isomorphism
`InvertibleModules.contractIso : dual R M ⊗ M ≅ 𝟙_` given by `Module.Invertible.linearEquiv`.
Extension of scalars along a ring homomorphism `f : R →+* S` restricts to a functor
`InvertibleModules.extendScalars f` between categories of invertible modules.

Passing to isomorphism classes identifies the skeleton of `(invertibleModules R).FullSubcategory`
with Mathlib's Picard group `CommRing.Pic R` by a multiplicative equivalence
`InvertibleModules.skeletonEquivPic`, intertwining `InvertibleModules.extendScalars f` with
`CommRing.Pic.mapRingHom f`. This provides the module-category half of the comparison between
line-bundle classes on `Spec R` and `CommRing.Pic R`.

## Main declarations

* `ModuleCat.invertible_extendScalars_obj`: extension of scalars along a ring homomorphism
  preserves `Module.Invertible`;
* `TauCeti.invertibleModules`: invertibility as an `ObjectProperty` on `ModuleCat.{u} R`, equipped
  with closure under isomorphisms and its symmetric monoidal subcategory structure;
* `TauCeti.invertibleModules_le_finiteProjectiveModules` and
  `TauCeti.InvertibleModules.toFiniteProjective`: the braided fully faithful inclusion into finite
  projective modules;
* `TauCeti.InvertibleModules.dual`, `TauCeti.InvertibleModules.dualFunctor`,
  `TauCeti.InvertibleModules.evalIso`, and `TauCeti.InvertibleModules.contractIso`: linear duality,
  biduality, and contraction on invertible modules;
* `TauCeti.InvertibleModules.extendScalars`: extension of scalars between categories of invertible
  modules;
* `TauCeti.InvertibleModules.skeletonEquivPic`: the multiplicative equivalence
  `Skeleton (invertibleModules R).FullSubcategory ≃* CommRing.Pic R`, compatible with base change
  (`TauCeti.InvertibleModules.skeletonEquivPic_extendScalars_mapSkeleton`).

## References

* [The Stacks Project, Tag 0AFW](https://stacks.math.columbia.edu/tag/0AFW)
* [The Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat

/-- Extension of scalars along a ring homomorphism preserves invertibility of modules. -/
instance invertible_extendScalars_obj {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) [Module.Invertible R M] :
    Module.Invertible S ((ModuleCat.extendScalars f).obj M) := by
  let _ : Algebra R S := f.toAlgebra
  exact Module.Invertible.congr
    (ModuleCat.extendScalarsAlgebraMapIso (R := R) (S := S) M).symm.toLinearEquiv

end ModuleCat

namespace TauCeti

/-- The object property on `ModuleCat.{u} R` cutting out the invertible `R`-modules. -/
def invertibleModules (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.Invertible R M

/-- An object of `ModuleCat.{u} R` satisfies `invertibleModules R` precisely when its underlying
module is invertible. -/
@[simp]
theorem invertibleModules_iff (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    invertibleModules R M ↔ Module.Invertible R M :=
  Iff.rfl

/-- Invertible `R`-modules are closed under isomorphism in `ModuleCat.{u} R`. -/
instance {R : Type u} [CommRing R] : (invertibleModules R).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    rw [invertibleModules_iff] at hM ⊢
    exact Module.Invertible.congr e.toLinearEquiv

/-- Every invertible `R`-module is finitely generated and projective. -/
theorem invertibleModules_le_finiteProjectiveModules (R : Type u) [CommRing R] :
    invertibleModules R ≤ finiteProjectiveModules R := by
  intro M hM
  let A : Type u := M
  have : Module.Invertible R A := (invertibleModules_iff R M).mp hM
  exact finiteProjectiveModules_iff.mpr
    ⟨inferInstanceAs (Module.Finite R A), inferInstanceAs (Module.Projective R A)⟩

/-- Invertible modules contain the regular module `R` and are closed under tensor products. -/
instance invertibleModules_isMonoidal (R : Type u) [CommRing R] :
    (invertibleModules R).IsMonoidal where
  prop_unit := (invertibleModules_iff R _).mpr (inferInstanceAs (Module.Invertible R R))
  prop_tensor M N hM hN := by
    have : Module.Invertible R M := (invertibleModules_iff R M).mp hM
    have : Module.Invertible R N := (invertibleModules_iff R N).mp hN
    exact (invertibleModules_iff R _).mpr (inferInstanceAs (Module.Invertible R (M ⊗[R] N)))

namespace InvertibleModules

section Basic

variable (R : Type u) [CommRing R]

variable {R} in
/-- The underlying `R`-module of an object in `(invertibleModules R).FullSubcategory` is
invertible. -/
instance invertible_obj (M : (invertibleModules R).FullSubcategory) :
    Module.Invertible R M.obj :=
  (invertibleModules_iff R M.obj).mp M.property

/-- The fully faithful braided monoidal inclusion of invertible `R`-modules into finite projective
`R`-modules. -/
abbrev toFiniteProjective :
    (invertibleModules R).FullSubcategory ⥤ (finiteProjectiveModules R).FullSubcategory :=
  ObjectProperty.ιOfLE (invertibleModules_le_finiteProjectiveModules R)

-- Exposed so that morphisms into and out of `(dual R M).obj` have domain and codomain
-- `ModuleCat.of R (Module.Dual R M.obj)`, matching `FiniteProjectiveModules.dual`.
/-- The linear dual of an invertible `R`-module, as an object of
`(invertibleModules R).FullSubcategory`. -/
@[expose]
def dual (M : (invertibleModules R).FullSubcategory) :
    (invertibleModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Module.Dual R M.obj), (invertibleModules_iff R _).mpr inferInstance⟩

/-- The underlying `R`-module of `dual R M` is `Module.Dual R M.obj`. -/
@[simp]
theorem dual_obj (M : (invertibleModules R).FullSubcategory) :
    (dual R M).obj = ModuleCat.of R (Module.Dual R M.obj) :=
  (rfl)

/-- Including into finite projective modules commutes with linear dualization. -/
@[simp]
theorem toFiniteProjective_obj_dual (M : (invertibleModules R).FullSubcategory) :
    (toFiniteProjective R).obj (dual R M) =
      FiniteProjectiveModules.dual R ((toFiniteProjective R).obj M) :=
  (rfl)

/-- A morphism of invertible modules induces the transpose morphism between their duals. -/
def dualMap {M N : (invertibleModules R).FullSubcategory} (f : M ⟶ N) :
    dual R N ⟶ dual R M :=
  ObjectProperty.homMk (ModuleCat.ofHom f.hom.hom.dualMap)

/-- On underlying modules, `dualMap R f` is the linear transpose `f.dualMap`. -/
@[simp]
theorem dualMap_hom {M N : (invertibleModules R).FullSubcategory} (f : M ⟶ N) :
    (dualMap R f).hom = ModuleCat.ofHom f.hom.hom.dualMap :=
  (rfl)

-- Exposed so `(dualFunctor R).obj M` reduces to `dual R M.unop` in morphism types, matching
-- `FiniteProjectiveModules.dualFunctor`.
/-- Linear dualization as a contravariant endofunctor on invertible `R`-modules. -/
@[expose]
def dualFunctor :
    ((invertibleModules R).FullSubcategory)ᵒᵖ ⥤ (invertibleModules R).FullSubcategory where
  obj M := dual R M.unop
  map f := dualMap R f.unop
  map_id _ := by
    apply ObjectProperty.hom_ext
    ext φ
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    ext φ
    rfl

/-- `dualFunctor R` acts on objects by `dual R`. -/
@[simp]
theorem dualFunctor_obj (M : ((invertibleModules R).FullSubcategory)ᵒᵖ) :
    (dualFunctor R).obj M = dual R M.unop :=
  (rfl)

/-- `dualFunctor R` acts on morphisms by `dualMap R`. -/
@[simp]
theorem dualFunctor_map {M N : ((invertibleModules R).FullSubcategory)ᵒᵖ} (f : M ⟶ N) :
    (dualFunctor R).map f = dualMap R f.unop :=
  (rfl)

/-- An invertible module is canonically isomorphic to its double dual. -/
noncomputable def evalIso (M : (invertibleModules R).FullSubcategory) :
    M ≅ dual R (dual R M) :=
  ObjectProperty.isoMk (invertibleModules R) (Module.evalEquiv R M.obj).toModuleIso

/-- On underlying modules, `evalIso R M` is `Module.evalEquiv R M.obj`. -/
@[simp]
theorem evalIso_hom_hom (M : (invertibleModules R).FullSubcategory) :
    (evalIso R M).hom.hom = (Module.evalEquiv R M.obj).toModuleIso.hom :=
  (rfl)

/-- The double-dual isomorphism is natural in the invertible module. -/
@[reassoc]
theorem evalIso_naturality {M N : (invertibleModules R).FullSubcategory} (f : M ⟶ N) :
    f ≫ (evalIso R N).hom = (evalIso R M).hom ≫ dualMap R (dualMap R f) := by
  apply ObjectProperty.hom_ext
  ext m
  rfl

/-- Contraction identifies `Mᵛ ⊗ M` with the monoidal unit `R` in the category of invertible
`R`-modules. -/
noncomputable def contractIso (M : (invertibleModules R).FullSubcategory) :
    dual R M ⊗ M ≅ 𝟙_ (invertibleModules R).FullSubcategory :=
  ObjectProperty.isoMk (invertibleModules R)
    (Module.Invertible.linearEquiv R M.obj).toModuleIso

/-- On underlying modules, `contractIso R M` is `Module.Invertible.linearEquiv R M.obj`. -/
@[simp]
theorem contractIso_hom_hom (M : (invertibleModules R).FullSubcategory) :
    (contractIso R M).hom.hom = (Module.Invertible.linearEquiv R M.obj).toModuleIso.hom :=
  (rfl)

end Basic

section ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

-- Exposed so `((extendScalars f).obj M).obj` reduces to `(ModuleCat.extendScalars f).obj M.obj`
-- in base-change morphism and isomorphism types.
/-- Extension of scalars along a ring homomorphism `f : R →+* S`, as a functor between categories
of invertible modules. -/
@[expose]
noncomputable def extendScalars :
    (invertibleModules R).FullSubcategory ⥤ (invertibleModules S).FullSubcategory :=
  (invertibleModules S).lift
    ((invertibleModules R).ι ⋙ ModuleCat.extendScalars f)
    fun M ↦ (invertibleModules_iff S _).mpr (ModuleCat.invertible_extendScalars_obj f M.obj)

/-- The underlying `S`-module of `(extendScalars f).obj M` is
`(ModuleCat.extendScalars f).obj M.obj`. -/
@[simp]
theorem extendScalars_obj_obj (M : (invertibleModules R).FullSubcategory) :
    ((extendScalars f).obj M).obj = (ModuleCat.extendScalars f).obj M.obj :=
  (rfl)

/-- `extendScalars f` acts on morphisms by `ModuleCat.extendScalars f`. -/
@[simp]
theorem extendScalars_map_hom {M N : (invertibleModules R).FullSubcategory} (g : M ⟶ N) :
    ((extendScalars f).map g).hom = (ModuleCat.extendScalars f).map g.hom :=
  (rfl)

end ExtendScalars

section Picard

variable (R : Type u) [CommRing R]

/-- A representative of `Skeleton (invertibleModules R).FullSubcategory` associated with a class in
`CommRing.Pic R`. -/
noncomputable def ofPic (P : CommRing.Pic R) : (invertibleModules R).FullSubcategory :=
  ⟨ModuleCat.of R P, (invertibleModules_iff R _).mpr inferInstance⟩

/-- The underlying module of `ofPic R P` is `ModuleCat.of R P`. -/
@[simp]
theorem ofPic_obj (P : CommRing.Pic R) : (ofPic R P).obj = ModuleCat.of R P :=
  (rfl)

/-- Every invertible `R`-module is isomorphic to `ofPic R` of its Picard class. -/
noncomputable def ofPicMkIso (M : (invertibleModules R).FullSubcategory) :
    ofPic R (CommRing.Pic.mk R M.obj) ≅ M :=
  ObjectProperty.isoMk (invertibleModules R)
    (eqToIso (ofPic_obj R _) ≪≫ (CommRing.Pic.mk.linearEquiv R M.obj).toModuleIso)

/-- The multiplicative equivalence between the skeleton of the category of invertible `R`-modules
and Mathlib's Picard group `CommRing.Pic R`, sending the isomorphism class of `M` to
`CommRing.Pic.mk R M.obj` and a Picard class `P` to the class of `ofPic R P`. -/
noncomputable def skeletonEquivPic :
    Skeleton (invertibleModules R).FullSubcategory ≃* CommRing.Pic R where
  toFun := (invertibleModules R).skeletonLift
    (fun M ↦ CommRing.Pic.mk R M.obj)
    (fun _ _ ⟨e⟩ ↦ CommRing.Pic.mk_eq_mk_iff.mpr ⟨e.toLinearEquiv⟩)
  invFun P := toSkeleton (ofPic R P)
  left_inv x := by
    obtain ⟨M, rfl⟩ : ∃ M, toSkeleton M = x := Quotient.inductionOn x fun M ↦ ⟨M, rfl⟩
    rw [ObjectProperty.skeletonLift_toSkeleton]
    exact toSkeleton_eq_toSkeleton_iff.mpr ⟨ofPicMkIso R M⟩
  right_inv P := by
    rw [ObjectProperty.skeletonLift_toSkeleton, CommRing.Pic.mk_eq_iff]
    exact ⟨(eqToIso (ofPic_obj R P)).toLinearEquiv⟩
  map_mul' x y := by
    obtain ⟨M, rfl⟩ : ∃ M, toSkeleton M = x := Quotient.inductionOn x fun M ↦ ⟨M, rfl⟩
    obtain ⟨N, rfl⟩ : ∃ N, toSkeleton N = y := Quotient.inductionOn y fun N ↦ ⟨N, rfl⟩
    rw [← Skeleton.toSkeleton_tensorObj, ObjectProperty.skeletonLift_toSkeleton,
      ObjectProperty.skeletonLift_toSkeleton, ObjectProperty.skeletonLift_toSkeleton]
    exact CommRing.Pic.mk_tensor

/-- `skeletonEquivPic R` sends the skeleton class of an invertible module `M` to
`CommRing.Pic.mk R M.obj`. -/
@[simp]
theorem skeletonEquivPic_toSkeleton (M : (invertibleModules R).FullSubcategory) :
    skeletonEquivPic R (toSkeleton M) = CommRing.Pic.mk R M.obj :=
  ObjectProperty.skeletonLift_toSkeleton _ M

/-- The inverse of `skeletonEquivPic R` sends a Picard class `P` to `toSkeleton (ofPic R P)`. -/
theorem skeletonEquivPic_symm_apply (P : CommRing.Pic R) :
    (skeletonEquivPic R).symm P = toSkeleton (ofPic R P) :=
  (rfl)

/-- The inverse of `skeletonEquivPic R` sends `CommRing.Pic.mk R M` to the skeleton class of
`ModuleCat.of R M`. -/
@[simp]
theorem skeletonEquivPic_symm_mk (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Invertible R M] :
    (skeletonEquivPic R).symm (CommRing.Pic.mk R M) =
      toSkeleton ⟨ModuleCat.of R M, (invertibleModules_iff R _).mpr ‹_›⟩ := by
  refine (skeletonEquivPic R).symm_apply_eq.mpr ((skeletonEquivPic_toSkeleton R _).trans ?_).symm
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨LinearEquiv.refl R M⟩

/-- `skeletonEquivPic R` sends the class of `M` to `P` if and only if `M.obj` is isomorphic to
`ModuleCat.of R P`. -/
theorem skeletonEquivPic_toSkeleton_eq_iff (M : (invertibleModules R).FullSubcategory)
    (P : CommRing.Pic R) :
    skeletonEquivPic R (toSkeleton M) = P ↔ Nonempty (M.obj ≅ ModuleCat.of R P) := by
  rw [skeletonEquivPic_toSkeleton, CommRing.Pic.mk_eq_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨e.toModuleIso⟩, fun ⟨e⟩ ↦ ⟨e.toLinearEquiv⟩⟩

/-- `skeletonEquivPic` intertwines extension of scalars on invertible modules with
`CommRing.Pic.mapRingHom`. -/
@[simp]
theorem skeletonEquivPic_extendScalars_mapSkeleton {S : Type u} [CommRing S] (f : R →+* S)
    (x : Skeleton (invertibleModules R).FullSubcategory) :
    skeletonEquivPic S ((extendScalars f).mapSkeleton.obj x) =
      CommRing.Pic.mapRingHom f (skeletonEquivPic R x) := by
  obtain ⟨M, rfl⟩ : ∃ M, toSkeleton M = x := Quotient.inductionOn x fun M ↦ ⟨M, rfl⟩
  let _ : Algebra R S := f.toAlgebra
  have hf : f = algebraMap R S := rfl
  rw [Functor.mapSkeleton_obj_toSkeleton, skeletonEquivPic_toSkeleton,
    skeletonEquivPic_toSkeleton, hf, CommRing.Pic.mapRingHom_algebraMap,
    CommRing.Pic.mapAlgebra_apply]
  exact CommRing.Pic.mk_eq_mk_iff.mpr
    ⟨(eqToIso (extendScalars_obj_obj (algebraMap R S) M)).toLinearEquiv ≪≫ₗ
      (ModuleCat.extendScalarsAlgebraMapIso (R := R) (S := S) M.obj).toLinearEquiv ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
        (CommRing.Pic.mk.linearEquiv R M.obj).symm⟩

end Picard

end InvertibleModules

end TauCeti
