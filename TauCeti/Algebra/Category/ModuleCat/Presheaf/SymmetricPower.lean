/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower

/-!
# Symmetric powers of presheaves of modules

Let `R` be a presheaf of commutative rings on a category `C`. For a presheaf of `R`-modules `M`
and `n : ℕ`, the `n`-th symmetric power of `M` is the presheaf of modules whose sections over `X`
are the symmetric power `(M.obj X).symmetricPower n` (`ModuleCat.symmetricPower`, the degree-`n`
part of the symmetric algebra of `M.obj X`), and whose restriction along `f : X ⟶ Y` sends a
product `m₁ ⋯ mₙ` to `M.map f m₁ ⋯ M.map f mₙ`. The restriction maps are induced by the
semilinear restriction maps of `M` through `SymmetricAlgebra.mapₛₗ`. This is the presheaf-level
input to symmetric powers of sheaves of modules, which are obtained by sheafification. As for
Mathlib's monoidal structure on these presheaves of modules
(`PresheafOfModulesOfCommRing.monoidalCategoryStruct`), modules are taken in the universe of the
rings.

## Main declarations

* `PresheafOfModulesOfCommRing.symmetricPower n` is the `n`-th symmetric power, as an
  endofunctor of presheaves of `R`-modules; `symmetricPower_obj_obj`,
  `coe_symmetricPower_obj_map_apply` and `symmetricPower_map_app` compute its sections,
  restriction maps and action on morphisms;
* `PresheafOfModulesOfCommRing.symmetricPowerZeroIso` identifies the zeroth symmetric power
  with the constant functor at the unit presheaf of modules `R`;
* `PresheafOfModulesOfCommRing.symmetricPowerOneIso` identifies the first symmetric power
  with the identity functor.
-/

public section

open CategoryTheory

universe u v w

noncomputable section

namespace PresheafOfModulesOfCommRing

open TauCeti.SymmetricAlgebra (homogeneousSubmoduleMapₛₗ)

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Auxiliary definition for `symmetricPower`: the restriction maps of the symmetric power of a
presheaf of modules, induced on degree-`n` parts of symmetric algebras by the semilinear
restriction map of the presheaf. -/
def symmetricPowerObjMap (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) :
    (M.obj X).symmetricPower n ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj Y).symmetricPower n) :=
  ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _ (homogeneousSubmoduleMapₛₗ
    ((ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _).symm (M.map f)) n)

/-- The restriction maps of the symmetric power are computed in the symmetric algebra by the
ring homomorphism induced by the restriction map of the presheaf. -/
lemma coe_symmetricPowerObjMap_apply (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (M.obj X).symmetricPower n) :
    Subtype.val (symmetricPowerObjMap M n f x) =
      SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _).symm
        (M.map f)) x.1 :=
  TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n x

/-- Auxiliary definition for `symmetricPower`: the symmetric power of a presheaf of modules. -/
@[expose]
def symmetricPowerObj (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    PresheafOfModulesOfCommRing.{u} R :=
  PresheafOfModulesOfCommRing.mk (fun X ↦ (M.obj X).symmetricPower n)
    (fun f ↦ symmetricPowerObjMap M n f)
    (fun X ↦ by
      ext x
      apply Subtype.ext
      rw [coe_symmetricPowerObjMap_apply]
      rw [SymmetricAlgebra.mapₛₗ_eq_id (fun r ↦ by simp) (fun m ↦ by simp)]
      rfl)
    (fun {_ _ Z} f g ↦ by
      ext x
      apply Subtype.ext
      rw [coe_symmetricPowerObjMap_apply]
      rw [← SymmetricAlgebra.mapₛₗ_comp_mapₛₗ
        ((ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _).symm (M.map f))
        ((ModuleCat.semilinearMapAddEquiv (R.map g).hom _ _).symm (M.map g))
        ((ModuleCat.semilinearMapAddEquiv (R.map (f ≫ g)).hom _ _).symm (M.map (f ≫ g)))
        (fun r ↦ by simp) (fun m ↦ (M.map_comp_apply f g m).symm)]
      rw [RingHom.comp_apply, ← coe_symmetricPowerObjMap_apply M n f x]
      -- the right-hand side is the composite `symmetricPowerObjMap M n g` after
      -- `symmetricPowerObjMap M n f`; the restriction-of-scalars maps are identities on elements
      exact (coe_symmetricPowerObjMap_apply M n g _).symm)

/-- The restriction maps of the symmetric power are natural in the presheaf of modules. -/
lemma symmetricPowerObjMap_naturality {M N : PresheafOfModulesOfCommRing.{u} R} (φ : M ⟶ N)
    (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    symmetricPowerObjMap M n f ≫ (ModuleCat.restrictScalars (R.map f).hom).map
        (ModuleCat.symmetricPower.map (φ.app' Y) n) =
      ModuleCat.symmetricPower.map (φ.app' X) n ≫ symmetricPowerObjMap N n f := by
  have key : (SymmetricAlgebra.map (R.obj Y) (φ.app' Y).hom : _ →+* _).comp
      (SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _).symm
        (M.map f))) =
      (SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _).symm
        (N.map f))).comp (SymmetricAlgebra.map (R.obj X) (φ.app' X).hom : _ →+* _) :=
    SymmetricAlgebra.ringHom_ext (fun r ↦ by simp) (fun m ↦ by
      simp only [RingHom.coe_coe, SymmetricAlgebra.map_apply_ι, SymmetricAlgebra.mapₛₗ_ι,
        RingHom.comp_apply]
      exact congrArg (SymmetricAlgebra.ι _ _) (naturality_apply φ f m))
  ext x
  apply Subtype.ext
  -- both sides are composites of the maps of symmetric algebras compared by `key`; the
  -- restriction-of-scalars map is the identity on elements
  exact ((ModuleCat.symmetricPower.coe_map_apply _ n _).trans
    (congrArg _ (coe_symmetricPowerObjMap_apply M n f x))).trans
      ((RingHom.congr_fun key x.1).trans
        ((congrArg _ (ModuleCat.symmetricPower.coe_map_apply _ n x).symm).trans
          (coe_symmetricPowerObjMap_apply N n f _).symm))

/-- The `n`-th symmetric power of presheaves of modules over a presheaf of commutative rings,
computed sectionwise: its sections over `X` are `(M.obj X).symmetricPower n`, and its restriction
maps send a product `m₁ ⋯ mₙ` to the product of the restrictions of the `mᵢ`. -/
@[expose]
def symmetricPower (n : ℕ) :
    PresheafOfModulesOfCommRing.{u} R ⥤ PresheafOfModulesOfCommRing.{u} R where
  obj M := symmetricPowerObj M n
  map φ := PresheafOfModulesOfCommRing.homMk
    (fun X ↦ ModuleCat.symmetricPower.map (φ.app' X) n)
    (fun f ↦ symmetricPowerObjMap_naturality φ n f)
  map_id M := by
    ext X : 1
    exact (ModuleCat.symmetricPower.functor _ n).map_id (M.obj X)
  map_comp φ ψ := by
    ext X : 1
    exact (ModuleCat.symmetricPower.functor _ n).map_comp (φ.app' X) (ψ.app' X)

/-- The sections of the symmetric power over `X` are the symmetric power of the sections. -/
lemma symmetricPower_obj_obj (n : ℕ) (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((symmetricPower n).obj M).obj X = (M.obj X).symmetricPower n :=
  rfl

/-- The restriction maps of the symmetric power are computed in the symmetric algebra by the
ring homomorphism induced by the restriction map of the presheaf, which sends the generator of
`m` to the generator of its restriction (`SymmetricAlgebra.mapₛₗ_ι`). -/
@[simp]
lemma coe_symmetricPower_obj_map_apply (n : ℕ) (M : PresheafOfModulesOfCommRing.{u} R)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (M.obj X).symmetricPower n) :
    Subtype.val (((symmetricPower n).obj M).map f x) =
      SymmetricAlgebra.mapₛₗ ((ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _).symm
        (M.map f)) x.1 :=
  coe_symmetricPowerObjMap_apply M n f x

/-- The symmetric power of a morphism is computed sectionwise. -/
@[simp]
lemma symmetricPower_map_app (n : ℕ) {M N : PresheafOfModulesOfCommRing.{u} R} (φ : M ⟶ N)
    (X : Cᵒᵖ) :
    ((symmetricPower n).map φ).app X = ModuleCat.symmetricPower.map (φ.app' X) n :=
  rfl

variable (R) in
/-- The zeroth symmetric power of a presheaf of `R`-modules is the unit presheaf of modules `R`,
naturally; on sections it is `ModuleCat.symmetricPower.iso₀`. -/
def symmetricPowerZeroIso :
    symmetricPower (R := R) 0 ≅ (Functor.const _).obj (PresheafOfModulesOfCommRing.unit R) :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModulesOfCommRing.isoMk
      (fun X ↦ ModuleCat.symmetricPower.iso₀ (M.obj X))
      (fun X Y f ↦ by
        ext x
        apply (SymmetricAlgebra.algebraMap_leftInverse (R := R.obj Y) (M.obj Y)).injective
        -- both sides are the image of the restricted scalar in the symmetric algebra
        exact (ModuleCat.symmetricPower.algebraMap_iso₀_hom_apply _ _).trans
          ((coe_symmetricPowerObjMap_apply M 0 f x).trans
            ((congrArg (SymmetricAlgebra.mapₛₗ _)
              (ModuleCat.symmetricPower.algebraMap_iso₀_hom_apply _ x).symm).trans
                (SymmetricAlgebra.mapₛₗ_algebraMap _ _)))))
    (fun φ ↦ by
      ext X : 1
      exact ModuleCat.symmetricPower.iso₀_hom_naturality (φ.app' X))

@[simp]
lemma symmetricPowerZeroIso_hom_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((symmetricPowerZeroIso R).hom.app M).app X =
      (ModuleCat.symmetricPower.iso₀ (M.obj X)).hom :=
  (rfl)

@[simp]
lemma symmetricPowerZeroIso_inv_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((symmetricPowerZeroIso R).inv.app M).app X =
      (ModuleCat.symmetricPower.iso₀ (M.obj X)).inv :=
  (rfl)

variable (R) in
/-- The first symmetric power of a presheaf of `R`-modules is the presheaf of modules itself,
naturally; on sections it is `ModuleCat.symmetricPower.iso₁`. -/
def symmetricPowerOneIso : symmetricPower (R := R) 1 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModulesOfCommRing.isoMk
      (fun X ↦ ModuleCat.symmetricPower.iso₁ (M.obj X))
      (fun X Y f ↦ by
        ext x
        apply TauCeti.SymmetricAlgebra.ι_injective (R.obj Y) (M.obj Y)
        -- both sides are the generator of the restricted element in the symmetric algebra
        exact (ModuleCat.symmetricPower.ι_iso₁_hom_apply _ _).trans
          ((coe_symmetricPowerObjMap_apply M 1 f x).trans
            ((congrArg (SymmetricAlgebra.mapₛₗ _)
              (ModuleCat.symmetricPower.ι_iso₁_hom_apply _ x).symm).trans
                (SymmetricAlgebra.mapₛₗ_ι _ _)))))
    (fun φ ↦ by
      ext X : 1
      exact ModuleCat.symmetricPower.iso₁_hom_naturality (φ.app' X))

@[simp]
lemma symmetricPowerOneIso_hom_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((symmetricPowerOneIso R).hom.app M).app X = (ModuleCat.symmetricPower.iso₁ (M.obj X)).hom :=
  (rfl)

@[simp]
lemma symmetricPowerOneIso_inv_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((symmetricPowerOneIso R).inv.app M).app X = (ModuleCat.symmetricPower.iso₁ (M.obj X)).inv :=
  (rfl)

end PresheafOfModulesOfCommRing

end
