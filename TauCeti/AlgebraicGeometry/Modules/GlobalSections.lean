/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Global-functions actions on sheaves of modules

This file constructs the canonical action of the ring of global functions on a sheaf of modules
on a scheme, shows that multiplication by a global unit is an isomorphism, and records how the
action is carried along a morphism of schemes `f : X ⟶ Y`: pushing forward multiplication by
`f^♯ r` is multiplication by `r`, and pulling back multiplication by `r` is multiplication by
`f^♯ r` (`Scheme.Modules.pushforward_map_globalSectionsSmul` and
`Scheme.Modules.pullback_map_globalSectionsSmul`). It also records the restriction of this
action to the base ring for a scheme over a commutative ring, and the morphism
`Scheme.baseRingToStructurePresheaf` from the constant presheaf of the base ring to the structure
presheaf, which on the whole scheme is the base-ring map to global functions
(`AlgebraicGeometry.Scheme.baseRingToStructurePresheaf_app_top`). The sections of the structure
sheaf over the whole scheme are identified base-linearly with global functions by
`Scheme.Modules.structureSheafSectionsBaseLinearEquiv`. Pullback of local functions by a morphism
over the base preserves these images
(`AlgebraicGeometry.Scheme.Modules.app_baseRingToStructurePresheaf`).

In a commuting square
over `Spec S ⟶ Spec R`, `Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_app` gives
the compatible base-ring actions on coordinate rings. For a cartesian square and an affine
open, `Scheme.isPushout_baseRingToStructurePresheaf_of_isAffineOpen` identifies those rings
as the pushout over the original base rings.

These constructions are independent of sheaf cohomology. They supply the scalar actions used by
`TauCeti.AlgebraicGeometry.Cohomology.Module.Basic`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The restriction of a global function to an open subset. -/
private def restrictGlobal (U : X.Opens) (r : Γ(X, ⊤)) :
    X.ringCatSheaf.obj.obj (.op U) :=
  X.presheaf.map (homOfLE le_top).op r

/-- Multiplication by a global function, as a morphism of sheaves of modules. -/
def globalSectionsSmul
    (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M where
  val.app U := by
    letI : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    exact ModuleCat.ofHom <|
      LinearMap.lsmul (X.ringCatSheaf.obj.obj U) (M.val.obj U) (restrictGlobal U.unop r)
  val.naturality {U V} f := by
    let : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    let : CommRing (X.ringCatSheaf.obj.obj V) :=
      inferInstanceAs (CommRing (X.presheaf.obj V))
    ext x
    dsimp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.lsmul_apply]
    rw [M.val.map_smul]
    -- The restriction-of-scalars wrapper is transparent but has no lemma exposing this
    -- pointwise goal, so normalize it to the presheaf action explicitly.
    change restrictGlobal V.unop r • M.val.map f x =
      X.ringCatSheaf.obj.map f (restrictGlobal U.unop r) • M.val.map f x
    congr 1
    change X.presheaf.map (homOfLE le_top).op r =
      X.presheaf.map f (X.presheaf.map (homOfLE le_top).op r)
    rw [← Functor.map_comp_apply]
    congr

@[simp]
lemma globalSectionsSmul_app
    (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) :
    (globalSectionsSmul M r).app U = (M.smul (X.presheaf.map U.leTop.op r)).asHom := by
  rfl

-- In the next four proofs, sheaf-morphism extensionality leaves pointwise bundled-module goals.
-- The wrappers have no pointwise equality lemmas, so each `change` records the corresponding
-- public presheaf/module formulation before applying the ring and module laws.
@[simp]
lemma globalSectionsSmul_zero
    (M : X.Modules) : globalSectionsSmul M 0 = 0 := by
  ext U x
  change X.presheaf.map U.leTop.op 0 • x = 0
  simp

@[simp]
lemma globalSectionsSmul_add
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r + s) = globalSectionsSmul M r + globalSectionsSmul M s := by
  ext U x
  change X.presheaf.map U.leTop.op (r + s) • x =
    X.presheaf.map U.leTop.op r • x +
      X.presheaf.map U.leTop.op s • x
  simp [add_smul]

@[simp]
lemma globalSectionsSmul_one
    (M : X.Modules) : globalSectionsSmul M 1 = 𝟙 M := by
  ext U x
  change X.presheaf.map U.leTop.op 1 • x = x
  simp

@[simp]
lemma globalSectionsSmul_mul
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r * s) = globalSectionsSmul M s ≫ globalSectionsSmul M r := by
  ext U x
  change X.presheaf.map U.leTop.op (r * s) • x =
    X.presheaf.map U.leTop.op r •
      X.presheaf.map U.leTop.op s • x
  rw [map_mul, mul_smul]

/-- Multiplication by a global unit is an isomorphism, with inverse multiplication by the inverse
unit. -/
instance isIso_globalSectionsSmul_units
    (M : X.Modules) (u : Γ(X, ⊤)ˣ) : IsIso (globalSectionsSmul M u) :=
  ⟨globalSectionsSmul M ↑u⁻¹,
    by rw [← globalSectionsSmul_mul, Units.inv_mul, globalSectionsSmul_one],
    by rw [← globalSectionsSmul_mul, Units.mul_inv, globalSectionsSmul_one]⟩

/-- The action of global functions on a sheaf of modules, bundled as a ring homomorphism into
the endomorphism ring of the sheaf. -/
def globalSectionsAction
    (M : X.Modules) : Γ(X, ⊤) →+* End M where
  toFun r := .of (globalSectionsSmul M r)
  map_one' := End.ext (globalSectionsSmul_one M)
  map_mul' := fun r s ↦ by
    apply End.ext
    exact globalSectionsSmul_mul M r s
  map_zero' := End.ext (globalSectionsSmul_zero M)
  map_add' := fun r s ↦ End.ext (globalSectionsSmul_add M r s)

@[simp]
lemma globalSectionsAction_apply
    (M : X.Modules) (r : Γ(X, ⊤)) :
    globalSectionsAction M r = End.of (globalSectionsSmul M r) :=
  by rfl

/-- Multiplication by a global function is natural in the sheaf of modules. -/
@[reassoc]
lemma globalSectionsSmul_naturality
    (f : M ⟶ N) (r : Γ(X, ⊤)) :
    globalSectionsSmul M r ≫ f = f ≫ globalSectionsSmul N r := by
  ext U x
  -- As above, extensionality exposes the underlying bundled maps only definitionally.
  change f.app U (X.presheaf.map U.leTop.op r • x) =
    X.presheaf.map U.leTop.op r • f.app U x
  exact f.app_smul _ _

section Functoriality

variable {Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pushing forward multiplication by the pullback `f^♯ r` of a global function `r` on `Y` gives
multiplication by `r` on the pushforward. -/
@[simp]
lemma pushforward_map_globalSectionsSmul
    (N : X.Modules) (r : Γ(Y, ⊤)) :
    (pushforward f).map (globalSectionsSmul N (f.appTop r)) =
      globalSectionsSmul ((pushforward f).obj N) r := by
  refine hom_ext _ _ fun U ↦ ?_
  rw [pushforward_map_app, globalSectionsSmul_app, globalSectionsSmul_app]
  -- The sections of the pushforward over `U` are the sections of `N` over `f ⁻¹ᵁ U`, with scalars
  -- restricted along `f.app U`; no lemma exposes this, so record it explicitly.
  ext x
  change X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop r) • x =
    f.app U (Y.presheaf.map U.leTop.op r) • x
  congr 1
  exact (ConcreteCategory.comp_apply _ _ r).symm.trans
    (congrArg (· r) (f.naturality U.leTop.op)).symm

/-- Pulling back multiplication by a global function `r` on `Y` gives multiplication by the
pullback `f^♯ r` of `r` on the pullback. -/
@[simp]
lemma pullback_map_globalSectionsSmul
    (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (pullback f).map (globalSectionsSmul M r) =
      globalSectionsSmul ((pullback f).obj M) (f.appTop r) := by
  -- Both sides are determined by their adjuncts `M ⟶ f_* f^* M`, which agree by naturality of
  -- the unit and of the global-functions action.
  apply ((pullbackPushforwardAdjunction f).homEquiv M
    ((pullback f).obj M)).injective
  simp only [Adjunction.homEquiv_apply, pushforward_map_globalSectionsSmul]
  exact ((pullbackPushforwardAdjunction f).unit.naturality (globalSectionsSmul M r)).symm.trans
    (globalSectionsSmul_naturality ((pullbackPushforwardAdjunction f).unit.app M) r)

end Functoriality

end AlgebraicGeometry.Scheme.Modules

section Base

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

namespace AlgebraicGeometry.Scheme.Modules

/-- The homomorphism from the base ring to global functions on a scheme over that ring. -/
def baseRingToGlobalSections : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop).hom

/-- The base ring acts through the pullback along the structure morphism: `r` is sent to the
global function obtained by pulling back the function on `Spec R` corresponding to `r`. -/
@[simp]
lemma baseRingToGlobalSections_apply (r : R) :
    baseRingToGlobalSections R X r =
      (X ↘ Spec (.of R)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) :=
  (rfl)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The morphism from the constant presheaf of rings `R` to the structure presheaf of a scheme
over `R`: on an open `U` it is the base ring map to global functions followed by restriction
to `U`. -/
def baseRingToStructurePresheaf :
    (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of R) ⟶ X.presheaf where
  app U := CommRingCat.ofHom (Modules.baseRingToGlobalSections R X) ≫
    X.presheaf.map U.unop.leTop.op
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    rfl

/-- On an open `U`, the base ring maps to sections over `U` through global functions followed by
restriction to `U`. -/
@[simp]
lemma baseRingToStructurePresheaf_app (U : X.Opensᵒᵖ) :
    (X.baseRingToStructurePresheaf R).app U =
      CommRingCat.ofHom (Modules.baseRingToGlobalSections R X) ≫
        X.presheaf.map U.unop.leTop.op :=
  (rfl)

/-- On an open `U`, the base-ring map `R → Γ(X, U)` is the composite of `R ≅ Γ(Spec R, ⊤)` with
the map on functions induced by the structure morphism. -/
lemma baseRingToStructurePresheaf_app_eq_appLE (U : X.Opens) :
    (X.baseRingToStructurePresheaf R).app (op U) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appLE ⊤ U le_top := by
  ext r
  rw [baseRingToStructurePresheaf_app, CommRingCat.comp_apply, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply, Modules.baseRingToGlobalSections_apply]
  -- Both sides restrict the pullback of `r` from `⊤` to `U`; `appLE ⊤ U` is by definition
  -- `app ⊤` followed by that restriction.
  rfl

/-- On the whole scheme, the base-ring map to sections is `baseRingToGlobalSections`. -/
lemma baseRingToStructurePresheaf_app_top :
    (X.baseRingToStructurePresheaf R).app (op ⊤) =
      CommRingCat.ofHom (Modules.baseRingToGlobalSections R X) := by
  rw [baseRingToStructurePresheaf_app, Subsingleton.elim (unop (op (⊤ : X.Opens))).leTop.op (𝟙 _),
    X.presheaf.map_id]
  exact Category.comp_id _

variable {R} in
/-- Compatible structure morphisms make the actions of the two base rings on sections
into a scalar tower. -/
theorem baseRingToStructurePresheaf_app_algebraMap
    {S : Type u} [CommRing S] [Algebra R S] [X.Over (Spec (.of S))]
    (h : (X ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      (X ↘ Spec (.of R))) (U : X.Opens) (r : R) :
    (X.baseRingToStructurePresheaf S).app (op U) (algebraMap R S r) =
      (X.baseRingToStructurePresheaf R).app (op U) r := by
  have htop := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at htop
  have hΓ : CommRingCat.ofHom (algebraMap R S) ≫ (Scheme.ΓSpecIso (.of S)).inv ≫
      (X ↘ Spec (.of S)).appTop =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, htop]
  rw [Scheme.baseRingToStructurePresheaf_app, Scheme.baseRingToStructurePresheaf_app,
    CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.ofHom_apply,
    CommRingCat.ofHom_apply, Scheme.Modules.baseRingToGlobalSections_apply,
    Scheme.Modules.baseRingToGlobalSections_apply]
  -- The base-ring maps use global sections followed by restriction to `U`.
  exact congrArg (fun a ↦ X.presheaf.map U.leTop.op a)
    (ConcreteCategory.congr_hom hΓ r)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X} in
/-- Pullback of local functions along a morphism over `Spec R` preserves the image of the
base ring. -/
lemma app_baseRingToStructurePresheaf {Y : Scheme.{u}} [Y.Over (Spec (.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (U : Y.Opens) (r : R) :
    f.app U ((Y.baseRingToStructurePresheaf R).app (op U) r) =
      (X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U)) r := by
  rw [Scheme.baseRingToStructurePresheaf_app, Scheme.baseRingToStructurePresheaf_app]
  -- The maps obtained from `CommRingCat.ofHom` compute through their bundled ring homs.
  change f.app U (Y.presheaf.map U.leTop.op (baseRingToGlobalSections R Y r)) =
    X.presheaf.map (f ⁻¹ᵁ U).leTop.op (baseRingToGlobalSections R X r)
  rw [← ConcreteCategory.comp_apply, f.naturality U.leTop.op]
  have h := congrArg Scheme.Hom.appTop
    (HomIsOver.comp_over (f := f) (S := Spec (.of R)))
  rw [Scheme.Hom.comp_appTop] at h
  rw [ConcreteCategory.comp_apply, baseRingToGlobalSections_apply,
    baseRingToGlobalSections_apply, ← h, ConcreteCategory.comp_apply]
  rfl

/-- Global sections of a sheaf of modules on a scheme over a commutative ring form a module over
the base ring. The priority is below the default so that the canonical action of
`Γ(X, ⊤)` is still the one found when the base ring is the ring of global functions itself. -/
instance (priority := 900) globalSectionsBaseModule
    (M : X.Modules) : Module R Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (baseRingToGlobalSections R X)

/-- The global sections of the structure sheaf as a module are its ring of global functions, as
modules over the base ring. -/
def structureSheafSectionsBaseLinearEquiv :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI : Module R Γ(M, ⊤) := Module.compHom _ (baseRingToGlobalSections R X)
    letI : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
    Γ(M, ⊤) ≃ₗ[R] Γ(X, ⊤) := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  letI : Module R Γ(M, ⊤) := Module.compHom _ (baseRingToGlobalSections R X)
  letI : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  exact
    { toFun s := s
      invFun s := s
      map_add' _ _ := rfl
      map_smul' r s := by
        rw [RingHom.id_apply]
        -- Both actions are multiplication in `Γ(X, ⊤)`: on `Γ(M, ⊤)` by the image of `r` under
        -- `baseRingToGlobalSections` (from `Module.compHom`), on `Γ(X, ⊤)` by its image under
        -- `baseRingToStructurePresheaf` (from `RingHom.toAlgebra`). Unfolding both actions
        -- reduces the goal to `baseRingToStructurePresheaf_app_top`.
        change baseRingToGlobalSections R X r * (show Γ(X, ⊤) from s) =
          (X.baseRingToStructurePresheaf R).app (op ⊤) r * (show Γ(X, ⊤) from s)
        exact (congrArg (· * (show Γ(X, ⊤) from s))
          (ConcreteCategory.congr_hom (Scheme.baseRingToStructurePresheaf_app_top R X) r)).symm
      left_inv _ := rfl
      right_inv _ := rfl }

@[simp]
lemma structureSheafSectionsBaseLinearEquiv_apply :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI : Module R Γ(M, ⊤) := Module.compHom _ (baseRingToGlobalSections R X)
    letI : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
    ∀ s : Γ(M, ⊤), structureSheafSectionsBaseLinearEquiv R X s = s := by
  intros
  rfl

@[simp]
lemma structureSheafSectionsBaseLinearEquiv_symm_apply :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI : Module R Γ(M, ⊤) := Module.compHom _ (baseRingToGlobalSections R X)
    letI : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
    ∀ s : Γ(X, ⊤), (structureSheafSectionsBaseLinearEquiv R X).symm s = s := by
  intros
  rfl

@[simp]
lemma base_smul_globalSections
    (M : X.Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = baseRingToGlobalSections R X r • x :=
  rfl

end AlgebraicGeometry.Scheme.Modules

end Base

namespace AlgebraicGeometry.Scheme
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of S))]
  {g : Y ⟶ X}
/-- In a cartesian square over affine bases, the coordinate rings of an affine open and
its inverse image form a pushout over the original base rings. -/
theorem isPushout_baseRingToStructurePresheaf_of_isAffineOpen
    (H : IsPullback g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {U : X.Opens} (hU : IsAffineOpen U) :
    let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R Γ(X, U)))
      (CommRingCat.ofHom (algebraMap S Γ(Y, g ⁻¹ᵁ U))) (g.app U) := by
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  have := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (UY := g ⁻¹ᵁ U) le_top le_top (by simp) (isAffineOpen_top _) (isAffineOpen_top _) hU
  refine ((isIso_pushoutSection_iff ..).mp this).flip.of_iso (Scheme.ΓSpecIso (.of R))
    (Scheme.ΓSpecIso (.of S)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← Scheme.ΓSpecIso_naturality]
    exact congrArg (· ≫ _) (Scheme.Hom.appLE_eq_app _)
  · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE, Iso.hom_inv_id_assoc, Iso.refl_hom,
      Category.comp_id]
  · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE, Iso.hom_inv_id_assoc, Iso.refl_hom,
      Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Scheme.Hom.appLE_eq_app]
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules
section BaseScalars
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of S))]
  (g : Y ⟶ X) (U : X.Opens)
/-- In a commuting square over `Spec S ⟶ Spec R`, the action of `R` on sections over
`g ⁻¹ᵁ U` through `g.app U` is compatible with the action of `S` from the structure morphism.
This supplies the scalar tower for comparing base-ring actions on these coordinate rings. -/
lemma isScalarTower_baseRingToStructurePresheaf_app
    (C : CommSq g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    letI : Algebra R Γ(Y, g ⁻¹ᵁ U) :=
      ((g.app U).hom.comp (algebraMap R Γ(X, U))).toAlgebra
    IsScalarTower R S Γ(Y, g ⁻¹ᵁ U) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  let : Algebra R Γ(Y, g ⁻¹ᵁ U) :=
    ((g.app U).hom.comp (algebraMap R Γ(X, U))).toAlgebra
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r ↦ ?_)
  let : Y.Over (Spec (.of R)) :=
    ⟨(Y ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
  have : g.IsOver (Spec (.of R)) := ⟨C.w⟩
  exact (app_baseRingToStructurePresheaf R g U r).trans
    (Y.baseRingToStructurePresheaf_app_algebraMap
      (R := R) (S := S) rfl (g ⁻¹ᵁ U) r).symm
end BaseScalars
end AlgebraicGeometry.Scheme.Modules

end
