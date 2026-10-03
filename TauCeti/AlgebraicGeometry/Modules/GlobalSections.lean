/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

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
presheaf. Pullback of local functions by a morphism over the base preserves these images
(`TauCeti.AlgebraicGeometry.Scheme.Modules.app_baseRingToStructurePresheaf`).

These constructions are independent of sheaf cohomology. They supply the scalar actions used by
`TauCeti.AlgebraicGeometry.Cohomology.Module.Basic`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The restriction of a global function to an open subset. -/
private def restrictGlobal (U : X.Opens) (r : Γ(X, ⊤)) :
    X.ringCatSheaf.obj.obj (.op U) :=
  X.presheaf.map (homOfLE le_top).op r

/-- Multiplication by a global function, as a morphism of sheaves of modules. -/
def _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul
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
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_app
    (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) :
    (globalSectionsSmul M r).app U = M.smul (X.presheaf.map U.leTop.op r) := by
  rfl

-- In the next four proofs, sheaf-morphism extensionality leaves pointwise bundled-module goals.
-- The wrappers have no pointwise equality lemmas, so each `change` records the corresponding
-- public presheaf/module formulation before applying the ring and module laws.
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_zero
    (M : X.Modules) : globalSectionsSmul M 0 = 0 := by
  ext U x
  change X.presheaf.map U.leTop.op 0 • x = 0
  simp

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_add
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r + s) = globalSectionsSmul M r + globalSectionsSmul M s := by
  ext U x
  change X.presheaf.map U.leTop.op (r + s) • x =
    X.presheaf.map U.leTop.op r • x +
      X.presheaf.map U.leTop.op s • x
  simp [add_smul]

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_one
    (M : X.Modules) : globalSectionsSmul M 1 = 𝟙 M := by
  ext U x
  change X.presheaf.map U.leTop.op 1 • x = x
  simp

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_mul
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r * s) = globalSectionsSmul M s ≫ globalSectionsSmul M r := by
  ext U x
  change X.presheaf.map U.leTop.op (r * s) • x =
    X.presheaf.map U.leTop.op r •
      X.presheaf.map U.leTop.op s • x
  rw [map_mul, mul_smul]

/-- Multiplication by a global unit is an isomorphism, with inverse multiplication by the inverse
unit. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isIso_globalSectionsSmul_units
    (M : X.Modules) (u : Γ(X, ⊤)ˣ) : IsIso (globalSectionsSmul M u) :=
  ⟨globalSectionsSmul M ↑u⁻¹,
    by rw [← globalSectionsSmul_mul, Units.inv_mul, globalSectionsSmul_one],
    by rw [← globalSectionsSmul_mul, Units.mul_inv, globalSectionsSmul_one]⟩

/-- The action of global functions on a sheaf of modules, bundled as a ring homomorphism into
the endomorphism ring of the sheaf. -/
def _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsAction
    (M : X.Modules) : Γ(X, ⊤) →+* End M where
  toFun := globalSectionsSmul M
  map_one' := globalSectionsSmul_one M
  map_mul' := fun r s ↦ by
    rw [globalSectionsSmul_mul]
    exact (End.mul_def _ _).symm
  map_zero' := globalSectionsSmul_zero M
  map_add' := globalSectionsSmul_add M

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsAction_apply
    (M : X.Modules) (r : Γ(X, ⊤)) :
    globalSectionsAction M r = globalSectionsSmul M r :=
  by rfl

/-- Multiplication by a global function is natural in the sheaf of modules. -/
@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_naturality
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
lemma _root_.AlgebraicGeometry.Scheme.Modules.pushforward_map_globalSectionsSmul
    (N : X.Modules) (r : Γ(Y, ⊤)) :
    (pushforward f).map (globalSectionsSmul N (f.appTop r)) =
      globalSectionsSmul ((pushforward f).obj N) r := by
  refine _root_.AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  rw [pushforward_map_app, globalSectionsSmul_app, globalSectionsSmul_app]
  -- The sections of the pushforward over `U` are the sections of `N` over `f ⁻¹ᵁ U`, with scalars
  -- restricted along `f.app U`; no lemma exposes this, so record it explicitly.
  change N.smul (X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop r)) =
    N.smul (f.app U (Y.presheaf.map U.leTop.op r))
  congr 1
  exact (ConcreteCategory.comp_apply _ _ r).symm.trans
    (congrArg (· r) (f.naturality U.leTop.op)).symm

/-- Pulling back multiplication by a global function `r` on `Y` gives multiplication by the
pullback `f^♯ r` of `r` on the pullback. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.pullback_map_globalSectionsSmul
    (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (globalSectionsSmul M r) =
      globalSectionsSmul ((Scheme.Modules.pullback f).obj M) (f.appTop r) := by
  -- Both sides are determined by their adjuncts `M ⟶ f_* f^* M`, which agree by naturality of
  -- the unit and of the global-functions action.
  apply ((pullbackPushforwardAdjunction f).homEquiv M
    ((Scheme.Modules.pullback f).obj M)).injective
  simp only [Adjunction.homEquiv_apply, pushforward_map_globalSectionsSmul]
  exact ((pullbackPushforwardAdjunction f).unit.naturality (globalSectionsSmul M r)).symm.trans
    (globalSectionsSmul_naturality ((pullbackPushforwardAdjunction f).unit.app M) r)

end Functoriality

section Base

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The homomorphism from the base ring to global functions on a scheme over that ring. -/
def _root_.AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop).hom

/-- The base ring acts through the pullback along the structure morphism: `r` is sent to the
global function obtained by pulling back the function on `Spec R` corresponding to `r`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections_apply (r : R) :
    baseRingToGlobalSections R X r =
      (X ↘ Spec (.of R)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) :=
  (rfl)

/-- The morphism from the constant presheaf of rings `R` to the structure presheaf of a scheme
over `R`: on an open `U` it is the base ring map to global functions followed by restriction
to `U`. -/
def _root_.AlgebraicGeometry.Scheme.baseRingToStructurePresheaf :
    (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of R) ⟶ X.presheaf where
  app U := CommRingCat.ofHom (Scheme.Modules.baseRingToGlobalSections R X) ≫
    X.presheaf.map U.unop.leTop.op
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    rfl

/-- On an open `U`, the base ring maps to sections over `U` through global functions followed by
restriction to `U`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.baseRingToStructurePresheaf_app (U : X.Opensᵒᵖ) :
    (X.baseRingToStructurePresheaf R).app U =
      CommRingCat.ofHom (Scheme.Modules.baseRingToGlobalSections R X) ≫
        X.presheaf.map U.unop.leTop.op :=
  (rfl)

/-- On an open `U`, the base-ring map `R → Γ(X, U)` is the composite of `R ≅ Γ(Spec R, ⊤)` with
the map on functions induced by the structure morphism. -/
lemma _root_.AlgebraicGeometry.Scheme.baseRingToStructurePresheaf_app_eq_appLE (U : X.Opens) :
    (X.baseRingToStructurePresheaf R).app (op U) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appLE ⊤ U le_top := by
  ext r
  rw [Scheme.baseRingToStructurePresheaf_app, CommRingCat.comp_apply, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply, Scheme.Modules.baseRingToGlobalSections_apply]
  -- Both sides restrict the pullback of `r` from `⊤` to `U`; `appLE ⊤ U` is by definition
  -- `app ⊤` followed by that restriction.
  rfl

variable {X} in
/-- Pullback of local functions along a morphism over `Spec R` preserves the image of the
base ring. -/
lemma app_baseRingToStructurePresheaf {Y : Scheme.{u}} [Y.Over (Spec (.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (U : Y.Opens) (r : R) :
    f.app U ((Y.baseRingToStructurePresheaf R).app (op U) r) =
      (X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U)) r := by
  rw [Scheme.baseRingToStructurePresheaf_app, Scheme.baseRingToStructurePresheaf_app]
  -- The maps obtained from `CommRingCat.ofHom` compute through their bundled ring homs.
  change f.app U (Y.presheaf.map U.leTop.op (Scheme.Modules.baseRingToGlobalSections R Y r)) =
    X.presheaf.map (f ⁻¹ᵁ U).leTop.op (Scheme.Modules.baseRingToGlobalSections R X r)
  rw [← ConcreteCategory.comp_apply, f.naturality U.leTop.op]
  have h := congrArg Scheme.Hom.appTop
    (HomIsOver.comp_over (f := f) (S := Spec (.of R)))
  rw [Scheme.Hom.comp_appTop] at h
  rw [ConcreteCategory.comp_apply, Scheme.Modules.baseRingToGlobalSections_apply,
    Scheme.Modules.baseRingToGlobalSections_apply, ← h, ConcreteCategory.comp_apply]
  rfl

/-- Global sections of a sheaf of modules on a scheme over a commutative ring form a module over
the base ring. The priority is below the default so that the canonical action of
`Γ(X, ⊤)` is still the one found when the base ring is the ring of global functions itself. -/
instance (priority := 900) _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsBaseModule
    (M : X.Modules) : Module R Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (baseRingToGlobalSections R X)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.base_smul_globalSections
    (M : X.Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = baseRingToGlobalSections R X r • x :=
  rfl

end Base

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
