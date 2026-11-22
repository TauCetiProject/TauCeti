/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Affine
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Dual
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Bidual
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.PairingDual

/-!
# Exterior powers of duals of vector bundles on an affine scheme

For a finite locally free sheaf `E` on `Spec R`, the `n`-th exterior power of the dual is the dual
of the `n`-th exterior power: `⋀ⁿ (E^∨) ≅ (⋀ⁿ E)^∨`. When `E` has constant rank `r`, the case
`n = r` is `det (E^∨) ≅ (det E)^∨`.

The sheaf `E` is `M~` for the finite projective module `M = Γ(Spec R, E)`
(`FiniteLocallyFreeSheaf.finiteProjectiveEquiv`), and the isomorphism is assembled from the
module isomorphism `⋀ⁿ (M^*) ≃ (⋀ⁿ M)^*` (`exteriorPower.pairingDualEquiv`) and the compatibility
of `M ↦ M~` with exterior powers (`TauCeti.AlgebraicGeometry.tildeExteriorPowerIso`) and with
duals (`FiniteLocallyFreeSheaf.finiteProjectiveEquivDualIso`).

## Main declarations

* `FiniteLocallyFreeSheaf.exteriorPowerDualIsoOfFiniteProjective`: `⋀ⁿ ((M~)^∨) ≅ (⋀ⁿ M~)^∨` for a
  finite projective `R`-module `M`;
* `FiniteLocallyFreeSheaf.exteriorPowerDualIsoOfSpec`: `⋀ⁿ (E^∨) ≅ (⋀ⁿ E)^∨` for every finite
  locally free sheaf `E` on `Spec R`.
* `FiniteLocallyFreeSheaf.exteriorPowerFiniteProjectiveEquivDualIso_hom_hom`: the sheaf comparison
  underlying both is the sheafified pairing `exteriorPower.pairingDual`; the `_def` lemmas of the
  two isomorphisms express them through it.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §11 (duality in the exterior algebra).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 and Exercise II.5.16.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}}

/-- The `n`-th exterior power of a finite projective module, as a finite projective module. -/
@[expose]
def finiteProjectiveExteriorPower (M : (finiteProjectiveModules R).FullSubcategory)
    (n : ℕ) : (finiteProjectiveModules R).FullSubcategory :=
  have := (finiteProjectiveModules_iff.mp M.property).1
  have := (finiteProjectiveModules_iff.mp M.property).2
  ⟨M.obj.exteriorPower n, finiteProjectiveModules_iff.mpr
    ⟨inferInstanceAs (Module.Finite R (⋀[R]^n M.obj)),
      inferInstanceAs (Module.Projective R (⋀[R]^n M.obj))⟩⟩

/-- The sheaf associated with `⋀ⁿ M` is the `n`-th exterior power of the sheaf associated with a
module `M`, as finite locally free sheaves. -/
def finiteProjectiveEquivExteriorPowerIso
    (M : (finiteProjectiveModules R).FullSubcategory) (n : ℕ) :
    (finiteProjectiveEquiv R).functor.obj (finiteProjectiveExteriorPower M n) ≅
      (exteriorPower (Spec R) n).obj ((finiteProjectiveEquiv R).functor.obj M) :=
  ObjectProperty.isoMk _ (tildeExteriorPowerIso n M.obj ≪≫
    eqToIso (exteriorPower_obj_obj (X := Spec R) n ((finiteProjectiveEquiv R).functor.obj M)).symm)

/-- The sheaf version of `⋀ⁿ (M^*) ≃ (⋀ⁿ M)^*`: the `n`-th exterior power of the sheaf associated
with `M^*` is the sheaf associated with `(⋀ⁿ M)^*`. -/
def exteriorPowerFiniteProjectiveEquivDualIso
    (M : (finiteProjectiveModules R).FullSubcategory) (n : ℕ) :
    (exteriorPower (Spec R) n).obj
        ((finiteProjectiveEquiv R).functor.obj (FiniteProjectiveModules.dual R M)) ≅
      (finiteProjectiveEquiv R).functor.obj
        (FiniteProjectiveModules.dual R (finiteProjectiveExteriorPower M n)) :=
  have := (finiteProjectiveModules_iff.mp M.property).1
  have := (finiteProjectiveModules_iff.mp M.property).2
  ObjectProperty.isoMk _ (eqToIso (exteriorPower_obj_obj (X := Spec R) n
      ((finiteProjectiveEquiv R).functor.obj (FiniteProjectiveModules.dual R M))) ≪≫
    (tildeExteriorPowerIso n (ModuleCat.of R (Module.Dual R M.obj))).symm ≪≫
    (tilde.functor R).mapIso (exteriorPower.pairingDualEquiv R M.obj n).toModuleIso)

/-- The underlying module of `finiteProjectiveExteriorPower M n` is `⋀ⁿ M`. -/
@[simp]
theorem finiteProjectiveExteriorPower_obj (M : (finiteProjectiveModules R).FullSubcategory)
    (n : ℕ) : (finiteProjectiveExteriorPower M n).obj = M.obj.exteriorPower n :=
  (rfl)

/-- The comparison `finiteProjectiveEquivExteriorPowerIso` is `tildeExteriorPowerIso`. -/
theorem finiteProjectiveEquivExteriorPowerIso_hom_hom
    (M : (finiteProjectiveModules R).FullSubcategory) (n : ℕ) :
    (finiteProjectiveEquivExteriorPowerIso M n).hom.hom =
      (tildeExteriorPowerIso n M.obj).hom ≫
        eqToHom (exteriorPower_obj_obj (X := Spec R) n
          ((finiteProjectiveEquiv R).functor.obj M)).symm :=
  (rfl)

/-- The sheaf comparison `exteriorPowerFiniteProjectiveEquivDualIso` is the sheafified pairing
`exteriorPower.pairingDual`. -/
theorem exteriorPowerFiniteProjectiveEquivDualIso_hom_hom
    (M : (finiteProjectiveModules R).FullSubcategory) (n : ℕ) :
    (exteriorPowerFiniteProjectiveEquivDualIso M n).hom.hom =
      eqToHom (exteriorPower_obj_obj (X := Spec R) n
          ((finiteProjectiveEquiv R).functor.obj (FiniteProjectiveModules.dual R M))) ≫
        (tildeExteriorPowerIso n (ModuleCat.of R (Module.Dual R M.obj))).inv ≫
        (tilde.functor R).map (ModuleCat.ofHom (exteriorPower.pairingDual R M.obj n)) := by
  have := (finiteProjectiveModules_iff.mp M.property).1
  have := (finiteProjectiveModules_iff.mp M.property).2
  have h : ModuleCat.ofHom (exteriorPower.pairingDual R M.obj n) =
      (exteriorPower.pairingDualEquiv R M.obj n).toModuleIso.hom :=
    ModuleCat.hom_ext (LinearMap.ext fun x ↦
      congrFun (exteriorPower.coe_pairingDualEquiv (R := R) (M := M.obj) n).symm x)
  rw [h]
  rfl

/-- **Exterior powers of the dual on `Spec R`, for an associated sheaf.** For a finite projective
`R`-module `M`, the `n`-th exterior power of the dual of `M~` is the dual of `⋀ⁿ M~`. It is the
sheaf version of `⋀ⁿ (M^*) ≃ (⋀ⁿ M)^*` (`exteriorPower.pairingDualEquiv`), transported through
the compatibility of `M ↦ M~` with exterior powers and duals. -/
def exteriorPowerDualIsoOfFiniteProjective (M : (finiteProjectiveModules R).FullSubcategory)
    (n : ℕ) :
    (exteriorPower (Spec R) n).obj (dual ((finiteProjectiveEquiv R).functor.obj M)) ≅
      dual ((exteriorPower (Spec R) n).obj ((finiteProjectiveEquiv R).functor.obj M)) :=
  (exteriorPower (Spec R) n).mapIso (finiteProjectiveEquivDualIso R M).symm ≪≫
    exteriorPowerFiniteProjectiveEquivDualIso M n ≪≫
    finiteProjectiveEquivDualIso R (finiteProjectiveExteriorPower M n) ≪≫
    dualIsoOfIso (finiteProjectiveEquivExteriorPowerIso M n).symm

/-- `exteriorPowerDualIsoOfFiniteProjective` is the sheafified pairing
`exteriorPowerFiniteProjectiveEquivDualIso`, composed with the comparisons of `M ↦ M~` with duals
(`finiteProjectiveEquivDualIso`) and exterior powers (`finiteProjectiveEquivExteriorPowerIso`). -/
theorem exteriorPowerDualIsoOfFiniteProjective_def
    (M : (finiteProjectiveModules R).FullSubcategory) (n : ℕ) :
    exteriorPowerDualIsoOfFiniteProjective M n =
      (exteriorPower (Spec R) n).mapIso (finiteProjectiveEquivDualIso R M).symm ≪≫
        exteriorPowerFiniteProjectiveEquivDualIso M n ≪≫
        finiteProjectiveEquivDualIso R (finiteProjectiveExteriorPower M n) ≪≫
        dualIsoOfIso (finiteProjectiveEquivExteriorPowerIso M n).symm :=
  (rfl)

/-- **Exterior powers of the dual on an affine scheme.** For every finite locally free sheaf `E` on
`Spec R`, the `n`-th exterior power of the dual of `E` is the dual of `⋀ⁿ E`. For `E` of constant
rank `r` and `n = r` this is `det (E^∨) ≅ (det E)^∨`. The sheaf `E` is identified with the sheaf
associated with its global sections, where `exteriorPowerDualIsoOfFiniteProjective` applies. -/
def exteriorPowerDualIsoOfSpec (E : FiniteLocallyFreeSheaf (Spec R)) (n : ℕ) :
    (exteriorPower (Spec R) n).obj (dual E) ≅ dual ((exteriorPower (Spec R) n).obj E) :=
  (exteriorPower (Spec R) n).mapIso
      (dualIsoOfIso ((finiteProjectiveEquiv R).counitIso.app E)) ≪≫
    exteriorPowerDualIsoOfFiniteProjective ((finiteProjectiveEquiv R).inverse.obj E) n ≪≫
    (dualIsoOfIso ((exteriorPower (Spec R) n).mapIso
      ((finiteProjectiveEquiv R).counitIso.app E))).symm

/-- `exteriorPowerDualIsoOfSpec E n` is `exteriorPowerDualIsoOfFiniteProjective` for the global
sections of `E`, transported along the counit `Γ(E)~ ≅ E`. -/
theorem exteriorPowerDualIsoOfSpec_def (E : FiniteLocallyFreeSheaf (Spec R)) (n : ℕ) :
    exteriorPowerDualIsoOfSpec E n =
      (exteriorPower (Spec R) n).mapIso
          (dualIsoOfIso ((finiteProjectiveEquiv R).counitIso.app E)) ≪≫
        exteriorPowerDualIsoOfFiniteProjective ((finiteProjectiveEquiv R).inverse.obj E) n ≪≫
        (dualIsoOfIso ((exteriorPower (Spec R) n).mapIso
          ((finiteProjectiveEquiv R).counitIso.app E))).symm :=
  (rfl)

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
