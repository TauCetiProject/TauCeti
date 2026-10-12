/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Monoidal

/-!
# Dual compatibility of the affine vector-bundle equivalence

The equivalence between finite projective `R`-modules and finite locally free sheaves on
`Spec R` identifies the linear dual of a module with the internal-Hom dual of its associated
sheaf. The comparison is the canonical internal-Hom comparison of the strong monoidal
associated-sheaf functor, after identifying linear duals with module internal Homs.

Its component formula is exposed, and the comparison is contravariantly natural in the finite
projective module. Together with the tensor compatibility of
`FiniteLocallyFreeSheaf.finiteProjectiveEquiv`, this completes the affine comparison of tensor
products and duals.

The construction uses Mathlib's `ModuleCat.homLinearEquiv` and the internal-Hom comparison for
strong monoidal functors.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 (b).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (R : CommRingCat.{u})

private theorem isIso_tildeIhomComparison
    (M : (finiteProjectiveModules R).FullSubcategory) :
    IsIso ((tilde.functor R).ihomComparison M.obj).natTrans := by
  obtain ⟨hfinite, hprojective⟩ := finiteProjectiveModules_iff.mp M.property
  let _ : Module.Finite R M.obj := hfinite
  let _ : Module.Projective R M.obj := hprojective
  let _ : ExactPairing ((ihom M.obj).obj (𝟙_ (ModuleCat.{u} R))) M.obj :=
    exactPairingOfIsIsoDualTensorIhom (Y := M.obj)
  exact (tilde.functor R).ihomComparison_isIso_of_exactPairing
    ((ihom M.obj).obj (𝟙_ (ModuleCat.{u} R))) M.obj

private def tildeIhomComparisonIso
    (M : (finiteProjectiveModules R).FullSubcategory) :
    ihom M.obj ⋙ tilde.functor R ≅
      tilde.functor R ⋙ ihom (tilde M.obj) :=
  @asIso _ _ _ _ ((tilde.functor R).ihomComparison M.obj).natTrans
    (isIso_tildeIhomComparison R M)

/-- The associated sheaf of the linear dual of a finite projective module is canonically
isomorphic to the internal-Hom dual of its associated finite locally free sheaf. -/
def finiteProjectiveEquivDualIso (M : (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveEquiv R).functor.obj (FiniteProjectiveModules.dual R M) ≅
      dual ((finiteProjectiveEquiv R).functor.obj M) :=
  ObjectProperty.isoMk _ ((tilde.functor R).mapIso
        (ModuleCat.homLinearEquiv.toModuleIso :
          (ihom M.obj).obj (𝟙_ (ModuleCat.{u} R)) ≅
            ModuleCat.of R (Module.Dual R M.obj)).symm ≪≫
      (tildeIhomComparisonIso R M).app (𝟙_ (ModuleCat.{u} R)) ≪≫
      (ihom (tilde M.obj)).mapIso (Functor.Monoidal.εIso (tilde.functor R)).symm)

/-- The underlying sheaf isomorphism comparing affine linear duals is the internal-Hom
comparison, preceded by the standard identification of a linear dual with a module internal Hom
and followed by the tensor-unit comparison. -/
@[simp]
theorem finiteProjectiveEquivDualIso_hom_hom
    (M : (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveEquivDualIso R M).hom.hom =
      (tilde.functor R).map
          (ModuleCat.homLinearEquiv.toModuleIso :
            (ihom M.obj).obj (𝟙_ (ModuleCat.{u} R)) ≅
              ModuleCat.of R (Module.Dual R M.obj)).inv ≫
        ((tilde.functor R).ihomComparison M.obj).natTrans.app
          (𝟙_ (ModuleCat.{u} R)) ≫
        (ihom ((tilde.functor R).obj M.obj)).map (η (tilde.functor R)) :=
  by
    rw [finiteProjectiveEquivDualIso]
    rfl

/-- The affine dual comparison is contravariantly natural in the finite projective module. -/
@[reassoc]
theorem finiteProjectiveEquivDualIso_naturality
    {M N : (finiteProjectiveModules R).FullSubcategory} (f : M ⟶ N) :
    (tilde.functor R).map (ModuleCat.ofHom f.hom.hom.dualMap) ≫
        (finiteProjectiveEquivDualIso R M).hom.hom =
      (finiteProjectiveEquivDualIso R N).hom.hom ≫
        (pre ((tilde.functor R).map f.hom)).app (𝟙_ (Spec R).Modules) := by
  rw [finiteProjectiveEquivDualIso_hom_hom, finiteProjectiveEquivDualIso_hom_hom]
  have hdual :
      ModuleCat.ofHom f.hom.hom.dualMap ≫
          (ModuleCat.homLinearEquiv.toModuleIso :
            (ihom M.obj).obj (𝟙_ (ModuleCat.{u} R)) ≅
              ModuleCat.of R (Module.Dual R M.obj)).inv =
        (ModuleCat.homLinearEquiv.toModuleIso :
            (ihom N.obj).obj (𝟙_ (ModuleCat.{u} R)) ≅
              ModuleCat.of R (Module.Dual R N.obj)).inv ≫
          (pre f.hom).app (𝟙_ (ModuleCat.{u} R)) := by
    ext φ
    rfl
  erw [← (tilde.functor R).map_comp_assoc]
  rw [hdual]
  erw [(tilde.functor R).map_comp_assoc]
  have hc := congrArg (fun S ↦ S.natTrans.app (𝟙_ (ModuleCat.{u} R)))
    (Functor.ihomComparison_whiskerLeft (F := tilde.functor R) f.hom)
  -- The equality is packaged as an equality of `TwoSquare`s; expose its component so it can
  -- rewrite the composite without unfolding the internal-Hom comparison itself.
  change ((tilde.functor R).ihomComparison N.obj).natTrans.app
        (𝟙_ (ModuleCat.{u} R)) ≫
      (pre ((tilde.functor R).map f.hom)).app
        ((tilde.functor R).obj (𝟙_ (ModuleCat.{u} R))) =
    (tilde.functor R).map ((pre f.hom).app (𝟙_ (ModuleCat.{u} R))) ≫
      ((tilde.functor R).ihomComparison M.obj).natTrans.app
        (𝟙_ (ModuleCat.{u} R)) at hc
  erw [← reassoc_of% hc]
  erw [← (pre ((tilde.functor R).map f.hom)).naturality]
  erw [Category.assoc, Category.assoc]
  rfl

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
