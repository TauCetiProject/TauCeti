/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import TauCeti.AlgebraicGeometry.Modules.Products
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Modules on a disjoint open cover

The restriction units express a module as the product of the pushforwards of its restrictions
to a disjoint open cover, with no finiteness hypothesis. Locally on each member, all other
factors have zero sections, so the comparison is an isomorphism on every member of the cover.
For a finite cover this also gives the finite direct-sum decomposition.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti TauCeti.AlgebraicGeometry
open scoped Function

universe u

noncomputable section

variable {X : Scheme.{u}} {J : Type u} (U : J → X.Opens)

private def TauCeti.AlgebraicGeometry.Scheme.Modules.unitToClopenCoverProduct
    (M : X.Modules) :
    M ⟶ ∏ᶜ fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M) :=
  Pi.lift fun j ↦ (restrictAdjunction (U j).ι).unit.app M

private theorem TauCeti.AlgebraicGeometry.Scheme.Modules.isIso_unitToClopenCoverProduct
    (hcover : ⨆ j, U j = ⊤)
    (hdisj : Pairwise (Disjoint on U)) (M : X.Modules) : IsIso (unitToClopenCoverProduct U M) := by
  apply (isIso_iff_of_isOpenCover (TopologicalSpace.IsOpenCover.mk hcover) _).mpr
  intro j
  have hiso : IsIso ((restrictFunctor (U j).ι).map (unitToClopenCoverProduct U M)) := by
    apply isIso_restrictFunctor_map_of_isIso_app _ (U j)
    intro V hV
    have hπ : IsIso ((Pi.π
        (fun i ↦ (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)) j).app V) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      apply bijective_app_π_of_subsingleton
      intro i hij
      exact subsingleton_sections_pushforward_of_disjoint _ ((hdisj hij).symm.mono_left hV)
    have hcomp : (unitToClopenCoverProduct U M).app V ≫ (Pi.π
        (fun i ↦ (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)) j).app V =
        ((restrictAdjunction (U j).ι).unit.app M).app V := by
      rw [← Hom.comp_app, unitToClopenCoverProduct, Pi.lift_comp_π]
    have : IsIso ((unitToClopenCoverProduct U M).app V ≫ (Pi.π
        (fun i ↦ (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)) j).app V) := by
      rw [hcomp]
      exact isIso_restrictAdjunction_unit_app_app (U j).ι M (by simpa using hV)
    exact IsIso.of_isIso_comp_right _ ((Pi.π
      (fun i ↦ (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)) j).app V)
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (U j).ι) _).mp hiso

/-- Restriction to a disjoint open cover identifies a module with the product of the
pushforwards of its restrictions. The cover may be infinite. -/
def TauCeti.AlgebraicGeometry.Scheme.Modules.clopenCoverProductIso
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U)) (M : X.Modules) :
    M ≅ ∏ᶜ fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M) := by
  have := isIso_unitToClopenCoverProduct U hcover hdisj M
  exact asIso (unitToClopenCoverProduct U M)

/-- Each projection of the product decomposition is the restriction unit. -/
@[reassoc (attr := simp)]
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.clopenCoverProductIso_hom_π
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U)) (M : X.Modules) (j : J) :
    (clopenCoverProductIso U hcover hdisj M).hom ≫ Pi.π
      (fun i ↦ (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)) j =
        (restrictAdjunction (U j).ι).unit.app M := by
  simp only [clopenCoverProductIso, asIso_hom, unitToClopenCoverProduct, Pi.lift_comp_π]

/-- When the pushforwards of the restrictions to a disjoint open cover admit a biproduct,
that biproduct is the original module. In particular this applies to finite covers. -/
def TauCeti.AlgebraicGeometry.Scheme.Modules.clopenCoverCoefficientIso
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U)) (M : X.Modules)
    [HasBiproduct (fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M))] :
    M ≅ ⨁ fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M) :=
  clopenCoverProductIso U hcover hdisj M ≪≫
    (biproduct.isoProduct
      (fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M))).symm

/-- Each projection of the coefficient decomposition is the restriction unit. -/
@[reassoc (attr := simp)]
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.clopenCoverCoefficientIso_hom_π
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U)) (M : X.Modules)
    [HasBiproduct (fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M))] (j : J) :
    (clopenCoverCoefficientIso U hcover hdisj M).hom ≫ biproduct.π
      (fun i ↦ (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)) j =
        (restrictAdjunction (U j).ι).unit.app M := by
  simp only [clopenCoverCoefficientIso, Iso.trans_hom, Iso.symm_hom,
    biproduct.isoProduct_inv, Category.assoc, biproduct.lift_π]
  exact clopenCoverProductIso_hom_π U hcover hdisj M j
