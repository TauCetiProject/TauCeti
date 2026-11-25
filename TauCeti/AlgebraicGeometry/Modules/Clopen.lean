/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.AlgebraicGeometry.Modules.DisjointGlue
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
    M ⟶ disjointGlue U fun j ↦ (restrictFunctor (U j).ι).obj M :=
  disjointGlue.lift U _ fun j ↦ (restrictAdjunction (U j).ι).unit.app M

private theorem TauCeti.AlgebraicGeometry.Scheme.Modules.isIso_unitToClopenCoverProduct
    (hcover : ⨆ j, U j = ⊤)
    (hdisj : Pairwise (Disjoint on U)) (M : X.Modules) : IsIso (unitToClopenCoverProduct U M) := by
  apply (isIso_iff_of_isOpenCover (TopologicalSpace.IsOpenCover.mk hcover) _).mpr
  intro j
  have hπ := isIso_restrictFunctor_map_π_disjointGlue
    (fun i ↦ (restrictFunctor (U i).ι).obj M) hdisj j
  have hunit : IsIso ((restrictFunctor (U j).ι).map ((restrictAdjunction (U j).ι).unit.app M)) :=
    isIso_restrictFunctor_map_of_isIso_app _ (U j) fun V hV ↦
      isIso_restrictAdjunction_unit_app_app (U j).ι M (by simpa using hV)
  have hiso : IsIso ((restrictFunctor (U j).ι).map (unitToClopenCoverProduct U M)) := by
    have : IsIso ((restrictFunctor (U j).ι).map (unitToClopenCoverProduct U M) ≫
        (restrictFunctor (U j).ι).map
          (disjointGlue.π U (fun i ↦ (restrictFunctor (U i).ι).obj M) j)) := by
      rw [← Functor.map_comp, unitToClopenCoverProduct, disjointGlue.lift_π]
      exact hunit
    exact IsIso.of_isIso_comp_right _ ((restrictFunctor (U j).ι).map
      (disjointGlue.π U (fun i ↦ (restrictFunctor (U i).ι).obj M) j))
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (U j).ι) _).mp hiso

/-- Restriction to a disjoint open cover identifies a module with `disjointGlue` of its
restrictions, the product of the pushforwards of its restrictions. The cover may be infinite. -/
def TauCeti.AlgebraicGeometry.Scheme.Modules.clopenCoverProductIso
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U)) (M : X.Modules) :
    M ≅ disjointGlue U fun j ↦ (restrictFunctor (U j).ι).obj M := by
  have := isIso_unitToClopenCoverProduct U hcover hdisj M
  exact asIso (unitToClopenCoverProduct U M)

/-- Each projection of the product decomposition is the restriction unit. -/
@[reassoc (attr := simp)]
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.clopenCoverProductIso_hom_π
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U)) (M : X.Modules) (j : J) :
    (clopenCoverProductIso U hcover hdisj M).hom ≫
      disjointGlue.π U (fun i ↦ (restrictFunctor (U i).ι).obj M) j =
        (restrictAdjunction (U j).ι).unit.app M := by
  simp only [clopenCoverProductIso, asIso_hom, unitToClopenCoverProduct, disjointGlue.lift_π]

/-- When the pushforwards of the restrictions to a disjoint open cover admit a biproduct,
that biproduct is the original module. In particular this applies to finite covers. -/
def TauCeti.AlgebraicGeometry.Scheme.Modules.clopenCoverCoefficientIso
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U)) (M : X.Modules)
    [HasBiproduct (fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M))] :
    M ≅ ⨁ fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M) :=
  clopenCoverProductIso U hcover hdisj M ≪≫
    (disjointGlue.isLimit U _).conePointUniqueUpToIso (biproduct.isLimit _)

/-- Each projection of the coefficient decomposition is the restriction unit. -/
@[reassoc (attr := simp)]
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.clopenCoverCoefficientIso_hom_π
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U)) (M : X.Modules)
    [HasBiproduct (fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M))] (j : J) :
    (clopenCoverCoefficientIso U hcover hdisj M).hom ≫ biproduct.π
      (fun i ↦ (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)) j =
        (restrictAdjunction (U j).ι).unit.app M := by
  rw [clopenCoverCoefficientIso, Iso.trans_hom, Category.assoc]
  exact (congrArg _ ((disjointGlue.isLimit U _).conePointUniqueUpToIso_hom_comp
    (biproduct.isLimit _) ⟨j⟩)).trans (clopenCoverProductIso_hom_π U hcover hdisj M j)
