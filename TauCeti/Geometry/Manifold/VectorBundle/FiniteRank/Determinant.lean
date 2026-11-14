/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Determinant
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.ExteriorPower

/-!
# Smooth and holomorphic determinant line comparisons

For a finite-rank core `A : FiniteRankBundleCore 𝕜 B`, the topological determinant-line comparisons
from `TauCeti.Topology.VectorBundle.FiniteRank.Determinant` upgrade to `C^n` maps and
diffeomorphisms at every regularity `n` (and in particular to holomorphic bundle equivalences when
`I = 𝓘(ℂ, EB)` and `n = ∞`):

* `FiniteRankBundleCore.detExteriorPowerDiffeomorph` upgrades `detExteriorPowerIso A hr` to a `C^n`
  diffeomorphism between `A.det` and `(exteriorPower 𝕜 B r).obj A`, and
  `FiniteRankBundleCore.contMDiff_totalSpaceMap_detMap` transfers `C^n` regularity of bundle maps
  to `detMap`;
* over a complete scalar field, `FiniteRankBundleCore.dualDetDiffeomorph` upgrades `dualDetIso A` to
  a `C^n` diffeomorphism between `(A.dual).det` and `(A.det).dual`, without smoothness assumptions
  on `A`;
* `FiniteRankBundleCore.dualDetTopFormTotalSpaceDiffeomorph` upgrades
  `dualDetTopFormTotalSpaceHomeomorph A` to a `C^n` diffeomorphism between `(A.dual).det` and
  Mathlib's bundle `fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜` of top-degree continuous
  alternating forms, without characteristic or core-smoothness hypotheses.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

section General

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

private theorem contMDiff_totalSpaceMap_detExteriorPowerIso_hom
    (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 B r).obj A).rank → 𝕜)) n
      (detExteriorPowerIso A hr).hom.totalSpaceMap := by
  subst hr
  refine contMDiff_totalSpaceMap_of_coordChange (detExteriorPowerIso A rfl).hom
    ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 rfl).symm).toContinuousLinearMap
    fun x b v ↦ (topExteriorScalarEquiv 𝕜 rfl).injective ?_
  rw [coordChange_exteriorPower_obj]
  refine (topExteriorScalarEquiv_exteriorPowerCoords_self (A.core.coordChange x b x) _).trans ?_
  rw [topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom]
  exact (detScalarEquiv_coordChange_det A x b x v).symm.trans
    ((topExteriorScalarEquiv 𝕜 rfl).apply_symm_apply _).symm

private theorem contMDiff_totalSpaceMap_detExteriorPowerIso_inv
    (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) :
    ContMDiff (I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 B r).obj A).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜)) n
      (detExteriorPowerIso A hr).inv.totalSpaceMap := by
  subst hr
  refine contMDiff_totalSpaceMap_of_coordChange (detExteriorPowerIso A rfl).inv
    ((topExteriorScalarEquiv 𝕜 rfl).trans (detScalarEquiv A).symm).toContinuousLinearMap
    fun x b v ↦ (detScalarEquiv A).injective ?_
  rw [detScalarEquiv_coordChange_det, detScalarEquiv_fiberMap_detExteriorPowerIso_inv,
    coordChange_exteriorPower_obj]
  exact (topExteriorScalarEquiv_exteriorPowerCoords_self (A.core.coordChange x b x) v).symm.trans
    ((detScalarEquiv A).apply_symm_apply _).symm

/-- For `r = A.rank`, `detExteriorPowerIso A hr` induces a `C^n` diffeomorphism of total spaces
between `A.det` and `(exteriorPower 𝕜 B r).obj A`. -/
noncomputable def detExteriorPowerDiffeomorph (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
    (hr : A.rank = r) (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    A.det.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 B r).obj A).rank → 𝕜)⟯
        ((exteriorPower 𝕜 B r).obj A).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv
    (detExteriorPowerIso A hr).hom (detExteriorPowerIso A hr).inv
    (detExteriorPowerIso A hr).hom_inv_id (detExteriorPowerIso A hr).inv_hom_id
    (contMDiff_totalSpaceMap_detExteriorPowerIso_hom A hr)
    (contMDiff_totalSpaceMap_detExteriorPowerIso_inv A hr)

@[simp] theorem coe_detExteriorPowerDiffeomorph (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
    (hr : A.rank = r) :
    ⇑(detExteriorPowerDiffeomorph A hr I n) = (detExteriorPowerIso A hr).hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp] theorem coe_detExteriorPowerDiffeomorph_symm (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
    (hr : A.rank = r) :
    ⇑(detExteriorPowerDiffeomorph A hr I n).symm = (detExteriorPowerIso A hr).inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

/-- A bundle map between `C^n` cores of rank `r` with `C^n` total-space map induces a `C^n`
total-space map on determinant line cores. -/
theorem contMDiff_totalSpaceMap_detMap [CompleteSpace 𝕜] (r : ℕ)
    {A D : FiniteRankBundleCore 𝕜 B} [A.core.IsContMDiff I n] [D.core.IsContMDiff I n]
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r)
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      f.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.det.rank → 𝕜)) n
      (detMap r f hA hD).totalSpaceMap := by
  rw [detMap_def]
  exact CoordinateHom.contMDiff_totalSpaceMap_comp
    (CoordinateHom.contMDiff_totalSpaceMap_comp
      (contMDiff_totalSpaceMap_detExteriorPowerIso_inv D hD)
      (contMDiff_totalSpaceMap_exteriorPower_map r f hf))
    (contMDiff_totalSpaceMap_detExteriorPowerIso_hom A hA)

end General

/-! ### Smooth dual determinants and top-degree alternating forms -/

section Dual

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- Over a complete scalar field, `(A.dual).det` and `(A.det).dual` are `C^n` diffeomorphic on
total spaces, upgrading `dualDetIso A` without smoothness assumptions on `A`. -/
noncomputable def dualDetDiffeomorph (A : FiniteRankBundleCore 𝕜 B)
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    A.dual.det.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.dual.det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin A.det.dual.rank → 𝕜)⟯ A.det.dual.core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv
    (dualDetIso A).hom (dualDetIso A).inv
    (dualDetIso A).hom_inv_id (dualDetIso A).inv_hom_id
    (contMDiff_totalSpaceMap_of_coordChange (dualDetIso A).hom
      ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm).toContinuousLinearMap
      fun x b v ↦ (detScalarEquiv A).injective <| by
        rw [coordChange_det_dual]
        have h1 : detScalarEquiv A
            (((A.core.coordChange b x x).det •
              ContinuousLinearMap.id 𝕜 (Fin A.det.dual.rank → 𝕜))
              ((dualDetIso A).hom.fiberMap x v)) =
            (A.core.coordChange b x x).det * detScalarEquiv A.dual v := by
          simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
          exact ((detScalarEquiv A).map_smul _ _).trans
            (congrArg _ (detScalarEquiv_fiberMap_dualDetIso_hom A x v))
        refine h1.trans ?_
        rw [coordChange_dual_det]
        simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
        exact ((detScalarEquiv A.dual).map_smul _ _).symm.trans
          ((detScalarEquiv A).apply_symm_apply _).symm)
    (contMDiff_totalSpaceMap_of_coordChange (dualDetIso A).inv
      ((detScalarEquiv A).trans (detScalarEquiv A.dual).symm).toContinuousLinearMap
      fun x b v ↦ (detScalarEquiv A.dual).injective <| by
        rw [coordChange_dual_det]
        have h1 : detScalarEquiv A.dual
            (((A.core.coordChange b x x).det •
              ContinuousLinearMap.id 𝕜 (Fin A.dual.det.rank → 𝕜))
              ((dualDetIso A).inv.fiberMap x v)) =
            (A.core.coordChange b x x).det * detScalarEquiv A v := by
          simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
          exact ((detScalarEquiv A.dual).map_smul _ _).trans
            (congrArg _ (detScalarEquiv_fiberMap_dualDetIso_inv A x v))
        refine h1.trans ?_
        rw [coordChange_det_dual]
        simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
        exact ((detScalarEquiv A).map_smul _ _).symm.trans
          ((detScalarEquiv A.dual).apply_symm_apply _).symm)

@[simp] theorem coe_dualDetDiffeomorph (A : FiniteRankBundleCore 𝕜 B) :
    ⇑(dualDetDiffeomorph A I n) = (dualDetIso A).hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp] theorem coe_dualDetDiffeomorph_symm (A : FiniteRankBundleCore 𝕜 B) :
    ⇑(dualDetDiffeomorph A I n).symm = (dualDetIso A).inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

/-- Reading `A.dual.det` vectors as top-degree continuous alternating forms on `A.core.Fiber` is
`C^n` on total spaces at every regularity `n`, without smoothness or characteristic assumptions. -/
theorem contMDiff_dualDetTopFormFiberEquiv (A : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.dual.det.rank → 𝕜))
      (I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)) n
      (fun p : A.dual.det.core.TotalSpace ↦
        TotalSpace.mk' ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
          (E := fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) p.proj
          (dualDetTopFormFiberEquiv A p.proj p.2)) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hp₀ : p₀ ∈ (A.dual.det.core.localTriv p₀.proj).source :=
    (A.dual.det.core.mem_localTriv_source p₀.proj p₀).2 (A.dual.det.mem_baseSet_self p₀.proj)
  have hU := (A.dual.det.core.localTriv p₀.proj).open_source.mem_nhds hp₀
  refine ((((detScalarEquiv A.dual).trans
    (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm).contDiff).comp_contMDiffAt
    (A.dual.det.contMDiffAt_localTriv_snd p₀)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with ⟨x, u⟩ hq
  have hx : x ∈ A.core.baseSet p₀.proj := by
    have hmem := (A.dual.det.core.mem_localTriv_source p₀.proj ⟨x, u⟩).1 hq
    rwa [baseSet_det] at hmem
  exact dualDetTopFormFiberEquiv_inCoordinates A p₀.proj x hx u

/-- The reconstructed total space of `A.dual.det` is `C^n` diffeomorphic over `B` to Mathlib's
bundle of top-degree scalar-valued continuous alternating forms on `A.core.Fiber`. -/
noncomputable def dualDetTopFormTotalSpaceDiffeomorph (A : FiniteRankBundleCore 𝕜 B)
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    A.dual.det.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.dual.det.rank → 𝕜),
      I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)⟯
        TotalSpace ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
          (fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) :=
  bundleDiffeomorph (dualDetTopFormFiberEquiv A) (contMDiff_dualDetTopFormFiberEquiv A)

@[simp] theorem dualDetTopFormTotalSpaceDiffeomorph_toHomeomorph (A : FiniteRankBundleCore 𝕜 B) :
    (dualDetTopFormTotalSpaceDiffeomorph A I n).toHomeomorph =
      dualDetTopFormTotalSpaceHomeomorph A := by
  apply Homeomorph.ext
  intro p
  exact (bundleDiffeomorph_apply (IB := I) (n := n) (dualDetTopFormFiberEquiv A)
    (contMDiff_dualDetTopFormFiberEquiv A) p).trans
    (dualDetTopFormTotalSpaceHomeomorph_apply A p).symm

@[simp] theorem dualDetTopFormTotalSpaceDiffeomorph_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    dualDetTopFormTotalSpaceDiffeomorph A I n p =
      ⟨p.proj, dualDetTopFormFiberEquiv A p.proj p.2⟩ :=
  bundleDiffeomorph_apply _ _ p

@[simp] theorem dualDetTopFormTotalSpaceDiffeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
      (fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜)) :
    (dualDetTopFormTotalSpaceDiffeomorph A I n).symm p =
      ⟨p.proj, (dualDetTopFormFiberEquiv A p.proj).symm p.2⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end Dual

end TauCeti.FiniteRankBundleCore
