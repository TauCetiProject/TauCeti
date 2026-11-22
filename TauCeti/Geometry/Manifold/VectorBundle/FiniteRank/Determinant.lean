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

Upgrades the topological determinant-line comparisons from
`TauCeti.Topology.VectorBundle.FiniteRank.Determinant` to `C^n` maps and diffeomorphisms at every
regularity `n` (holomorphic when `I = 𝓘(ℂ, EB)` and `n = ∞`):

* `detExteriorPowerDiffeomorph` upgrades `detExteriorPowerIso A hr` and
  `contMDiff_totalSpaceMap_detMap` transfers `C^n` regularity of bundle maps to `detMap`.
* Over a complete field, `dualDetDiffeomorph` upgrades `dualDetIso A`, and
  `dualDetTopFormTotalSpaceDiffeomorph` upgrades `dualDetTopFormTotalSpaceHomeomorph A`.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

section General

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- For `r = A.rank`, `detExteriorPowerIso A hr` induces a `C^n` diffeomorphism of total spaces
between `A.det` and `(exteriorPower 𝕜 B r).obj A`. -/
noncomputable def detExteriorPowerDiffeomorph (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
    (hr : A.rank = r) (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    A.det.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin ((exteriorPower 𝕜 B r).obj A).rank → 𝕜)⟯
        ((exteriorPower 𝕜 B r).obj A).core.TotalSpace :=
  constIsoDiffeomorph (A := A.det) (D := (exteriorPower 𝕜 B r).obj A)
    (fun i ↦ (baseSet_det A i).trans (localTriv_baseSet_exteriorPower_obj r A i).symm)
    ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 hr).symm)
    fun i j x _ _ ↦ coordChange_comp_detExteriorPower A hr i j x

@[simp] theorem coe_detExteriorPowerDiffeomorph (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
    (hr : A.rank = r) :
    ⇑(detExteriorPowerDiffeomorph A hr I n) = (detExteriorPowerIso A hr).hom.totalSpaceMap := by
  rw [detExteriorPowerDiffeomorph, coe_constIsoDiffeomorph]
  refine congrArg CoordinateHom.totalSpaceMap (hom_ext fun x ↦ ContinuousLinearMap.ext fun u ↦
    (topExteriorScalarEquiv 𝕜 hr).injective ?_)
  exact (congrArg (topExteriorScalarEquiv 𝕜 hr) (DFunLike.congr_fun
    (fiberMap_constIso_hom (A := A.det) (D := (exteriorPower 𝕜 B r).obj A)
      _ ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 hr).symm) _ x) u)).trans
    (((topExteriorScalarEquiv 𝕜 hr).apply_symm_apply _).trans
      (topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom A hr x u).symm)

@[simp] theorem coe_detExteriorPowerDiffeomorph_symm (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
    (hr : A.rank = r) :
    ⇑(detExteriorPowerDiffeomorph A hr I n).symm =
      (detExteriorPowerIso A hr).inv.totalSpaceMap := by
  rw [detExteriorPowerDiffeomorph, coe_constIsoDiffeomorph_symm]
  refine congrArg CoordinateHom.totalSpaceMap (hom_ext fun x ↦ ContinuousLinearMap.ext fun w ↦
    (detScalarEquiv A).injective ?_)
  exact (congrArg (detScalarEquiv A) (DFunLike.congr_fun
    (fiberMap_constIso_inv (A := A.det) (D := (exteriorPower 𝕜 B r).obj A)
      _ ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 hr).symm) _ x) w)).trans
    (((detScalarEquiv A).apply_symm_apply _).trans
      (detScalarEquiv_fiberMap_detExteriorPowerIso_inv A hr x w).symm)

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
      (by
        rw [← coe_detExteriorPowerDiffeomorph_symm (I := I) (n := n) D hD]
        exact (detExteriorPowerDiffeomorph D hD I n).symm.contMDiff)
      (contMDiff_totalSpaceMap_exteriorPower_map r f hf))
    (by
      rw [← coe_detExteriorPowerDiffeomorph (I := I) (n := n) A hA]
      exact (detExteriorPowerDiffeomorph A hA I n).contMDiff)

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
  constIsoDiffeomorph (A := A.dual.det) (D := A.det.dual)
    (fun i ↦ (baseSet_det A.dual i).trans ((localTriv_baseSet_dual A i).trans
      ((baseSet_det A i).symm.trans (localTriv_baseSet_dual A.det i).symm)))
    ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm)
    fun i j x _ _ ↦ coordChange_comp_dualDet A i j x

@[simp] theorem coe_dualDetDiffeomorph (A : FiniteRankBundleCore 𝕜 B) :
    ⇑(dualDetDiffeomorph A I n) = (dualDetIso A).hom.totalSpaceMap := by
  rw [dualDetDiffeomorph, coe_constIsoDiffeomorph]
  refine congrArg CoordinateHom.totalSpaceMap (hom_ext fun x ↦ ContinuousLinearMap.ext fun u ↦
    (detScalarEquiv A).injective ?_)
  exact (congrArg (detScalarEquiv A)
    (DFunLike.congr_fun (fiberMap_constIso_hom (A := A.dual.det) (D := A.det.dual)
      _ ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm) _ x) u)).trans
    (((detScalarEquiv A).apply_symm_apply _).trans
      (detScalarEquiv_fiberMap_dualDetIso_hom A x u).symm)

@[simp] theorem coe_dualDetDiffeomorph_symm (A : FiniteRankBundleCore 𝕜 B) :
    ⇑(dualDetDiffeomorph A I n).symm = (dualDetIso A).inv.totalSpaceMap := by
  rw [dualDetDiffeomorph, coe_constIsoDiffeomorph_symm]
  refine congrArg CoordinateHom.totalSpaceMap (hom_ext fun x ↦ ContinuousLinearMap.ext fun u ↦
    (detScalarEquiv A.dual).injective ?_)
  exact (congrArg (detScalarEquiv A.dual)
    (DFunLike.congr_fun (fiberMap_constIso_inv (A := A.dual.det) (D := A.det.dual)
      _ ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm) _ x) u)).trans
    (((detScalarEquiv A.dual).apply_symm_apply _).trans
      (detScalarEquiv_fiberMap_dualDetIso_inv A x u).symm)

/-- Reading `A.dual.det` vectors as top-degree continuous alternating forms on `A.core.Fiber` is
`C^n` on total spaces at every regularity `n`, without smoothness or characteristic assumptions. -/
theorem contMDiff_dualDetTopFormFiberEquiv (A : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.dual.det.rank → 𝕜))
      (I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)) n
      (fun p : A.dual.det.core.TotalSpace ↦
        TotalSpace.mk' ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
          (E := fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) p.proj
          (dualDetTopFormFiberEquiv A p.proj p.snd)) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hU := (A.dual.det.core.localTriv p₀.proj).open_source.mem_nhds
    ((A.dual.det.core.mem_localTriv_source p₀.proj p₀).2 (A.dual.det.mem_baseSet_self p₀.proj))
  exact (((detScalarEquiv A.dual).trans
    (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm).contDiff.comp_contMDiffAt
    (A.dual.det.contMDiffAt_localTriv_snd p₀)).congr_of_eventuallyEq
      (Filter.eventually_of_mem hU fun ⟨x, u⟩ hq ↦
        dualDetTopFormFiberEquiv_inCoordinates A p₀.proj x
          (by simpa [baseSet_det] using (A.dual.det.core.mem_localTriv_source p₀.proj ⟨x, u⟩).1 hq)
          u)

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
      dualDetTopFormTotalSpaceHomeomorph A :=
  Homeomorph.ext fun p ↦ (bundleDiffeomorph_apply ..).trans
    (dualDetTopFormTotalSpaceHomeomorph_apply A p).symm

@[simp] theorem dualDetTopFormTotalSpaceDiffeomorph_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    dualDetTopFormTotalSpaceDiffeomorph A I n p =
      ⟨p.proj, dualDetTopFormFiberEquiv A p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

@[simp] theorem dualDetTopFormTotalSpaceDiffeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
      (fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜)) :
    (dualDetTopFormTotalSpaceDiffeomorph A I n).symm p =
      ⟨p.proj, (dualDetTopFormFiberEquiv A p.proj).symm p.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end Dual

end TauCeti.FiniteRankBundleCore
