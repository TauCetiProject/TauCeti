/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.FiniteRank
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Determinant
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Determinant of the cotangent core and comparison with the canonical line bundle

Develops the determinant line `(cotangentCore I b M).det` for a basis `b : Basis (Fin r) 𝕜 E` on a
`C¹` manifold `M` modelled on `I : ModelWithCorners 𝕜 E H` over a complete field `𝕜`, and
identifies it smoothly (and biholomorphically on complex manifolds) with `CanonicalBundle I M`:

1. **Rank-generic cotangent determinant:** `coordChange_cotangentCore_det`,
   `isContMDiff_cotangentCore_det`, `tangentDualDetCotangentDetIso`, and
   `cotangentDetChangeBasisIso` (scaling coordinates by `b₁.det b₂`).
2. **Comparison with `CanonicalBundle I M`:** for `b : Basis (Fin (finrank 𝕜 E)) 𝕜 E`,
   `canonicalCore`, `cotangentDetCanonicalCoreIso`, `cotangentDetCanonicalFiberEquiv`,
   `cotangentDetCanonicalDiffeomorph`, `cotangentDetCanonicalHomeomorph`,
   `cotangentDetCanonicalFiberEquiv_localTriv_symm_one`, and
   `cotangentDetCanonicalFiberEquiv_changeBasis`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1, Section 1.
-/

public section

open Bundle CategoryTheory Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

/-! ### Rank-generic determinant of the cotangent core -/

section CotangentDeterminant

variable {r : ℕ} {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- On a `C^(k+1)` manifold, `(cotangentCore I b M).det` is a `C^k` line core (holomorphic when
`I = 𝓘(ℂ, E)` and `k = ∞`). -/
theorem isContMDiff_cotangentCore_det (b : Basis (Fin r) 𝕜 E) {k : ℕ∞ω} [IsManifold I (k + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
    (cotangentCore I b M).det.core.IsContMDiff I k := by
  have : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
  have := isContMDiff_cotangentCore (I := I) (M := M) (k := k) b
  infer_instance

variable [IsManifold I 1 M]

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `(cotangentCore I b M).det` is
scalar multiplication by `LinearMap.det (tangentCoordChange I x₁ x₀ x)`, independent of `b`. -/
theorem coordChange_cotangentCore_det (b : Basis (Fin r) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (cotangentCore I b M).det.core.coordChange x₀ x₁ x =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) •
        ContinuousLinearMap.id 𝕜 (Fin (cotangentCore I b M).det.rank → 𝕜) := by
  rw [FiniteRankBundleCore.coordChange_det, coordChange_cotangentCore b hx₀ hx₁]
  exact congrArg (· • ContinuousLinearMap.id 𝕜 _)
    ((ContinuousLinearMap.det_piTranspose _).trans (b.equivFunL.det_arrowCongr_self _))

/-- Determinant isomorphism `(tangentCore I b M).dual.det ≅ (cotangentCore I b M).det` induced by
`tangentDualCotangentIso I b M`. -/
noncomputable def tangentDualDetCotangentDetIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (tangentCore I b M).dual.det ≅ (cotangentCore I b M).det :=
  FiniteRankBundleCore.detIso r (tangentDualCotangentIso I b M)
    ((FiniteRankBundleCore.rank_dual _).trans (rank_tangentCore b))
    (rank_cotangentCore b)

/-- The forward map of `tangentDualDetCotangentDetIso` preserves determinant scalar coordinates. -/
theorem detScalarEquiv_fiberMap_tangentDualDetCotangentDetIso_hom
    (b : Basis (Fin r) 𝕜 E) (x : M) (u : Fin (tangentCore I b M).dual.det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)
        ((tangentDualDetCotangentDetIso I b M).hom.fiberMap x u) =
      FiniteRankBundleCore.detScalarEquiv (tangentCore I b M).dual u := by
  rw [tangentDualDetCotangentDetIso, FiniteRankBundleCore.detIso_hom,
    FiniteRankBundleCore.detMap_def,
    FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    FiniteRankBundleCore.detScalarEquiv_fiberMap_detExteriorPowerIso_inv,
    FiniteRankBundleCore.fiberMap_exteriorPower_map, fiberMap_tangentDualCotangentIso_hom]
  refine (FiniteRankBundleCore.topExteriorScalarEquiv_exteriorPowerCoords_self
    (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜)) _).trans ?_
  rw [ContinuousLinearMap.det_id, one_mul]
  exact FiniteRankBundleCore.topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom _ _ x u

/-- The inverse map of `tangentDualDetCotangentDetIso` preserves determinant scalar coordinates. -/
theorem detScalarEquiv_fiberMap_tangentDualDetCotangentDetIso_inv
    (b : Basis (Fin r) 𝕜 E) (x : M) (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (tangentCore I b M).dual
        ((tangentDualDetCotangentDetIso I b M).inv.fiberMap x u) =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := by
  rw [← detScalarEquiv_fiberMap_tangentDualDetCotangentDetIso_hom b x
      ((tangentDualDetCotangentDetIso I b M).inv.fiberMap x u),
    ← ContinuousLinearMap.comp_apply, ← FiniteRankBundleCore.fiberMap_comp,
    Iso.inv_hom_id, FiniteRankBundleCore.fiberMap_id, ContinuousLinearMap.id_apply]

/-- Determinant isomorphism `(cotangentCore I b₁ M).det ≅ (cotangentCore I b₂ M).det` induced by
changing the model basis from `b₁` to `b₂`. -/
noncomputable def cotangentDetChangeBasisIso
    (I : ModelWithCorners 𝕜 E H) (b₁ b₂ : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b₁ M).det ≅ (cotangentCore I b₂ M).det :=
  FiniteRankBundleCore.detIso r
    (FiniteRankBundleCore.ofLinearEquivChangeIso
      (FiniteRankBundleCore.dualCoords b₁.equivFunL)
      (FiniteRankBundleCore.dualCoords b₂.equivFunL)
      (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜))
    (rank_cotangentCore b₁) (rank_cotangentCore b₂)

/-- Changing the model basis from `b₁` to `b₂` multiplies scalar coordinates in
`(cotangentCore I b M).det` by `b₁.det b₂`. -/
theorem detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom
    (b₁ b₂ : Basis (Fin r) 𝕜 E) (x : M) (u : Fin (cotangentCore I b₁ M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₂ M)
        ((cotangentDetChangeBasisIso I b₁ b₂ M).hom.fiberMap x u) =
      b₁.det b₂ * FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₁ M) u :=
  (FiniteRankBundleCore.detScalarEquiv_fiberMap_ofLinearEquivChangeIso_hom
    (FiniteRankBundleCore.dualCoords b₁.equivFunL)
    (FiniteRankBundleCore.dualCoords b₂.equivFunL)
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x u).trans
    (congrArg (· * _) (FiniteRankBundleCore.det_dualCoords_equivFunL_symm_trans b₁ b₂))

/-- The inverse change-of-basis map from `b₂` to `b₁` multiplies scalar coordinates in
`(cotangentCore I b M).det` by `b₂.det b₁`. -/
theorem detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_inv
    (b₁ b₂ : Basis (Fin r) 𝕜 E) (x : M) (u : Fin (cotangentCore I b₂ M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₁ M)
        ((cotangentDetChangeBasisIso I b₁ b₂ M).inv.fiberMap x u) =
      b₂.det b₁ * FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₂ M) u :=
  (FiniteRankBundleCore.detScalarEquiv_fiberMap_ofLinearEquivChangeIso_inv
    (FiniteRankBundleCore.dualCoords b₁.equivFunL)
    (FiniteRankBundleCore.dualCoords b₂.equivFunL)
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x u).trans
    (congrArg (· * _) (FiniteRankBundleCore.det_dualCoords_equivFunL_symm_trans b₂ b₁))

end CotangentDeterminant

/-! ### Comparison of `(cotangentCore I b M).det` with `CanonicalBundle I M` -/

section CanonicalComparison

variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Scalar coordinate equivalence on the model fibre `E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜` of
`CanonicalBundle I M`, evaluating a model top-degree form on `b` in `Fin 1 → 𝕜`. -/
noncomputable def canonicalModelCoords (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) ≃L[𝕜] (Fin 1 → 𝕜) :=
  b.topFormEquiv.trans (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm

/-- `canonicalModelCoords b` evaluates a model top-degree alternating form on the basis `b`. -/
@[simp] theorem canonicalModelCoords_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (η : E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (i : Fin 1) :
    canonicalModelCoords b η i = η b :=
  b.topFormEquiv_apply η

/-- The inverse of `canonicalModelCoords b` scales `b.continuousDet` by the unique coordinate. -/
@[simp] theorem canonicalModelCoords_symm_apply (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (u : Fin 1 → 𝕜) :
    (canonicalModelCoords b).symm u = u 0 • b.continuousDet :=
  b.topFormEquiv_symm_eq_smul (u 0)

variable [IsManifold I 1 M]

/-- The finite-rank line core presenting `CanonicalBundle I M` in `canonicalModelCoords b`. -/
noncomputable def canonicalCore (I : ModelWithCorners 𝕜 E H)
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] :
    FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofLinearEquiv (canonicalModelCoords b) (CanonicalBundle I M)

/-- The canonical line core has rank one. -/
@[simp] theorem rank_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    (canonicalCore I b M).rank = 1 := (rfl)

/-- The chart domain of `canonicalCore I b M` at `x₀` is `(chartAt H x₀).source`. -/
theorem baseSet_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x₀ : M) :
    (canonicalCore I b M).core.baseSet x₀ = (chartAt H x₀).source := by
  simp [canonicalCore]

/-- The base set of the local trivialization of `canonicalCore I b M` at `x₀` is the chart
source. -/
@[simp] theorem localTriv_baseSet_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x₀ : M) :
    ((canonicalCore I b M).core.localTriv x₀).baseSet = (chartAt H x₀).source :=
  baseSet_canonicalCore b x₀

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `canonicalCore I b M` is
scalar multiplication by `LinearMap.det (tangentCoordChange I x₁ x₀ x)`. -/
theorem coordChange_canonicalCore (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (canonicalCore I b M).core.coordChange x₀ x₁ x =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) •
        ContinuousLinearMap.id 𝕜 (Fin (canonicalCore I b M).rank → 𝕜) := by
  refine (FiniteRankBundleCore.coordChange_ofLinearEquiv (canonicalModelCoords b)
    (CanonicalBundle I M) x₀ x₁ x).trans ?_
  ext u i
  let F := E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜
  have hb₀ : x ∈ (trivializationAt F (CanonicalBundle I M) x₀).baseSet := by simpa [F] using hx₀
  rw [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.coe_coe,
    canonicalModelCoords_apply, Trivialization.coordChangeL_apply _ _ ⟨hb₀, by simpa [F] using hx₁⟩,
    CanonicalBundle.trivializationAt_apply_snd_basis_eq_det_mul hx₀ hx₁ _ b,
    Trivialization.apply_mk_symm _ hb₀, canonicalModelCoords_symm_apply]
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp [b.det_self]; rfl

/-- Core-level isomorphism in `FiniteRankBundleCore 𝕜 M` between `(cotangentCore I b M).det` and
`canonicalCore I b M`, preserving scalar coordinates. -/
noncomputable def cotangentDetCanonicalCoreIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b M).det ≅ canonicalCore I b M :=
  FiniteRankBundleCore.constIso
    (fun _ ↦ by
      rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore, baseSet_canonicalCore])
    ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm)
    fun x₀ x₁ x hx₀ hx₁ ↦ by
      rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore] at hx₀ hx₁
      ext u : 1
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        coordChange_cotangentCore_det b hx₀ hx₁, coordChange_canonicalCore b hx₀ hx₁]
      simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul]

/-- Every coordinate entry of `(cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u` is
`detScalarEquiv (cotangentCore I b M) u`. -/
@[simp] theorem fiberMap_cotangentDetCanonicalCoreIso_hom_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b M).det.rank → 𝕜) (i : Fin (canonicalCore I b M).rank) :
    (cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u i =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := by
  rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_hom]; rfl

/-- Every coordinate entry of `(cotangentDetCanonicalCoreIso I b M).inv.fiberMap x w` is the unique
coordinate entry of `w` in `canonicalCore I b M`. -/
@[simp] theorem fiberMap_cotangentDetCanonicalCoreIso_inv_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (w : Fin (canonicalCore I b M).rank → 𝕜) (i : Fin (cotangentCore I b M).det.rank) :
    (cotangentDetCanonicalCoreIso I b M).inv.fiberMap x w i =
      w ⟨0, (rank_canonicalCore (I := I) (M := M) b) ▸ Nat.zero_lt_one⟩ := by
  rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_inv]
  exact (congrFun (ContinuousLinearEquiv.symm_trans_apply
    (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm
    (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)) w) i).trans
    (FiniteRankBundleCore.detScalarEquiv_symm_apply (cotangentCore I b M) _ i)

/-- Fibrewise continuous linear equivalence identifying `(cotangentCore I b M).det.core.Fiber x`
with `CanonicalBundle I M x` via `detScalarEquiv` and `CanonicalBundle.coordForm`. -/
noncomputable def cotangentDetCanonicalFiberEquiv
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (x : M) :
    (cotangentCore I b M).det.core.Fiber x ≃L[𝕜] CanonicalBundle I M x :=
  ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans b.topFormEquiv.symm).trans
    (VectorBundle.continuousLinearEquivAt 𝕜 (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)
      (CanonicalBundle I M) x).symm

/-- `cotangentDetCanonicalFiberEquiv` sends `u` to the corresponding scalar multiple of
`CanonicalBundle.coordForm I x b x`. -/
@[simp] theorem cotangentDetCanonicalFiberEquiv_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M) (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
    cotangentDetCanonicalFiberEquiv I b M x u =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u •
        CanonicalBundle.coordForm I x b x := by
  let F := E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜
  refine (ContinuousLinearEquiv.trans_apply
    ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans b.topFormEquiv.symm)
    (VectorBundle.continuousLinearEquivAt 𝕜 F (CanonicalBundle I M) x).symm u).trans ?_
  rw [ContinuousLinearEquiv.trans_apply, b.topFormEquiv_symm_eq_smul, map_smul,
    VectorBundle.continuousLinearEquivAt_symm_apply,
    ← CanonicalBundle.trivializationAt_apply_snd_coordForm (I := I) (b := b) (mem_chart_source H x),
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F (CanonicalBundle I M) x)]

/-- The inverse of `cotangentDetCanonicalFiberEquiv` evaluates `η` on the coordinate basis vectors
`(trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i)`. -/
@[simp] theorem cotangentDetCanonicalFiberEquiv_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M) (η : CanonicalBundle I M x) :
    (cotangentDetCanonicalFiberEquiv I b M x).symm η =
      (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm
        (η fun i ↦ (trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i)) := by
  apply (cotangentDetCanonicalFiberEquiv I b M x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, cotangentDetCanonicalFiberEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  have htriv : (trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) x
      ⟨x, η⟩).2 b = η fun i ↦ (trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i) := by
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]; rfl
  rw [← htriv]
  exact CanonicalBundle.eq_smul_coordForm (b := b) (mem_chart_source H x) η

private theorem contMDiff_cotangentDetCanonicalFiberEquiv (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    {k : ℕ∞ω} :
    ContMDiff (I.prod 𝓘(𝕜, Fin (cotangentCore I b M).det.rank → 𝕜))
      (I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)) k
      (fun p : (cotangentCore I b M).det.core.TotalSpace ↦
        TotalSpace.mk' (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (E := CanonicalBundle I M)
          p.proj (cotangentDetCanonicalFiberEquiv I b M p.proj p.snd)) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hU := ((cotangentCore I b M).det.core.localTriv p₀.proj).open_source.mem_nhds
    (((cotangentCore I b M).det.core.mem_localTriv_source p₀.proj p₀).2
      ((cotangentCore I b M).det.mem_baseSet_self p₀.proj))
  refine (((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
    b.topFormEquiv.symm).contDiff.comp_contMDiffAt
    ((cotangentCore I b M).det.contMDiffAt_localTriv_snd p₀)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with ⟨x, w⟩ hq
  have hx₀ : x ∈ (chartAt H p₀.proj).source := by
    simpa [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore] using
      ((cotangentCore I b M).det.core.mem_localTriv_source p₀.proj ⟨x, w⟩).1 hq
  have hlhs (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
      b.topFormEquiv (trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)
        (CanonicalBundle I M) p₀.proj ⟨x, cotangentDetCanonicalFiberEquiv I b M x u⟩).2 =
      LinearMap.det (tangentCoordChange I p₀.proj x x : E →ₗ[𝕜] E) *
        FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := by
    rw [b.topFormEquiv_apply, cotangentDetCanonicalFiberEquiv_apply,
      CanonicalBundle.trivializationAt_apply_snd_basis_eq_det_mul (mem_chart_source H x) hx₀ _ b,
      ← Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ (mem_baseSet_trivializationAt _ _ x),
      map_smul, Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _
        (mem_baseSet_trivializationAt _ _ x),
      CanonicalBundle.trivializationAt_apply_snd_coordForm (mem_chart_source H x)]
    simp [b.det_self]
  have hrhs (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
      b.topFormEquiv (((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
        b.topFormEquiv.symm)
        (((cotangentCore I b M).det.core.coordChange x p₀.proj x) u)) =
      LinearMap.det (tangentCoordChange I p₀.proj x x : E →ₗ[𝕜] E) *
        FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
      coordChange_cotangentCore_det b (mem_chart_source H x) hx₀]
    simp [_root_.smul_apply]
  apply b.topFormEquiv.injective
  dsimp only [Function.comp_apply]
  rw [VectorBundleCore.localTriv_apply, (cotangentCore I b M).det.indexAt_eq]
  -- `VectorBundleCore.Fiber` is a semireducible `def` equal to the model fibre
  -- `Fin (cotangentCore I b M).det.rank → 𝕜` with no wrapper lemma in Mathlib, so `rw` cannot
  -- bridge them at reducible transparency; pass `w` directly into `hlhs` and `hrhs`.
  exact (hlhs w).trans (hrhs w).symm

/-- The reconstructed total space of `(cotangentCore I b M).det` is `C^k` diffeomorphic over `M` to
`CanonicalBundle I M` at every regularity `k` (biholomorphic when `I = 𝓘(ℂ, E)` and `k = ∞`). -/
noncomputable def cotangentDetCanonicalDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).det.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).det.rank → 𝕜),
      I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)⟯
        TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  bundleDiffeomorph (cotangentDetCanonicalFiberEquiv I b M)
    (contMDiff_cotangentDetCanonicalFiberEquiv b)

/-- Topological bundle equivalence underlying `cotangentDetCanonicalDiffeomorph`. -/
noncomputable def cotangentDetCanonicalHomeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b M).det.core.TotalSpace ≃ₜ
      TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  (cotangentDetCanonicalDiffeomorph I b M 0).toHomeomorph

/-- On total spaces, `cotangentDetCanonicalDiffeomorph` acts fibrewise by
`cotangentDetCanonicalFiberEquiv`. -/
@[simp] theorem cotangentDetCanonicalDiffeomorph_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : (cotangentCore I b M).det.core.TotalSpace) :
    cotangentDetCanonicalDiffeomorph I b M k p =
      ⟨p.proj, cotangentDetCanonicalFiberEquiv I b M p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

/-- On total spaces, the inverse of `cotangentDetCanonicalDiffeomorph` acts fibrewise by
`(cotangentDetCanonicalFiberEquiv I b M p.proj).symm`. -/
@[simp] theorem cotangentDetCanonicalDiffeomorph_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)) :
    (cotangentDetCanonicalDiffeomorph I b M k).symm p =
      ⟨p.proj, (cotangentDetCanonicalFiberEquiv I b M p.proj).symm p.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

/-- The underlying homeomorphism of `cotangentDetCanonicalDiffeomorph` at any regularity `k` agrees
with `cotangentDetCanonicalHomeomorph`. -/
@[simp] theorem cotangentDetCanonicalDiffeomorph_toHomeomorph
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω) :
    (cotangentDetCanonicalDiffeomorph I b M k).toHomeomorph =
      cotangentDetCanonicalHomeomorph I b M :=
  Homeomorph.ext fun p ↦ (cotangentDetCanonicalDiffeomorph_apply b k p).trans
    (cotangentDetCanonicalDiffeomorph_apply b 0 p).symm

/-- Over the chart at `x₀`, the unit scalar coordinate `1` in the `x₀`-trivialization of
`(cotangentCore I b M).det` maps to `dz₁ ∧ ⋯ ∧ dzₙ = CanonicalBundle.coordForm I x₀ b x`. -/
theorem cotangentDetCanonicalFiberEquiv_localTriv_symm_one
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x : M} (hx₀ : x ∈ (chartAt H x₀).source) :
    cotangentDetCanonicalFiberEquiv I b M x
        (((cotangentCore I b M).det.core.localTriv x₀).symm x
          ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm 1)) =
      CanonicalBundle.coordForm I x₀ b x := by
  have hb₀ : x ∈ ((cotangentCore I b M).det.core.localTriv x₀).baseSet := by
    rwa [FiniteRankBundleCore.localTriv_baseSet_det, baseSet_cotangentCore]
  rw [((cotangentCore I b M).det.core).localTriv_symm_apply (i := x₀) hb₀,
    (cotangentCore I b M).det.indexAt_eq, cotangentDetCanonicalFiberEquiv_apply,
    coordChange_cotangentCore_det b hx₀ (mem_chart_source H x)]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  exact (CanonicalBundle.coordForm_eq_det_smul_coordForm hx₀ (mem_chart_source H x)).symm

/-- The canonical identification `cotangentDetCanonicalFiberEquiv` commutes with changes of model
basis. -/
theorem cotangentDetCanonicalFiberEquiv_changeBasis
    (b₁ b₂ : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M) (u : Fin (cotangentCore I b₁ M).det.rank → 𝕜) :
    cotangentDetCanonicalFiberEquiv I b₂ M x
        ((cotangentDetChangeBasisIso I b₁ b₂ M).hom.fiberMap x u) =
      cotangentDetCanonicalFiberEquiv I b₁ M x u := by
  rw [cotangentDetCanonicalFiberEquiv_apply, cotangentDetCanonicalFiberEquiv_apply,
    detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom,
    CanonicalBundle.coordForm_basis_change x b₁ b₂ x, smul_smul, mul_comm]

end CanonicalComparison

end TauCeti
