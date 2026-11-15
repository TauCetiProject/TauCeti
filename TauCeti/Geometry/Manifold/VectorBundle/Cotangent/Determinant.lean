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

Let `M` be a `C¹` manifold modelled on `I : ModelWithCorners 𝕜 E H` over a complete nontrivially
normed field `𝕜`, equipped with a finite basis `b : Basis (Fin r) 𝕜 E` of the model space. Using
the finite-rank tangent and cotangent cores from
`TauCeti.Geometry.Manifold.VectorBundle.Tangent.FiniteRank` and
`TauCeti.Geometry.Manifold.VectorBundle.Cotangent.FiniteRank`, this file develops the determinant
line `(cotangentCore I b M).det` and identifies it smoothly (and biholomorphically on complex
manifolds) with `TauCeti.CanonicalBundle I M`:

1. **Rank-generic cotangent determinant.** For any basis `b : Basis (Fin r) 𝕜 E`, the transition
   maps of `(cotangentCore I b M).det` are scalar multiplication by
   `LinearMap.det (tangentCoordChange I x₁ x₀ x)`, independent of `b`
   (`coordChange_cotangentCore_det`). On a `C^(k+1)` manifold, `(cotangentCore I b M).det` is a
   `C^k` line core (`isContMDiff_cotangentCore_det`); on a complex manifold (`I = 𝓘(ℂ, E)`,
   `k = ∞`) it is holomorphic. The duality isomorphism `tangentDualCotangentIso` induces
   `tangentDualDetCotangentDetIso : (tangentCore I b M).dual.det ≅ (cotangentCore I b M).det`
   preserving scalar coordinates, and changing the model basis from `b₁` to `b₂` induces
   `cotangentDetChangeBasisIso`, scaling determinant coordinates by `b₁.det b₂`
   (`detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom`).
2. **Comparison with `CanonicalBundle I M`.** When `b : Basis (Fin (finrank 𝕜 E)) 𝕜 E`, evaluating
   model top-degree forms on `b` presents `CanonicalBundle I M` as the line core
   `TauCeti.canonicalCore I b M`, canonically isomorphic to `(cotangentCore I b M).det`
   (`cotangentDetCanonicalCoreIso`). Composing with the reconstruction diffeomorphism yields
   `TauCeti.cotangentDetCanonicalDiffeomorph` (and `TauCeti.cotangentDetCanonicalHomeomorph`),
   which sends the unit scalar coordinate in the chart at `x₀` to the coordinate form
   `dz₁ ∧ ⋯ ∧ dzₙ = CanonicalBundle.coordForm I x₀ b`
   (`cotangentDetCanonicalFiberEquiv_localTriv_symm_one`) and commutes with changes of model basis
   (`cotangentDetCanonicalFiberEquiv_changeBasis`).

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* Phillip Griffiths and Joseph Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1,
  Section 1.
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

/-- On a `C^(k+1)` manifold, the determinant line `(cotangentCore I b M).det` is a `C^k` line core
(holomorphic when `I = 𝓘(ℂ, E)` and `k = ∞`). -/
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
    (b : Basis (Fin r) 𝕜 E) (x : M)
    (u : Fin (tangentCore I b M).dual.det.rank → 𝕜) :
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
  exact FiniteRankBundleCore.topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom
    (tangentCore I b M).dual _ x u

/-- The inverse map of `tangentDualDetCotangentDetIso` preserves determinant scalar coordinates. -/
theorem detScalarEquiv_fiberMap_tangentDualDetCotangentDetIso_inv
    (b : Basis (Fin r) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (tangentCore I b M).dual
        ((tangentDualDetCotangentDetIso I b M).inv.fiberMap x u) =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := by
  rw [tangentDualDetCotangentDetIso, FiniteRankBundleCore.detIso_inv,
    FiniteRankBundleCore.detMap_def,
    FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    FiniteRankBundleCore.detScalarEquiv_fiberMap_detExteriorPowerIso_inv,
    FiniteRankBundleCore.fiberMap_exteriorPower_map, fiberMap_tangentDualCotangentIso_inv]
  refine (FiniteRankBundleCore.topExteriorScalarEquiv_exteriorPowerCoords_self
    (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜)) _).trans ?_
  rw [ContinuousLinearMap.det_id, one_mul]
  exact FiniteRankBundleCore.topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom
    (cotangentCore I b M) _ x u

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
    (rank_cotangentCore b₁)
    (rank_cotangentCore b₂)

/-- Changing the model basis from `b₁` to `b₂` multiplies scalar coordinates in
`(cotangentCore I b M).det` by `b₁.det b₂`. -/
theorem detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom
    (b₁ b₂ : Basis (Fin r) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b₁ M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₂ M)
        ((cotangentDetChangeBasisIso I b₁ b₂ M).hom.fiberMap x u) =
      b₁.det b₂ * FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₁ M) u := by
  refine (FiniteRankBundleCore.detScalarEquiv_fiberMap_ofLinearEquivChangeIso_hom
    (FiniteRankBundleCore.dualCoords b₁.equivFunL)
    (FiniteRankBundleCore.dualCoords b₂.equivFunL)
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x u).trans ?_
  exact congrArg (· * _) (FiniteRankBundleCore.det_dualCoords_equivFunL_symm_trans b₁ b₂)

/-- The inverse change-of-basis map from `b₂` to `b₁` multiplies scalar coordinates in
`(cotangentCore I b M).det` by `b₂.det b₁`. -/
theorem detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_inv
    (b₁ b₂ : Basis (Fin r) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b₂ M).det.rank → 𝕜) :
    FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₁ M)
        ((cotangentDetChangeBasisIso I b₁ b₂ M).inv.fiberMap x u) =
      b₂.det b₁ * FiniteRankBundleCore.detScalarEquiv (cotangentCore I b₂ M) u := by
  refine (FiniteRankBundleCore.detScalarEquiv_fiberMap_ofLinearEquivChangeIso_inv
    (FiniteRankBundleCore.dualCoords b₁.equivFunL)
    (FiniteRankBundleCore.dualCoords b₂.equivFunL)
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x u).trans ?_
  exact congrArg (· * _) (FiniteRankBundleCore.det_dualCoords_equivFunL_symm_trans b₂ b₁)

end CotangentDeterminant

/-! ### Comparison of `(cotangentCore I b M).det` with `CanonicalBundle I M` -/

section CanonicalComparison

variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Scalar coordinate equivalence on the model fibre `E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜` of
`CanonicalBundle I M` determined by `b`: evaluates a model top-degree form on `b` and views the
resulting scalar in `Fin 1 → 𝕜`. -/
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

/-- The chart domain of `canonicalCore I b M` at `x₀` is the chart source
`(chartAt H x₀).source`. -/
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
  have hb₁ : x ∈ (trivializationAt F (CanonicalBundle I M) x₁).baseSet := by simpa [F] using hx₁
  rw [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.coe_coe,
    canonicalModelCoords_apply, Trivialization.coordChangeL_apply _ _ ⟨hb₀, hb₁⟩,
    CanonicalBundle.trivializationAt_apply_snd_basis_eq_det_mul hx₀ hx₁ _ b,
    Trivialization.apply_mk_symm _ hb₀, canonicalModelCoords_symm_apply]
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [ContinuousAlternatingMap.smul_apply, Basis.continuousDet_apply, b.det_self,
    smul_eq_mul, mul_one]
  rw [← smul_eq_mul]
  rfl

/-- Core-level isomorphism in `FiniteRankBundleCore 𝕜 M` between the finite-rank determinant of the
cotangent core `(cotangentCore I b M).det` and `canonicalCore I b M`, preserving scalar
coordinates. -/
noncomputable def cotangentDetCanonicalCoreIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (cotangentCore I b M).det ≅ canonicalCore I b M :=
  FiniteRankBundleCore.constIso
    (fun x₀ ↦ by
      rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore, baseSet_canonicalCore])
    ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm)
    fun x₀ x₁ x hx₀ hx₁ ↦ by
      rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore] at hx₀ hx₁
      ext u : 1
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        coordChange_cotangentCore_det b hx₀ hx₁, coordChange_canonicalCore b hx₀ hx₁]
      simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul]

/-- Every coordinate entry of `(cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u` is the
determinant scalar coordinate `detScalarEquiv (cotangentCore I b M) u`. -/
@[simp] theorem fiberMap_cotangentDetCanonicalCoreIso_hom_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b M).det.rank → 𝕜) (i : Fin (canonicalCore I b M).rank) :
    (cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u i =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u := by
  rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_hom]
  rfl

/-- Every coordinate entry of `(cotangentDetCanonicalCoreIso I b M).inv.fiberMap x w` is the unique
coordinate entry of `w` in `canonicalCore I b M`. -/
@[simp] theorem fiberMap_cotangentDetCanonicalCoreIso_inv_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (w : Fin (canonicalCore I b M).rank → 𝕜) (i : Fin (cotangentCore I b M).det.rank) :
    (cotangentDetCanonicalCoreIso I b M).inv.fiberMap x w i =
      w ⟨0, (rank_canonicalCore (I := I) (M := M) b) ▸ Nat.zero_lt_one⟩ := by
  rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_inv]
  refine (congrFun
    (ContinuousLinearEquiv.symm_trans_apply
      (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm
      (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)) w) i).trans ?_
  exact FiniteRankBundleCore.detScalarEquiv_symm_apply (cotangentCore I b M) _ i

/-- Fibrewise continuous linear equivalence identifying `(cotangentCore I b M).det.core.Fiber x`
with `CanonicalBundle I M x` by multiplying `CanonicalBundle.coordForm I x b x` by the scalar
coordinate `detScalarEquiv (cotangentCore I b M)`. -/
noncomputable def cotangentDetCanonicalFiberEquiv
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (x : M) :
    (cotangentCore I b M).det.core.Fiber x ≃L[𝕜] CanonicalBundle I M x :=
  ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans b.topFormEquiv.symm).trans
    (VectorBundle.continuousLinearEquivAt 𝕜 (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)
      (CanonicalBundle I M) x).symm

/-- `cotangentDetCanonicalFiberEquiv` sends a determinant fibre vector `u` to the corresponding
scalar multiple of `CanonicalBundle.coordForm I x b x`. -/
@[simp] theorem cotangentDetCanonicalFiberEquiv_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b M).det.rank → 𝕜) :
    cotangentDetCanonicalFiberEquiv I b M x u =
      FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u •
        CanonicalBundle.coordForm I x b x := by
  let F := E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜
  have hx : x ∈ (trivializationAt F (CanonicalBundle I M) x).baseSet :=
    mem_baseSet_trivializationAt F (CanonicalBundle I M) x
  refine (ContinuousLinearEquiv.trans_apply
    ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans b.topFormEquiv.symm)
    (VectorBundle.continuousLinearEquivAt 𝕜 F (CanonicalBundle I M) x).symm u).trans ?_
  rw [ContinuousLinearEquiv.trans_apply, b.topFormEquiv_symm_eq_smul, map_smul,
    VectorBundle.continuousLinearEquivAt_symm_apply,
    ← CanonicalBundle.trivializationAt_apply_snd_coordForm (I := I) (b := b)
      (mem_chart_source H x),
    Trivialization.symm_apply_apply_mk _ hx]

/-- The inverse of `cotangentDetCanonicalFiberEquiv` reads a top-degree form `η` by evaluating it
on the coordinate basis vectors `(trivializationAt E (TangentSpace I) x).symmL 𝕜 x (b i)`. -/
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
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rfl
  rw [← htriv]
  exact CanonicalBundle.eq_smul_coordForm (b := b) (mem_chart_source H x) η

private noncomputable def cotangentDetCanonicalCoreDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).det.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (canonicalCore I b M).rank → 𝕜)⟯ (canonicalCore I b M).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv
    (cotangentDetCanonicalCoreIso I b M).hom (cotangentDetCanonicalCoreIso I b M).inv
    (cotangentDetCanonicalCoreIso I b M).hom_inv_id
    (cotangentDetCanonicalCoreIso I b M).inv_hom_id
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_of_mem_baseSet _
      ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
        (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm).toContinuousLinearMap
      fun x x₀ hx₀ v ↦ by
        rw [FiniteRankBundleCore.baseSet_det, baseSet_cotangentCore] at hx₀
        rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_hom,
          coordChange_canonicalCore b (mem_chart_source H x) hx₀,
          coordChange_cotangentCore_det b (mem_chart_source H x) hx₀]
        simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
        exact (((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).trans
          (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm).map_smul _ v).symm)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_of_mem_baseSet _
      ((ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).trans
        (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm).toContinuousLinearMap
      fun x x₀ hx₀ v ↦ by
        rw [baseSet_canonicalCore] at hx₀
        rw [cotangentDetCanonicalCoreIso, FiniteRankBundleCore.fiberMap_constIso_inv,
          coordChange_cotangentCore_det b (mem_chart_source H x) hx₀,
          coordChange_canonicalCore b (mem_chart_source H x) hx₀]
        simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
        exact (((ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).trans
          (FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm).map_smul _ v).symm)

private noncomputable def canonicalCoreTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (canonicalCore I b M).core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (canonicalCore I b M).rank → 𝕜),
      I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)⟯
        TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph (canonicalModelCoords b)
    (CanonicalBundle I M) I k

/-- The reconstructed total space of `(cotangentCore I b M).det` is `C^k` diffeomorphic over `M` to
the total space of `CanonicalBundle I M` at every regularity `k` (and in particular biholomorphic on
a complex manifold when `I = 𝓘(ℂ, E)` and `k = ∞`). -/
noncomputable def cotangentDetCanonicalDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).det.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).det.rank → 𝕜),
      I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)⟯
        TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) :=
  (cotangentDetCanonicalCoreDiffeomorph I b M k).trans
    (canonicalCoreTotalSpaceDiffeomorph I b M k)

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
      ⟨p.proj, cotangentDetCanonicalFiberEquiv I b M p.proj p.2⟩ := by
  rcases p with ⟨x, u⟩
  dsimp only
  rw [cotangentDetCanonicalDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    cotangentDetCanonicalCoreDiffeomorph, CoordinateHom.coe_toDiffeomorphOfInv,
    CoordinateHom.totalSpaceMap_mk]
  refine (FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph_apply
    (canonicalModelCoords b) (CanonicalBundle I M) (I := I) (n := k)
    ⟨x, (cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u⟩).trans ?_
  refine congrArg (TotalSpace.mk' _ x) ?_
  dsimp only
  change Fin (cotangentCore I b M).det.rank → 𝕜 at u
  refine (FiniteRankBundleCore.ofLinearEquivFiberEquiv_apply (canonicalModelCoords b)
    (CanonicalBundle I M) x ((cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u)).trans ?_
  have hcoord :
      (canonicalModelCoords b).symm ((cotangentDetCanonicalCoreIso I b M).hom.fiberMap x u) =
        FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M) u • b.continuousDet :=
    (canonicalModelCoords_symm_apply b _).trans <|
      congrArg (· • b.continuousDet)
        (fiberMap_cotangentDetCanonicalCoreIso_hom_apply b x u
          ⟨0, (rank_canonicalCore (I := I) (M := M) b) ▸ Nat.zero_lt_one⟩)
  rw [hcoord, cotangentDetCanonicalFiberEquiv_apply,
    ← VectorBundle.continuousLinearEquivAt_symm_apply (R := 𝕜), map_smul,
    VectorBundle.continuousLinearEquivAt_symm_apply,
    ← CanonicalBundle.trivializationAt_apply_snd_coordForm (I := I) (b := b)
      (mem_chart_source H x),
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt _ _ x)]

/-- On total spaces, the inverse of `cotangentDetCanonicalDiffeomorph` acts fibrewise by
`(cotangentDetCanonicalFiberEquiv I b M p.proj).symm`. -/
@[simp] theorem cotangentDetCanonicalDiffeomorph_symm_apply
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω)
    (p : TotalSpace (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)) :
    (cotangentDetCanonicalDiffeomorph I b M k).symm p =
      ⟨p.proj, (cotangentDetCanonicalFiberEquiv I b M p.proj).symm p.2⟩ := by
  apply EquivLike.injective (cotangentDetCanonicalDiffeomorph I b M k)
  rw [Diffeomorph.apply_symm_apply, cotangentDetCanonicalDiffeomorph_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The underlying homeomorphism of `cotangentDetCanonicalDiffeomorph` at any regularity `k` agrees
with `cotangentDetCanonicalHomeomorph`. -/
@[simp] theorem cotangentDetCanonicalDiffeomorph_toHomeomorph
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (k : ℕ∞ω) :
    (cotangentDetCanonicalDiffeomorph I b M k).toHomeomorph =
      cotangentDetCanonicalHomeomorph I b M := by
  apply Homeomorph.ext
  intro p
  exact (cotangentDetCanonicalDiffeomorph_apply b k p).trans
    (cotangentDetCanonicalDiffeomorph_apply b 0 p).symm

/-- Over the domain of the chart at `x₀`, the unit scalar coordinate `1` in the `x₀`-trivialization
of `(cotangentCore I b M).det` corresponds under `cotangentDetCanonicalFiberEquiv` to the local
coordinate top-form `dz₁ ∧ ⋯ ∧ dzₙ = CanonicalBundle.coordForm I x₀ b x`. -/
theorem cotangentDetCanonicalFiberEquiv_localTriv_symm_one
    (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) {x₀ x : M} (hx₀ : x ∈ (chartAt H x₀).source) :
    cotangentDetCanonicalFiberEquiv I b M x
        (((cotangentCore I b M).det.core.localTriv x₀).symm x
          ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm 1)) =
      CanonicalBundle.coordForm I x₀ b x := by
  have hb₀ : x ∈ ((cotangentCore I b M).det.core.localTriv x₀).baseSet := by
    rwa [FiniteRankBundleCore.localTriv_baseSet_det, baseSet_cotangentCore]
  have hsymm := ((cotangentCore I b M).det.core).localTriv_symm_apply (i := x₀) hb₀
    ((FiniteRankBundleCore.detScalarEquiv (cotangentCore I b M)).symm 1)
  rw [hsymm, (cotangentCore I b M).det.indexAt_eq, cotangentDetCanonicalFiberEquiv_apply,
    coordChange_cotangentCore_det b hx₀ (mem_chart_source H x)]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  exact (CanonicalBundle.coordForm_eq_det_smul_coordForm hx₀ (mem_chart_source H x)).symm

/-- The canonical identification `cotangentDetCanonicalFiberEquiv` commutes with changes of model
basis: the scaling `b₁.det b₂` of cotangent determinant coordinates cancels the inverse scaling of
`CanonicalBundle.coordForm`. -/
theorem cotangentDetCanonicalFiberEquiv_changeBasis
    (b₁ b₂ : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M)
    (u : Fin (cotangentCore I b₁ M).det.rank → 𝕜) :
    cotangentDetCanonicalFiberEquiv I b₂ M x
        ((cotangentDetChangeBasisIso I b₁ b₂ M).hom.fiberMap x u) =
      cotangentDetCanonicalFiberEquiv I b₁ M x u := by
  rw [cotangentDetCanonicalFiberEquiv_apply, cotangentDetCanonicalFiberEquiv_apply,
    detScalarEquiv_fiberMap_cotangentDetChangeBasisIso_hom,
    CanonicalBundle.coordForm_basis_change x b₁ b₂ x, smul_smul, mul_comm]

end CanonicalComparison

end TauCeti
