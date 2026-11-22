/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.FiniteRank
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Finite-rank cotangent bundle cores and duality with the tangent core

For a `C¹` manifold `M` modelled on `I : ModelWithCorners 𝕜 E H` over a complete field `𝕜` with
basis `b : Basis (Fin r) 𝕜 E`, `TauCeti.cotangentCore I b M` presents the cotangent bundle
`fun x ↦ TangentSpace I x →L[𝕜] 𝕜` in `FiniteRankBundleCore.dualCoords b.equivFunL`:

* `coordChange_cotangentCore`: chart transitions are transposed reverse Jacobians in `b`.
* `cotangentCoreTotalSpaceDiffeomorph`: `C^k` diffeomorphism onto `CotangentBundle I M`.
* `tangentDualCotangentIso` and `tangentDualCotangentDiffeomorph`: canonical identity identification
  `(tangentCore I b M).dual ≅ cotangentCore I b M`.
* `isContMDiff_cotangentCore`: `C^k` core on a `C^(k+1)` manifold (holomorphic when `I = 𝓘(ℂ, E)`
  and `k = ∞`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Chapter 11.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle CategoryTheory Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

/-- The finite-rank core presenting the cotangent bundle `fun x ↦ TangentSpace I x →L[𝕜] 𝕜` on `M`
in `FiniteRankBundleCore.dualCoords b.equivFunL` (`p ↦ fun i ↦ p (b i)`). -/
-- Expose the rank projection so dependent coordinate spaces reduce to `Fin r → 𝕜`.
@[expose]
noncomputable def cotangentCore {r : ℕ} (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofLinearEquiv (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)

section Basic

variable {r : ℕ} {I : ModelWithCorners 𝕜 E H} (b : Basis (Fin r) 𝕜 E)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section ManifoldOne

variable [IsManifold I 1 M]

/-- The cotangent core in a `Fin r`-indexed basis has rank `r`. -/
@[simp] theorem rank_cotangentCore : (cotangentCore I b M).rank = r := (rfl)

/-- The chart domain of `cotangentCore I b M` at `x₀` is `(chartAt H x₀).source`. -/
theorem baseSet_cotangentCore (x₀ : M) :
    (cotangentCore I b M).core.baseSet x₀ = (chartAt H x₀).source := by
  rw [cotangentCore, FiniteRankBundleCore.baseSet_ofLinearEquiv]
  simp

/-- The base set of the local trivialization of `cotangentCore I b M` at `x₀` is the chart
source. -/
@[simp] theorem localTriv_baseSet_cotangentCore (x₀ : M) :
    ((cotangentCore I b M).core.localTriv x₀).baseSet = (chartAt H x₀).source :=
  baseSet_cotangentCore b x₀

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `cotangentCore I b M` is the
transpose of the reverse Jacobian `tangentCoordChange I x₁ x₀ x` written in the basis `b`. -/
theorem coordChange_cotangentCore {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (cotangentCore I b M).core.coordChange x₀ x₁ x =
      (b.equivFunL.arrowCongr b.equivFunL (tangentCoordChange I x₁ x₀ x)).piTranspose := by
  refine (FiniteRankBundleCore.coordChange_ofLinearEquiv_dualCoords b.equivFunL
    (TangentSpace I : M → Type _) (by simpa using hx₀) (by simpa using hx₁)).trans ?_
  rw [FiniteRankBundleCore.coordChange_dual]
  exact congrArg ContinuousLinearMap.piTranspose (coordChange_tangentCore b hx₁ hx₀)

/-- Reconstructed total space of `cotangentCore I b M` identified `C^k`-diffeomorphically with
`CotangentBundle I M`. -/
noncomputable def cotangentCoreTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (cotangentCore I b M).core.TotalSpace ≃ₘ^k⟮I.prod 𝓘(𝕜, Fin (cotangentCore I b M).rank → 𝕜),
      I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯ CotangentBundle I M :=
  FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph
    (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) I k

/-- At `p.proj`, `cotangentCoreTotalSpaceDiffeomorph` pulls `(dualCoords b.equivFunL).symm p.snd`
back through the tangent trivialization at `p.proj`. -/
@[simp] theorem cotangentCoreTotalSpaceDiffeomorph_apply
    (k : ℕ∞ω) (p : (cotangentCore I b M).core.TotalSpace) :
    cotangentCoreTotalSpaceDiffeomorph I b M k p =
      ⟨p.proj, ((FiniteRankBundleCore.dualCoords b.equivFunL).symm p.snd).comp
        ((trivializationAt E (TangentSpace I) p.proj).continuousLinearMapAt 𝕜 p.proj)⟩ := by
  -- Chain via `.trans`: `cotangentCore` and `VectorBundleCore.Fiber` are non-reducible `def`s
  -- (defeq to `ofLinearEquiv ...` and `Fin r → 𝕜`), so `rw` cannot match them directly.
  refine (FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph_apply
    (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) (I := I) (n := k) p).trans ?_
  refine congrArg (TotalSpace.mk' (E →L[𝕜] 𝕜) p.proj) ?_
  refine (FiniteRankBundleCore.ofLinearEquivFiberEquiv_apply
    (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) p.proj p.snd).trans ?_
  exact trivializationAt_dual_symm_eq (TangentSpace I : M → Type _)
    (mem_baseSet_trivializationAt E (TangentSpace I) p.proj) _

/-- At `p.proj`, the inverse of `cotangentCoreTotalSpaceDiffeomorph` evaluates `p.snd` on the chart
basis vectors `(trivializationAt E (TangentSpace I) p.proj).symmL 𝕜 p.proj (b i)`. -/
@[simp] theorem cotangentCoreTotalSpaceDiffeomorph_symm_apply
    (k : ℕ∞ω) (p : CotangentBundle I M) :
    (cotangentCoreTotalSpaceDiffeomorph I b M k).symm p =
      ⟨p.proj, fun i ↦
        p.snd ((trivializationAt E (TangentSpace I) p.proj).symmL 𝕜 p.proj (b i))⟩ := by
  rcases p with ⟨x, q⟩
  refine (FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph_symm_apply
    (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) (I := I) (n := k) ⟨x, q⟩).trans ?_
  rw [FiniteRankBundleCore.ofLinearEquivFiberEquiv_symm_apply]
  refine congrArg (TotalSpace.mk' (Fin r → 𝕜) x) (funext fun i ↦ ?_)
  rw [FiniteRankBundleCore.dualCoords_equivFunL_apply, Manifold.symmL_trivializationAt_self]
  have hself := CotangentBundle.continuousLinearMapAt_trivializationAt_self (I := I) x q
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _
    (mem_baseSet_trivializationAt (E →L[𝕜] 𝕜) (fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜) x)] at hself
  exact congrArg (· (b i)) hself

/-- `(tangentCore I b M).dual` is canonically isomorphic in `FiniteRankBundleCore 𝕜 M` to
`cotangentCore I b M` by the identity on every coordinate fibre. -/
noncomputable def tangentDualCotangentIso
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    (tangentCore I b M).dual ≅ cotangentCore I b M :=
  FiniteRankBundleCore.ofLinearEquivDualIso b.equivFunL (TangentSpace I : M → Type _)

/-- On every fibre, `(tangentDualCotangentIso I b M).hom` is the identity on coordinate vectors. -/
@[simp] theorem fiberMap_tangentDualCotangentIso_hom (x : M) :
    (tangentDualCotangentIso I b M).hom.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin r → 𝕜) :=
  FiniteRankBundleCore.fiberMap_ofLinearEquivDualIso_hom b.equivFunL (TangentSpace I : M → Type _) x

/-- On every fibre, `(tangentDualCotangentIso I b M).inv` is the identity on coordinate vectors. -/
@[simp] theorem fiberMap_tangentDualCotangentIso_inv (x : M) :
    (tangentDualCotangentIso I b M).inv.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin r → 𝕜) :=
  FiniteRankBundleCore.fiberMap_ofLinearEquivDualIso_inv b.equivFunL (TangentSpace I : M → Type _) x

/-- The `C^k` diffeomorphism of total spaces induced by `tangentDualCotangentIso`. -/
noncomputable def tangentDualCotangentDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] (k : ℕ∞ω) :
    (tangentCore I b M).dual.core.TotalSpace ≃ₘ^k⟮
      I.prod 𝓘(𝕜, Fin (tangentCore I b M).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (cotangentCore I b M).rank → 𝕜)⟯
        (cotangentCore I b M).core.TotalSpace :=
  FiniteRankBundleCore.ofLinearEquivDualDiffeomorph b.equivFunL (TangentSpace I : M → Type _) I k

/-- On total spaces, `tangentDualCotangentDiffeomorph` acts as the identity on base points and
coordinate vectors. -/
@[simp] theorem tangentDualCotangentDiffeomorph_apply (k : ℕ∞ω)
    (p : (tangentCore I b M).dual.core.TotalSpace) :
    tangentDualCotangentDiffeomorph I b M k p = ⟨p.proj, p.snd⟩ := by
  -- Use `.trans` rather than `rw` across `tangentCore`/`cotangentCore` (non-reducible `@[expose]`
  -- `def`s whose rank is defeq to `r`).
  refine (congrFun (FiniteRankBundleCore.coe_ofLinearEquivDualDiffeomorph
    b.equivFunL (TangentSpace I : M → Type _) (I := I) (n := k)) p).trans ?_
  refine (CoordinateHom.totalSpaceMap_mk (tangentDualCotangentIso I b M).hom p.proj p.snd).trans ?_
  exact congrArg (TotalSpace.mk' _ p.proj)
    ((DFunLike.congr_fun (fiberMap_tangentDualCotangentIso_hom b p.proj) p.snd).trans
      (ContinuousLinearMap.id_apply p.snd))

/-- On total spaces, the inverse of `tangentDualCotangentDiffeomorph` acts as the identity on base
points and coordinate vectors. -/
@[simp] theorem tangentDualCotangentDiffeomorph_symm_apply (k : ℕ∞ω)
    (p : (cotangentCore I b M).core.TotalSpace) :
    (tangentDualCotangentDiffeomorph I b M k).symm p = ⟨p.proj, p.snd⟩ := by
  -- Use `.trans` rather than `rw` across `tangentCore`/`cotangentCore` (non-reducible `@[expose]`
  -- `def`s whose rank is defeq to `r`).
  refine (congrFun (FiniteRankBundleCore.coe_ofLinearEquivDualDiffeomorph_symm
    b.equivFunL (TangentSpace I : M → Type _) (I := I) (n := k)) p).trans ?_
  refine (CoordinateHom.totalSpaceMap_mk (tangentDualCotangentIso I b M).inv p.proj p.snd).trans ?_
  exact congrArg (TotalSpace.mk' _ p.proj)
    ((DFunLike.congr_fun (fiberMap_tangentDualCotangentIso_inv b p.proj) p.snd).trans
      (ContinuousLinearMap.id_apply p.snd))

end ManifoldOne

/-- On a `C^(k+1)` manifold, `cotangentCore I b M` is a `C^k` core (holomorphic when `I = 𝓘(ℂ, E)`
and `k = ∞`). -/
theorem isContMDiff_cotangentCore {k : ℕ∞ω} [IsManifold I (k + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
    (cotangentCore I b M).core.IsContMDiff I k := by
  have : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
  let : ContMDiffVectorBundle k E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact FiniteRankBundleCore.isContMDiff_ofLinearEquiv
    (FiniteRankBundleCore.dualCoords b.equivFunL)
    (fun x : M ↦ TangentSpace I x →L[𝕜] Trivial M 𝕜 x)

end Basic

end TauCeti
