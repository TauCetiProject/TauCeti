/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.LinearEquiv

/-!
# Finite-rank tangent bundle cores

Let `M` be a `C¹` manifold modelled on `I : ModelWithCorners 𝕜 E H` over a complete nontrivially
normed field `𝕜`, equipped with a finite basis `b : Basis (Fin r) 𝕜 E` of the model space. Reading
model tangent vectors in the coordinate equivalence `b.equivFunL` via
`FiniteRankBundleCore.ofLinearEquiv` presents `TangentSpace I` as a point-indexed finite-rank core
`TauCeti.tangentCore I b M` of rank `r` in the category `FiniteRankBundleCore 𝕜 M`.

On the overlap of the charts at `x₀` and `x₁`, the transition map of `tangentCore I b M` is the
Jacobian `tangentCoordChange I x₀ x₁ x` conjugated by `b.equivFunL` (`coordChange_tangentCore`).
When `M` is a `C^(k+1)` manifold, `tangentCore I b M` is a `C^k` core (`isContMDiff_tangentCore`);
on a complex manifold (`I = 𝓘(ℂ, E)`, `k = ∞`) this is the holomorphic tangent core.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 10.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

/-- The finite-rank core presenting `TangentSpace I` on `M` in the coordinates `b.equivFunL` of a
basis `b : Basis (Fin r) 𝕜 E`. -/
-- Expose the rank projection so dependent coordinate spaces reduce to `Fin r → 𝕜`.
@[expose]
noncomputable def tangentCore {r : ℕ} (I : ModelWithCorners 𝕜 E H) (b : Basis (Fin r) 𝕜 E)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofLinearEquiv b.equivFunL (TangentSpace I : M → Type _)

section Basic

variable {r : ℕ} {I : ModelWithCorners 𝕜 E H} (b : Basis (Fin r) 𝕜 E)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section ManifoldOne

variable [IsManifold I 1 M]

/-- The tangent core in a `Fin r`-indexed basis has rank `r`. -/
@[simp] theorem rank_tangentCore : (tangentCore I b M).rank = r := (rfl)

/-- The chart domain of `tangentCore I b M` at `x₀` is the chart source `(chartAt H x₀).source`. -/
theorem baseSet_tangentCore (x₀ : M) :
    (tangentCore I b M).core.baseSet x₀ = (chartAt H x₀).source := by
  rw [tangentCore, FiniteRankBundleCore.baseSet_ofLinearEquiv,
    TangentBundle.trivializationAt_baseSet]

/-- The base set of the local trivialization of `tangentCore I b M` at `x₀` is the chart source. -/
@[simp] theorem localTriv_baseSet_tangentCore (x₀ : M) :
    ((tangentCore I b M).core.localTriv x₀).baseSet = (chartAt H x₀).source :=
  baseSet_tangentCore b x₀

/-- On the overlap of the charts at `x₀` and `x₁`, the transition of `tangentCore I b M` is the
Jacobian `tangentCoordChange I x₀ x₁ x` written in the basis `b`. -/
theorem coordChange_tangentCore {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (tangentCore I b M).core.coordChange x₀ x₁ x =
      b.equivFunL.arrowCongr b.equivFunL (tangentCoordChange I x₀ x₁ x) := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet ∩
      (trivializationAt E (TangentSpace I) x₁).baseSet :=
    ⟨by simpa using hx₀, by simpa using hx₁⟩
  refine (FiniteRankBundleCore.coordChange_ofLinearEquiv b.equivFunL
    (TangentSpace I : M → Type _) x₀ x₁ x).trans ?_
  exact congrArg (b.equivFunL.arrowCongr b.equivFunL)
    ((tangentBundleCore I M).trivializationAt_coordChangeL hx)

end ManifoldOne

/-- On a `C^(k+1)` manifold, `tangentCore I b M` is a `C^k` core (holomorphic when `I = 𝓘(ℂ, E)` and
`k = ∞`). -/
theorem isContMDiff_tangentCore {k : ℕ∞ω} [IsManifold I (k + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
    (tangentCore I b M).core.IsContMDiff I k := by
  have : IsManifold I 1 M := .of_le (n := k + 1) le_add_self
  let : ContMDiffVectorBundle k E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact FiniteRankBundleCore.isContMDiff_ofLinearEquiv b.equivFunL (TangentSpace I : M → Type _)

end Basic

end TauCeti
