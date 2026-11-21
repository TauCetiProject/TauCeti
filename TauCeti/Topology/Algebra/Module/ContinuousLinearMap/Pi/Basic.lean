/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuous linear maps out of finite coordinate spaces

Every continuous linear map `L : (ι → R) →L[R] G` out of a finite product of scalars expands as the
finite sum of rank-one operators `(proj i).smulRight (L (Pi.single i 1))`
(`ContinuousLinearMap.eq_sum_smulRight_proj`).

Consequently, over any nontrivially normed field `𝕜` and into any topological `𝕜`-vector space `G`,
convergence and continuity of a family `T : Z → (ι → 𝕜) →L[𝕜] G` in the topology of bounded
convergence (which coincides with the operator-norm topology when `G` is normed) are equivalent to
pointwise convergence and continuity on every vector `v : ι → 𝕜` (`TauCeti.tendsto_clm_pi_iff`,
`TauCeti.continuousWithinAt_clm_pi_iff`, `TauCeti.continuousAt_clm_pi_iff`,
`TauCeti.continuousOn_clm_pi_iff`, `TauCeti.continuous_clm_pi_iff`). Unlike Mathlib's
`continuousAt_clm_apply` for an arbitrary finite-dimensional normed domain, these results require
neither completeness of `𝕜` nor a norm on `G`.

The constructions build on Mathlib's `ContinuousLinearMap.proj`, `ContinuousLinearMap.smulRight`,
`ContinuousLinearMap.toSpanSingletonCLE`, and `ContinuousLinearMap.precomp`.
-/

public section

open Filter
open scoped Topology

namespace ContinuousLinearMap

/-- Every continuous linear map out of a finite product `ι → R` expands as the sum of rank-one
operators along the coordinate projections `proj i` and standard basis vectors `Pi.single i 1`. -/
theorem eq_sum_smulRight_proj {R ι G : Type*} [Semiring R] [TopologicalSpace R]
    [Fintype ι] [DecidableEq ι] [AddCommMonoid G] [Module R G] [TopologicalSpace G]
    [ContinuousAdd G] [ContinuousSMul R G] (L : (ι → R) →L[R] G) :
    L = ∑ i : ι, (proj (R := R) i).smulRight (L (Pi.single i 1)) := by
  ext v
  have hv : ∑ i : ι, v i • (Pi.single i (1 : R) : ι → R) = v := by
    ext j
    simp [Pi.single_apply]
  simpa only [sum_apply, smulRight_apply, proj_apply, ← map_smul, ← map_sum] using
    congrArg L hv.symm

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 Z G ι : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul 𝕜 G] [Finite ι]

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` converges in the
topology of bounded convergence (the operator-norm topology when `G` is normed) if and only if its
evaluations at every vector `v : ι → 𝕜` converge. Neither completeness of `𝕜` nor a norm on `G` is
required. -/
theorem tendsto_clm_pi_iff {l : Filter Z} {T : Z → (ι → 𝕜) →L[𝕜] G} {L : (ι → 𝕜) →L[𝕜] G} :
    Tendsto T l (𝓝 L) ↔ ∀ v, Tendsto (fun z ↦ T z v) l (𝓝 (L v)) := by
  refine ⟨fun h v ↦ ((continuous_eval_const v).tendsto L).comp h, fun h ↦ ?_⟩
  cases nonempty_fintype ι
  classical
  let p (i : ι) : (ι → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i
  let r (i : ι) : G →L[𝕜] (ι → 𝕜) →L[𝕜] G :=
    ((p i).precomp G).comp
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜) (E := G)).toContinuousLinearMap
  have hr (i : ι) (g : G) : r i g = (p i).smulRight g := by
    ext v
    rfl
  have hterm (A : (ι → 𝕜) →L[𝕜] G) : ∑ i : ι, r i (A (Pi.single i 1)) = A := by
    simpa only [hr] using A.eq_sum_smulRight_proj.symm
  have hsum : Tendsto (fun z ↦ ∑ i : ι, r i (T z (Pi.single i 1))) l
      (𝓝 (∑ i : ι, r i (L (Pi.single i 1)))) :=
    tendsto_finsetSum Finset.univ fun i _ ↦
      ((r i).continuous.tendsto (L (Pi.single i 1))).comp (h (Pi.single i 1))
  simpa only [hterm] using hsum

variable [TopologicalSpace Z]

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` is continuous within
a set at a point if and only if all of its pointwise evaluations are. -/
theorem continuousWithinAt_clm_pi_iff {T : Z → (ι → 𝕜) →L[𝕜] G} {s : Set Z} {z₀ : Z} :
    ContinuousWithinAt T s z₀ ↔ ∀ v, ContinuousWithinAt (fun z ↦ T z v) s z₀ :=
  tendsto_clm_pi_iff

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` is continuous at a
point if and only if all of its pointwise evaluations are. -/
theorem continuousAt_clm_pi_iff {T : Z → (ι → 𝕜) →L[𝕜] G} {z₀ : Z} :
    ContinuousAt T z₀ ↔ ∀ v, ContinuousAt (fun z ↦ T z v) z₀ :=
  tendsto_clm_pi_iff

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` is continuous on a
set if and only if all of its pointwise evaluations are. -/
theorem continuousOn_clm_pi_iff {T : Z → (ι → 𝕜) →L[𝕜] G} {s : Set Z} :
    ContinuousOn T s ↔ ∀ v, ContinuousOn (fun z ↦ T z v) s := by
  simp_rw [ContinuousOn, continuousWithinAt_clm_pi_iff, imp_forall_iff]
  exact forall_comm

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` is continuous if
and only if all of its pointwise evaluations are. -/
theorem continuous_clm_pi_iff {T : Z → (ι → 𝕜) →L[𝕜] G} :
    Continuous T ↔ ∀ v, Continuous (fun z ↦ T z v) := by
  simp_rw [continuous_iff_continuousAt, continuousAt_clm_pi_iff]
  exact forall_comm

end TauCeti
