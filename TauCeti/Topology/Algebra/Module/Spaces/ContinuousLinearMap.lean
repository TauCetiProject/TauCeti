/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Pointwise continuity criterion for operators out of finite coordinate spaces

For a finite index type `ι` and a topological vector space `G` over a nontrivially normed field `𝕜`,
a family of continuous linear maps `(ι → 𝕜) →L[𝕜] G` is continuous for the topology of bounded
convergence if and only if its evaluation at every vector is continuous. Unlike Mathlib's
`continuousWithinAt_clm_apply` and its variants, neither completeness of `𝕜` nor a norm on `G` is
needed: each map expands in the standard coordinate functionals via `ContinuousLinearMap.precomp`
and `ContinuousLinearMap.toSpanSingletonCLE`.

## Main results

* `TauCeti.tendsto_clm_pi_nhds`: filter convergence in `(ι → 𝕜) →L[𝕜] G` via pointwise convergence.
* `TauCeti.continuousWithinAt_clm_pi`: pointwise-to-operator continuity within a set at a point.
* `TauCeti.continuousOn_clm_pi`: pointwise-to-operator continuity on a set.
* `TauCeti.continuousAt_clm_pi`: pointwise-to-operator continuity at a point.
* `TauCeti.continuous_clm_pi`: global pointwise-to-operator continuity.
-/

public section

open scoped Topology

namespace TauCeti

section Pi

variable {𝕜 ι G : Type*} [NontriviallyNormedField 𝕜] [Finite ι]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul 𝕜 G]

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` converges along a
filter `l` to `g` if and only if its evaluation at every vector converges. Neither completeness of
`𝕜` nor a norm on `G` is required. -/
theorem tendsto_clm_pi_nhds {α : Type*} {l : Filter α} {f : α → (ι → 𝕜) →L[𝕜] G}
    {g : (ι → 𝕜) →L[𝕜] G} :
    Filter.Tendsto f l (𝓝 g) ↔ ∀ v : ι → 𝕜, Filter.Tendsto (fun a ↦ f a v) l (𝓝 (g v)) := by
  refine ⟨fun hf v ↦ ((continuous_eval_const v).tendsto g).comp hf, fun hf ↦ ?_⟩
  cases nonempty_fintype ι
  classical
  let φ (k : ι) : G →L[𝕜] ((ι → 𝕜) →L[𝕜] G) :=
    ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) k).precomp G).comp
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := 𝕜)).toContinuousLinearMap
  have hsum (T : (ι → 𝕜) →L[𝕜] G) : T = ∑ k : ι, φ k (T (Pi.single k 1)) := by
    ext v
    have hv : v = ∑ k : ι, v k • Pi.single k (1 : 𝕜) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp [φ, map_sum, map_smul, sum_apply]
  rw [hsum g, show f = fun a ↦ ∑ k : ι, φ k (f a (Pi.single k 1)) from funext fun a ↦ hsum (f a)]
  exact tendsto_finsetSum Finset.univ fun k _ ↦
    ((φ k).continuous.tendsto _).comp (hf (Pi.single k 1))

variable {B : Type*} [TopologicalSpace B]

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` is continuous
within `s` at `x` if and only if its evaluation at every vector is. -/
theorem continuousWithinAt_clm_pi {f : B → (ι → 𝕜) →L[𝕜] G} {s : Set B} {x : B} :
    ContinuousWithinAt f s x ↔ ∀ v : ι → 𝕜, ContinuousWithinAt (fun y ↦ f y v) s x :=
  tendsto_clm_pi_nhds

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` is continuous on `s`
if and only if its evaluation at every vector is. -/
theorem continuousOn_clm_pi {f : B → (ι → 𝕜) →L[𝕜] G} {s : Set B} :
    ContinuousOn f s ↔ ∀ v : ι → 𝕜, ContinuousOn (fun y ↦ f y v) s := by
  simp_rw [ContinuousOn, continuousWithinAt_clm_pi]
  exact ⟨fun hf v x hx ↦ hf x hx v, fun hf x hx v ↦ hf v x hx⟩

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` is continuous at `x`
if and only if its evaluation at every vector is. -/
theorem continuousAt_clm_pi {f : B → (ι → 𝕜) →L[𝕜] G} {x : B} :
    ContinuousAt f x ↔ ∀ v : ι → 𝕜, ContinuousAt (fun y ↦ f y v) x :=
  tendsto_clm_pi_nhds

/-- A family of continuous linear maps out of a finite coordinate space `ι → 𝕜` is continuous if and
only if its evaluation at every vector is. -/
theorem continuous_clm_pi {f : B → (ι → 𝕜) →L[𝕜] G} :
    Continuous f ↔ ∀ v : ι → 𝕜, Continuous (fun y ↦ f y v) := by
  simp_rw [continuous_iff_continuousAt, continuousAt_clm_pi]
  exact forall_comm

end Pi

end TauCeti
