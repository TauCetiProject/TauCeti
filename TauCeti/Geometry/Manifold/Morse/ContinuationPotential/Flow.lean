/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.ContinuationPotential.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.ExtChartAt.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.IntegralCurve.Prod
import TauCeti.Topology.Order.OrderClosed

/-!
# Trajectories of a continuation field in the slab

Let `f : M × ℝ → ℝ` be a path `f_t = f (·, t)` of functions on a manifold `M`, independent of `t`
for `t < δ` and for `t > 1 - δ`, and let `F(x, t) = C h(t) + f(x, t)` be its continuation
potential (`TauCeti.continuationPotential`). A *continuation field* is a vector field `V` on
`M × ℝ` whose time component is `C t (1 - t²) - ∂ₜ f`, as for the negative gradient of `F` for
any metric of the form `dt² + g_t`. Such a field is in general not complete on `M × ℝ`: above
`t = 1` its time component behaves like `-C t³`, so backward trajectories escape in finite time.
The continuation map counts trajectories in the slab `M × [0, 1]`, and this file shows that they
are well behaved there.

* **Invariance.** The time component `τ` of a trajectory solves `τ' = C τ (1 - τ²) - ∂ₜ f`, which
  is the base equation `τ' = C τ (1 - τ²)` near `τ = 0` and `τ = 1`. By uniqueness for the base
  equation, the two end levels `M × {0}` and `M × {1}` and the open slab `M × (0, 1)` are each
  invariant, so the slab `M × [0, 1]` is invariant.
* **Completeness in the slab.** On a compact manifold `M` the slab is compact, so the trajectories
  through its points are defined for all time, although nothing is asserted outside the slab.
* **Ends of the trajectories.** If moreover `V` decreases `F` away from its critical points and
  `f₀ = f (·, 0)` and `f₁ = f (·, 1)` have finitely many critical points, then every trajectory in
  the slab converges in both directions of time to critical points of `F` in the slab, that is, to
  points `(p, 0)` with `p` a critical point of `f₀` or `(q, 1)` with `q` a critical point of `f₁`,
  provided `∂ₜ f < C t (1 - t²)` in the open slab. A trajectory in the open slab starts at such a
  `(p, 0)` and ends at such a `(q, 1)`: its time component increases, since
  `τ' = C τ (1 - τ²) - ∂ₜ f > 0`, so it can neither end on `M × {0}` nor start on `M × {1}`. For
  its forward end only the critical points of `f₁` need to be finitely many, and for its backward
  end only those of `f₀`. These are the trajectories counted by the continuation map from the
  Morse complex of `f₀` to that of `f₁`.

The convergence applies the Lyapunov argument of `Flow.exists_tendsto_atTop_of_antitone` and
`Flow.exists_tendsto_atBot_of_antitone` to the flow of `V` on the compact slab
(`TauCeti.continuationSlabFlow`, an instance of `TauCeti.globalFlowOn`), with `F` as the Lyapunov
function.

## Main results

* `IsMIntegralCurveOn.snd_eq_zero_of_snd_eq_zero_of_intervalBase`,
  `IsMIntegralCurveOn.snd_eq_one_of_snd_eq_one_of_intervalBase`,
  `IsMIntegralCurveOn.snd_mem_Ioo_of_snd_mem_Ioo_of_intervalBase` and
  `IsMIntegralCurveOn.snd_mem_Icc_of_snd_mem_Icc_of_intervalBase`: invariance of the two end
  levels, of the open slab and of the slab.
* `TauCeti.maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc_of_intervalBase`: on a compact
  manifold the trajectories through the slab are defined for all time.
* `TauCeti.snd_maximalIntegralCurve_eq_zero_of_intervalBase`,
  `TauCeti.snd_maximalIntegralCurve_eq_one_of_intervalBase`,
  `TauCeti.snd_maximalIntegralCurve_mem_Ioo_of_intervalBase` and
  `TauCeti.snd_maximalIntegralCurve_mem_Icc_of_intervalBase`: these trajectories stay in the end
  level, the open slab or the slab through which they pass.
* `TauCeti.strictMono_snd_maximalIntegralCurve_of_intervalBase`: the time increases along a
  trajectory in the open slab.
* `TauCeti.continuationSlabFlow`: the flow of `V` on the slab, with
  `TauCeti.coe_continuationSlabFlow_apply` identifying it with the maximal integral curves.
* `TauCeti.exists_tendsto_maximalIntegralCurve_atTop_of_continuationPotential_of_snd_mem_Icc` and
  `TauCeti.exists_tendsto_maximalIntegralCurve_atBot_of_continuationPotential_of_snd_mem_Icc`: the
  trajectories through the slab converge to critical points of `f₀` or `f₁` on the end levels.
* `TauCeti.exists_tendsto_maximalIntegralCurve_atTop_of_continuationPotential_of_snd_mem_Ioo` and
  `TauCeti.exists_tendsto_maximalIntegralCurve_atBot_of_continuationPotential_of_snd_mem_Ioo`: a
  trajectory in the open slab runs from a critical point `(p, 0)` of `f₀` to a critical point
  `(q, 1)` of `f₁`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (continuation maps).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 (convergence of the trajectories of a pseudo-gradient field).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {C δ : ℝ}
  {f : M × ℝ → ℝ} {V : (z : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ)) z} {γ : ℝ → M × ℝ}
  {s : Set ℝ}

/-! ### Invariance of the slab -/

/-- The time component `τ` of an integral curve of a continuation field solves
`τ' = C τ (1 - τ²) - ∂ₜ f`. -/
private theorem _root_.IsMIntegralCurveOn.hasDerivAt_snd_of_intervalBase
    (hγ : IsMIntegralCurveOn γ V s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    {t : ℝ} (hs : s ∈ 𝓝 t) :
    HasDerivAt (fun r ↦ (γ r).2)
      (C * (γ t).2 * (1 - (γ t).2 ^ 2) - deriv (fun s ↦ f ((γ t).1, s)) (γ t).2) t := by
  rw [← hV]
  exact hγ.hasDerivAt_snd hs

/-- **Invariance of the source level.** Let `V` be a continuation field for a path `f` independent
of the time for `t < δ`. An integral curve of `V` on an open preconnected set which meets the level
`M × {0}` stays in it. -/
theorem _root_.IsMIntegralCurveOn.snd_eq_zero_of_snd_eq_zero_of_intervalBase
    (hγ : IsMIntegralCurveOn γ V s) (hs : IsOpen s) (hs' : IsPreconnected s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) {s₀ t : ℝ} (hs₀ : s₀ ∈ s)
    (h₀ : (γ s₀).2 = 0) (ht : t ∈ s) : (γ t).2 = 0 :=
  eqOn_const_of_hasDerivAt_intervalBase (c := 0) (by simp) hδ hs hs'
    (fun r hr ↦ hγ.hasDerivAt_snd_of_intervalBase hV (hs.mem_nhds hr))
    (fun _ _ hr ↦ deriv_prodMk_eq_zero_of_lt hf₀ (by simpa using (abs_lt.1 hr).2)) hs₀ h₀ ht

/-- **Invariance of the target level.** Let `V` be a continuation field for a path `f` independent
of the time for `t > 1 - δ`. An integral curve of `V` on an open preconnected set which meets the
level `M × {1}` stays in it. -/
theorem _root_.IsMIntegralCurveOn.snd_eq_one_of_snd_eq_one_of_intervalBase
    (hγ : IsMIntegralCurveOn γ V s) (hs : IsOpen s) (hs' : IsPreconnected s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) {s₀ t : ℝ} (hs₀ : s₀ ∈ s)
    (h₁ : (γ s₀).2 = 1) (ht : t ∈ s) : (γ t).2 = 1 :=
  eqOn_const_of_hasDerivAt_intervalBase (c := 1) (by simp) hδ hs hs'
    (fun r hr ↦ hγ.hasDerivAt_snd_of_intervalBase hV (hs.mem_nhds hr))
    (fun _ _ hr ↦ deriv_prodMk_eq_zero_of_gt hf₁ (by linarith [(abs_lt.1 hr).1])) hs₀ h₁ ht

/-- **Invariance of the open slab.** Let `V` be a continuation field for a path `f` independent of
the time for `t < δ` and for `t > 1 - δ`. An integral curve of `V` on an open preconnected set which
meets the open slab `M × (0, 1)` stays in it. -/
theorem _root_.IsMIntegralCurveOn.snd_mem_Ioo_of_snd_mem_Ioo_of_intervalBase
    (hγ : IsMIntegralCurveOn γ V s) (hs : IsOpen s) (hs' : IsPreconnected s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) {s₀ t : ℝ} (hs₀ : s₀ ∈ s)
    (h : (γ s₀).2 ∈ Ioo 0 1) (ht : t ∈ s) : (γ t).2 ∈ Ioo 0 1 :=
  mapsTo_Ioo_of_hasDerivAt_intervalBase hδ hs hs'
    (fun r hr ↦ hγ.hasDerivAt_snd_of_intervalBase hV (hs.mem_nhds hr))
    (fun _ _ hr ↦ deriv_prodMk_eq_zero_of_lt hf₀ (by simpa using (abs_lt.1 hr).2))
    (fun _ _ hr ↦ deriv_prodMk_eq_zero_of_gt hf₁ (by linarith [(abs_lt.1 hr).1])) hs₀ h ht

/-- **Invariance of the slab.** Let `V` be a continuation field for a path `f` independent of the
time for `t < δ` and for `t > 1 - δ`. An integral curve of `V` on an open preconnected set which
meets the slab `M × [0, 1]` stays in it. -/
theorem _root_.IsMIntegralCurveOn.snd_mem_Icc_of_snd_mem_Icc_of_intervalBase
    (hγ : IsMIntegralCurveOn γ V s) (hs : IsOpen s) (hs' : IsPreconnected s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) {s₀ t : ℝ} (hs₀ : s₀ ∈ s)
    (h : (γ s₀).2 ∈ Icc 0 1) (ht : t ∈ s) : (γ t).2 ∈ Icc 0 1 := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc h with h | h | h
  · rw [hγ.snd_eq_zero_of_snd_eq_zero_of_intervalBase hs hs' hV hδ hf₀ hs₀ h ht]
    exact left_mem_Icc.2 zero_le_one
  · rw [hγ.snd_eq_one_of_snd_eq_one_of_intervalBase hs hs' hV hδ hf₁ hs₀ h ht]
    exact right_mem_Icc.2 zero_le_one
  · exact Ioo_subset_Icc_self
      (hγ.snd_mem_Ioo_of_snd_mem_Ioo_of_intervalBase hs hs' hV hδ hf₀ hf₁ hs₀ h ht)

/-! ### Completeness in the slab -/

section Complete

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] [CompactSpace M]
  (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
    (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
  (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
  (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
  (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
include hv hV hδ hf₀ hf₁

omit hV hδ hf₀ hf₁ in
/-- **Trajectories trapped in a compact range of times.** Let `T` be a compact set of times such
that an integral curve of `V` on an open preconnected set which meets `M × T` stays in it. Then the
maximal integral curve of `V` through a point of `M × T` is defined for all time and stays in
`M × T`, since it is confined to the compact set `M × T`. -/
private theorem maximalIntegralCurveInterval_eq_univ_and_snd_mem {T : Set ℝ} (hT : IsCompact T)
    (hinv : ∀ {γ : ℝ → M × ℝ} {s : Set ℝ}, IsMIntegralCurveOn γ V s → IsOpen s →
      IsPreconnected s → ∀ {s₀ t : ℝ}, s₀ ∈ s → (γ s₀).2 ∈ T → t ∈ s → (γ t).2 ∈ T)
    {z : M × ℝ} (hz : z.2 ∈ T) :
    maximalIntegralCurveInterval V z = univ ∧ ∀ t, (maximalIntegralCurve V z t).2 ∈ T := by
  have : Nonempty M := ⟨z.1⟩
  have := CompleteSpace.of_locallyCompact_manifold M I
  have h : ∀ t ∈ maximalIntegralCurveInterval V z, (maximalIntegralCurve V z t).2 ∈ T :=
    fun _ ↦ hinv (isMIntegralCurveOn_maximalIntegralCurve hv) isOpen_maximalIntegralCurveInterval
      isPreconnected_maximalIntegralCurveInterval
      (zero_mem_maximalIntegralCurveInterval (v := V) (x := z) hv.contMDiffAt)
      (by rwa [maximalIntegralCurve_zero])
  have huniv := maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (isCompact_univ.prod hT) fun t ht ↦ ⟨mem_univ _, h t ht⟩
  exact ⟨huniv, fun t ↦ h t (huniv ▸ mem_univ t)⟩

/-- **The trajectories through the slab are complete.** Let `M` be a compact boundaryless
manifold and `V` a `C¹` continuation field for a path `f` independent of the time for `t < δ` and
for `t > 1 - δ`. The maximal integral curve of `V` through a point of the slab `M × [0, 1]` is
defined for all time. -/
theorem maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc_of_intervalBase {z : M × ℝ}
    (hz : z.2 ∈ Icc 0 1) : maximalIntegralCurveInterval V z = univ :=
  (maximalIntegralCurveInterval_eq_univ_and_snd_mem hv isCompact_Icc
    (fun hγ hs hs' ↦ hγ.snd_mem_Icc_of_snd_mem_Icc_of_intervalBase hs hs' hV hδ hf₀ hf₁) hz).1

/-- The maximal integral curve through a point of the slab is a global integral curve. -/
private theorem isMIntegralCurveOn_univ_maximalIntegralCurve_of_intervalBase {z : M × ℝ}
    (hz : z.2 ∈ Icc 0 1) : IsMIntegralCurveOn (maximalIntegralCurve V z) V univ :=
  (isMIntegralCurve_maximalIntegralCurve_of_eq_univ hv
    (maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc_of_intervalBase hv hV hδ hf₀ hf₁
      hz)).isMIntegralCurveOn univ

omit hf₁ in
/-- **The trajectories through the source level stay in it.** Let `M` be a compact boundaryless
manifold and `V` a `C¹` continuation field for a path `f` independent of the time for `t < δ`. The
maximal integral curve of `V` through a point of `M × {0}` stays in `M × {0}` for all time. -/
theorem snd_maximalIntegralCurve_eq_zero_of_intervalBase {z : M × ℝ} (hz : z.2 = 0) (t : ℝ) :
    (maximalIntegralCurve V z t).2 = 0 :=
  (maximalIntegralCurveInterval_eq_univ_and_snd_mem hv isCompact_singleton
    (fun hγ hs hs' ↦ hγ.snd_eq_zero_of_snd_eq_zero_of_intervalBase hs hs' hV hδ hf₀) hz).2 t

omit hf₀ in
/-- **The trajectories through the target level stay in it.** Let `M` be a compact boundaryless
manifold and `V` a `C¹` continuation field for a path `f` independent of the time for
`t > 1 - δ`. The maximal integral curve of `V` through a point of `M × {1}` stays in `M × {1}` for
all time. -/
theorem snd_maximalIntegralCurve_eq_one_of_intervalBase {z : M × ℝ} (hz : z.2 = 1) (t : ℝ) :
    (maximalIntegralCurve V z t).2 = 1 :=
  (maximalIntegralCurveInterval_eq_univ_and_snd_mem hv isCompact_singleton
    (fun hγ hs hs' ↦ hγ.snd_eq_one_of_snd_eq_one_of_intervalBase hs hs' hV hδ hf₁) hz).2 t

/-- **The trajectories through the open slab stay in it.** Under the hypotheses of
`TauCeti.maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc_of_intervalBase`, the maximal integral
curve of `V` through a point of the open slab `M × (0, 1)` stays in the open slab for all time. -/
theorem snd_maximalIntegralCurve_mem_Ioo_of_intervalBase {z : M × ℝ} (hz : z.2 ∈ Ioo 0 1)
    (t : ℝ) : (maximalIntegralCurve V z t).2 ∈ Ioo 0 1 :=
  (isMIntegralCurveOn_univ_maximalIntegralCurve_of_intervalBase hv hV hδ hf₀ hf₁
    (Ioo_subset_Icc_self hz)).snd_mem_Ioo_of_snd_mem_Ioo_of_intervalBase isOpen_univ
    isPreconnected_univ hV hδ hf₀ hf₁ (mem_univ 0) (by rwa [maximalIntegralCurve_zero])
    (mem_univ t)

/-- **The trajectories through the slab stay in it.** Under the hypotheses of
`TauCeti.maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc_of_intervalBase`, the maximal integral
curve of `V` through a point of the slab `M × [0, 1]` stays in the slab for all time. -/
theorem snd_maximalIntegralCurve_mem_Icc_of_intervalBase {z : M × ℝ} (hz : z.2 ∈ Icc 0 1)
    (t : ℝ) : (maximalIntegralCurve V z t).2 ∈ Icc 0 1 :=
  (maximalIntegralCurveInterval_eq_univ_and_snd_mem hv isCompact_Icc
    (fun hγ hs hs' ↦ hγ.snd_mem_Icc_of_snd_mem_Icc_of_intervalBase hs hs' hV hδ hf₀ hf₁) hz).2 t

/-- **The time increases along a trajectory in the open slab.** Under the hypotheses of
`TauCeti.maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc_of_intervalBase`, if
`∂ₜ f < C t (1 - t²)` in the open slab, then along the maximal integral curve of `V` through a
point of the open slab `M × (0, 1)` the time component `τ` is strictly increasing, since
`τ' = C τ (1 - τ²) - ∂ₜ f > 0`. -/
theorem strictMono_snd_maximalIntegralCurve_of_intervalBase
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    {z : M × ℝ} (hz : z.2 ∈ Ioo 0 1) : StrictMono fun t ↦ (maximalIntegralCurve V z t).2 :=
  (isMIntegralCurve_maximalIntegralCurve_of_eq_univ hv
    (maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc_of_intervalBase hv hV hδ hf₀ hf₁
      (Ioo_subset_Icc_self hz))).strictMono_snd fun t ↦ by
    rw [hV]
    linarith [hlt (maximalIntegralCurve V z t).1 _
      (snd_maximalIntegralCurve_mem_Ioo_of_intervalBase hv hV hδ hf₀ hf₁ hz t)]

/-- **The flow of a continuation field on the slab.** Let `M` be a compact boundaryless manifold
and `V` a `C¹` continuation field for a path `f` independent of the time for `t < δ` and for
`t > 1 - δ`. The trajectories of `V` through the slab `M × [0, 1]` are defined for all time and
stay in the slab, so they form a flow of `ℝ` on the slab, although `V` need not be complete. -/
noncomputable def continuationSlabFlow [CompleteSpace E] :
    Flow ℝ (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ)) :=
  globalFlowOn V hv _
    (fun _ hz ↦ maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc_of_intervalBase hv hV hδ hf₀
      hf₁ hz.2)
    fun _ hz t ↦
      ⟨mem_univ _, snd_maximalIntegralCurve_mem_Icc_of_intervalBase hv hV hδ hf₀ hf₁ hz.2 t⟩

/-- The flow of a continuation field on the slab is the maximal integral curve. -/
@[simp]
theorem coe_continuationSlabFlow_apply [CompleteSpace E] (t : ℝ)
    (z : (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ))) :
    (continuationSlabFlow hv hV hδ hf₀ hf₁ t z : M × ℝ) = maximalIntegralCurve V z t :=
  coe_globalFlowOn_apply hv _ _ t z

end Complete

/-! ### The ends of the trajectories -/

section Ends

variable [T2Space M] [IsManifold I 1 M] [I.Boundaryless] [CompactSpace M]

/-- The Lyapunov properties of the continuation potential for the flow on the slab: it is antitone
along every orbit, and the points along whose orbit it is constant are its critical points. -/
private theorem continuationSlabFlow_lyapunov [CompleteSpace E]
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0) :
    (∀ y, Antitone fun t ↦
      continuationPotential C f (continuationSlabFlow hv hV hδ hf₀ hf₁ t y)) ∧
      ∀ y, (∀ t, continuationPotential C f (continuationSlabFlow hv hV hδ hf₀ hf₁ t y) =
        continuationPotential C f y) →
          (y : M × ℝ) ∈ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) := by
  have hF : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) (continuationPotential C f) :=
    hf.continuationPotential
  have hγ : ∀ y,
      IsMIntegralCurve (fun t ↦ (continuationSlabFlow hv hV hδ hf₀ hf₁ t y : M × ℝ)) V :=
    isMIntegralCurve_coe_globalFlowOn hv _ _
  refine ⟨fun y ↦ (hγ y).antitone_comp (fun t ↦ hF _) fun t ↦ ?_, fun y hy ↦ ?_⟩
  · -- `dF(V) ≤ 0`, as `dF(V) < 0` off the critical points of `F`.
    by_cases hc : (continuationSlabFlow hv hV hδ hf₀ hf₁ t y : M × ℝ) ∈
      criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f)
    · simp [mem_criticalPoints.1 hc]
    · exact (hVF _ (continuationSlabFlow hv hV hδ hf₀ hf₁ t y).property.2 hc).le
  · -- Along the orbit `F` is constant, so its derivative `dF(V)` at `y` vanishes.
    by_contra hc
    have h := (hγ y).isMIntegralCurveAt 0
      |>.mfderiv_apply_eq_zero_of_eventuallyEq_const (hF _) (.of_forall hy)
    rw [Flow.map_zero_apply] at h
    exact (hVF y y.property.2 hc).ne h

/-- **Ends of the trajectories in the slab, relative to a finite set.** Let `l` be `atTop` or
`atBot`. If the critical points of the continuation potential in the slab which are cluster points
of the trajectory of `V` through `z` along `l` lie in a finite set `S`, the trajectory converges
along `l` to a point of `S`. -/
private theorem exists_tendsto_maximalIntegralCurve_of_finite {l : Filter ℝ}
    (hl : l = atTop ∨ l = atBot)
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0)
    {S : Set (M × ℝ)} (hS : S.Finite) {z : M × ℝ} (hz : z.2 ∈ Icc 0 1)
    (hSc : ∀ w : M × ℝ, w.2 ∈ Icc 0 1 →
      w ∈ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        MapClusterPt w l (maximalIntegralCurve V z) → w ∈ S) :
    ∃ w ∈ S, Tendsto (maximalIntegralCurve V z) l (𝓝 w) := by
  have : Nonempty M := ⟨z.1⟩
  have := CompleteSpace.of_locallyCompact_manifold M I
  have : CompactSpace (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ)) :=
    isCompact_iff_compactSpace.1 (isCompact_univ.prod isCompact_Icc)
  obtain ⟨hanti, hrest⟩ := continuationSlabFlow_lyapunov hv hf hV hδ hf₀ hf₁ hVF
  have hcoe : (fun t ↦ (continuationSlabFlow hv hV hδ hf₀ hf₁ t ⟨z, mem_univ _, hz⟩ : M × ℝ)) =
      maximalIntegralCurve V z := funext fun t ↦ coe_continuationSlabFlow_apply hv hV hδ hf₀ hf₁ t _
  have hrest' : ∀ w,
      MapClusterPt w l (fun t ↦ continuationSlabFlow hv hV hδ hf₀ hf₁ t ⟨z, mem_univ _, hz⟩) →
      (∀ t, continuationPotential C f (continuationSlabFlow hv hV hδ hf₀ hf₁ t w) =
        continuationPotential C f w) → (w : M × ℝ) ∈ S := fun w hw hc ↦
    hSc w w.property.2 (hrest w hc) (by
      rw [← hcoe]
      exact hw.continuousAt_comp continuous_subtypeVal.continuousAt)
  have hg : Continuous fun y : (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ)) ↦
      continuationPotential C f y := hf.continuationPotential.continuous.comp continuous_subtypeVal
  obtain ⟨w, hw, hlim⟩ : ∃ w ∈ Subtype.val ⁻¹' S,
      Tendsto (fun t ↦ continuationSlabFlow hv hV hδ hf₀ hf₁ t ⟨z, mem_univ _, hz⟩) l (𝓝 w) := by
    rcases hl with rfl | rfl
    · exact Flow.exists_tendsto_atTop_of_antitone _ hg _ (hanti _)
        (hS.preimage Subtype.val_injective.injOn) hrest'
    · exact Flow.exists_tendsto_atBot_of_antitone _ hg _ (hanti _)
        (hS.preimage Subtype.val_injective.injOn) hrest'
  refine ⟨w, hw, ?_⟩
  rw [← hcoe]
  exact (continuous_subtypeVal.tendsto w).comp hlim

/-- **Forward ends of the trajectories in the slab.** Let `M` be a compact boundaryless manifold,
`f` a differentiable path independent of the time for `t < δ` and for `t > 1 - δ`, with
`∂ₜ f < C t (1 - t²)` in the open slab, whose ends `f₀` and `f₁` have finitely many critical points.
Let `V` be a `C¹` continuation field for `f` which decreases the continuation potential `F` at the
points of the slab that are not critical for `F`. Then the trajectory of `V` through a point of the
slab `M × [0, 1]` converges at `+∞` to a point `(p, 0)` with `p` a critical point of `f₀` or
`(p, 1)` with `p` a critical point of `f₁`. -/
theorem exists_tendsto_maximalIntegralCurve_atTop_of_continuationPotential_of_snd_mem_Icc
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0)
    (h₀ : (criticalPoints I fun x ↦ f (x, 0)).Finite)
    (h₁ : (criticalPoints I fun x ↦ f (x, 1)).Finite) {z : M × ℝ} (hz : z.2 ∈ Icc 0 1) :
    ∃ w : M × ℝ, (w.2 = 0 ∨ w.2 = 1) ∧ w.1 ∈ criticalPoints I (fun x ↦ f (x, w.2)) ∧
      Tendsto (maximalIntegralCurve V z) atTop (𝓝 w) := by
  obtain ⟨w, hw, hlim⟩ := exists_tendsto_maximalIntegralCurve_of_finite (.inl rfl) hv hf hV hδ
    hf₀ hf₁ hVF (finite_setOf_snd_eq_zero_or_one_and_fst_mem_criticalPoints h₀ h₁) hz
    fun w hw hc _ ↦
      (mem_criticalPoints_continuationPotential_iff_of_mem_Icc_of_intervalBase (hf w) hδ hf₀ hf₁
        hlt hw).1 hc
  exact ⟨w, hw.1, hw.2, hlim⟩

/-- **Backward ends of the trajectories in the slab.** Under the hypotheses of
`TauCeti.exists_tendsto_maximalIntegralCurve_atTop_of_continuationPotential_of_snd_mem_Icc`, the
trajectory of `V` through a point of the slab `M × [0, 1]` converges at `-∞` to a point `(p, 0)`
with `p` a critical point of `f₀` or `(p, 1)` with `p` a critical point of `f₁`. -/
theorem exists_tendsto_maximalIntegralCurve_atBot_of_continuationPotential_of_snd_mem_Icc
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0)
    (h₀ : (criticalPoints I fun x ↦ f (x, 0)).Finite)
    (h₁ : (criticalPoints I fun x ↦ f (x, 1)).Finite) {z : M × ℝ} (hz : z.2 ∈ Icc 0 1) :
    ∃ w : M × ℝ, (w.2 = 0 ∨ w.2 = 1) ∧ w.1 ∈ criticalPoints I (fun x ↦ f (x, w.2)) ∧
      Tendsto (maximalIntegralCurve V z) atBot (𝓝 w) := by
  obtain ⟨w, hw, hlim⟩ := exists_tendsto_maximalIntegralCurve_of_finite (.inr rfl) hv hf hV hδ
    hf₀ hf₁ hVF (finite_setOf_snd_eq_zero_or_one_and_fst_mem_criticalPoints h₀ h₁) hz
    fun w hw hc _ ↦
      (mem_criticalPoints_continuationPotential_iff_of_mem_Icc_of_intervalBase (hf w) hδ hf₀ hf₁
        hlt hw).1 hc
  exact ⟨w, hw.1, hw.2, hlim⟩

/-- **A trajectory in the open slab ends on the target level.** Let `M` be a compact boundaryless
manifold, `f` a differentiable path independent of the time for `t < δ` and for `t > 1 - δ`, with
`∂ₜ f < C t (1 - t²)` in the open slab, whose end `f₁` has finitely many critical points. Let `V`
be a `C¹` continuation field for `f` which decreases the continuation potential `F` at the points
of the slab that are not critical for `F`. Then the trajectory of `V` through a point of the open
slab `M × (0, 1)` converges at `+∞` to `(q, 1)` for a critical point `q` of `f₁`. -/
theorem exists_tendsto_maximalIntegralCurve_atTop_of_continuationPotential_of_snd_mem_Ioo
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0)
    (h₁ : (criticalPoints I fun x ↦ f (x, 1)).Finite) {z : M × ℝ} (hz : z.2 ∈ Ioo 0 1) :
    ∃ q ∈ criticalPoints I (fun x ↦ f (x, 1)),
      Tendsto (maximalIntegralCurve V z) atTop (𝓝 (q, 1)) := by
  obtain ⟨⟨q, _⟩, ⟨hq, rfl⟩, hlim⟩ := exists_tendsto_maximalIntegralCurve_of_finite
    (.inl rfl) hv hf hV hδ hf₀ hf₁ hVF (h₁.prod (finite_singleton (1 : ℝ))) (Ioo_subset_Icc_self hz)
    fun w hw hc hcl ↦ by
      obtain ⟨h01, hw1⟩ :=
        (mem_criticalPoints_continuationPotential_iff_of_mem_Icc_of_intervalBase (hf w) hδ hf₀ hf₁
          hlt hw).1 hc
      -- The time component increases, so it stays above `z.2 > 0` in forward time.
      have hle : z.2 ≤ w.2 := by
        simpa only [Function.comp_apply, maximalIntegralCurve_zero] using
          (hcl.continuousAt_comp continuous_snd.continuousAt).ge_of_monotone_atTop
            (strictMono_snd_maximalIntegralCurve_of_intervalBase hv hV hδ hf₀ hf₁ hlt hz).monotone 0
      have h : w.2 = 1 := h01.resolve_left fun h ↦ by linarith [hz.1]
      exact ⟨by rwa [h] at hw1, h⟩
  exact ⟨q, hq, hlim⟩

/-- **A trajectory in the open slab starts on the source level.** Let `M` be a compact boundaryless
manifold, `f` a differentiable path independent of the time for `t < δ` and for `t > 1 - δ`, with
`∂ₜ f < C t (1 - t²)` in the open slab, whose end `f₀` has finitely many critical points. Let `V`
be a `C¹` continuation field for `f` which decreases the continuation potential `F` at the points
of the slab that are not critical for `F`. Then the trajectory of `V` through a point of the open
slab `M × (0, 1)` converges at `-∞` to `(p, 0)` for a critical point `p` of `f₀`. -/
theorem exists_tendsto_maximalIntegralCurve_atBot_of_continuationPotential_of_snd_mem_Ioo
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0)
    (h₀ : (criticalPoints I fun x ↦ f (x, 0)).Finite) {z : M × ℝ} (hz : z.2 ∈ Ioo 0 1) :
    ∃ p ∈ criticalPoints I (fun x ↦ f (x, 0)),
      Tendsto (maximalIntegralCurve V z) atBot (𝓝 (p, 0)) := by
  obtain ⟨⟨p, _⟩, ⟨hp, rfl⟩, hlim⟩ := exists_tendsto_maximalIntegralCurve_of_finite
    (.inr rfl) hv hf hV hδ hf₀ hf₁ hVF (h₀.prod (finite_singleton (0 : ℝ))) (Ioo_subset_Icc_self hz)
    fun w hw hc hcl ↦ by
      obtain ⟨h01, hw0⟩ :=
        (mem_criticalPoints_continuationPotential_iff_of_mem_Icc_of_intervalBase (hf w) hδ hf₀ hf₁
          hlt hw).1 hc
      -- The time component increases, so it stays below `z.2 < 1` in backward time.
      have hle : w.2 ≤ z.2 := by
        simpa only [Function.comp_apply, maximalIntegralCurve_zero] using
          (hcl.continuousAt_comp continuous_snd.continuousAt).le_of_monotone_atBot
            (strictMono_snd_maximalIntegralCurve_of_intervalBase hv hV hδ hf₀ hf₁ hlt hz).monotone 0
      have h : w.2 = 0 := h01.resolve_right fun h ↦ by linarith [hz.2]
      exact ⟨by rwa [h] at hw0, h⟩
  exact ⟨p, hp, hlim⟩

end Ends

end TauCeti
