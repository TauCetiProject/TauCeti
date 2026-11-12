/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.ContinuationPotential.Basic
public import TauCeti.Geometry.Manifold.Flow.InvariantSet
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.Prod

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
  `τ' = C τ (1 - τ²) - ∂ₜ f > 0`, so it can neither end on `M × {0}` nor start on `M × {1}`. These
  are the trajectories counted by the continuation map from the Morse complex of `f₀` to that of
  `f₁`.

The convergence applies the Lyapunov argument of `Flow.exists_tendsto_atTop_of_antitone` to the
flow of `V` on the compact slab (`TauCeti.globalFlowOn`), with `F` as the Lyapunov function.

## Main results

* `IsMIntegralCurveOn.hasDerivAt_snd_of_continuationField`: the time component of a trajectory
  solves `τ' = C τ (1 - τ²) - ∂ₜ f`.
* `IsMIntegralCurveOn.snd_eq_zero_of_snd_eq_zero`, `IsMIntegralCurveOn.snd_eq_one_of_snd_eq_one`,
  `IsMIntegralCurveOn.snd_mem_Ioo_of_snd_mem_Ioo` and
  `IsMIntegralCurveOn.snd_mem_Icc_of_snd_mem_Icc`: invariance of the two end levels, of the open
  slab and of the slab.
* `IsMIntegralCurve.strictMono_snd`: the time increases along a trajectory in the open slab.
* `TauCeti.maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc` and
  `TauCeti.snd_maximalIntegralCurve_mem_Icc`: on a compact manifold the trajectories through the
  slab are defined for all time and stay in it.
* `TauCeti.exists_tendsto_maximalIntegralCurve_atTop_of_snd_mem_Icc` and
  `TauCeti.exists_tendsto_maximalIntegralCurve_atBot_of_snd_mem_Icc`: the trajectories through the
  slab converge to critical points of `f₀` or `f₁` on the end levels.
* `TauCeti.exists_tendsto_maximalIntegralCurve_atTop_of_snd_mem_Ioo` and
  `TauCeti.exists_tendsto_maximalIntegralCurve_atBot_of_snd_mem_Ioo`: a trajectory in the open
  slab runs from a critical point `(p, 0)` of `f₀` to a critical point `(q, 1)` of `f₁`.

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

/-- **The time component of a continuation trajectory.** Let `V` be a vector field on `M × ℝ`
whose time component is `C t (1 - t²) - ∂ₜ f`. Along an integral curve `γ` of `V` on a
neighbourhood of `t`, the time component `τ = (γ ·).2` has derivative
`C τ (1 - τ²) - ∂ₜ f (γ t)` at `t`. -/
theorem _root_.IsMIntegralCurveOn.hasDerivAt_snd_of_continuationField
    (hγ : IsMIntegralCurveOn γ V s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    {t : ℝ} (hs : s ∈ 𝓝 t) :
    HasDerivAt (fun r ↦ (γ r).2)
      (C * (γ t).2 * (1 - (γ t).2 ^ 2) - deriv (fun s ↦ f ((γ t).1, s)) (γ t).2) t := by
  have h := Manifold.hasDerivAt_comp_curve (g := id ∘ Prod.snd)
    (mdifferentiableAt_id.comp _ mdifferentiableAt_snd)
    ((hγ t (mem_of_mem_nhds hs)).hasMFDerivAt hs)
  rw [mvfderiv_comp_snd_apply_eq_smul_deriv, deriv_id, smul_eq_mul, mul_one] at h
  -- The tangent vector `V (γ t)` is a pair in `E × ℝ`; its second component is given by `hV`.
  rw [← hV]
  exact h

/-- **Invariance of the source level.** Let `V` be a continuation field for a path `f` independent
of the time for `t < δ`. An integral curve of `V` on an open preconnected set which meets the level
`M × {0}` stays in it. -/
theorem _root_.IsMIntegralCurveOn.snd_eq_zero_of_snd_eq_zero (hγ : IsMIntegralCurveOn γ V s)
    (hs : IsOpen s) (hs' : IsPreconnected s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) {s₀ t : ℝ} (hs₀ : s₀ ∈ s)
    (h₀ : (γ s₀).2 = 0) (ht : t ∈ s) : (γ t).2 = 0 :=
  eqOn_const_of_hasDerivAt_intervalBase (c := 0) (by simp) hδ hs hs'
    (fun r hr ↦ hγ.hasDerivAt_snd_of_continuationField hV (hs.mem_nhds hr))
    (fun _ _ hr ↦ deriv_prodMk_eq_zero_of_lt hf₀ (by simpa using (abs_lt.1 hr).2)) hs₀ h₀ ht

/-- **Invariance of the target level.** Let `V` be a continuation field for a path `f` independent
of the time for `t > 1 - δ`. An integral curve of `V` on an open preconnected set which meets the
level `M × {1}` stays in it. -/
theorem _root_.IsMIntegralCurveOn.snd_eq_one_of_snd_eq_one (hγ : IsMIntegralCurveOn γ V s)
    (hs : IsOpen s) (hs' : IsPreconnected s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) {s₀ t : ℝ} (hs₀ : s₀ ∈ s)
    (h₁ : (γ s₀).2 = 1) (ht : t ∈ s) : (γ t).2 = 1 :=
  eqOn_const_of_hasDerivAt_intervalBase (c := 1) (by simp) hδ hs hs'
    (fun r hr ↦ hγ.hasDerivAt_snd_of_continuationField hV (hs.mem_nhds hr))
    (fun _ _ hr ↦ deriv_prodMk_eq_zero_of_gt hf₁ (by linarith [(abs_lt.1 hr).1])) hs₀ h₁ ht

/-- **Invariance of the open slab.** Let `V` be a continuation field for a path `f` independent of
the time for `t < δ` and for `t > 1 - δ`. An integral curve of `V` on an open preconnected set which
meets the open slab `M × (0, 1)` stays in it. -/
theorem _root_.IsMIntegralCurveOn.snd_mem_Ioo_of_snd_mem_Ioo (hγ : IsMIntegralCurveOn γ V s)
    (hs : IsOpen s) (hs' : IsPreconnected s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) {s₀ t : ℝ} (hs₀ : s₀ ∈ s)
    (h : (γ s₀).2 ∈ Ioo 0 1) (ht : t ∈ s) : (γ t).2 ∈ Ioo 0 1 :=
  mapsTo_Ioo_of_hasDerivAt_intervalBase hδ hs hs'
    (fun r hr ↦ hγ.hasDerivAt_snd_of_continuationField hV (hs.mem_nhds hr))
    (fun _ _ hr ↦ deriv_prodMk_eq_zero_of_lt hf₀ (by simpa using (abs_lt.1 hr).2))
    (fun _ _ hr ↦ deriv_prodMk_eq_zero_of_gt hf₁ (by linarith [(abs_lt.1 hr).1])) hs₀ h ht

/-- **Invariance of the slab.** Let `V` be a continuation field for a path `f` independent of the
time for `t < δ` and for `t > 1 - δ`. An integral curve of `V` on an open preconnected set which
meets the slab `M × [0, 1]` stays in it. -/
theorem _root_.IsMIntegralCurveOn.snd_mem_Icc_of_snd_mem_Icc (hγ : IsMIntegralCurveOn γ V s)
    (hs : IsOpen s) (hs' : IsPreconnected s)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) {s₀ t : ℝ} (hs₀ : s₀ ∈ s)
    (h : (γ s₀).2 ∈ Icc 0 1) (ht : t ∈ s) : (γ t).2 ∈ Icc 0 1 := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc h with h | h | h
  · rw [hγ.snd_eq_zero_of_snd_eq_zero hs hs' hV hδ hf₀ hs₀ h ht]
    exact left_mem_Icc.2 zero_le_one
  · rw [hγ.snd_eq_one_of_snd_eq_one hs hs' hV hδ hf₁ hs₀ h ht]
    exact right_mem_Icc.2 zero_le_one
  · exact Ioo_subset_Icc_self (hγ.snd_mem_Ioo_of_snd_mem_Ioo hs hs' hV hδ hf₀ hf₁ hs₀ h ht)

/-! ### Completeness in the slab -/

section Complete

variable [T2Space M] [IsManifold I 1 M] [I.Boundaryless] [CompactSpace M]

/-- **The trajectories through the slab are complete.** Let `M` be a compact boundaryless
manifold and `V` a `C¹` continuation field for a path `f` independent of the time for `t < δ` and
for `t > 1 - δ`. The maximal integral curve of `V` through a point of the slab `M × [0, 1]` is
defined for all time. -/
theorem maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) {z : M × ℝ} (hz : z.2 ∈ Icc 0 1) :
    maximalIntegralCurveInterval V z = univ := by
  -- The model space is complete: a nonempty compact manifold is finite-dimensional.
  have : Nonempty M := ⟨z.1⟩
  have : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have h0 := zero_mem_maximalIntegralCurveInterval (v := V) (x := z) hv.contMDiffAt
  refine maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (isCompact_univ.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))) fun t ht ↦ ⟨mem_univ _, ?_⟩
  exact (isMIntegralCurveOn_maximalIntegralCurve hv).snd_mem_Icc_of_snd_mem_Icc
    isOpen_maximalIntegralCurveInterval isPreconnected_maximalIntegralCurveInterval hV hδ hf₀ hf₁
    h0 (by rwa [maximalIntegralCurve_zero]) ht

/-- **The trajectories through the slab stay in it.** Under the hypotheses of
`TauCeti.maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc`, the maximal integral curve of `V`
through a point of the slab `M × [0, 1]` stays in the slab for all time. -/
theorem snd_maximalIntegralCurve_mem_Icc
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) {z : M × ℝ} (hz : z.2 ∈ Icc 0 1) (t : ℝ) :
    (maximalIntegralCurve V z t).2 ∈ Icc 0 1 := by
  have huniv := maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc hv hV hδ hf₀ hf₁ hz
  have hγ := isMIntegralCurveOn_maximalIntegralCurve (x := z) hv
  rw [huniv] at hγ
  exact hγ.snd_mem_Icc_of_snd_mem_Icc isOpen_univ isPreconnected_univ hV hδ hf₀ hf₁ (mem_univ 0)
    (by rwa [maximalIntegralCurve_zero]) (mem_univ t)

end Complete

/-! ### The ends of the trajectories -/

/-- **The time increases along a trajectory in the open slab.** Let `V` be a continuation field
for a path `f` with `∂ₜ f < C t (1 - t²)` in the open slab. Along an integral curve of `V` staying
in the open slab `M × (0, 1)`, the time component `τ` is strictly increasing, since
`τ' = C τ (1 - τ²) - ∂ₜ f > 0`. -/
theorem _root_.IsMIntegralCurve.strictMono_snd (hγ : IsMIntegralCurve γ V)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    (hI : ∀ t, (γ t).2 ∈ Ioo 0 1) : StrictMono fun t ↦ (γ t).2 :=
  strictMono_of_hasDerivAt_pos
    (fun t ↦ (hγ.isMIntegralCurveOn univ).hasDerivAt_snd_of_continuationField hV univ_mem)
    fun t ↦ by linarith [hlt (γ t).1 _ (hI t)]

section Ends

variable [T2Space M] [IsManifold I 1 M] [I.Boundaryless] [CompactSpace M]

omit [T2Space M] [IsManifold I 1 M] [CompactSpace M] in
/-- At a point of the slab, a critical point of the continuation potential lies over a critical
point of `f₀` on `M × {0}` or of `f₁` on `M × {1}`. -/
private theorem mem_criticalPoints_continuationPotential_iff_of_snd_mem_Icc
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f) (hδ : 0 < δ)
    (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0)) (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    {z : M × ℝ} (hz : z.2 ∈ Icc 0 1) :
    z ∈ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) ↔
      (z.2 = 0 ∨ z.2 = 1) ∧ z.1 ∈ criticalPoints I (fun x ↦ f (x, z.2)) := by
  refine mem_criticalPoints_continuationPotential_iff_of_mem_Icc
    (hf.mdifferentiableAt one_ne_zero) hz (hlt z.1 z.2) fun hz' ↦ ?_
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hz with h | h | h
  · exact deriv_prodMk_eq_zero_of_lt hf₀ (h ▸ hδ)
  · exact deriv_prodMk_eq_zero_of_gt hf₁ (by linarith)
  · exact absurd h hz'

/-- The flow of a continuation field on the slab `M × [0, 1]` of a compact manifold. -/
private noncomputable def slabFlow [CompleteSpace E]
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) :
    Flow ℝ (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ)) :=
  globalFlowOn V hv _
    (fun _ hz ↦ maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc hv hV hδ hf₀ hf₁ hz.2)
    fun _ hz t ↦ ⟨mem_univ _, snd_maximalIntegralCurve_mem_Icc hv hV hδ hf₀ hf₁ hz.2 t⟩

/-- The orbits of the flow on the slab are integral curves of the continuation field. -/
private theorem isMIntegralCurve_slabFlow [CompleteSpace E]
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) (y : (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ))) :
    IsMIntegralCurve (fun t ↦ (slabFlow hv hV hδ hf₀ hf₁ t y : M × ℝ)) V :=
  isMIntegralCurve_coe_globalFlowOn hv _ _ y

/-- The flow on the slab is the maximal integral curve of the continuation field. -/
private theorem coe_slabFlow_apply [CompleteSpace E]
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1)) (t : ℝ)
    (y : (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ))) :
    (slabFlow hv hV hδ hf₀ hf₁ t y : M × ℝ) = maximalIntegralCurve V y t :=
  coe_globalFlowOn_apply hv _ _ t y

/-- The Lyapunov properties of the continuation potential for the flow on the slab: it is antitone
along every orbit, the points along whose orbit it is constant are its critical points, and these
are finitely many. -/
private theorem slabFlow_lyapunov [CompleteSpace E]
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0)
    (h₀ : (criticalPoints I fun x ↦ f (x, 0)).Finite)
    (h₁ : (criticalPoints I fun x ↦ f (x, 1)).Finite) :
    (∀ y, Antitone fun t ↦ continuationPotential C f (slabFlow hv hV hδ hf₀ hf₁ t y)) ∧
      (∀ y, (∀ t, continuationPotential C f (slabFlow hv hV hδ hf₀ hf₁ t y) =
        continuationPotential C f y) →
          y ∈ (↑) ⁻¹' criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f)) ∧
      ((↑) ⁻¹' criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) :
        Set (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ))).Finite := by
  have hF : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) (continuationPotential C f) :=
    hf.continuationPotential.mdifferentiable one_ne_zero
  have hγ := isMIntegralCurve_slabFlow hv hV hδ hf₀ hf₁
  refine ⟨fun y ↦ (hγ y).antitone_comp (fun t ↦ hF _) fun t ↦ ?_, fun y hy ↦ ?_, ?_⟩
  · -- `dF(V) ≤ 0`, as `dF(V) < 0` off the critical points of `F`.
    by_cases hc : (slabFlow hv hV hδ hf₀ hf₁ t y : M × ℝ) ∈
      criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f)
    · simp [mem_criticalPoints.1 hc]
    · exact (hVF _ (slabFlow hv hV hδ hf₀ hf₁ t y).2.2 hc).le
  · -- Along the orbit `F` is constant, so its derivative `dF(V)` at `y` vanishes.
    by_contra hc
    have hd := Manifold.hasDerivAt_comp_curve (hF _) (hγ y 0)
    have horbit : (continuationPotential C f ∘ fun t ↦ (slabFlow hv hV hδ hf₀ hf₁ t y : M × ℝ)) =
        fun _ ↦ continuationPotential C f y := funext hy
    rw [horbit] at hd
    have hy0 : (slabFlow hv hV hδ hf₀ hf₁ 0 y : M × ℝ) = y := by rw [Flow.map_zero_apply]
    exact (hVF _ (slabFlow hv hV hδ hf₀ hf₁ 0 y).2.2 (by rwa [hy0])).ne
      (hd.unique (hasDerivAt_const _ _))
  · -- The critical points in the slab lie over those of `f₀` and `f₁`.
    refine ((h₀.prod (finite_singleton (0 : ℝ))).union
      (h₁.prod (finite_singleton (1 : ℝ)))).preimage Subtype.val_injective.injOn
      |>.subset fun y hy ↦ ?_
    obtain ⟨h01, hy1⟩ := (mem_criticalPoints_continuationPotential_iff_of_snd_mem_Icc hf hδ hf₀ hf₁
      hlt y.2.2).1 hy
    rcases h01 with h | h
    · exact .inl ⟨by rwa [h] at hy1, h⟩
    · exact .inr ⟨by rwa [h] at hy1, h⟩

/-- **Forward ends of the trajectories in the slab.** Let `M` be a compact boundaryless manifold,
`f` a `C¹` path independent of the time for `t < δ` and for `t > 1 - δ`, with
`∂ₜ f < C t (1 - t²)` in the open slab, whose ends `f₀` and `f₁` have finitely many critical points.
Let `V` be a `C¹` continuation field for `f` which decreases the continuation potential `F` at the
points of the slab that are not critical for `F`. Then the trajectory of `V` through a point of the
slab `M × [0, 1]` converges at `+∞` to a point `(p, 0)` with `p` a critical point of `f₀` or
`(p, 1)` with `p` a critical point of `f₁`. -/
theorem exists_tendsto_maximalIntegralCurve_atTop_of_snd_mem_Icc
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f)
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
  have : Nonempty M := ⟨z.1⟩
  have : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompactSpace (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ)) :=
    isCompact_iff_compactSpace.1 (isCompact_univ.prod isCompact_Icc)
  obtain ⟨hanti, hrest, hfin⟩ := slabFlow_lyapunov hv hf hV hδ hf₀ hf₁ hlt hVF h₀ h₁
  obtain ⟨w, hw, hlim⟩ := Flow.exists_tendsto_atTop_of_antitone (slabFlow hv hV hδ hf₀ hf₁)
    (hf.continuationPotential.continuous.comp continuous_subtype_val) hanti hfin hrest
    ⟨z, mem_univ _, hz⟩
  obtain ⟨h01, hw⟩ := (mem_criticalPoints_continuationPotential_iff_of_snd_mem_Icc hf hδ hf₀ hf₁ hlt
    w.2.2).1 hw
  refine ⟨w, h01, hw, ?_⟩
  simpa only [comp_def, coe_slabFlow_apply] using (continuous_subtype_val.tendsto w).comp hlim

/-- **Backward ends of the trajectories in the slab.** Under the hypotheses of
`TauCeti.exists_tendsto_maximalIntegralCurve_atTop_of_snd_mem_Icc`, the trajectory of `V` through a
point of the slab `M × [0, 1]` converges at `-∞` to a point `(p, 0)` with `p` a critical point of
`f₀` or `(p, 1)` with `p` a critical point of `f₁`. -/
theorem exists_tendsto_maximalIntegralCurve_atBot_of_snd_mem_Icc
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f)
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
  have : Nonempty M := ⟨z.1⟩
  have : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompactSpace (univ ×ˢ Icc (0 : ℝ) 1 : Set (M × ℝ)) :=
    isCompact_iff_compactSpace.1 (isCompact_univ.prod isCompact_Icc)
  obtain ⟨hanti, hrest, hfin⟩ := slabFlow_lyapunov hv hf hV hδ hf₀ hf₁ hlt hVF h₀ h₁
  -- Apply the forward convergence to the reversed flow, along which `-F` is antitone.
  obtain ⟨w, hw, hlim⟩ := Flow.exists_tendsto_atTop_of_antitone
    (slabFlow hv hV hδ hf₀ hf₁).reverse
    (hf.continuationPotential.continuous.comp continuous_subtype_val).neg
    (fun y _ _ hst ↦ by
      simp only [Flow.reverse_apply, Pi.neg_apply, comp_apply]
      exact neg_le_neg (hanti y (neg_le_neg hst)))
    hfin
    (fun y hy ↦ hrest y fun t ↦ by
      have := hy (-t)
      simp only [Flow.reverse_apply, neg_neg, Pi.neg_apply, comp_apply] at this
      exact neg_inj.1 this)
    ⟨z, mem_univ _, hz⟩
  obtain ⟨h01, hw⟩ := (mem_criticalPoints_continuationPotential_iff_of_snd_mem_Icc hf hδ hf₀ hf₁ hlt
    w.2.2).1 hw
  refine ⟨w, h01, hw, ?_⟩
  have := ((continuous_subtype_val.tendsto w).comp hlim).comp tendsto_neg_atBot_atTop
  simpa only [comp_def, Flow.reverse_apply, neg_neg, coe_slabFlow_apply] using this

/-- **A trajectory in the open slab ends on the target level.** Under the hypotheses of
`TauCeti.exists_tendsto_maximalIntegralCurve_atTop_of_snd_mem_Icc`, the trajectory of `V` through a
point of the open slab `M × (0, 1)` converges at `+∞` to `(q, 1)` for a critical point `q` of
`f₁`. -/
theorem exists_tendsto_maximalIntegralCurve_atTop_of_snd_mem_Ioo
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0)
    (h₀ : (criticalPoints I fun x ↦ f (x, 0)).Finite)
    (h₁ : (criticalPoints I fun x ↦ f (x, 1)).Finite) {z : M × ℝ} (hz : z.2 ∈ Ioo 0 1) :
    ∃ q ∈ criticalPoints I (fun x ↦ f (x, 1)),
      Tendsto (maximalIntegralCurve V z) atTop (𝓝 (q, 1)) := by
  obtain ⟨w, h01, hw, hlim⟩ := exists_tendsto_maximalIntegralCurve_atTop_of_snd_mem_Icc hv hf hV hδ
    hf₀ hf₁ hlt hVF h₀ h₁ (Ioo_subset_Icc_self hz)
  have hγ := isMIntegralCurve_maximalIntegralCurve_of_eq_univ hv
    (maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc hv hV hδ hf₀ hf₁ (Ioo_subset_Icc_self hz))
  have hI : ∀ t, (maximalIntegralCurve V z t).2 ∈ Ioo 0 1 := fun t ↦
    (hγ.isMIntegralCurveOn univ).snd_mem_Ioo_of_snd_mem_Ioo isOpen_univ isPreconnected_univ hV hδ
      hf₀ hf₁ (mem_univ 0) (by rwa [maximalIntegralCurve_zero]) (mem_univ t)
  have hτ := (continuous_snd.tendsto w).comp hlim
  rcases h01 with h | h
  · -- The time component increases, so it cannot tend to `0`.
    rw [h] at hτ
    exact absurd ((hγ.strictMono_snd hV hlt hI).monotone.ge_of_tendsto hτ 0) (hI 0).1.not_ge
  · exact ⟨w.1, h ▸ hw, by rwa [← h]⟩

/-- **A trajectory in the open slab starts on the source level.** Under the hypotheses of
`TauCeti.exists_tendsto_maximalIntegralCurve_atTop_of_snd_mem_Icc`, the trajectory of `V` through a
point of the open slab `M × (0, 1)` converges at `-∞` to `(p, 0)` for a critical point `p` of
`f₀`. -/
theorem exists_tendsto_maximalIntegralCurve_atBot_of_snd_mem_Ioo
    (hv : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent 1
      (fun z ↦ (⟨z, V z⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))))
    (hf : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) 1 f)
    (hV : ∀ z, (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) - deriv (fun s ↦ f (z.1, s)) z.2)
    (hδ : 0 < δ) (hf₀ : ∀ x t, t < δ → f (x, t) = f (x, 0))
    (hf₁ : ∀ x t, 1 - δ < t → f (x, t) = f (x, 1))
    (hlt : ∀ x, ∀ t ∈ Ioo (0 : ℝ) 1, deriv (fun s ↦ f (x, s)) t < C * t * (1 - t ^ 2))
    (hVF : ∀ z : M × ℝ, z.2 ∈ Icc 0 1 →
      z ∉ criticalPoints (I.prod 𝓘(ℝ)) (continuationPotential C f) →
        mvfderiv (I.prod 𝓘(ℝ)) (continuationPotential C f) z (V z) < 0)
    (h₀ : (criticalPoints I fun x ↦ f (x, 0)).Finite)
    (h₁ : (criticalPoints I fun x ↦ f (x, 1)).Finite) {z : M × ℝ} (hz : z.2 ∈ Ioo 0 1) :
    ∃ p ∈ criticalPoints I (fun x ↦ f (x, 0)),
      Tendsto (maximalIntegralCurve V z) atBot (𝓝 (p, 0)) := by
  obtain ⟨w, h01, hw, hlim⟩ := exists_tendsto_maximalIntegralCurve_atBot_of_snd_mem_Icc hv hf hV hδ
    hf₀ hf₁ hlt hVF h₀ h₁ (Ioo_subset_Icc_self hz)
  have hγ := isMIntegralCurve_maximalIntegralCurve_of_eq_univ hv
    (maximalIntegralCurveInterval_eq_univ_of_snd_mem_Icc hv hV hδ hf₀ hf₁ (Ioo_subset_Icc_self hz))
  have hI : ∀ t, (maximalIntegralCurve V z t).2 ∈ Ioo 0 1 := fun t ↦
    (hγ.isMIntegralCurveOn univ).snd_mem_Ioo_of_snd_mem_Ioo isOpen_univ isPreconnected_univ hV hδ
      hf₀ hf₁ (mem_univ 0) (by rwa [maximalIntegralCurve_zero]) (mem_univ t)
  have hτ := (continuous_snd.tendsto w).comp hlim
  rcases h01 with h | h
  · exact ⟨w.1, h ▸ hw, by rwa [← h]⟩
  · -- The time component increases, so it cannot tend to `1` backward in time.
    rw [h] at hτ
    exact absurd ((hγ.strictMono_snd hV hlt hI).monotone.le_of_tendsto hτ 0) (hI 0).2.not_ge

end Ends

end TauCeti
