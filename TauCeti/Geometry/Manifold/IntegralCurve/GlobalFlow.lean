/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import Mathlib.Dynamics.Flow
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The flow of a complete vector field

A `C¹` vector field `v` on a boundaryless manifold is **complete** when its maximal integral curves
are all defined for all time. Its maximal integral curves then assemble into a flow of `ℝ` on the
manifold, and this file packages them as a Mathlib `Flow`. Every `C¹` vector field on a compact
boundaryless manifold is complete (`isCompleteVectorField_of_compactSpace`).

## Main declarations

* `TauCeti.globalFlow`: the flow of a complete `C¹` vector field.
* `TauCeti.isMIntegralCurve_globalFlow`: its orbits are integral curves of the field.
* `TauCeti.apply_globalFlow_eq_sub`: a function `f` with `df(v) = -1` on a band decreases at unit
  speed along the flow while the flow stays in the band.
* `TauCeti.globalFlow_eq_of_isMIntegralCurve`: every integral curve is an orbit.
* `TauCeti.contMDiff_globalFlow_uncurry`: for a complete `C^n` field, the flow is jointly `C^n` in
  time and space.
* `TauCeti.globalFlowDiffeomorph`: for a complete `C^n` field, the time-`t` map is a `C^n`
  diffeomorphism; `TauCeti.globalFlowDiffeomorph_symm_apply`: its inverse is the time-`(-t)` map.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, Springer, 2012, Theorems 9.12 and 9.16.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

/-- The flow of a complete `C¹` vector field: `globalFlow v hv hcomplete t x` is the value at time
`t` of the integral curve of `v` through `x`. -/
noncomputable def globalFlow (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v) : Flow ℝ M where
  toFun t x := maximalIntegralCurve v x t
  cont' := by
    have h := contMDiffOn_maximalIntegralCurve (n := 1) le_rfl hv
    rw [maximalIntegralCurveFlowDomain_eq_univ
      hcomplete.maximalIntegralCurveInterval_eq_univ, contMDiffOn_univ] at h
    exact h.continuous.comp continuous_swap
  map_add' t₁ t₂ x := by
    rw [add_comm, maximalIntegralCurve_add hv (hcomplete.mem_maximalIntegralCurveInterval _ _)
      (hcomplete.mem_maximalIntegralCurveInterval _ _)]
  map_zero' x := maximalIntegralCurve_zero (hcomplete.mem_maximalIntegralCurveInterval x 0)

variable (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hcomplete : IsCompleteVectorField v)
include hv hcomplete

/-- The flow at time `t` is the maximal integral curve at time `t`. -/
@[simp]
theorem globalFlow_apply (t : ℝ) (x : M) :
    globalFlow v hv hcomplete t x = maximalIntegralCurve v x t := by
  rw [globalFlow]

/-- The orbits of the flow are integral curves of the field. -/
theorem isMIntegralCurve_globalFlow (x : M) :
    IsMIntegralCurve (fun t ↦ globalFlow v hv hcomplete t x) v := by
  simp only [globalFlow_apply]
  rw [isMIntegralCurve_iff_isMIntegralCurveOn,
    ← hcomplete.maximalIntegralCurveInterval_eq_univ x]
  exact isMIntegralCurveOn_maximalIntegralCurve hv

/-- **Unit-speed descent along a flow.** Let `v` be a complete `C¹` vector field with
`df(v) = -1` on an open set `U` containing the band `a ≤ f ≤ b`. If `f x ≤ b`, then `f` decreases
at unit speed along the flow line of `x` until it reaches the level `a`. -/
theorem apply_globalFlow_eq_sub {f : M → ℝ} {a b : ℝ} (hf : Continuous f) {U : Set M}
    (hU : IsOpen U) (hvU : ∀ y ∈ U, mvfderiv I f y (v y) = -1)
    (hband : ∀ y, a ≤ f y → f y ≤ b → y ∈ U)
    {x : M} {t : ℝ} (ht : 0 ≤ t) (hxt : a ≤ f x - t) (hxb : f x ≤ b) :
    f (globalFlow v hv hcomplete t x) = f x - t := by
  set γ : ℝ → M := fun u ↦ globalFlow v hv hcomplete u x
  have hγ : Continuous γ := (globalFlow v hv hcomplete).continuous continuous_id continuous_const
  -- The set of times at which the unit-speed identity holds is closed and contains `0`; near any
  -- such time before `t` the flow line stays in `U`, where `f ∘ γ + id` has zero derivative.
  let S := {u : ℝ | f (γ u) = f x - u}
  have hS : IsClosed S := isClosed_eq (hf.comp hγ) (continuous_const.sub continuous_id)
  suffices Icc 0 t ⊆ S from this ⟨ht, le_rfl⟩
  refine (hS.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin ?_ ?_
  · simp only [S, γ, mem_ofPred_eq, Flow.map_zero_apply, sub_zero]
  rintro u ⟨hu, hu0, hut⟩
  have hu' : f (γ u) = f x - u := hu
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hγ) u
    (hband _ (by rw [hu']; linarith) (by rw [hu']; linarith))
  have hderiv : ∀ s ∈ Metric.ball u ε, HasDerivAt (fun w ↦ f (γ w) + w) 0 s := by
    intro s hs
    have hsU : γ s ∈ U := hball hs
    have hmd : MDifferentiableAt I 𝓘(ℝ) f (γ s) :=
      mdifferentiableAt_of_mvfderiv_apply_ne_zero (by rw [hvU _ hsU]; norm_num)
    have h := Manifold.hasDerivAt_comp_curve hmd (isMIntegralCurve_globalFlow hv hcomplete x s)
    rw [hvU _ hsU] at h
    have h' := h.add (hasDerivAt_id' s)
    rwa [neg_add_cancel] at h'
  have hconst : ∀ s ∈ Metric.ball u ε, f (γ s) + s = f (γ u) + u := fun s hs ↦
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball u ε).isPreconnected
      (fun w hw ↦ (hderiv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hderiv w hw).deriv) hs (Metric.mem_ball_self hε)
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds u hε)] with s hs
  simp only [S, mem_ofPred_eq]
  linarith [hconst s hs]

/-- Every integral curve of the field is an orbit of the flow. -/
theorem globalFlow_eq_of_isMIntegralCurve {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    globalFlow v hv hcomplete t (γ 0) = γ t := by
  have h := (hγ.isMIntegralCurveOn (Ioo (-(|t| + 1)) (|t| + 1))).eqOn_maximalIntegralCurve hv
    (by constructor <;> linarith [abs_nonneg t]) rfl
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  rw [globalFlow_apply]
  exact h ht

omit hv in
/-- The flow of a complete `C^n` vector field, `1 ≤ n`, is jointly `C^n` in time and space. -/
theorem contMDiff_globalFlow_uncurry {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I n
      (fun p : ℝ × M ↦ globalFlow v (hvn.of_le (by exact_mod_cast hn)) hcomplete p.1 p.2) := by
  have h := contMDiffOn_maximalIntegralCurve hn hvn
  rw [maximalIntegralCurveFlowDomain_eq_univ
    hcomplete.maximalIntegralCurveInterval_eq_univ, contMDiffOn_univ] at h
  simp only [globalFlow_apply]
  exact h.comp (contMDiff_snd.prodMk contMDiff_fst)

omit hv in
/-- For a fixed time `t`, the time-`t` map of the flow of a complete `C^n` vector field, `1 ≤ n`,
is `C^n`. -/
theorem contMDiff_globalFlow_apply {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (t : ℝ) :
    ContMDiff I I n (globalFlow v (hvn.of_le (by exact_mod_cast hn)) hcomplete t) :=
  (contMDiff_globalFlow_uncurry hcomplete hn hvn).comp (contMDiff_const.prodMk contMDiff_id)

omit hv in
/-- The time-`t` map of the flow of a complete `C^n` vector field, `1 ≤ n`, as a `C^n`
diffeomorphism. Its inverse is the time-`(-t)` map. -/
noncomputable def globalFlowDiffeomorph {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (t : ℝ) :
    M ≃ₘ^n⟮I, I⟯ M where
  toEquiv := ((globalFlow v (hvn.of_le (by exact_mod_cast hn)) hcomplete).toHomeomorph t).toEquiv
  contMDiff_toFun := contMDiff_globalFlow_apply hcomplete hn hvn t
  contMDiff_invFun := contMDiff_globalFlow_apply hcomplete hn hvn (-t)

omit hv in
/-- The diffeomorphism `globalFlowDiffeomorph` is the time-`t` map of the flow. -/
@[simp]
theorem globalFlowDiffeomorph_apply {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (t : ℝ) (x : M) :
    globalFlowDiffeomorph hcomplete hn hvn t x =
      globalFlow v (hvn.of_le (by exact_mod_cast hn)) hcomplete t x := by
  rw [← Diffeomorph.coe_toEquiv, globalFlowDiffeomorph, Homeomorph.coe_toEquiv,
    Flow.toHomeomorph_apply]

omit hv in
/-- The inverse of `globalFlowDiffeomorph` at time `t` is the time-`(-t)` map of the flow. -/
@[simp]
theorem globalFlowDiffeomorph_symm_apply {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (t : ℝ) (x : M) :
    (globalFlowDiffeomorph hcomplete hn hvn t).symm x =
      globalFlow v (hvn.of_le (by exact_mod_cast hn)) hcomplete (-t) x := by
  rw [← Diffeomorph.coe_toEquiv, Diffeomorph.symm_toEquiv, globalFlowDiffeomorph,
    Homeomorph.coe_symm_toEquiv, Flow.toHomeomorph_symm_apply]

end TauCeti
