/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Extending bounded-operator convergence from dense subsets

This file records two standard density arguments for uniformly bounded families of continuous
semilinear maps between seminormed spaces. Pointwise convergence on a dense subset extends to
pointwise convergence everywhere, and uniform Cauchy convergence on a parameter set does likewise.
Both rest on the same estimate
`ContinuousLinearMap.norm_sub_apply_le_of_norm_le`, which moves the point at which a
difference of two bounded operators is evaluated to a nearby point of the dense subset.

For series, the same kind of estimate shows that if the finite partial sums `∑ i ∈ s, T i` of a
family of operators into a complete space are uniformly bounded, then the vectors `x` for which
`∑ i, T i x` converges form a closed set (`ContinuousLinearMap.isClosed_setOf_summable_apply`).
-/

public section

namespace ContinuousLinearMap

open Filter

variable {𝕜 𝕜₂ X Y : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜₂ Y]

/-- Comparing continuous semilinear maps of norms at most `K` and `L` at `x` costs at most
`(K + L) ‖x - y‖` more than comparing them at `y`. This is the shared estimate of the two density
arguments below: `y` is chosen in the dense subset, close to the arbitrary vector `x`. -/
theorem norm_sub_apply_le_of_norm_le {T S : X →SL[σ₁₂] Y} {K L : ℝ}
    (hT : ‖T‖ ≤ K) (hS : ‖S‖ ≤ L)
    (x y : X) : ‖T x - S x‖ ≤ ‖T y - S y‖ + (K + L) * ‖x - y‖ := by
  have h := (T - S).le_of_opNorm_le_of_le ((norm_sub_le T S).trans (add_le_add hT hS))
    (le_refl ‖x - y‖)
  have := norm_le_norm_add_norm_sub' ((T - S) x) ((T - S) y)
  simp only [map_sub, sub_apply] at h this
  linarith

/-- A uniformly bounded family of continuous semilinear maps that converges pointwise on a dense
subset converges pointwise everywhere. -/
theorem tendsto_apply_of_dense {ι : Type*} {l : Filter ι} {D : Set X}
    (hD : Dense D) {f : ι → X →SL[σ₁₂] Y} {g : X →SL[σ₁₂] Y} {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (htendsto : ∀ x ∈ D, Tendsto (fun i => f i x) l (nhds (g x))) (x : X) :
    Tendsto (fun i => f i x) l (nhds (g x)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x (by positivity : 0 < ε / (3 * (|C| + ‖g‖ + 1)))
  rw [lt_div_iff₀ (by positivity), dist_eq_norm] at hxy
  filter_upwards [hbound, Metric.tendsto_nhds.mp (htendsto y hyD) (ε / 3) (by positivity)]
    with i hi hiy
  rw [dist_eq_norm] at hiy ⊢
  have := norm_sub_apply_le_of_norm_le
    (hi.trans (by linarith [le_abs_self C, norm_nonneg g] : C ≤ |C| + ‖g‖ + 1))
    (by linarith [abs_nonneg C] : ‖g‖ ≤ |C| + ‖g‖ + 1) x y
  linarith

/-- A uniformly bounded family of continuous semilinear maps that is uniformly Cauchy on a
parameter set at every vector in a dense subset is uniformly Cauchy there at every vector. -/
theorem uniformCauchySeqOn_apply_of_dense {ι Z : Type*} {p : Filter ι}
    {D : Set X}
    (hD : Dense D) {f : ι → Z → X →SL[σ₁₂] Y} {s : Set Z} {C : ℝ}
    (hbound : ∀ᶠ i in p, ∀ z ∈ s, ‖f i z‖ ≤ C)
    (hcauchy : ∀ x ∈ D, UniformCauchySeqOn (fun i z => f i z x) p s) (x : X) :
    UniformCauchySeqOn (fun i z => f i z x) p s := by
  intro u hu
  obtain ⟨ε, hε, hball⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x (by positivity : 0 < ε / (3 * (|C| + 1)))
  rw [lt_div_iff₀ (by positivity), dist_eq_norm] at hxy
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  filter_upwards [hbound.prod_inl p, hbound.prod_inr p,
    hcauchy y hyD _ (Metric.dist_mem_uniformity (by positivity : 0 < ε / 3))] with m hi hj hm z hz
  refine hball ?_
  have hmid : dist (f m.1 z y) (f m.2 z y) < ε / 3 := hm z hz
  rw [dist_eq_norm] at hmid ⊢
  have := norm_sub_apply_le_of_norm_le ((hi z hz).trans hC) ((hj z hz).trans hC) x y
  linarith

/-- If the finite partial sums of a family of operators into a complete space are uniformly
bounded, then the vectors `x` for which the series `∑ i, T i x` converges form a closed set. -/
theorem isClosed_setOf_summable_apply [CompleteSpace Y] {ι : Type*} {T : ι → X →SL[σ₁₂] Y}
    {A : ℝ} (hT : ∀ s : Finset ι, ‖∑ i ∈ s, T i‖ ≤ A) : IsClosed {x | Summable fun i ↦ T i x} := by
  refine isClosed_of_closure_subset fun x hx ↦ summable_iff_vanishing_norm.mpr fun ε hε ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / (2 * (|A| + 1))) (by positivity)
  rw [lt_div_iff₀ (by positivity), dist_eq_norm] at hxy
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hy (ε / 2) (half_pos hε)
  refine ⟨s, fun t ht ↦ ?_⟩
  have h : ‖∑ i ∈ t, T i x‖ ≤ ‖(∑ i ∈ t, T i) (x - y)‖ + ‖∑ i ∈ t, T i y‖ := by
    simpa only [sum_apply, map_sub] using norm_le_norm_sub_add (∑ i ∈ t, T i x) (∑ i ∈ t, T i y)
  have hop : ‖∑ i ∈ t, T i‖ * ‖x - y‖ ≤ (|A| + 1) * ‖x - y‖ := by
    gcongr
    linarith [hT t, le_abs_self A]
  linarith [hs t ht, le_opNorm (∑ i ∈ t, T i) (x - y)]

end ContinuousLinearMap
