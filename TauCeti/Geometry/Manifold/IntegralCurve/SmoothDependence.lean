/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.ODE.InitialCondition
public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal

/-!
# Smooth dependence of the maximal integral curve near time zero

Let `v` be a vector field on a separated boundaryless `C^1` manifold `M` modelled on a
finite-dimensional space. This file shows that if `v` is `C^(n+1)` at `x₀`, then the maximal flow
`(x, t) ↦ maximalIntegralCurve v x t` is jointly `C^(n+1)` in the initial point and the time at
`(x₀, 0)`. Together with
`TauCeti.eventually_mem_maximalIntegralCurveInterval`, which puts a neighbourhood of `(x₀, 0)` in
the domain of the maximal flow, this is the local input to the smooth flow of a vector field, and
in particular to the geodesic flow, which is the flow of the geodesic spray on the tangent bundle.

For the smoothness statement, the model-space input is `ODE.exists_contDiffAt_localFlow`, applied
to the vector field read in the extended chart at `x₀`. That theorem produces a local flow `Φ` in
coordinates. Applying the inverse chart to the curves `t ↦ Φ (extChartAt I x₀ x) t` gives, for
every `x` near `x₀`, an integral curve of `v` through `x` on one fixed interval around `0`.
Fixed-chart uniqueness of integral curves, `IsMIntegralCurveOn.eqOn_of_contDiffOn_extChartAt`,
identifies these curves with the witnesses defining the maximal integral curves, so the maximal
flow agrees near `(x₀, 0)` with the chart expression
`(x, t) ↦ (extChartAt I x₀).symm (Φ (extChartAt I x₀ x) t)`, which is visibly `C^(n+1)`.
The maximal flow is defined without any choice of local flow, so the finite orders assemble into
the smooth case.

## Main results

* `contMDiffAt_maximalIntegralCurve`: the maximal flow is `C^(n+1)` in the initial point and the
  time at `(x₀, 0)`.

## References

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012],
  Chapter 9, Theorem 9.12.
* [Winston Yin, mathlib4#26394: _Existence of local flows on
  manifolds_](https://github.com/leanprover-community/mathlib4/pull/26394), for the manifold
  local-flow formulation.
-/

public section

open Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M]
  [FiniteDimensional ℝ E] [T2Space M] {v : (x : M) → TangentSpace I x} {x₀ : M}

/-- **The maximal flow in a chart.** If the vector field `v`, read in the extended chart at `x₀`,
is `C^(n+1)` near the image of `x₀`, then there is a coordinate map `Φ` with `Φ z 0 = z`, jointly
`C^(n+1)` at `(extChartAt I x₀ x₀, 0)`, such that near `(x₀, 0)` the maximal flow is `Φ` read back
through the chart. -/
private theorem exists_contDiffAt_maximalIntegralCurve_eq_extChartAt_symm {n : ℕ∞}
    {u : Set E} (hu : u ∈ 𝓝 (extChartAt I x₀ x₀))
    (hvu : ContDiffOn ℝ (n + 1) (fun z ↦ tangentCoordChange I ((extChartAt I x₀).symm z) x₀
      ((extChartAt I x₀).symm z) (v ((extChartAt I x₀).symm z))) u) :
    ∃ Φ : E → ℝ → E, ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ Φ p.1 p.2) (extChartAt I x₀ x₀, 0) ∧
      (∀ z, Φ z 0 = z) ∧ ∀ᶠ p in 𝓝 ((x₀, 0) : M × ℝ),
        maximalIntegralCurve v p.1 p.2 = (extChartAt I x₀).symm (Φ (extChartAt I x₀ p.1) p.2) := by
  set φ := extChartAt I x₀
  obtain ⟨o, hou, ho, hxo⟩ := mem_nhds_iff.mp hu
  obtain ⟨Φ, hΦ, hΦ0, -, hΦderiv⟩ := ODE.exists_contDiffAt_localFlow _ hvu hu
  refine ⟨Φ, hΦ, hΦ0, ?_⟩
  -- Near `(φ x₀, 0)` the coordinate flow solves the equation and stays inside the chart target.
  have htarget : interior φ.target ∈ 𝓝 (φ x₀) :=
    isOpen_interior.mem_nhds (I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint)
  have hmem : ∀ᶠ p in 𝓝 ((φ x₀, 0) : E × ℝ), Φ p.1 p.2 ∈ interior φ.target :=
    hΦ.continuousAt.eventually_mem (by simpa [hΦ0] using htarget)
  have hmemu : ∀ᶠ p in 𝓝 ((φ x₀, 0) : E × ℝ), Φ p.1 p.2 ∈ o :=
    hΦ.continuousAt.eventually_mem (by simpa [hΦ0] using ho.mem_nhds hxo)
  -- Shrink to a product of a neighbourhood of `φ x₀` and a symmetric interval of times.
  have hbox := hΦderiv.and (hmem.and hmemu)
  rw [nhds_prod_eq] at hbox
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.mp hbox
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hpb
  have hIoo : ∀ t ∈ Ioo (-ε) ε, pb t := fun t ht ↦ hball t <| by
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
    exact ht
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  -- For each nearby initial point, the chart image of the coordinate flow is an integral curve of
  -- `v` through that point on `Ioo (-ε) ε`.
  have hcurve : ∀ x ∈ φ.source, pa (φ x) →
      IsMIntegralCurveOn (φ.symm ∘ Φ (φ x)) v (Ioo (-ε) ε) ∧ (φ.symm ∘ Φ (φ x)) 0 = x := by
    intro x hx hpax
    refine ⟨IsMIntegralCurveAt.isMIntegralCurveOn fun t ht ↦ ?_, by simp [hΦ0, φ.left_inv hx]⟩
    refine IsMIntegralCurveAt.of_extChartAt_symm ?_ ?_
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using (hab hpax (hIoo s hs)).2.1
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using (hab hpax (hIoo s hs)).1
  have hx : ∀ᶠ x in 𝓝 x₀, x ∈ φ.source ∧ pa (φ x) :=
    Filter.Eventually.and (extChartAt_source_mem_nhds (I := I) x₀)
      ((continuousAt_extChartAt x₀).eventually hpa)
  filter_upwards [hx.prod_nhds (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)] with p hp
  obtain ⟨hγ, hγ0⟩ := hcurve p.1 hp.1.1 hp.1.2
  have hpt : p.2 ∈ maximalIntegralCurveInterval v p.1 :=
    hγ.subset_maximalIntegralCurveInterval h0 hγ0 hp.2
  obtain ⟨δ, c, d, hδ, hδ0, hc0, hpcd, hmax⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq hpt
  let a := max (-ε) c
  let b := min ε d
  have hsubγ : Ioo a b ⊆ Ioo (-ε) ε :=
    Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hsubδ : Ioo a b ⊆ Ioo c d :=
    Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have h0' : (0 : ℝ) ∈ Ioo a b := ⟨max_lt h0.1 hc0.1, lt_min h0.2 hc0.2⟩
  have hp' : p.2 ∈ Ioo a b := ⟨max_lt hp.2.1 hpcd.1, lt_min hp.2.2 hpcd.2⟩
  have hγsrc : ∀ t ∈ Ioo a b, (φ.symm ∘ Φ (φ p.1)) t ∈ φ.source := by
    intro t ht
    exact φ.map_target (interior_subset (hab hp.1.2 (hIoo t (hsubγ ht))).2.1)
  have hγu : ∀ t ∈ Ioo a b, φ ((φ.symm ∘ Φ (φ p.1)) t) ∈ o := by
    intro t ht
    have htarget' := interior_subset (hab hp.1.2 (hIoo t (hsubγ ht))).2.1
    rw [Function.comp_apply, φ.right_inv htarget']
    exact (hab hp.1.2 (hIoo t (hsubγ ht))).2.2
  have heq := (hγ.mono hsubγ).eqOn_of_contDiffOn_extChartAt ho
    ((hvu.mono hou).of_le (by simp)) (hδ.mono hsubδ) hγsrc hγu h0' (hγ0.trans hδ0.symm)
  exact hmax.trans (heq hp').symm

/-- The finite-order case of `contMDiffAt_maximalIntegralCurve`, where a field which is `C^(n+1)` at
`x₀` is `C^(n+1)` on a neighbourhood of `x₀`. -/
private theorem contMDiffAt_maximalIntegralCurve_nat (n : ℕ)
    (hvx : CMDiffAt (n + 1) (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) x₀) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I (n + 1) (fun p : M × ℝ ↦ maximalIntegralCurve v p.1 p.2)
      (x₀, 0) := by
  -- Read in the extended chart at `x₀`, the field is `C^(n+1)` on a neighbourhood of `x₀`, since
  -- the order is finite.
  have hvc : ContDiffAt ℝ (n + 1) (fun z ↦ tangentCoordChange I ((extChartAt I x₀).symm z) x₀
      ((extChartAt I x₀).symm z) (v ((extChartAt I x₀).symm z))) (extChartAt I x₀ x₀) :=
    ((contMDiffAt_iff.mp hvx).2.contDiffAt (range_mem_nhds_isInteriorPoint
      BoundarylessManifold.isInteriorPoint)).snd
  obtain ⟨u, hu, hvu⟩ := hvc.contDiffOn (m := ((n + 1 : ℕ) : ℕ∞ω)) (by norm_cast) (by simp)
  obtain ⟨Φ, hΦ, hΦ0, h⟩ :=
    exists_contDiffAt_maximalIntegralCurve_eq_extChartAt_symm (n := n) hu (by exact_mod_cast hvu)
  have hchart : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) (n + 1)
      (fun p : M × ℝ ↦ (extChartAt I x₀ p.1, p.2)) (x₀, 0) :=
    ((contMDiffAt_extChartAt (I := I) (n := n + 1) (x := x₀)).comp (x₀, (0 : ℝ))
      (contMDiffAt_fst (I := I) (J := 𝓘(ℝ, ℝ)))).prodMk_space
      (contMDiffAt_snd (I := I) (J := 𝓘(ℝ, ℝ)))
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I (n + 1) (extChartAt I x₀).symm (extChartAt I x₀ x₀) :=
    (contMDiffWithinAt_extChartAt_symm_range_self x₀).contMDiffAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
  have hΦ' : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) (n + 1) (fun p : E × ℝ ↦ Φ p.1 p.2)
      (extChartAt I x₀ x₀, 0) :=
    hΦ.contMDiffAt
  have hflow := hsymm.comp_of_eq (hΦ'.comp (x₀, (0 : ℝ)) hchart) (by simp [hΦ0])
  exact hflow.congr_of_eventuallyEq h

/-- **The maximal flow is `C^(n+1)` near time zero.** Suppose `v` is `C^(n+1)` at `x₀`, for `n`
finite or infinite, on a separated boundaryless manifold modelled on a finite-dimensional space.
Then the maximal flow
`(x, t) ↦ maximalIntegralCurve v x t` is `C^(n+1)` jointly in the initial point and the time at
`(x₀, 0)`. -/
theorem contMDiffAt_maximalIntegralCurve {n : ℕ∞}
    (hvx : CMDiffAt (n + 1) (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) x₀) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I (n + 1) (fun p : M × ℝ ↦ maximalIntegralCurve v p.1 p.2)
      (x₀, 0) := by
  induction n using ENat.recTopCoe with
  | top =>
    have htop : ((⊤ : ℕ∞) : ℕ∞ω) + 1 = ∞ := by
      norm_cast
    rw [htop] at hvx ⊢
    exact contMDiffAt_infty.2 fun m ↦
      (contMDiffAt_maximalIntegralCurve_nat m (hvx.of_le (by exact_mod_cast le_top))).of_le
        (by exact_mod_cast Nat.le_succ m)
  | coe m => exact contMDiffAt_maximalIntegralCurve_nat m (by exact_mod_cast hvx)

end TauCeti

end
