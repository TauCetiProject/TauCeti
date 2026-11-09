/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Analysis.ODE.Yorke
import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.SmoothDependence
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Short periodic orbits of vector fields are constant

Let `v` be a `C¹` vector field on a compact boundaryless manifold `M` modelled on a
finite-dimensional space. There is a time `T₀ > 0` such that every periodic integral curve of `v`
with a period `T ∈ (0, T₀]` is constant
(`TauCeti.exists_pos_forall_isMIntegralCurve_eq_const_of_periodic`). Rescaling time, for every
`ε ∈ (0, T₀]` the `1`-periodic solutions of the field `ε v` are constant
(`TauCeti.exists_pos_forall_mem_periodicSolutions_smul_eq_const`): they are the curves
`t ↦ γ (ε t)` for the `ε`-periodic integral curves `γ` of `v`. Applied to the Hamiltonian vector
field of `εH`, this says that a small multiple of an autonomous Hamiltonian on a closed manifold
has only constant `1`-periodic orbits, the first step in comparing Hamiltonian Floer homology of a
`C²`-small Morse function with its Morse homology.

The proof is local. Near a point `p`, read the field in the extended chart at `p`: it is `C¹`
there, hence `K`-Lipschitz near the image of `p`. The flow of `v` is continuous at `(p, 0)`, so
there are a neighbourhood `W` of `p` and a time `δ > 0` such that every trajectory starting in `W`
stays in this chart region up to time `δ`. A periodic trajectory of period `T ≤ δ` takes all its
values before time `T`, so it stays in the chart region for all time, where it is a periodic
solution of a Lipschitz equation. Yorke's theorem
(`TauCeti.exists_pos_forall_periodic_eq_const_of_lipschitzOnWith`) makes it constant once `K T` is
smaller than a constant depending only on the model space
(`TauCeti.exists_mem_nhds_forall_isMIntegralCurve_eq_const_of_periodic`). Finitely many such
neighbourhoods cover the compact manifold, and `T₀` is the least of their times.

## Main results

* `TauCeti.exists_mem_nhds_forall_isMIntegralCurve_eq_const_of_periodic`: near every point,
  periodic trajectories of small period are constant.
* `TauCeti.exists_pos_forall_isMIntegralCurve_eq_const_of_periodic`: on a compact manifold,
  periodic trajectories of period at most some `T₀ > 0` are constant.
* `TauCeti.exists_pos_forall_mem_periodicSolutions_smul_eq_const`: on a compact manifold, for
  every small `ε > 0` the `1`-periodic solutions of `ε v` are constant.

## References

* J. A. Yorke, *Periods of periodic solutions and the Lipschitz constant*, Proc. Amer. Math. Soc.
  22 (1969), 509–512.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the Hamiltonian `εH` of a Morse function `H`).
-/

public section

noncomputable section

open Function Set Filter
open scoped Manifold NNReal Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M] {v : (x : M) → TangentSpace I x}

/-- **Periodic trajectories of small period near a point are constant.** For a `C¹` vector field
`v` and a point `p`, there are a neighbourhood `W` of `p` and a time `δ > 0` such that every
`T`-periodic integral curve of `v` starting in `W`, with `0 < T ≤ δ`, is constant. -/
theorem exists_mem_nhds_forall_isMIntegralCurve_eq_const_of_periodic
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (p : M) :
    ∃ W ∈ 𝓝 p, ∃ δ > (0 : ℝ), ∀ γ : ℝ → M, IsMIntegralCurve γ v → γ 0 ∈ W →
      ∀ T, 0 < T → T ≤ δ → Periodic γ T → γ = fun _ ↦ γ 0 := by
  set φ := extChartAt I p
  -- The field read in the extended chart at `p` is `C¹`, hence Lipschitz, near `φ p`.
  set g : E → E := fun z ↦ tangentCoordChange I (φ.symm z) p (φ.symm z) (v (φ.symm z))
  have hgc : ContDiffAt ℝ 1 g (φ p) :=
    ((contMDiffAt_iff.mp (hv p)).2.contDiffAt (range_mem_nhds_isInteriorPoint
      BoundarylessManifold.isInteriorPoint)).snd
  obtain ⟨K, z, hz, hlip⟩ := hgc.exists_lipschitzOnWith
  set N := φ.source ∩ φ ⁻¹' z
  have hN : N ∈ 𝓝 p :=
    inter_mem (extChartAt_source_mem_nhds p) ((continuousAt_extChartAt p).preimage_mem_nhds hz)
  -- The flow is continuous at `(p, 0)`, so trajectories from near `p` stay in `N` for a while.
  have hflow : ContinuousAt (fun q : M × ℝ ↦ maximalIntegralCurve v q.1 q.2) (p, 0) :=
    (contMDiffAt_maximalIntegralCurve (n := 0) (by simpa using hv p)).continuousAt
  have hp : maximalIntegralCurve v p 0 = p := by
    rw [← flowOf_apply]
    exact flowOf_zero hv p
  obtain ⟨W, hW, U, hU, hWU⟩ :=
    mem_nhds_prod_iff.1 (hflow.preimage_mem_nhds (by simpa only [hp] using hN))
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨c, hc, hYorke⟩ := exists_pos_forall_periodic_eq_const_of_lipschitzOnWith (E := E)
  refine ⟨W, hW, min (ε / 2) (c / (K + 1)), by positivity, fun γ hγ hγ0 T hT hTδ hper ↦ ?_⟩
  -- The trajectory stays in `N` up to time `T`, hence, being `T`-periodic, for all time.
  have hγN (t : ℝ) : γ t ∈ N := by
    obtain ⟨s, hs, hst⟩ : γ t ∈ γ '' Icc 0 (0 + T) := hper.image_Icc hT 0 ▸ mem_range_self t
    rw [zero_add] at hs
    have hsU : s ∈ U := hεU (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      linarith [hs.2, min_le_left (ε / 2) (c / (K + 1))])
    have h := hWU (mk_mem_prod hγ0 hsU)
    rwa [mem_preimage, ← flowOf_apply, flowOf_eq_of_isMIntegralCurve hv hγ, hst] at h
  -- Read in the chart, `γ` is a `T`-periodic solution of `x' = g(x)`, with `g` `K`-Lipschitz along
  -- it, so it is constant by Yorke's theorem; and the chart is injective on `N`.
  have hx (t : ℝ) : HasDerivAt (fun t ↦ φ (γ t)) (g (φ (γ t))) t := by
    have hgt : g (φ (γ t)) = tangentCoordChange I (γ t) p (γ t) (v (γ t)) := by
      simp only [g]
      rw [φ.left_inv (hγN t).1]
    rw [hgt]
    exact (hγ t).hasDerivAt_extChartAt_comp (hγN t).1
  have hKT : K * T < c := by
    have hT' : (K : ℝ) * T ≤ K * (c / (K + 1)) := by
      gcongr
      exact hTδ.trans (min_le_right _ _)
    refine hT'.trans_lt ?_
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hconst := hYorke g _ K T (fun t ↦ by simp only [hper t]) hT hx
    (hlip.mono (range_subset_iff.2 fun t ↦ (hγN t).2)) hKT
  funext t
  exact φ.injOn (hγN t).1 (hγN 0).1 (congrFun hconst t)

variable [CompactSpace M]

/-- **Periodic trajectories of small period are constant.** For a `C¹` vector field `v` on a
compact boundaryless manifold modelled on a finite-dimensional space, there is `T₀ > 0` such that
every `T`-periodic integral curve of `v` with `0 < T ≤ T₀` is constant. -/
theorem exists_pos_forall_isMIntegralCurve_eq_const_of_periodic
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    ∃ T₀ > (0 : ℝ), ∀ γ : ℝ → M, IsMIntegralCurve γ v →
      ∀ T, 0 < T → T ≤ T₀ → Periodic γ T → γ = fun _ ↦ γ 0 := by
  classical
  choose W hW δ hδ hγ using exists_mem_nhds_forall_isMIntegralCurve_eq_const_of_periodic hv
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover W fun p _ ↦ hW p
  -- The least of the finitely many times `δ p`, `p ∈ s`.
  obtain ⟨T₀, hT₀, hle⟩ : ∃ T₀ > (0 : ℝ), ∀ p ∈ s, T₀ ≤ δ p := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | insert q s _ ih =>
      obtain ⟨T₀, hT₀, hle⟩ := ih
      refine ⟨min T₀ (δ q), lt_min hT₀ (hδ q), fun p hp ↦ ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle p hp)
  refine ⟨T₀, hT₀, fun γ hγv T hT hTT₀ hper ↦ ?_⟩
  obtain ⟨p, hps, hp⟩ := mem_iUnion₂.1 (hs (mem_univ (γ 0)))
  exact hγ p γ hγv hp T hT (hTT₀.trans (hle p hps)) hper

/-- **Small multiples of a vector field have only constant `1`-periodic solutions.** For a `C¹`
vector field `v` on a compact boundaryless manifold modelled on a finite-dimensional space, there
is `ε₀ > 0` such that for `0 < ε ≤ ε₀` every `1`-periodic solution of the field `ε v` is constant.
-/
theorem exists_pos_forall_mem_periodicSolutions_smul_eq_const
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ γ ∈ periodicSolutions (fun _ ↦ ε • v) 1, γ = fun _ ↦ γ 0 := by
  obtain ⟨T₀, hT₀, h⟩ := exists_pos_forall_isMIntegralCurve_eq_const_of_periodic hv
  refine ⟨T₀, hT₀, fun ε hε hεT₀ γ hγ ↦ ?_⟩
  obtain ⟨hγv, hγper⟩ := mem_periodicSolutions.1 hγ
  -- `t ↦ γ (t / ε)` is an `ε`-periodic integral curve of `v`.
  have hγv : IsMIntegralCurve γ (ε • v) := hγv
  have hδ : IsMIntegralCurve (γ ∘ (· * ε⁻¹)) v := by
    simpa [smul_smul, inv_mul_cancel₀ hε.ne'] using hγv.comp_mul ε⁻¹
  have hper : Periodic (γ ∘ (· * ε⁻¹)) ε := fun t ↦ by
    simp [add_mul, mul_inv_cancel₀ hε.ne', hγper]
  have hconst := h _ hδ ε hε hεT₀ hper
  funext t
  simpa [hε.ne'] using congrFun hconst (t * ε)

end TauCeti
