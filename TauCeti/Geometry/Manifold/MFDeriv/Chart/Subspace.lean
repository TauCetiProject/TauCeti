/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# A subspace of the model space through a point of a manifold

Every subspace `K` of the model space of a finite-dimensional boundaryless manifold maps smoothly
into the manifold through any given point `x₀`, with differential at `0` the inclusion of `K`
(`TauCeti.exists_contMDiff_mfderiv_apply_eq_coe`). The map reads `k` in the extended chart at `x₀`
as the translate `e x₀ + k`, truncated by a bump function so that it stays in the chart target.
Taking `K` to be a hyperplane gives a hypersurface through `x₀` with a prescribed tangent space.

## Main results

* `TauCeti.exists_contMDiff_mfderiv_apply_eq_coe`: every subspace `K` of the model space maps
  smoothly into the manifold through a given point, with differential at `0` the inclusion of `K`.
-/

public section

open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [FiniteDimensional ℝ E] {n : ℕ∞} [IsManifold I n M]

/-- **A subspace through a point.** For every subspace `K` of the model space of a
finite-dimensional boundaryless `C^n` manifold, `1 ≤ n`, and every point `x₀`, there is a `C^n`
map `ι : K → M` with `ι 0 = x₀` whose differential at `0` is the inclusion of `K`. -/
theorem exists_contMDiff_mfderiv_apply_eq_coe (hn : 1 ≤ n) (K : Submodule ℝ E) (x₀ : M) :
    ∃ ι : K → M, ContMDiff 𝓘(ℝ, K) I n ι ∧ ι 0 = x₀ ∧
      ∀ w : K, mfderiv 𝓘(ℝ, K) I ι 0 w = (w : E) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := n) (by exact_mod_cast hn)
  set e := extChartAt I x₀
  -- A ball around `e x₀` in the chart target, and a bump function on `K` supported in it.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (extChartAt_target_mem_nhds (I := I) x₀)
  let χ : ContDiffBump (0 : K) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set c : K → E := fun k ↦ χ k • (k : E)
  have hc : ContDiff ℝ n c := χ.contDiff.smul K.subtypeL.contDiff
  have hcr (k : K) : e x₀ + c k ∈ e.target := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    by_cases hk : χ k = 0
    · simp [c, hk, hr]
    have hkr : k ∈ Metric.ball (0 : K) r := χ.support_eq ▸ hk
    calc ‖c k‖ ≤ ‖k‖ := by
          simpa [c, norm_smul, abs_of_nonneg χ.nonneg] using
            mul_le_of_le_one_left (norm_nonneg k) χ.le_one
      _ < r := by simpa using hkr
  set ι : K → M := fun k ↦ e.symm (e x₀ + c k)
  have hι : ContMDiff 𝓘(ℝ, K) I n ι :=
    (contMDiffOn_extChartAt_symm x₀).comp_contMDiff
      (contMDiff_iff_contDiff.2 (contDiff_const.add hc)) hcr
  have hι₀ : ι 0 = x₀ := by simp [ι, c, e]
  refine ⟨ι, hι, hι₀, fun w ↦ ?_⟩
  -- Near `0`, the chart reads `ι` as the translate `k ↦ e x₀ + k`, so `dι₀` is the inclusion.
  have heq : e ∘ ι =ᶠ[𝓝 0] fun k ↦ e x₀ + (k : E) := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : K) (half_pos hr)] with k hk
    have hχ : χ k = 1 := χ.one_of_mem_closedBall hk
    simpa [ι, c, hχ] using e.right_inv (by simpa [c, hχ] using hcr k)
  have hlin : mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) (e ∘ ι) 0 w = (w : E) := by
    have hd : HasFDerivAt (fun k : K ↦ e x₀ + (k : E)) K.subtypeL 0 :=
      K.subtypeL.hasFDerivAt.const_add (e x₀)
    rw [heq.mfderiv_eq, mfderiv_eq_fderiv, hd.fderiv]
    -- The tangent identifications of the model spaces are the identity.
    rfl
  have he : MDifferentiableAt I 𝓘(ℝ, E) e x₀ :=
    mdifferentiableAt_extChartAt (mem_chart_source H x₀)
  have h := (mfderiv_comp_apply_of_eq 0 he (hι.mdifferentiableAt (by
    exact_mod_cast (zero_lt_one.trans_le hn).ne')) hι₀ w).symm.trans hlin
  rwa [mfderiv_extChartAt_eq_id] at h

end TauCeti
