/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Completion
import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Elements of every Sobolev space of a compact manifold are smooth

Let `M` be a manifold modelled on `ℝⁿ`, and let `ψᵢ` be finitely many cutoffs in charts `eᵢ` whose
readings `ψᵢ ∘ eᵢ` on `M`, extended by `0`, add up to `1`. The Sobolev space `H^s(M)` of this chart
partition is the closure of the chart readings `(ψᵢ · (u ∘ eᵢ⁻¹))ᵢ` of the smooth functions `u` in
the Hilbert sum `⨁ᵢ H^s(ℝⁿ)` (`TauCeti.chartSobolevSpace`), and for `s ≤ t` the space `H^t(M)` is
included in `H^s(M)` (`TauCeti.chartSobolevInclusion`). Such chart partitions exist on every
compact manifold (`IsCompact.exists_sum_cutoffPullback_eq_one`).

This file proves that `C^∞(M) = ⋂ₜ H^t(M)`: an element of `H^s(M)` is the chart reading of a
smooth function exactly when it lies in `H^t(M)` for every `t ≥ s`
(`TauCeti.mem_range_toChartSobolevSpace_iff`). This is the form in which elliptic regularity
shows that Sobolev solutions of elliptic equations with smooth data are smooth: a parametrix
places such a solution in every `H^t(M)`.

## The argument

Let `x ∈ H^s(M)` lie in `H^t(M)` for every `t ≥ s`. By the Sobolev embedding
(`BesselPotentialSpace.toZeroAtInfty`), the `i`-th component of `x`, an element of `H^t(ℝⁿ)` for
every large `t`, has a continuous representative `gᵢ`, which is `C^k` for every `k`
(`BesselPotentialSpace.contDiff_toZeroAtInfty`), hence smooth. Point evaluations of continuous
representatives are continuous on `H^t(ℝⁿ)` for `t > n / 2`, so pointwise identities satisfied by
the chart readings of all smooth functions pass to their closure `H^t(M)`. Two such identities are
used:

* `gᵢ` vanishes outside the support of `ψᵢ`, as every reading `ψᵢ · (v ∘ eᵢ⁻¹)` does;
* `gⱼ = ψⱼ · (u ∘ eⱼ⁻¹)` for the function `u = ∑ᵢ gᵢ ∘ eᵢ` on `M` (each term extended by `0`
  outside the chart source), since a smooth `v` satisfies `v = ∑ᵢ (ψᵢ ∘ eᵢ) v`.

The first makes `u` smooth, and the second says that `x` is the chart reading of `u`.

## Main results

* `TauCeti.mem_range_toChartSobolevSpace_iff`: an element of `H^s(M)` is the chart reading of a
  smooth function if and only if it lies in `H^t(M)` for every `t ≥ s`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds and the Sobolev embedding theorem).
-/

public section

noncomputable section

open Set Module TauCeti OpenPartialHomeomorph BesselPotentialSpace
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {ι : Type*} [Fintype ι] {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)}

omit [T2Space M] in
/-- A closed condition on `⨁ᵢ H^t(ℝⁿ)` satisfied by the chart readings of all smooth functions
holds on `H^t(M)`. -/
private theorem mem_of_forall_chartReading_mem {t : ℝ}
    {S : Set (PiLp 2 fun _ : ι ↦ H^{t}(CoordinateSpace n))} (hS : IsClosed S)
    (h : ∀ u, chartReading he ψ t u ∈ S) (z : chartSobolevSpace he ψ t) :
    (z : PiLp 2 fun _ : ι ↦ H^{t}(CoordinateSpace n)) ∈ S :=
  closure_minimal (range_subset_iff.2 h) hS ((mem_chartSobolevSpace_iff he ψ).1 z.property)

variable {t : ℝ} (ht : finrank ℝ (CoordinateSpace n) < 2 * t)
include ht

omit [T2Space M] [Fintype ι] in
/-- For `t > n / 2`, the value at a point of the continuous representative of a component is a
continuous function on `⨁ᵢ H^t(ℝⁿ)`. -/
private theorem continuous_toZeroAtInfty_apply (i : ι) (w : CoordinateSpace n) :
    Continuous fun z : PiLp 2 (fun _ : ι ↦ H^{t}(CoordinateSpace n)) ↦
      toZeroAtInfty ht (z i) w :=
  ((ZeroAtInftyContinuousMap.evalCLM ℂ w ∘L toZeroAtInfty ht).continuous.comp
    (PiLp.continuous_apply 2 _ i)).congr fun _ ↦ by simp

omit [T2Space M] in
/-- For `t > n / 2`, the continuous representative of the `i`-th component of an element of
`H^t(M)` vanishes outside the support of `ψᵢ`, as every reading `ψᵢ · (v ∘ eᵢ⁻¹)` does. -/
private theorem toZeroAtInfty_apply_eq_zero_of_notMem_tsupport (z : chartSobolevSpace he ψ t)
    (i : ι) {w : CoordinateSpace n} (hw : w ∉ tsupport (ψ i)) :
    toZeroAtInfty ht ((z : PiLp 2 fun _ : ι ↦ H^{t}(CoordinateSpace n)) i) w = 0 :=
  mem_of_forall_chartReading_mem (S := {z | toZeroAtInfty ht (z i) w = 0})
    (isClosed_eq (continuous_toZeroAtInfty_apply ht i w) continuous_const)
    (fun v ↦ by simp [image_eq_zero_of_notMem_tsupport hw]) z

/-- For `t > n / 2`, the continuous representatives `gᵢ` of the components of an element of
`H^t(M)` satisfy `gⱼ = ψⱼ · (u ∘ eⱼ⁻¹)` for `u = ∑ᵢ gᵢ ∘ eᵢ`, each term extended by `0` outside
the chart source, as the readings of every smooth function do. -/
private theorem toZeroAtInfty_apply_eq_smul_sum_indicator
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (z : chartSobolevSpace he ψ t)
    (j : ι) (w : CoordinateSpace n) :
    toZeroAtInfty ht ((z : PiLp 2 fun _ : ι ↦ H^{t}(CoordinateSpace n)) j) w = ψ j w •
      ∑ i, (e i).source.indicator (fun q ↦ toZeroAtInfty ht
        ((z : PiLp 2 fun _ : ι ↦ H^{t}(CoordinateSpace n)) i) (e i q)) ((e j).symm w) := by
  refine mem_of_forall_chartReading_mem (S := {z | toZeroAtInfty ht (z j) w = ψ j w •
    ∑ i, (e i).source.indicator (fun q ↦ toZeroAtInfty ht (z i) (e i q)) ((e j).symm w)})
    (isClosed_eq (continuous_toZeroAtInfty_apply ht j w)
      ((continuous_finsetSum _ fun i _ ↦ ?_).fun_const_smul _)) (fun v ↦ ?_) z
  · by_cases hp : (e j).symm w ∈ (e i).source
    · simp only [indicator_of_mem hp]
      exact continuous_toZeroAtInfty_apply ht i _
    · simp only [indicator_of_notMem hp]
      exact continuous_const
  · simp only [mem_ofPred_eq, chartReading_apply, toZeroAtInfty_toBesselPotentialSpaceCLM,
      SchwartzMap.toZeroAtInfty_apply]
    rw [sum_indicator_cutoffPushforwardSchwartz_apply he ψ hψ, cutoffPushforwardSchwartz_apply]

/-- For `t > n / 2`, an element of `H^t(M)` whose components have smooth continuous
representatives `gᵢ` is the element of the smooth function `∑ᵢ gᵢ ∘ eᵢ`, each term extended by `0`
outside the chart source. -/
private theorem exists_toChartSobolevSpace_eq_of_contDiff
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (z : chartSobolevSpace he ψ t)
    (hz : ∀ i, ContDiff ℝ ∞
      (toZeroAtInfty ht ((z : PiLp 2 fun _ : ι ↦ H^{t}(CoordinateSpace n)) i))) :
    ∃ u, toChartSobolevSpace he ψ t u = z := by
  let g (i : ι) := toZeroAtInfty ht ((z : PiLp 2 fun _ : ι ↦ H^{t}(CoordinateSpace n)) i)
  have hgs (i : ι) : tsupport (g i) ⊆ tsupport (ψ i) :=
    closure_minimal (fun w hw ↦ by_contra fun h ↦
      hw (toZeroAtInfty_apply_eq_zero_of_notMem_tsupport ht z i h)) (isClosed_tsupport _)
  -- Each `gᵢ ∘ eᵢ`, extended by `0`, is smooth on `M`, since `gᵢ` is supported in `supp ψᵢ`.
  let U (p : M) : ℂ := ∑ i, (e i).source.indicator (fun q ↦ g i (e i q)) p
  have hU : ContMDiff 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, ℂ) ∞ U := ContMDiff.sum fun i _ ↦
    (e i).contMDiff_indicator_comp_extend (he i) (hz i)
      ((ψ i).hasCompactSupport.mono' ((subset_tsupport _).trans (hgs i)))
      (by rw [extend_target', modelWithCornersSelf_coe, image_id]
          exact (hgs i).trans (ψ i).tsupport_subset)
  let u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ := ⟨U, hU⟩
  refine ⟨u, ?_⟩
  ext1
  ext1 j
  rw [coe_toChartSobolevSpace, chartReading_apply]
  -- Both components have the continuous representative `gⱼ = ψⱼ · (u ∘ eⱼ⁻¹)`.
  refine (toZeroAtInfty_injective (hs := ht) ?_).symm
  ext w
  rw [toZeroAtInfty_toBesselPotentialSpaceCLM, SchwartzMap.toZeroAtInfty_apply,
    cutoffPushforwardSchwartz_apply]
  exact toZeroAtInfty_apply_eq_smul_sum_indicator ht hψ z j w

omit ht

variable (he ψ) in
/-- **`C^∞(M) = ⋂ₜ H^t(M)`.** For a chart partition `ψᵢ` of `M`, whose readings on `M` add up to
`1`, an element of the Sobolev space `H^s(M)` is the chart reading of a smooth function on `M` if
and only if it lies in `H^t(M)` for every `t ≥ s`. -/
theorem mem_range_toChartSobolevSpace_iff
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) {s : ℝ}
    (x : chartSobolevSpace he ψ s) :
    x ∈ range (toChartSobolevSpace he ψ s) ↔
      ∀ t (h : s ≤ t), x ∈ range (chartSobolevInclusion he ψ h) := by
  refine ⟨fun ⟨u, hu⟩ t h ↦ ⟨toChartSobolevSpace he ψ t u, by
    rw [chartSobolevInclusion_toChartSobolevSpace, hu]⟩, fun hx ↦ ?_⟩
  choose y hy using hx
  -- All the lifts of `x` have the components of `x`, as tempered distributions.
  have hyx (t : ℝ) (h : s ≤ t) (i : ι) :
      ((y t h : PiLp 2 fun _ : ι ↦ H^{t}(CoordinateSpace n)) i).toDistr =
        ((x : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) i).toDistr := by
    rw [← hy t h, coe_chartSobolevInclusion_apply, toDistr_inclusion]
  -- Orders `T k ≥ s` at which the Sobolev embedding lands in `C^k`.
  let T (k : ℕ) : ℝ := max s (n + k + 1)
  have hsT (k : ℕ) : s ≤ T k := le_max_left _ _
  have hTk (k : ℕ) : finrank ℝ (CoordinateSpace n) + 2 * (k : ℝ) < 2 * T k := by
    rw [finrank_euclideanSpace_fin]
    have := le_max_right s ((n : ℝ) + k + 1)
    linarith
  have hT (k : ℕ) : (finrank ℝ (CoordinateSpace n) : ℝ) < 2 * T k := by
    have := hTk k
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  -- The lift of `x` to `H^{T 0}(M)` has smooth continuous representatives, hence is smooth.
  obtain ⟨u, hu⟩ := exists_toChartSobolevSpace_eq_of_contDiff (hT 0) hψ (y (T 0) (hsT 0))
    fun i ↦ contDiff_infty.2 fun k ↦ by
      rw [toZeroAtInfty_congr (hr := hT k)
        (v := (y (T k) (hsT k) : PiLp 2 fun _ : ι ↦ H^{T k}(CoordinateSpace n)) i)
        (by rw [hyx, hyx])]
      exact contDiff_toZeroAtInfty (hTk k) _
  exact ⟨u, by rw [← hy (T 0) (hsT 0), ← hu, chartSobolevInclusion_toChartSobolevSpace]⟩

end TauCeti
