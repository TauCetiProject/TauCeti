/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Critical
public import TauCeti.Analysis.Sobolev.Local.LogLogExample
public import TauCeti.Analysis.Calculus.BumpFunction.UnitDisc
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Local

/-!
# `\dot H^1(ℝ²)` is not contained in `L^∞`: the function `log log (4 / ‖z‖)`

In dimension `n`, the homogeneous Sobolev space `\dot H^{n/2} = \dot B^{n/2}_{2,2}` is the critical
space for the embedding into `L^∞`, and the embedding fails there: only the smaller space
`\dot B^{n/2}_{2,1}`, whose norm sums the weighted block norms `2^{jn/2} ‖Pⱼ f‖₂` instead of
square-summing them, lies in `L^∞`
(`TemperedDistribution.MemHomogeneousBesov.memLp_top`). This file
proves the failure in the plane `ℂ = ℝ²`, where `n / 2 = 1`, with the classical example

`f(z) = χ(z) log log (4 / ‖z‖)`

(`TauCeti.logLogCutoff`), the function `TauCeti.logLogInterior` cut off by the smooth bump function
`χ = TauCeti.unitDiscCutoff`, equal to `1` on the closed unit disc and supported in the closed disc
of radius `2`:

* `f ∈ L²(ℂ)`, and its tempered distribution lies in the Sobolev space `H¹ = H^{1,2}`
  (`TauCeti.memSobolev_logLogCutoffLp`), hence in `\dot H^1 = \dot B^1_{2,2}`
  (`TauCeti.memHomogeneousBesov_logLogCutoffLp`);
* `f` is not essentially bounded (`TauCeti.not_memLp_top_logLogCutoff`), since it tends to `∞` at
  the origin;
* so `f ∉ \dot B^1_{2,1}` (`TauCeti.not_memHomogeneousBesov_logLogCutoffLp`): its weighted block
  norms `2^j ‖Pⱼ f‖₂` are square summable but not summable.

This is why the Strichartz estimates at the spatial exponent `r = ∞`, such as the bound on
`‖cos(tD) f‖_{L^∞_t L^∞_x}` for the wave equation, are stated with `\dot B^{n/2}_{2,1}` data, and
the Sobolev versions only for finite `r`.

## The argument

On the disc of radius `3`, `log log (4 / ‖z‖)` and its classical derivative are square integrable,
and the classical derivative is its weak derivative across the origin
(`TauCeti.hasWeakFDerivOn_logLogInterior`), so it is the value of an element of `W^{1,2}` of that
disc. Multiplying by `χ`, supported inside the disc, and extending by zero gives an element of
`W^{1,2}(ℂ)` (`Distribution.exists_memSobolev_mul_of_wkp`), which is `H¹` by Calderón's theorem.
At `p = q = 2` the Sobolev and Besov scales agree
(`TemperedDistribution.memBesov_two_two_iff_memSobolev`), and inhomogeneous Besov spaces of
positive order lie in the homogeneous ones (`TemperedDistribution.MemBesov.memHomogeneousBesov`).

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.3 (the example `log log (1 / |x|)` of an
  unbounded `W^{1,n}` function).
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 (the Besov endpoint `r = ∞` of the wave
  Strichartz estimates).
-/

public section

noncomputable section

open MeasureTheory Filter Metric Set TopologicalSpace
open scoped ENNReal Topology ContDiff SchwartzMap

namespace TauCeti

/-- The function `f(z) = χ(z) log log (4 / ‖z‖)`, with `χ = TauCeti.unitDiscCutoff`: a compactly
supported function in `H¹(ℝ²)` that is unbounded near the origin. -/
def logLogCutoff (z : ℂ) : ℝ := unitDiscCutoff z * logLogInterior z

/-- The defining formula of `TauCeti.logLogCutoff`. -/
theorem logLogCutoff_def (z : ℂ) : logLogCutoff z = unitDiscCutoff z * logLogInterior z :=
  (rfl)

/-- The function `χ(z) log log (4 / ‖z‖)` is supported in the closed disc of radius `2`. -/
theorem tsupport_logLogCutoff_subset : tsupport logLogCutoff ⊆ closedBall 0 2 := by
  have h := tsupport_mul_subset_left (f := (unitDiscCutoff : ℂ → ℝ)) (g := logLogInterior)
  rwa [unitDiscCutoff.tsupport_eq, unitDiscCutoff_rOut] at h

/-- The function `χ(z) log log (4 / ‖z‖)` is compactly supported. -/
theorem hasCompactSupport_logLogCutoff : HasCompactSupport logLogCutoff :=
  (isCompact_closedBall 0 2).of_isClosed_subset (isClosed_tsupport _) tsupport_logLogCutoff_subset

/-- The function `χ(z) log log (4 / ‖z‖)` is measurable. -/
@[fun_prop]
theorem measurable_logLogCutoff : Measurable logLogCutoff :=
  unitDiscCutoff.continuous.measurable.mul measurable_logLogInterior

/-- On the closed unit disc, `TauCeti.logLogCutoff` is `log log (4 / ‖z‖)`. -/
theorem logLogCutoff_eq_of_mem_closedBall {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    logLogCutoff z = logLogInterior z := by
  rw [logLogCutoff_def, unitDiscCutoff_of_norm_le_one (mem_closedBall_zero_iff.1 hz), one_mul]

/-- The function `χ(z) log log (4 / ‖z‖)` is the value of an `L²` function whose tempered
distribution lies in the Sobolev space `H¹ = H^{1,2}`. -/
private theorem exists_memSobolev_logLogCutoff :
    ∃ g : Lp ℂ 2 (volume : Measure ℂ), (g =ᵐ[volume] fun z ↦ (logLogCutoff z : ℂ)) ∧
      TemperedDistribution.MemSobolev 1 2 (g : 𝓢'(ℂ, ℂ)) := by
  let U : Opens ℂ := ⟨ball 0 3, isOpen_ball⟩
  -- On the disc of radius `3`, `log log (4 / ‖z‖)` is the value of an element of `W^{1,2}`.
  obtain ⟨w, hw, -⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn (Omega := U)
    (memLp_logLogInterior (R := 3) (by norm_num))
    (memLp_fderiv_logLogInterior (R := 3) (by norm_num))
    (hasWeakFDerivOn_logLogInterior.mono fun z hz ↦ ball_subset_ball (by norm_num) hz)
  have hsupp : tsupport unitDiscCutoff ⊆ U := by
    rw [unitDiscCutoff.tsupport_eq]
    rw [unitDiscCutoff_rOut]
    exact closedBall_subset_ball (by norm_num)
  have h1 : Wkp.value (p := 2) 1 w = W1p.value w := Wkp.value_one w
  have hw1 : (Wkp.value (p := 2) 1 w : ℂ → ℝ) =ᵐ[volume.restrict U] logLogInterior := by
    rw [h1]
    exact hw
  obtain ⟨g, hg, hgS⟩ := Distribution.exists_memSobolev_mul_of_wkp ENNReal.one_lt_two
    ENNReal.ofNat_ne_top hw1 unitDiscCutoff.contDiff unitDiscCutoff.hasCompactSupport hsupp
  refine ⟨g, hg.trans (ae_of_all _ fun z ↦ ?_), by exact_mod_cast hgS⟩
  simp [logLogCutoff_def]

/-- The function `χ(z) log log (4 / ‖z‖)` is square integrable. -/
theorem memLp_logLogCutoff : MemLp (fun z ↦ (logLogCutoff z : ℂ)) 2 volume :=
  let ⟨g, hg, _⟩ := exists_memSobolev_logLogCutoff
  (Lp.memLp g).ae_eq hg

/-- The function `χ(z) log log (4 / ‖z‖)` as an element of `L²(ℂ)`. -/
def logLogCutoffLp : Lp ℂ 2 (volume : Measure ℂ) := memLp_logLogCutoff.toLp _

/-- The element `TauCeti.logLogCutoffLp` of `L²(ℂ)` is represented by `χ(z) log log (4 / ‖z‖)`. -/
theorem coeFn_logLogCutoffLp : logLogCutoffLp =ᵐ[volume] fun z ↦ (logLogCutoff z : ℂ) :=
  memLp_logLogCutoff.coeFn_toLp

/-- **`χ(z) log log (4 / ‖z‖)` lies in `H¹(ℝ²)`**: its tempered distribution lies in the Sobolev
space `H^{1,2}`. -/
theorem memSobolev_logLogCutoffLp :
    TemperedDistribution.MemSobolev 1 2 (logLogCutoffLp : 𝓢'(ℂ, ℂ)) := by
  obtain ⟨g, hg, hgS⟩ := exists_memSobolev_logLogCutoff
  rwa [show logLogCutoffLp = g from Lp.ext (coeFn_logLogCutoffLp.trans hg.symm)]

/-- **`χ(z) log log (4 / ‖z‖)` lies in `\dot H^1(ℝ²) = \dot B^1_{2,2}`**, the homogeneous Sobolev
space of the critical order `n / 2 = 1`, for the Littlewood–Paley blocks of any bump function
`φ`. -/
theorem memHomogeneousBesov_logLogCutoffLp (φ : ContDiffBump (0 : ℂ)) :
    (logLogCutoffLp : 𝓢'(ℂ, ℂ)).MemHomogeneousBesov φ 1 2 2 :=
  ((TemperedDistribution.memBesov_two_two_iff_memSobolev φ).2
    memSobolev_logLogCutoffLp).memHomogeneousBesov one_pos two_ne_zero

/-- **`χ(z) log log (4 / ‖z‖)` is not essentially bounded**: it tends to `∞` at the origin. -/
theorem not_memLp_top_logLogCutoff : ¬ MemLp logLogCutoff ∞ volume := by
  intro h
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ᵐ z ∂(volume : Measure ℂ), logLogCutoff z ≤ M := by
    refine ⟨(eLpNorm logLogCutoff ∞ volume).toReal, ?_⟩
    filter_upwards [ae_le_eLpNormEssSup (f := logLogCutoff) (μ := volume)] with z hz
    rw [Real.eNorm_eq_ofReal_abs] at hz
    exact (le_abs_self _).trans
      ((ENNReal.ofReal_le_iff_le_toReal h.ne).1 (hz.trans eLpNormEssSup_le_eLpNorm_top))
  -- Near the origin `log log (4 / ‖z‖)` exceeds `M`, and so does `χ(z) log log (4 / ‖z‖)`.
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_nhdsWithin_iff.1 (tendsto_logLogInterior.eventually_gt_atTop M))
  have hpos : 0 < (volume : Measure ℂ) (ball 0 (min δ 1) \ {0}) := by
    rw [measure_sdiff_null (measure_singleton 0)]
    exact measure_ball_pos _ _ (lt_min hδ one_pos)
  refine hpos.ne' (measure_mono_null (fun z hz ↦ ?_) (ae_iff.1 hM))
  have hz1 : z ∈ ball (0 : ℂ) δ := ball_subset_ball (min_le_left _ _) hz.1
  have hzc : z ∈ closedBall (0 : ℂ) 1 :=
    ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hz.1)
  simpa [logLogCutoff_eq_of_mem_closedBall hzc] using hball z hz1 hz.2

/-- **`χ(z) log log (4 / ‖z‖)` does not lie in `\dot B^1_{2,1}(ℝ²)`.** Its weighted block norms
`2^j ‖Pⱼ f‖₂` are square summable (`TauCeti.memHomogeneousBesov_logLogCutoffLp`) but not summable,
for the Littlewood–Paley blocks of any bump function `φ`: an `L²` function of `\dot B^1_{2,1}(ℝ²)`
is essentially bounded. -/
theorem not_memHomogeneousBesov_logLogCutoffLp (φ : ContDiffBump (0 : ℂ)) :
    ¬ (logLogCutoffLp : 𝓢'(ℂ, ℂ)).MemHomogeneousBesov φ 1 2 1 := by
  intro h
  have hn : (Module.finrank ℝ ℂ : ℝ) / 2 = 1 := by norm_num [Complex.finrank_real_complex]
  have hf := (hn ▸ h).memLp_top
  refine not_memLp_top_logLogCutoff (memLp_iff.2 ?_)
  rw [eLpNorm_congr_eNorm_ae (g := fun z ↦ (logLogCutoff z : ℂ)) (by fun_prop) (by fun_prop)
    (ae_of_all _ fun z ↦ by rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real])]
  exact memLp_iff.1 (hf.ae_eq coeFn_logLogCutoffLp)

end TauCeti
