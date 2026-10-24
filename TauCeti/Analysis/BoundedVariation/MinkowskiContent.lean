/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# Perimeter and outer Minkowski content

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E`. For
every set `s` and every open set `Ω`, the perimeter of the closure of `s` in `Ω` is at most the
lower outer Minkowski content of `s` in `Ω`:

`P(closure s; Ω) ≤ liminf_{ε → 0⁺} μ((s_ε \ closure s) ∩ Ω) / ε`,

where `s_ε = Metric.thickening ε s` is the open `ε`-neighbourhood of `s`
(`TauCeti.perimeter_closure_le_liminf_measure_thickening_sdiff_div`). No measurability, finite
measure or regularity hypothesis on `s` is needed.

For a compact set `K`, the closed neighbourhoods `K + t • closedBall 0 1` are the outer parallel
sets of `K`. If their volume has a right derivative `D` at `t = 0`, then `P(K) ≤ D`
(`IsCompact.perimeter_le_of_hasDerivWithinAt`). For convex bodies of positive volume this is
one half of the identification of the perimeter with the first variation of parallel volume.

The proof approximates the indicator of the closure of `s` by Lipschitz functions. Mathlib's
`ε`-thickened indicator `thickenedIndicator` of `s` is `ε⁻¹`-Lipschitz, equals one on the
closure of `s` and vanishes off `s_ε`. It attains its maximum on the closure of `s` and its
minimum off `s_ε`, so its derivative vanishes there, and its total variation in `Ω` is at most
`ε⁻¹ μ((s_ε \ closure s) ∩ Ω)`. The thickened indicators converge to the indicator of the closure
of `s` locally in `L¹`, since the shells `s_ε \ closure s` decrease to the empty set, and lower
semicontinuity of the total variation concludes.

## Main results

* `TauCeti.perimeter_closure_le_liminf_measure_thickening_sdiff_div`: the perimeter of the closure
  is at most the lower outer Minkowski content.
* `IsCompact.perimeter_le_of_hasDerivWithinAt`: the perimeter of a compact set is at most the
  right derivative at zero of the volume of its outer parallel sets.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 12.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Section 2.13, for Minkowski content.
-/

public section

noncomputable section

open MeasureTheory Metric Filter Set TopologicalSpace
open scoped ENNReal NNReal Pointwise Topology

namespace TauCeti

section Cutoff

variable {E : Type*} [NormedAddCommGroup E]

/-- The real-valued `ε`-thickened indicator of `s`: one on the closure of `s`, zero off the
`ε`-thickening of `s`, and affine in the distance to `s` in between. -/
private def thickenedCutoff (s : Set E) (ε : ℝ) (x : E) : ℝ :=
  (thickenedIndicatorAux ε s x).toReal

private theorem thickenedCutoff_eq_coe {s : Set E} {ε : ℝ} (hε : 0 < ε) (x : E) :
    thickenedCutoff s ε x = thickenedIndicator hε s x := by
  rw [thickenedIndicator_apply, ENNReal.coe_toNNReal_eq_toReal, thickenedCutoff]

private theorem thickenedCutoff_nonneg (s : Set E) (ε : ℝ) (x : E) :
    0 ≤ thickenedCutoff s ε x :=
  ENNReal.toReal_nonneg

private theorem thickenedCutoff_le_one (s : Set E) (ε : ℝ) (x : E) :
    thickenedCutoff s ε x ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    simpa using thickenedIndicatorAux_le_one ε s x)

private theorem thickenedCutoff_of_mem_closure {s : Set E} (ε : ℝ) {x : E}
    (hx : x ∈ closure s) : thickenedCutoff s ε x = 1 := by
  simp [thickenedCutoff, thickenedIndicatorAux_one_of_mem_closure ε s hx]

private theorem thickenedCutoff_of_notMem_thickening {s : Set E} {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : x ∉ thickening ε s) : thickenedCutoff s ε x = 0 := by
  simp [thickenedCutoff, thickenedIndicatorAux_zero hε s hx]

private theorem lipschitzWith_thickenedCutoff (s : Set E) {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ε.toNNReal⁻¹ (thickenedCutoff s ε) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [thickenedCutoff_eq_coe hε, thickenedCutoff_eq_coe hε, Real.dist_eq, ← NNReal.dist_eq]
  exact (lipschitzWith_thickenedIndicator hε s).dist_le_mul x y

/-- The derivative of the thickened cutoff vanishes off the shell `s_ε \ closure s`, where the
cutoff attains its maximum or its minimum, and is at most `ε⁻¹` everywhere. -/
private theorem enorm_fderiv_thickenedCutoff_le [NormedSpace ℝ E] (s : Set E) {ε : ℝ}
    (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ (thickenedCutoff s ε) x‖ₑ ≤
      (thickening ε s \ closure s).indicator (fun _ => ENNReal.ofReal ε⁻¹) x := by
  by_cases hx : x ∈ thickening ε s \ closure s
  · rw [indicator_of_mem hx, ← ofReal_norm, ← Real.coe_toNNReal _ (inv_nonneg.2 hε.le),
      Real.toNNReal_inv]
    exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ
      (lipschitzWith_thickenedCutoff s hε))
  rw [indicator_of_notMem hx, nonpos_iff_eq_zero]
  suffices fderiv ℝ (thickenedCutoff s ε) x = 0 by simp [this, enorm_eq_nnnorm]
  rw [Set.mem_sdiff, not_and_or, not_not] at hx
  rcases hx with hx | hx
  · refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun y => ?_)
    rw [thickenedCutoff_of_notMem_thickening hε hx]
    exact thickenedCutoff_nonneg s ε y
  · refine IsLocalMax.fderiv_eq_zero (Filter.Eventually.of_forall fun y => ?_)
    rw [thickenedCutoff_of_mem_closure ε hx]
    exact thickenedCutoff_le_one s ε y

/-- The thickened cutoff differs from the indicator of the closure of `s` only on the shell
`s_ε \ closure s`, and by at most one there. -/
private theorem enorm_thickenedCutoff_sub_indicator_le (s : Set E) {ε : ℝ} (hε : 0 < ε)
    (x : E) :
    ‖thickenedCutoff s ε x - (closure s).indicator 1 x‖ₑ ≤
      (thickening ε s \ closure s).indicator 1 x := by
  by_cases hc : x ∈ closure s
  · simp [thickenedCutoff_of_mem_closure ε hc, hc]
  by_cases ht : x ∈ thickening ε s
  · rw [indicator_of_mem (mem_sdiff_of_mem ht hc), indicator_of_notMem hc, sub_zero,
      Pi.one_apply, ← ofReal_norm, Real.norm_of_nonneg (thickenedCutoff_nonneg s ε x)]
    exact ENNReal.ofReal_le_one.2 (thickenedCutoff_le_one s ε x)
  · simp [thickenedCutoff_of_notMem_thickening hε ht, hc]

end Cutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The total variation in `Ω` of the thickened cutoff is at most its slope `ε⁻¹` times the
measure of the part of the shell `s_ε \ closure s` in `Ω`. -/
private theorem totalVariationOn_thickenedCutoff_le (Ω : Opens E) (s : Set E) {ε : ℝ}
    (hε : 0 < ε) :
    totalVariationOn μ Ω (thickenedCutoff s ε) ≤
      μ ((thickening ε s \ closure s) ∩ Ω) / ENNReal.ofReal ε := by
  have hmeas : MeasurableSet (thickening ε s \ closure s) :=
    isOpen_thickening.measurableSet.diff isClosed_closure.measurableSet
  rw [(lipschitzWith_thickenedCutoff s hε).locallyLipschitz.locallyLipschitzOn
      |>.totalVariationOn_eq_setLIntegral_enorm_fderiv]
  calc ∫⁻ x in Ω, ‖fderiv ℝ (thickenedCutoff s ε) x‖ₑ ∂μ
      ≤ ∫⁻ x in Ω, (thickening ε s \ closure s).indicator (fun _ => ENNReal.ofReal ε⁻¹) x ∂μ :=
        lintegral_mono (enorm_fderiv_thickenedCutoff_le s hε)
    _ = μ ((thickening ε s \ closure s) ∩ Ω) / ENNReal.ofReal ε := by
        rw [lintegral_indicator_const hmeas, Measure.restrict_apply hmeas,
          ENNReal.ofReal_inv_of_pos hε, ENNReal.div_eq_inv_mul]

/-- **The perimeter is at most the lower outer Minkowski content.** For every set `s` and every
open set `Ω`, the perimeter of the closure of `s` in `Ω` is at most
`liminf_{ε → 0⁺} μ((s_ε \ closure s) ∩ Ω) / ε`, where `s_ε` is the open `ε`-thickening of `s`.
No measurability, finite-measure or regularity hypothesis on `s` is needed. -/
theorem perimeter_closure_le_liminf_measure_thickening_sdiff_div (Ω : Opens E) (s : Set E) :
    perimeter μ Ω (closure s) ≤
      liminf (fun ε => μ ((thickening ε s \ closure s) ∩ Ω) / ENNReal.ofReal ε) (𝓝[>] 0) := by
  have hmeas (ε : ℝ) : MeasurableSet (thickening ε s \ closure s) :=
    isOpen_thickening.measurableSet.diff isClosed_closure.measurableSet
  have hu : ∀ᶠ ε in 𝓝[>] (0 : ℝ), LocallyIntegrableOn (thickenedCutoff s ε) Ω μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (lipschitzWith_thickenedCutoff s hε).continuous.locallyIntegrable.locallyIntegrableOn _
  have hu₀ : LocallyIntegrableOn ((closure s).indicator (1 : E → ℝ)) Ω μ :=
    ((locallyIntegrable_const 1).indicator isClosed_closure.measurableSet).locallyIntegrableOn _
  -- On a compact set the shells `s_ε \ closure s` have measure tending to zero, since they
  -- decrease to the empty set.
  have hL1 (K : Set E) (hK : IsCompact K) (_ : K ⊆ Ω) : Tendsto
      (fun ε => ∫⁻ x in K, ‖thickenedCutoff s ε x - (closure s).indicator 1 x‖ₑ ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
    have hshell : Tendsto (fun ε => μ ((thickening ε s \ closure s) ∩ K)) (𝓝[>] 0) (𝓝 0) := by
      have h := tendsto_measure_biInter_gt (μ := μ) (a := (0 : ℝ))
        (s := fun ε => (thickening ε s \ closure s) ∩ K)
        (fun ε _ => ((hmeas ε).inter hK.measurableSet).nullMeasurableSet)
        (fun i j _ hij => inter_subset_inter_left _ (sdiff_subset_sdiff_left
          (thickening_mono hij s)))
        ⟨1, one_pos, measure_ne_top_of_subset inter_subset_right hK.measure_lt_top.ne⟩
      have hempty : ⋂ ε > (0 : ℝ), (thickening ε s \ closure s) ∩ K = ∅ := by
        refine eq_empty_of_forall_notMem fun x hx => ?_
        simp only [mem_iInter, mem_inter_iff, Set.mem_sdiff] at hx
        refine (hx 1 one_pos).1.2 ?_
        rw [closure_eq_iInter_thickening, mem_iInter₂]
        exact fun δ hδ => (hx δ hδ).1.1
      rwa [hempty, measure_empty] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hshell
      (.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    calc ∫⁻ x in K, ‖thickenedCutoff s ε x - (closure s).indicator 1 x‖ₑ ∂μ
        ≤ ∫⁻ x in K, (thickening ε s \ closure s).indicator 1 x ∂μ :=
          lintegral_mono (enorm_thickenedCutoff_sub_indicator_le s hε)
      _ = μ ((thickening ε s \ closure s) ∩ K) := by
          rw [lintegral_indicator_one (hmeas ε), Measure.restrict_apply (hmeas ε)]
  calc perimeter μ Ω (closure s)
      ≤ liminf (fun ε => totalVariationOn μ Ω (thickenedCutoff s ε)) (𝓝[>] 0) := by
        rw [perimeter_def]
        exact totalVariationOn_le_liminf hu hu₀ hL1
    _ ≤ liminf (fun ε => μ ((thickening ε s \ closure s) ∩ Ω) / ENNReal.ofReal ε) (𝓝[>] 0) := by
        refine liminf_le_liminf ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact totalVariationOn_thickenedCutoff_le Ω s hε

end TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The perimeter of a compact set is at most the first variation of its parallel volume.**
If the volume of the outer parallel sets `K + t • closedBall 0 1` of a compact set `K` has right
derivative `D` at `t = 0`, then `P(K) ≤ D`. -/
theorem IsCompact.perimeter_le_of_hasDerivWithinAt {K : Set E} (hK : IsCompact K) {D : ℝ}
    (hD : HasDerivWithinAt (fun t : ℝ => μ.real (K + t • closedBall (0 : E) 1)) D (Ioi 0) 0) :
    TauCeti.perimeter μ ⊤ K ≤ ENNReal.ofReal D := by
  -- For `t > 0` the outer parallel set is the closed `t`-thickening of `K`.
  have hpar {t : ℝ} (ht : 0 ≤ t) : K + t • closedBall (0 : E) 1 = cthickening t K := by
    rw [smul_unitClosedBall_of_nonneg ht, hK.add_closedBall_zero ht]
  -- For `t > 0` the difference quotient of the parallel volume is the shell measure over `t`.
  have hshell {t : ℝ} (ht : 0 < t) :
      ENNReal.ofReal (slope (fun t : ℝ => μ.real (K + t • closedBall (0 : E) 1)) 0 t) =
        μ (cthickening t K \ K) / ENNReal.ofReal t := by
    have hfin : μ (cthickening t K) ≠ ∞ := (hK.cthickening (r := t)).measure_lt_top.ne
    rw [slope_def_field, sub_zero, hpar ht.le, hpar le_rfl, cthickening_zero,
      hK.isClosed.closure_eq, ENNReal.ofReal_div_of_pos ht,
      ← measureReal_sdiff (self_subset_cthickening K) hK.measurableSet hfin,
      ofReal_measureReal (measure_ne_top_of_subset sdiff_subset hfin)]
  have hslope : Tendsto (fun t : ℝ => μ (cthickening t K \ K) / ENNReal.ofReal t) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal D)) := by
    refine (ENNReal.tendsto_ofReal ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl 0)).1
      hD)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hshell ht
  calc TauCeti.perimeter μ ⊤ K
      = TauCeti.perimeter μ ⊤ (closure K) := by rw [hK.isClosed.closure_eq]
    _ ≤ liminf (fun t => μ ((thickening t K \ closure K) ∩ (⊤ : Opens E)) / ENNReal.ofReal t)
        (𝓝[>] 0) := TauCeti.perimeter_closure_le_liminf_measure_thickening_sdiff_div ⊤ K
    _ ≤ liminf (fun t : ℝ => μ (cthickening t K \ K) / ENNReal.ofReal t) (𝓝[>] 0) := by
        refine liminf_le_liminf (.of_forall fun t => ?_)
        rw [hK.isClosed.closure_eq, Opens.coe_top, inter_univ]
        gcongr
        exact thickening_subset_cthickening t K
    _ = ENNReal.ofReal D := hslope.liminf_eq
