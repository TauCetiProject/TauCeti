/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import TauCeti.Analysis.BoundedVariation.Calibration
import TauCeti.Analysis.Calculus.ContDiff.LevelSet
import TauCeti.Analysis.Calculus.FDeriv.LevelSet
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Topology.Order.Sublevel

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

The first bound is proved by approximating the indicator of the closure of `s` by Lipschitz
functions. Mathlib's `ε`-thickened indicator `thickenedIndicator` of `s` is `ε⁻¹`-Lipschitz,
equals one on the closure of `s` and vanishes off `s_ε`. It attains its maximum on the closure of
`s` and its minimum off `s_ε`, so its derivative vanishes there, and its total variation in `Ω` is
at most `ε⁻¹ μ((s_ε \ closure s) ∩ Ω)`. The thickened indicators converge to the indicator of the
closure of `s` locally in `L¹`, since the shells `s_ε \ closure s` decrease to the empty set, and
lower semicontinuity of the total variation concludes.

For sets with smooth boundary the outer Minkowski content is the perimeter. If `u` is smooth and
compactly supported and `t > 0` is a regular value of `u`, the closed superlevel set
`s = {u ≥ t}` satisfies `|s_ε \ s| / ε → P(s)` as `ε → 0⁺`
(`ContDiff.tendsto_volume_thickening_sdiff_div`). The lower bound is the general one above. For
the upper bound, write `s = {w ≥ 0}` for a smooth defining function `w` with `‖Dw‖ = 1` on the
boundary (`ContDiff.exists_contDiff_setOf_pos_eq_setOf_lt`). Since `‖Dw‖ ≤ 1 + δ` near the
boundary, `s_ε \ s` lies in the shell `{-(1 + δ) ε < w < 0}` for small `ε`, and the calibration
estimate for `-w` bounds the volume of that shell by `(1 + δ) ε P(s) / (1 - 2 δ)`
(`ContDiff.setIntegral_norm_fderiv_le`).

## Main results

* `TauCeti.perimeter_closure_le_liminf_measure_thickening_sdiff_div`: the perimeter of the closure
  is at most the lower outer Minkowski content.
* `IsCompact.tendsto_measure_cthickening_sdiff_div`: if the parallel volume of a compact set
  has right derivative `D` at zero, its outer shells have volume `D t + o(t)`.
* `IsCompact.perimeter_le_of_hasDerivWithinAt`: the perimeter of a compact set is at most the
  right derivative at zero of the volume of its outer parallel sets.
* `ContDiff.tendsto_volume_thickening_sdiff_div`: the outer Minkowski content of a regular closed
  superlevel set of a compactly supported smooth function is its perimeter.

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

/-- If the volume of the outer parallel sets `K + t • closedBall 0 1` of a compact set `K` has
right derivative `D` at `t = 0`, then the shells `cthickening t K \ K` have volume `D t + o(t)`
as `t → 0⁺`. -/
theorem IsCompact.tendsto_measure_cthickening_sdiff_div {K : Set E} (hK : IsCompact K) {D : ℝ}
    (hD : HasDerivWithinAt (fun t : ℝ => μ.real (K + t • closedBall (0 : E) 1)) D (Ioi 0) 0) :
    Tendsto (fun t : ℝ => μ (cthickening t K \ K) / ENNReal.ofReal t) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal D)) := by
  -- For `t > 0` the difference quotient of the parallel volume is the shell measure over `t`.
  have hshell {t : ℝ} (ht : 0 < t) :
      ENNReal.ofReal (slope (fun t : ℝ => μ.real (K + t • closedBall (0 : E) 1)) 0 t) =
        μ (cthickening t K \ K) / ENNReal.ofReal t := by
    have hfin : μ (cthickening t K) ≠ ∞ := (hK.cthickening (r := t)).measure_lt_top.ne
    rw [slope_def_field, sub_zero, hK.add_smul_closedBall_eq_cthickening ht.le,
      hK.add_smul_closedBall_eq_cthickening le_rfl, cthickening_zero,
      hK.isClosed.closure_eq, ENNReal.ofReal_div_of_pos ht,
      ← measureReal_sdiff (self_subset_cthickening K) hK.measurableSet hfin,
      ofReal_measureReal (measure_ne_top_of_subset sdiff_subset hfin)]
  refine (ENNReal.tendsto_ofReal ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl 0)).1
    hD)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hshell ht

/-- **The perimeter of a compact set is at most the first variation of its parallel volume.**
If the volume of the outer parallel sets `K + t • closedBall 0 1` of a compact set `K` has right
derivative `D` at `t = 0`, then `P(K) ≤ D`. -/
theorem IsCompact.perimeter_le_of_hasDerivWithinAt {K : Set E} (hK : IsCompact K) {D : ℝ}
    (hD : HasDerivWithinAt (fun t : ℝ => μ.real (K + t • closedBall (0 : E) 1)) D (Ioi 0) 0) :
    TauCeti.perimeter μ ⊤ K ≤ ENNReal.ofReal D :=
  calc TauCeti.perimeter μ ⊤ K
      = TauCeti.perimeter μ ⊤ (closure K) := by rw [hK.isClosed.closure_eq]
    _ ≤ liminf (fun t => μ ((thickening t K \ closure K) ∩ (⊤ : Opens E)) / ENNReal.ofReal t)
        (𝓝[>] 0) := TauCeti.perimeter_closure_le_liminf_measure_thickening_sdiff_div ⊤ K
    _ ≤ liminf (fun t : ℝ => μ (cthickening t K \ K) / ENNReal.ofReal t) (𝓝[>] 0) := by
        refine liminf_le_liminf (.of_forall fun t => ?_)
        rw [hK.isClosed.closure_eq, Opens.coe_top, inter_univ]
        gcongr
        exact thickening_subset_cthickening t K
    _ = ENNReal.ofReal D := (hK.tendsto_measure_cthickening_sdiff_div hD).liminf_eq

/-! ### Regular superlevel sets of smooth functions -/

section Smooth

open TauCeti TestFunction
open scoped ContDiff Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The calibrated outer shell estimate.** Let `w` be `C¹` and let `ψ` be an admissible test
vector field with `Dw (ψ) = -‖Dw‖` on the outer shell `S = {-η < w < 0}`, on which
`‖Dw‖ ≥ 1 - ε`. If `|div ψ| ≤ C` and `η C ≤ ε < 1 / 2`, then
`|S| ≤ η / (1 - 2 ε) P({w ≥ 0})`. -/
private theorem volume_preimage_Ioo_neg_le {w : E → ℝ} (hw : ContDiff ℝ 1 w) {η ε C : ℝ}
    (hη : 0 < η) (hε2 : ε < 1 / 2) (ψ : 𝓓(⊤, E)) (hψ1 : ∀ x, ‖ψ x‖ ≤ 1)
    (hC : ∀ x, ‖divergenceCLM ψ x‖ ≤ C) (hηC : η * C ≤ ε)
    (hψ : ∀ x, w x ∈ Ioo (-η) 0 → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖)
    (hgrad : ∀ x, w x ∈ Ioo (-η) 0 → 1 - ε ≤ ‖fderiv ℝ w x‖)
    (hfin : volume (w ⁻¹' Ioo (-η) 0) ≠ ⊤)
    (hint : IntegrableOn (fun x => ‖fderiv ℝ w x‖) (w ⁻¹' Ioo (-η) 0)) :
    volume (w ⁻¹' Ioo (-η) 0) ≤
      ENNReal.ofReal (η / (1 - 2 * ε)) * perimeter volume ⊤ {x | 0 ≤ w x} := by
  set S := w ⁻¹' Ioo (-η) 0
  have hSm : MeasurableSet S := hw.continuous.measurable measurableSet_Ioo
  -- Calibrate `-w` on the shell `S = {0 < -w < η}` with the test vector field `-ψ`.
  have hfdn (x : E) : ‖fderiv ℝ (fun y => -w y) x‖ = ‖fderiv ℝ w x‖ := by
    rw [fderiv_fun_neg, norm_neg]
  have hpre : (fun y => -w y) ⁻¹' Ioo 0 η = S := by
    ext x
    simp only [mem_preimage, mem_Ioo, S]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hcal := hw.neg.setIntegral_norm_fderiv_le hη (-ψ) fun x hx => by
    have hx : x ∈ S := hpre ▸ hx
    simp [fderiv_fun_neg, hψ x hx]
  rw [hpre] at hcal
  simp_rw [hfdn] at hcal
  set I := ∫ x, divergenceCLM (-ψ) x * {x | 0 < -w x}.indicator 1 x
  -- The divergence term is at most the perimeter of `{w < 0}`, which is that of `{w ≥ 0}`.
  have hI : ENNReal.ofReal I ≤ perimeter volume ⊤ {x | 0 ≤ w x} := by
    have hc : {x | 0 < -w x} = {x | 0 ≤ w x}ᶜ := by
      ext x
      simp
    rw [← perimeter_compl, ← hc, perimeter_def]
    exact ofReal_integral_le_totalVariationOn (-ψ) fun x => by simpa using hψ1 x
  have hJ : ∫ x in S, |divergenceCLM (-ψ) x| ≤ C * volume.real S := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const hfin.lt_top fun x _ => ?_
    simpa using hC x
  have hlow : (1 - ε) * volume.real S ≤ ∫ x in S, ‖fderiv ℝ w x‖ :=
    setIntegral_ge_of_const_le_real hSm hfin hgrad hint
  -- Altogether `(1 - ε) |S| ≤ η (I + C |S|) ≤ η I + ε |S|`.
  have hV : volume.real S ≤ η / (1 - 2 * ε) * I := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith [measureReal_nonneg (μ := volume) (s := S)]
  calc volume S = ENNReal.ofReal (volume.real S) := (ofReal_measureReal hfin).symm
    _ ≤ ENNReal.ofReal (η / (1 - 2 * ε) * I) := ENNReal.ofReal_le_ofReal hV
    _ = ENNReal.ofReal (η / (1 - 2 * ε)) * ENNReal.ofReal I :=
        ENNReal.ofReal_mul (div_nonneg hη.le (by linarith))
    _ ≤ ENNReal.ofReal (η / (1 - 2 * ε)) * perimeter volume ⊤ {x | 0 ≤ w x} := by
        gcongr

/-- **The outer shells of a smooth set are controlled by its perimeter.** Let `w` be smooth with
`{w ≥ -δ}` compact and `‖Dw‖ = 1` on its zero level, and let `s = {w ≥ 0}`. For every
`0 < ε < 1 / 2`, eventually as `r → 0⁺`,
`|s_r \ s| ≤ (1 + ε) / (1 - 2 ε) r P(s)`, where `s_r` is the open `r`-neighbourhood of `s`. -/
private theorem eventually_volume_thickening_sdiff_le {w : E → ℝ} (hw : ContDiff ℝ ∞ w) {δ : ℝ}
    (hδ : 0 < δ) (hK : IsCompact {x | -δ ≤ w x}) (hnorm : ∀ x, w x = 0 → ‖fderiv ℝ w x‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∀ᶠ r in 𝓝[>] 0, volume (thickening r {x | 0 ≤ w x} \ {x | 0 ≤ w x}) ≤
      ENNReal.ofReal ((1 + ε) / (1 - 2 * ε) * r) * perimeter volume ⊤ {x | 0 ≤ w x} := by
  set s := {x | 0 ≤ w x}
  have hfd : Continuous fun x => ‖fderiv ℝ w x‖ := (hw.continuous_fderiv (by simp)).norm
  -- A test vector field `ψ` calibrating `w` near its zero level, as `-∇w / ‖∇w‖` does.
  obtain ⟨η₀, hη₀, ψ, hψ1, hψ⟩ := hw.exists_testFunction_fderiv_apply_eq_neg_norm hδ hK
    fun x hx h0 => by simpa [h0] using hnorm x hx
  -- Near the zero level, `‖Dw‖` lies within `ε` of `1`.
  obtain ⟨η₁, hη₁, hη₁δ, hη₁C⟩ := exists_forall_abs_le_notMem hw.continuous hδ hK
    (C := {x | ε ≤ |‖fderiv ℝ w x‖ - 1|})
    (isClosed_le continuous_const (hfd.sub continuous_const).abs) fun x hx h0 => by
      have hx : ε ≤ |‖fderiv ℝ w x‖ - 1| := hx
      rw [hnorm x h0, sub_self, abs_zero] at hx
      linarith
  have hgrad {x : E} (hx : |w x| ≤ η₁) : |‖fderiv ℝ w x‖ - 1| < ε := lt_of_not_ge (hη₁C x hx)
  obtain ⟨C, hC⟩ := (divergenceCLM ψ).continuous.bounded_above_of_compact_support
    (divergenceCLM ψ).hasCompactSupport
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set m := min (min η₀ η₁) (ε / (C + 1))
  have hm : 0 < m := lt_min (lt_min hη₀ hη₁) (by positivity)
  have hmε : 0 < m / (1 + ε) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hmε] with r ⟨hr, hrm⟩
  -- Write `η = (1 + ε) r` for the width of the outer shell `S = {-η < w < 0}`.
  set η := (1 + ε) * r
  have hη : 0 < η := by positivity
  have hηε : η / (1 - 2 * ε) = (1 + ε) / (1 - 2 * ε) * r := by simp only [η]; ring
  have hηm : η ≤ m := by
    have := (lt_div_iff₀' (by linarith : (0 : ℝ) < 1 + ε)).1 hrm
    linarith
  have hη₀' : η ≤ η₀ := hηm.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hη₁' : η ≤ η₁ := hηm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηC : η * C ≤ ε := by
    calc η * C ≤ ε / (C + 1) * C := mul_le_mul_of_nonneg_right (hηm.trans (min_le_right _ _)) hC0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  set S := w ⁻¹' Ioo (-η) 0
  have hband {x : E} (hx : x ∈ S) : |w x| ≤ η := abs_le.2 ⟨hx.1.le, by linarith [hx.2]⟩
  have hSK : S ⊆ {x | -δ ≤ w x} := fun x hx =>
    (neg_le_neg (hη₁'.trans hη₁δ)).trans hx.1.le
  have hsub : thickening r s \ s ⊆ S :=
    (hw.differentiable (by simp)).thickening_sdiff_subset_preimage_Ioo_of_norm_fderiv_le
      (by linarith : (0 : ℝ) < 1 + ε) fun x h1 h2 => by
        have := (abs_lt.1 (hgrad ((abs_le.2 ⟨h1, by linarith⟩).trans hη₁'))).2
        linarith
  calc volume (thickening r s \ s) ≤ volume S := measure_mono hsub
    _ ≤ ENNReal.ofReal (η / (1 - 2 * ε)) * perimeter volume ⊤ s :=
        volume_preimage_Ioo_neg_le (hw.of_le (by simp)) hη hε2 ψ hψ1 hC hηC
          (fun x hx => hψ x ((hband hx).trans hη₀'))
          (fun x hx => by linarith [(abs_lt.1 (hgrad ((hband hx).trans hη₁'))).1])
          (ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono hSK))
          ((hfd.continuousOn.integrableOn_compact hK).mono_set hSK)
    _ = ENNReal.ofReal ((1 + ε) / (1 - 2 * ε) * r) * perimeter volume ⊤ s := by
        rw [hηε]

/-- **Outer Minkowski content of a regular superlevel set.** Let `u` be smooth and compactly
supported, and let `t > 0` be a regular value of `u`. The closed superlevel set
`s = {u ≥ t}` has outer Minkowski content equal to its perimeter:
`|s_r \ s| / r → P(s)` as `r → 0⁺`, where `s_r` is the open `r`-neighbourhood of `s`. -/
theorem ContDiff.tendsto_volume_thickening_sdiff_div {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 < t) (hreg : ∀ x, u x = t → fderiv ℝ u x ≠ 0) :
    Tendsto (fun r => volume (thickening r {x | t ≤ u x} \ {x | t ≤ u x}) / ENNReal.ofReal r)
      (𝓝[>] 0) (𝓝 (perimeter volume ⊤ {x | t ≤ u x})) := by
  obtain ⟨w, hw, hK, hnorm, hset⟩ := hu.exists_contDiff_setOf_pos_eq_setOf_lt huc ht hreg
  -- The closed superlevel set `{u ≥ t}` is `{w ≥ 0}`, the closure of `{u > t} = {w > 0}`.
  have hs : {x | t ≤ u x} = {x | 0 ≤ w x} := by
    rw [← hu.continuous.closure_setOf_lt_eq_of_fderiv_ne_zero hreg, ← hset,
      hw.continuous.closure_setOf_lt_eq_of_fderiv_ne_zero fun x hx h0 => by
        simpa [h0] using hnorm x hx]
  rw [hs]
  set s := {x | 0 ≤ w x}
  have hsc : IsClosed s := isClosed_le continuous_const hw.continuous
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · -- The lower bound holds for every closed set.
    calc perimeter volume ⊤ s = perimeter volume ⊤ (closure s) := by
          rw [hsc.closure_eq]
      _ ≤ liminf (fun r => volume ((thickening r s \ closure s) ∩ (⊤ : Opens E)) /
            ENNReal.ofReal r) (𝓝[>] 0) :=
          perimeter_closure_le_liminf_measure_thickening_sdiff_div ⊤ s
      _ = liminf (fun r => volume (thickening r s \ s) / ENNReal.ofReal r) (𝓝[>] 0) := by
          rw [hsc.closure_eq, Opens.coe_top]
          simp_rw [inter_univ]
  · -- The upper bound with constant `(1 + ε) / (1 - 2 ε)`, for every small `ε > 0`.
    have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) / (1 - 2 * ε)) *
        perimeter volume ⊤ s) (𝓝[>] 0) (𝓝 (perimeter volume ⊤ s)) := by
      have h : Tendsto (fun ε : ℝ => (1 + ε) / (1 - 2 * ε)) (𝓝[>] 0) (𝓝 1) := by
        have : ContinuousAt (fun ε : ℝ => (1 + ε) / (1 - 2 * ε)) 0 := by
          fun_prop (disch := norm_num)
        simpa using this.tendsto.mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h) (Or.inl (by simp))
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (one_half_pos : (0 : ℝ) < 1 / 2)] with ε ⟨hε, hε2⟩
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_volume_thickening_sdiff_le hw (by norm_num) hK hnorm hε hε2]
      with r hr
    refine ENNReal.div_le_of_le_mul (hr.trans_eq ?_)
    rw [ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith)), mul_right_comm]

end Smooth
