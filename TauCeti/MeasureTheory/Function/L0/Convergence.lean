/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.MeasureTheory.Function.L0.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The bounded integral metric and convergence in measure

The metric on `TauCeti.L0 μ` induces exactly native convergence in measure. The two
quantitative estimates retain the total mass of an arbitrary finite measure; no probability
normalization is imposed.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace TauCeti.L0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The natural inclusion of a real `Lp` space into real random variables. It preserves
the underlying almost-everywhere class and does not require finiteness of the measure. -/
def ofLp {p : ℝ≥0∞} (f : Lp ℝ p μ) : L0 μ := ⟨f⟩

/-- The `Lp` inclusion preserves the native almost-everywhere equivalence class. -/
@[simp]
theorem toAEEqFun_ofLp {p : ℝ≥0∞} (f : Lp ℝ p μ) :
    (ofLp f).toAEEqFun = (f : Ω →ₘ[μ] ℝ) := (rfl)

/-- The `Lp` inclusion uses the same representative as the native `Lp` carrier. -/
theorem coeFn_ofLp {p : ℝ≥0∞} (f : Lp ℝ p μ) : (ofLp f : Ω → ℝ) = f := (rfl)

variable [IsFiniteMeasure μ]

/-- Markov's inequality for the bounded integral metric, including the threshold itself. -/
theorem measureReal_ge_le_dist (f g : L0 μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε ≤ |f x - g x|} ≤ ((1 + ε) / ε) * dist f g := by
  have hp : 0 < ε / (1 + ε) := by positivity
  have hs : {x | ε ≤ |f x - g x|} ⊆
      {x | ε / (1 + ε) ≤ |f x - g x| / (1 + |f x - g x|)} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [abs_nonneg (f x - g x)]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun x ↦ by positivity) (integrable_distIntegrand f g) (ε / (1 + ε))
  calc
    μ.real {x | ε ≤ |f x - g x|} ≤
        μ.real {x | ε / (1 + ε) ≤ |f x - g x| / (1 + |f x - g x|)} :=
      measureReal_mono hs
    _ ≤ dist f g / (ε / (1 + ε)) := (le_div_iff₀ hp).2 (by
      simpa only [dist_def, mul_comm] using hm)
    _ = ((1 + ε) / ε) * dist f g := by field_simp

/-- Split the integral into small differences and the exceptional event. The factor
`μ.real univ` is essential for finite measures of arbitrary total mass. -/
theorem dist_le_add_measureReal_lt (f g : L0 μ) {ε : ℝ} (hε : 0 ≤ ε) :
    dist f g ≤ ε * μ.real univ + μ.real {x | ε < |f x - g x|} := by
  classical
  let s : Set Ω := {x | ε < |f x - g x|}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (f.measurable.sub g.measurable).norm
  have hi : Integrable (s.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const _).indicator hs
  have hb : ∀ x, |f x - g x| / (1 + |f x - g x|) ≤
      ε + s.indicator (fun _ ↦ (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      have : |f x - g x| / (1 + |f x - g x|) ≤ 1 :=
        (div_le_one (by positivity)).2 (by linarith [abs_nonneg (f x - g x)])
      linarith
    · rw [indicator_of_notMem hx, add_zero]
      have hx' : |f x - g x| ≤ ε := le_of_not_gt hx
      exact (div_le_self (abs_nonneg _) (by linarith [abs_nonneg (f x - g x)])).trans hx'
  calc
    dist f g ≤ ∫ x, ε + s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ :=
      integral_mono (integrable_distIntegrand f g) ((integrable_const ε).add hi) hb
    _ = ε * μ.real univ + μ.real {x | ε < |f x - g x|} := by
      rw [integral_add (integrable_const ε) hi, integral_const, integral_indicator hs,
        setIntegral_const]
      simp [s, smul_eq_mul, mul_comm]

/-- Convergence for the bounded integral metric is exactly convergence in measure of
the chosen representatives, for an arbitrary index filter. -/
theorem tendsto_iff_tendstoInMeasure {ι : Type*} {l : Filter ι} {f : ι → L0 μ} {g : L0 μ} :
    Tendsto f l (𝓝 g) ↔ TendstoInMeasure μ (fun i ↦ (f i : Ω → ℝ)) l g := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  constructor
  · intro h ε hε
    have hd := tendsto_iff_dist_tendsto_zero.mp h
    apply squeeze_zero (fun i ↦ measureReal_nonneg)
      (fun i ↦ measureReal_ge_le_dist (f i) g hε)
    simpa using hd.const_mul ((1 + ε) / ε)
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    let ε : ℝ := δ / (2 * (μ.real univ + 1))
    have hε : 0 < ε := by dsimp [ε]; positivity
    have he : ε * μ.real univ < δ / 2 := by
      dsimp [ε]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have hevent := (h ε hε).eventually (gt_mem_nhds (half_pos hδ))
    filter_upwards [hevent] with i hi
    have hb := dist_le_add_measureReal_lt (f i) g hε.le
    have hsub : μ.real {x | ε < |f i x - g x|} ≤ μ.real {x | ε ≤ |f i x - g x|} := by
      exact measureReal_mono (by
        intro x hx
        simp only [mem_ofPred_eq] at hx ⊢
        exact hx.le)
    simp only [Real.dist_eq] at hi
    linarith

/-- Convergence in the native `Lp` norm implies convergence in the bounded integral metric. -/
theorem continuous_ofLp {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Continuous (ofLp : Lp ℝ p μ → L0 μ) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply tendsto_iff_tendstoInMeasure.mpr
  simpa only [coeFn_ofLp, id_eq] using tendstoInMeasure_of_tendsto_Lp
    (f := id) (g := f) (l := 𝓝 f) tendsto_id

end TauCeti.L0
