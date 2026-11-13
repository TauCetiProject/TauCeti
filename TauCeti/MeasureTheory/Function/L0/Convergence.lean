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
# The bounded integral pseudometric and convergence in measure

The pseudometric on `TauCeti.L0 E μ` induces exactly native convergence in measure. The two
quantitative estimates retain the total mass of an arbitrary finite measure; no probability
normalization is imposed. The inclusion `TauCeti.L0.ofLp` preserves the native almost-everywhere
class without requiring measure finiteness. On finite measure spaces, `TauCeti.L0.continuous_ofLp`
proves its continuity for every `1 ≤ p`, including infinity.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace TauCeti.L0

variable {E Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Lp

variable [NormedAddCommGroup E]

/-- The natural inclusion of an `Lp` space into random variables. It preserves
the underlying almost-everywhere class and does not require finiteness of the measure. -/
def ofLp {p : ℝ≥0∞} (f : Lp E p μ) : L0 E μ := ⟨f⟩

/-- The `Lp` inclusion preserves the native almost-everywhere equivalence class. -/
@[simp]
theorem toAEEqFun_ofLp {p : ℝ≥0∞} (f : Lp E p μ) :
    (ofLp f).toAEEqFun = (f : Ω →ₘ[μ] E) := (rfl)

/-- The `Lp` inclusion uses the same representative as the native `Lp` carrier. -/
theorem coeFn_ofLp {p : ℝ≥0∞} (f : Lp E p μ) : (ofLp f : Ω → E) = f := (rfl)

/-- The native `Lp` inclusion is injective. -/
theorem ofLp_injective {p : ℝ≥0∞} : Function.Injective (ofLp : Lp E p μ → L0 E μ) := by
  intro f g h
  exact Subtype.ext (congrArg toAEEqFun h)

/-- Equality after the `Lp` inclusion is equality in `Lp`. -/
@[simp]
theorem ofLp_inj {p : ℝ≥0∞} {f g : Lp E p μ} : ofLp f = ofLp g ↔ f = g :=
  ofLp_injective.eq_iff

/-- Including a function constructed in `Lp` gives its almost-everywhere class in `L0`. -/
@[simp]
theorem ofLp_toLp {p : ℝ≥0∞} (f : Ω → E) (hf : MemLp f p μ) :
    ofLp (hf.toLp f) = ofFun f hf.aestronglyMeasurable := by
  apply toAEEqFun_injective
  simpa only [toAEEqFun_ofLp, toAEEqFun_ofFun] using hf.toLp_val

end Lp

section FiniteMeasure

variable [PseudoMetricSpace E] [IsFiniteMeasure μ]

/-- Markov's inequality for the bounded integral pseudometric, including the threshold itself. -/
theorem measureReal_ge_le_mul_dist (f g : L0 E μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε ≤ dist (f x) (g x)} ≤ ((1 + ε) / ε) * dist f g := by
  have hp : 0 < ε / (1 + ε) := by positivity
  have hs : {x | ε ≤ dist (f x) (g x)} ⊆
      {x | ε / (1 + ε) ≤ dist (f x) (g x) / (1 + dist (f x) (g x))} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [dist_nonneg (x := f x) (y := g x)]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun x ↦ by positivity) (integrable_dist_div_one_add_dist f g) (ε / (1 + ε))
  calc
    μ.real {x | ε ≤ dist (f x) (g x)} ≤
        μ.real {x | ε / (1 + ε) ≤ dist (f x) (g x) / (1 + dist (f x) (g x))} :=
      measureReal_mono hs
    _ ≤ dist f g / (ε / (1 + ε)) := (le_div_iff₀ hp).2 (by
      simpa only [dist_def, mul_comm] using hm)
    _ = ((1 + ε) / ε) * dist f g := by field_simp

/-- For `0 ≤ ε`, the distance is at most `ε * μ.real univ` plus the real measure of
`{x | ε < dist (f x) (g x)}`. The total-mass factor allows arbitrary finite measures. -/
theorem dist_le_mul_measureReal_univ_add_measureReal_gt (f g : L0 E μ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    dist f g ≤ ε * μ.real univ + μ.real {x | ε < dist (f x) (g x)} := by
  classical
  let s : Set Ω := {x | ε < dist (f x) (g x)}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (f.stronglyMeasurable.dist g.stronglyMeasurable).measurable
  have hi : Integrable (s.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const _).indicator hs
  have hb : ∀ x, dist (f x) (g x) / (1 + dist (f x) (g x)) ≤
      ε + s.indicator (fun _ ↦ (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      have : dist (f x) (g x) / (1 + dist (f x) (g x)) ≤ 1 :=
        (div_le_one (by positivity)).2 (by linarith [dist_nonneg (x := f x) (y := g x)])
      linarith
    · rw [indicator_of_notMem hx, add_zero]
      have hx' : dist (f x) (g x) ≤ ε := le_of_not_gt hx
      exact (div_le_self dist_nonneg (by linarith [dist_nonneg (x := f x) (y := g x)])).trans hx'
  calc
    dist f g ≤ ∫ x, ε + s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ :=
      integral_mono (integrable_dist_div_one_add_dist f g) ((integrable_const ε).add hi) hb
    _ = ε * μ.real univ + μ.real {x | ε < dist (f x) (g x)} := by
      rw [integral_add (integrable_const ε) hi, integral_const, integral_indicator hs,
        setIntegral_const]
      simp [s, smul_eq_mul, mul_comm]

/-- Convergence for the bounded integral pseudometric is exactly convergence in measure of
the chosen representatives, for an arbitrary index filter. -/
theorem tendsto_iff_tendstoInMeasure {ι : Type*} {l : Filter ι} {f : ι → L0 E μ}
    {g : L0 E μ} :
    Tendsto f l (𝓝 g) ↔ TendstoInMeasure μ (fun i ↦ (f i : Ω → E)) l g := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  constructor
  · intro h ε hε
    have hd := tendsto_iff_dist_tendsto_zero.mp h
    apply squeeze_zero (fun i ↦ measureReal_nonneg)
      (fun i ↦ measureReal_ge_le_mul_dist (f i) g hε)
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
    have hb := dist_le_mul_measureReal_univ_add_measureReal_gt (f i) g hε.le
    have hsub : μ.real {x | ε < dist (f i x) (g x)} ≤
        μ.real {x | ε ≤ dist (f i x) (g x)} := by
      exact measureReal_mono (by
        intro x hx
        simp only [mem_ofPred_eq] at hx ⊢
        exact hx.le)
    linarith

/-- Convergence to a constructed random variable is convergence in measure to its supplied
representative. -/
theorem tendsto_nhds_ofFun_iff_tendstoInMeasure {ι : Type*} {l : Filter ι} {f : ι → L0 E μ}
    {g : Ω → E} (hg : AEStronglyMeasurable g μ) :
    Tendsto f l (𝓝 (ofFun g hg)) ↔ TendstoInMeasure μ (fun i ↦ (f i : Ω → E)) l g := by
  rw [tendsto_iff_tendstoInMeasure]
  exact ⟨fun h ↦ h.congr_right (coeFn_ofFun g hg),
    fun h ↦ h.congr_right (coeFn_ofFun g hg).symm⟩

/-- Constructed random variables converge exactly when the supplied functions converge in
measure, for an arbitrary index filter. -/
theorem tendsto_ofFun_iff_tendstoInMeasure {ι : Type*} {l : Filter ι}
    {f : ι → Ω → E} {g : Ω → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hg : AEStronglyMeasurable g μ) :
    Tendsto (fun i ↦ ofFun (f i) (hf i)) l (𝓝 (ofFun g hg)) ↔ TendstoInMeasure μ f l g := by
  rw [tendsto_nhds_ofFun_iff_tendstoInMeasure hg]
  exact ⟨fun h ↦ h.congr_left (fun i ↦ coeFn_ofFun (f i) (hf i)),
    fun h ↦ h.congr_left (fun i ↦ (coeFn_ofFun (f i) (hf i)).symm)⟩

end FiniteMeasure

section Lp

variable [NormedAddCommGroup E] [IsFiniteMeasure μ]

/-- Convergence in the native `Lp` norm implies convergence in the bounded integral pseudometric. -/
@[fun_prop]
theorem continuous_ofLp {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Continuous (ofLp : Lp E p μ → L0 E μ) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply tendsto_iff_tendstoInMeasure.mpr
  simpa only [coeFn_ofLp, id_eq] using tendstoInMeasure_of_tendsto_Lp
    (f := id) (g := f) (l := 𝓝 f) tendsto_id

end Lp

end TauCeti.L0
