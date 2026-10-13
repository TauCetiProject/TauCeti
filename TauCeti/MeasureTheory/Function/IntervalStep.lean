/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Approximation by interval step functions

Sampling a continuous function at the left nodes of a sufficiently fine uniform subdivision
approximates it uniformly on a compact interval. Together with the density of continuous functions
in `L¹`, this gives approximation of an integrable function by interval step functions.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped Topology BoundedContinuousFunction

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

/-- Sampling at the left endpoints of intervals of width `δ` starting at `a`. -/
def intervalStep (a δ : ℝ) (g : ℝ → E) (t : ℝ) : E :=
  g (a + (⌊(t - a) / δ⌋₊ : ℝ) * δ)

private theorem measurable_sample (a δ : ℝ) :
    Measurable (fun t : ℝ ↦ a + (⌊(t - a) / δ⌋₊ : ℝ) * δ) := by
  fun_prop

/-- Sampling a bounded continuous function gives a step function integrable on a finite interval. -/
theorem integrableOn_intervalStep (a b δ : ℝ) (g : ℝ →ᵇ E) :
    IntegrableOn (intervalStep a δ g) (Ioc a b) := by
  apply (integrable_const ‖g‖).mono'
    (g.continuous.stronglyMeasurable.comp_measurable (measurable_sample a δ)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t ↦ g.norm_coe_le_norm _

private theorem sample_bounds {a δ t : ℝ} (hδ : 0 < δ) (hat : a ≤ t) :
    a ≤ a + (⌊(t - a) / δ⌋₊ : ℝ) * δ ∧
    a + (⌊(t - a) / δ⌋₊ : ℝ) * δ ≤ t ∧
    t - (a + (⌊(t - a) / δ⌋₊ : ℝ) * δ) < δ := by
  have hx : 0 ≤ (t - a) / δ := div_nonneg (sub_nonneg.mpr hat) hδ.le
  have hlo := (mul_le_mul_of_nonneg_right (Nat.floor_le hx) hδ.le)
  have hhi := (mul_lt_mul_of_pos_right (Nat.lt_floor_add_one ((t - a) / δ)) hδ)
  rw [div_mul_cancel₀ _ hδ.ne'] at hlo hhi
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ.le)
  constructor
  · linarith
  · linarith

/-- Left-node sampling on a sufficiently fine uniform subdivision gives uniform approximation. -/
theorem exists_intervalStep_norm_sub_le (g : ℝ →ᵇ E) {a b ε : ℝ}
    (hab : a < b) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ t ∈ Icc a b,
      ‖intervalStep a ((b - a) / N) g t - g t‖ ≤ ε := by
  obtain ⟨η, hη, hg⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous g.continuous.continuousOn) ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hη (sub_pos.mpr hab))
  let N := n + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hδ : 0 < (b - a) / N := div_pos (sub_pos.mpr hab) hN
  have hmesh : (b - a) / N < η := by
    have h := mul_lt_mul_of_pos_right hn (sub_pos.mpr hab)
    rw [div_mul_cancel₀ _ (sub_pos.mpr hab).ne'] at h
    dsimp [N]
    push_cast
    convert h using 1
    ring
  refine ⟨N, by dsimp [N]; positivity, fun t ht ↦ ?_⟩
  obtain ⟨hs0, hs1, hs2⟩ := sample_bounds hδ ht.1
  have hs : a + (⌊(t - a) / ((b - a) / N)⌋₊ : ℝ) * ((b - a) / N) ∈ Icc a b :=
    ⟨hs0, hs1.trans ht.2⟩
  have hd : dist (a + (⌊(t - a) / ((b - a) / N)⌋₊ : ℝ) * ((b - a) / N)) t < η := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs1)]
    linarith
  simpa only [intervalStep, dist_eq_norm] using (hg _ hs t ht hd).le

omit [NormedAddCommGroup E] in
/-- The sampled step function is constant between two successive subdivision nodes. -/
theorem intervalStep_eq {a δ t : ℝ} (hδ : 0 < δ) (g : ℝ → E) (i : ℕ)
    (ht : t ∈ Ico (a + i * δ) (a + (i + 1) * δ)) :
    intervalStep a δ g t = g (a + i * δ) := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  have ht0 : 0 ≤ (t - a) / δ := by
    apply div_nonneg _ hδ.le
    nlinarith [ht.1]
  have hf : ⌊(t - a) / δ⌋₊ = i := (Nat.floor_eq_iff ht0).mpr ⟨by
    rw [le_div_iff₀ hδ]
    linarith [ht.1], by
    rw [div_lt_iff₀ hδ]
    linarith [ht.2]⟩
  simp only [intervalStep, hf]

/-- An integrable function on a finite interval can be approximated in `L¹` by finite interval
step functions. -/
theorem IntegrableOn.exists_intervalStep_integral_norm_sub_le [NormedSpace ℝ E]
    {f : ℝ → E} {a b ε : ℝ} (hf : IntegrableOn f (Ioc a b))
    (hab : a < b) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : ℝ →ᵇ E,
      (∫ t in Ioc a b, ‖intervalStep a ((b - a) / N) g t - f t‖) ≤ ε := by
  obtain ⟨g, hg, hgi⟩ := hf.exists_boundedContinuous_integral_sub_le (half_pos hε)
  obtain ⟨N, hN, hs⟩ := exists_intervalStep_norm_sub_le g hab
    (div_pos (half_pos hε) (sub_pos.mpr hab))
  refine ⟨N, hN, g, ?_⟩
  have hsi := integrableOn_intervalStep a b ((b - a) / N) g
  have hbound : (∫ t in Ioc a b, ‖intervalStep a ((b - a) / N) g t - g t‖) ≤ ε / 2 := by
    calc
      _ ≤ ∫ _ in Ioc a b, (ε / 2) / (b - a) := by
        apply integral_mono_ae (hsi.sub hgi).norm (integrable_const _)
        exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ hs t ⟨ht.1.le, ht.2⟩
      _ = ε / 2 := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
        simp only [smul_eq_mul]
        field_simp [(sub_pos.mpr hab).ne']
  calc
    _ ≤ ∫ t in Ioc a b, ‖intervalStep a ((b - a) / N) g t - g t‖ + ‖f t - g t‖ := by
      apply integral_mono (hsi.sub hf).norm ((hsi.sub hgi).norm.add (hf.sub hgi).norm)
      intro t
      simpa only [Pi.sub_apply, Pi.add_apply, norm_sub_rev (g t) (f t)] using
        norm_sub_le_norm_sub_add_norm_sub (intervalStep a ((b - a) / N) g t) (g t) (f t)
    _ = (∫ t in Ioc a b, ‖intervalStep a ((b - a) / N) g t - g t‖) +
        ∫ t in Ioc a b, ‖f t - g t‖ := integral_add (hsi.sub hgi).norm (hf.sub hgi).norm
    _ ≤ ε := by linarith

end MeasureTheory
