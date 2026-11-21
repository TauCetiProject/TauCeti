/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Approximation by interval step functions

Sampling a continuous function at the left nodes of a sufficiently fine uniform subdivision
approximates it uniformly on a compact interval. Together with the density of continuous functions
in `L¹`, this gives approximation of an integrable function by interval step functions.

A step function of the integer ceiling, `t ↦ g ⌈t⌉` for an arbitrary `g : ℤ → E`, is bounded on
every bounded interval, so it is interval integrable between any two points
(`intervalIntegrable_comp_ceil`).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace MeasureTheory

variable {E : Type*}

/-- Sampling at the left endpoints of intervals of width `δ` starting at `a`.
Points to the left of `a` are sampled at `a` when `0 < δ`. -/
def intervalStep (a δ : ℝ) (g : ℝ → E) (t : ℝ) : E :=
  g (a + (⌊(t - a) / δ⌋₊ : ℝ) * δ)

variable [NormedAddCommGroup E] in
/-- Sampling any function gives a step function integrable on a finite interval. -/
theorem integrableOn_intervalStep (a b δ : ℝ) (g : ℝ → E) :
    IntegrableOn (intervalStep a δ g) (Ioc a b) := by
  have hm : StronglyMeasurable (intervalStep a δ g) := by
    unfold intervalStep
    exact (StronglyMeasurable.of_discrete (f := fun n : ℕ ↦ g (a + n * δ))).comp_measurable
      (by fun_prop : Measurable fun t : ℝ ↦ ⌊(t - a) / δ⌋₊)
  have hfinite : (intervalStep a δ g '' Icc a b).Finite := by
    have h := (Nat.floor_mono.map_bddAbove
      (isCompact_Icc.bddAbove_image (by fun_prop : ContinuousOn (fun t : ℝ ↦ (t - a) / δ)
        (Icc a b)))).finite
    unfold intervalStep
    simpa only [image_image, Function.comp_def] using
      h.image (fun n : ℕ ↦ g (a + n * δ))
  obtain ⟨C, hC⟩ := hfinite.isBounded.exists_norm_le
  apply volume.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable
  exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦
    hC _ (mem_image_of_mem _ ⟨ht.1.le, ht.2⟩)

variable [NormedAddCommGroup E] in
/-- A step function `t ↦ g ⌈t⌉` of the integer ceiling, for an arbitrary `g : ℤ → E`, is interval
integrable between any two points: on a bounded interval it takes only finitely many values. -/
theorem intervalIntegrable_comp_ceil (g : ℤ → E) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ g ⌈t⌉) volume a b := by
  rw [intervalIntegrable_iff, uIoc]
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    ((StronglyMeasurable.of_discrete.comp_measurable Int.measurable_ceil).aestronglyMeasurable)
    (∑ i ∈ Finset.Icc ⌈min a b⌉ ⌈max a b⌉, ‖g i‖)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_)
  exact Finset.single_le_sum (f := fun i ↦ ‖g i‖) (fun i _ ↦ norm_nonneg _)
    (Finset.mem_Icc.2 ⟨Int.ceil_mono ht.1.le, Int.ceil_mono ht.2⟩)

private theorem sample_bounds {a δ t : ℝ} (hδ : 0 < δ) (hat : a ≤ t) :
    a ≤ a + (⌊(t - a) / δ⌋₊ : ℝ) * δ ∧
    a + (⌊(t - a) / δ⌋₊ : ℝ) * δ ≤ t ∧
    t - (a + (⌊(t - a) / δ⌋₊ : ℝ) * δ) < δ := by
  have hlo := mul_le_mul_of_nonneg_right
    (Nat.floor_le (div_nonneg (sub_nonneg.mpr hat) hδ.le)) hδ.le
  have hhi := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one ((t - a) / δ)) hδ
  rw [div_mul_cancel₀ _ hδ.ne'] at hlo hhi
  exact ⟨le_add_of_nonneg_right (by positivity), by linarith, by linarith⟩

/-- Left-node sampling of a function continuous on `Icc a b`, on the uniform subdivision of
`Icc a b` into `N` cells, converges to the function uniformly on `Icc a b` as `N → ∞`. -/
theorem tendstoUniformlyOn_intervalStep [UniformSpace E] {g : ℝ → E} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    TendstoUniformlyOn (fun N : ℕ ↦ intervalStep a ((b - a) / N) g) g atTop (Icc a b) := by
  intro U hU
  rcases le_or_gt b a with hba | hab
  · -- The interval is empty or the single point `a`, which is sampled at itself.
    refine Eventually.of_forall fun N t ht ↦ ?_
    obtain rfl : t = a := le_antisymm (ht.2.trans hba) ht.1
    simpa only [intervalStep, sub_self, zero_div, Nat.floor_zero, Nat.cast_zero, zero_mul,
      add_zero] using refl_mem_uniformity hU
  -- Uniform continuity gives a mesh `η` below which sampling moves `g` by less than `U`.
  obtain ⟨η, hη, hηU⟩ := Metric.mem_uniformity_dist.mp
    (mem_inf_principal.mp (isCompact_Icc.uniformContinuousOn_of_continuous hg hU))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ((b - a) / η)] with N hN t ht
  have hNpos : (0 : ℝ) < N := (div_pos (sub_pos.mpr hab) hη).trans hN
  have hδ : 0 < (b - a) / N := div_pos (sub_pos.mpr hab) hNpos
  obtain ⟨hs0, hs1, hs2⟩ := sample_bounds hδ ht.1
  have hd : dist t (a + (⌊(t - a) / ((b - a) / N)⌋₊ : ℝ) * ((b - a) / N)) < η := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs1)]
    exact hs2.trans ((div_lt_comm₀ hη hNpos).mp hN)
  simpa only [intervalStep, mem_preimage] using hηU hd ⟨ht, hs0, hs1.trans ht.2⟩

/-- The sampled step function is constant between two successive subdivision nodes. -/
theorem intervalStep_eq {a δ t : ℝ} (g : ℝ → E) (i : ℕ)
    (ht : t ∈ Ico (a + i * δ) (a + (i + 1) * δ)) :
    intervalStep a δ g t = g (a + i * δ) := by
  -- A nonempty cell forces a positive mesh.
  have hδ : 0 < δ := by linarith [ht.1.trans_lt ht.2]
  have hlo : (i : ℝ) ≤ (t - a) / δ := by
    rw [le_div_iff₀ hδ]
    linarith [ht.1]
  have hf : ⌊(t - a) / δ⌋₊ = i := (Nat.floor_eq_iff (i.cast_nonneg.trans hlo)).mpr ⟨hlo, by
    rw [div_lt_iff₀ hδ]
    linarith [ht.2]⟩
  simp only [intervalStep, hf]

/-- An integrable function on a finite interval can be approximated in `L¹` by finite interval
step functions. -/
theorem IntegrableOn.exists_intervalStep_integral_norm_sub_le
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b ε : ℝ} (hf : IntegrableOn f (Ioc a b)) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : ℝ →ᵇ E,
      (∫ t in Ioc a b, ‖intervalStep a ((b - a) / N) g t - f t‖) ≤ ε := by
  rcases le_or_gt b a with hba | hab
  · exact ⟨1, one_pos, 0, by simp [Ioc_eq_empty_of_le hba, hε.le]⟩
  obtain ⟨g, hg, hgi⟩ := hf.exists_boundedContinuous_integral_sub_le (half_pos hε)
  obtain ⟨N, hs, hN⟩ := ((Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_intervalStep g.continuous.continuousOn) _
    (div_pos (half_pos hε) (sub_pos.mpr hab))).and (eventually_gt_atTop 0)).exists
  refine ⟨N, hN, g, ?_⟩
  have hsi := integrableOn_intervalStep a b ((b - a) / N) g
  have hbound : (∫ t in Ioc a b, ‖intervalStep a ((b - a) / N) g t - g t‖) ≤ ε / 2 := by
    calc
      _ ≤ ∫ _ in Ioc a b, (ε / 2) / (b - a) := by
        apply integral_mono_ae (hsi.sub hgi).norm (integrable_const _)
        exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht ↦ by
          simpa only [dist_eq_norm_sub', Pi.sub_apply] using (hs t ⟨ht.1.le, ht.2⟩).le
      _ = ε / 2 := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hab.le, smul_eq_mul]
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
