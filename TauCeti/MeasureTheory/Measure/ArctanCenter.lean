/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The arctan center of a finite measure on the line

For a finite measure `μ` on `ℝ`, the *arctan balance*

`G_μ(m) = ∫ arctan (s - m) dμ(s)`

(`MeasureTheory.Measure.arctanBalance`) is continuous and, when `μ ≠ 0`, strictly decreasing in
`m`, from `π/2 · μ(ℝ)` at `-∞` to `-π/2 · μ(ℝ)` at `+∞`. It therefore has exactly one zero, the
*arctan center* `MeasureTheory.Measure.arctanCenter μ`: the point balancing the mass of `μ` on
its two sides, each point `s` pulling with weight `arctan (s - m)`. In statistics this is the
M-estimator of location with the bounded monotone score function `arctan`.

Unlike the mean, the center exists for every finite measure, with no moment condition. Unlike a
median, it is unique and depends continuously on the measure: if finite measures `μᵢ` converge
weakly to `μ ≠ 0`, their centers converge to that of `μ`
(`MeasureTheory.FiniteMeasure.tendsto_arctanCenter`). It is equivariant under translations,
`arctanCenter (μ.map (· + c)) = arctanCenter μ + c` (`MeasureTheory.Measure.arctanCenter_map_add`),
and invariant under positive rescaling of the measure
(`MeasureTheory.Measure.arctanCenter_smul`).

These are the properties making the center a slice for an action of `ℝ` by translations: a family
of objects carrying finite nonzero measures on `ℝ`, which translate along with the objects, is
trivialized by recentering each measure at `0`. Floer cylinders, which translate along the strip,
are recentered in this way by the distribution of their energy.

Any strictly increasing bounded continuous score function, negative near `-∞` and positive near
`+∞`, would serve; `arctan` is a fixed choice, so that the center is a well-defined function of
the measure.

## Main definitions

* `MeasureTheory.Measure.arctanBalance μ m`: the balance `∫ arctan (s - m) dμ(s)`.
* `MeasureTheory.Measure.arctanCenter μ`: its unique zero, for a finite nonzero measure.

## Main results

* `MeasureTheory.Measure.arctanBalance_eq_zero_iff`: the zeros of the balance are the center.
* `MeasureTheory.Measure.arctanCenter_map_add`: translation equivariance.
* `MeasureTheory.FiniteMeasure.tendsto_arctanCenter`: continuity in the weak topology.

## References

* P. J. Huber, *Robust estimation of a location parameter*, Ann. Math. Statist. **35** (1964),
  73–101, on M-estimators of location defined by a monotone score function.
-/

public section

noncomputable section

open BoundedContinuousFunction Filter Real Set Topology

namespace MeasureTheory

namespace Measure

variable (μ : Measure ℝ)

/-- The *arctan balance* of a measure `μ` on `ℝ` at `m`: the integral `∫ arctan (s - m) dμ(s)`.
For a finite nonzero measure its unique zero is the arctan center
`MeasureTheory.Measure.arctanCenter μ`. -/
def arctanBalance (m : ℝ) : ℝ :=
  ∫ s, arctan (s - m) ∂μ

theorem arctanBalance_def (m : ℝ) : μ.arctanBalance m = ∫ s, arctan (s - m) ∂μ := (rfl)

/-- The arctan balance of the zero measure vanishes identically. -/
@[simp]
theorem arctanBalance_zero : (0 : Measure ℝ).arctanBalance = 0 :=
  funext fun _ ↦ integral_zero_measure _

/-- The arctan balance of a finite measure is continuous. -/
theorem continuous_arctanBalance [IsFiniteMeasure μ] : Continuous μ.arctanBalance :=
  continuous_of_dominated
    (fun m ↦ (continuous_arctan.comp (continuous_sub_right m)).aestronglyMeasurable)
    (fun m ↦ ae_of_all _ fun s ↦ (abs_arctan_lt_pi_div_two (s - m)).le) (integrable_const (π / 2))
    (ae_of_all _ fun s ↦ continuous_arctan.comp (continuous_sub_left s))

/-- The arctan balance of a finite nonzero measure is strictly decreasing. -/
theorem strictAnti_arctanBalance [IsFiniteMeasure μ] [NeZero μ] : StrictAnti μ.arctanBalance := by
  have hint (m : ℝ) : Integrable (fun s ↦ arctan (s - m)) μ :=
    Integrable.of_bound (continuous_arctan.comp (continuous_sub_right m)).aestronglyMeasurable
      (π / 2) (ae_of_all _ fun s ↦ (abs_arctan_lt_pi_div_two (s - m)).le)
  intro m m' hmm'
  rw [← sub_pos, arctanBalance_def, arctanBalance_def, ← integral_sub (hint m) (hint m'),
    integral_pos_iff_support_of_nonneg
      (fun s ↦ sub_nonneg.2 (arctan_mono (by linarith))) ((hint m).sub (hint m'))]
  have hsupp : Function.support (fun s ↦ arctan (s - m) - arctan (s - m')) = univ :=
    Function.support_eq_univ fun s ↦
      (sub_pos.2 (arctan_strictMono (by linarith))).ne'
  rw [hsupp, Measure.measure_univ_pos]
  exact NeZero.ne μ

/-- As `m → -∞` the arctan balance of a finite measure tends to `π / 2` times its total mass. -/
theorem tendsto_arctanBalance_atBot [IsFiniteMeasure μ] :
    Tendsto μ.arctanBalance atBot (𝓝 (π / 2 * μ.real univ)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atBot)
    (F := fun m s ↦ arctan (s - m)) (f := fun _ ↦ π / 2) (fun _ ↦ π / 2)
    (Eventually.of_forall fun m ↦
      (continuous_arctan.comp (continuous_sub_right m)).aestronglyMeasurable)
    (Eventually.of_forall fun m ↦ ae_of_all _ fun s ↦ (abs_arctan_lt_pi_div_two (s - m)).le)
    (integrable_const _)
    (ae_of_all _ fun s ↦ tendsto_nhds_of_tendsto_nhdsWithin
      (tendsto_arctan_atTop.comp ((tendsto_atTop_add_const_left atBot s
        tendsto_neg_atBot_atTop).congr fun m ↦ (sub_eq_add_neg s m).symm)))
  rw [tendsto_congr (arctanBalance_def μ)]
  simpa [integral_const, smul_eq_mul, mul_comm] using h

/-- As `m → +∞` the arctan balance of a finite measure tends to `-π / 2` times its total mass. -/
theorem tendsto_arctanBalance_atTop [IsFiniteMeasure μ] :
    Tendsto μ.arctanBalance atTop (𝓝 (-(π / 2) * μ.real univ)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun m s ↦ arctan (s - m)) (f := fun _ ↦ -(π / 2)) (fun _ ↦ π / 2)
    (Eventually.of_forall fun m ↦
      (continuous_arctan.comp (continuous_sub_right m)).aestronglyMeasurable)
    (Eventually.of_forall fun m ↦ ae_of_all _ fun s ↦ (abs_arctan_lt_pi_div_two (s - m)).le)
    (integrable_const _)
    (ae_of_all _ fun s ↦ tendsto_nhds_of_tendsto_nhdsWithin
      (tendsto_arctan_atBot.comp ((tendsto_atBot_add_const_left atTop s
        tendsto_neg_atTop_atBot).congr fun m ↦ (sub_eq_add_neg s m).symm)))
  rw [tendsto_congr (arctanBalance_def μ)]
  simpa [integral_const, smul_eq_mul, mul_comm] using h

/-- The arctan balance of a finite nonzero measure has exactly one zero. -/
theorem existsUnique_arctanBalance_eq_zero [IsFiniteMeasure μ] [NeZero μ] :
    ∃! m, μ.arctanBalance m = 0 := by
  have hpos : 0 < π / 2 * μ.real univ := mul_pos (by positivity) measureReal_univ_pos
  obtain ⟨a, ha⟩ := ((tendsto_arctanBalance_atBot μ).eventually (lt_mem_nhds hpos)).exists
  have hneg : -(π / 2) * μ.real univ < 0 := by linarith
  obtain ⟨b, hb⟩ := ((tendsto_arctanBalance_atTop μ).eventually (gt_mem_nhds hneg)).exists
  have hab : a ≤ b := by
    by_contra! h
    exact absurd ((strictAnti_arctanBalance μ).antitone h.le) (by linarith)
  obtain ⟨m, -, hm⟩ := intermediate_value_Icc' hab (continuous_arctanBalance μ).continuousOn
    ⟨hb.le, ha.le⟩
  exact ⟨m, hm, fun m' hm' ↦ (strictAnti_arctanBalance μ).injective (hm'.trans hm.symm)⟩

/-- The *arctan center* of a measure `μ` on `ℝ`: for a finite nonzero measure, the unique point
`m` with `∫ arctan (s - m) dμ(s) = 0` (`MeasureTheory.Measure.arctanBalance_eq_zero_iff`). It is
`0` when the balance does not have exactly one zero, for instance for the zero measure. -/
def arctanCenter : ℝ :=
  open scoped Classical in
  if h : ∃! m, μ.arctanBalance m = 0 then h.exists.choose else 0

/-- The arctan balance vanishes at the arctan center. -/
@[simp]
theorem arctanBalance_arctanCenter [IsFiniteMeasure μ] [NeZero μ] :
    μ.arctanBalance μ.arctanCenter = 0 := by
  have h := existsUnique_arctanBalance_eq_zero μ
  unfold arctanCenter
  split_ifs
  exact h.exists.choose_spec

/-- The arctan center of the zero measure is `0`: its balance vanishes identically, so it does not
have exactly one zero. -/
@[simp]
theorem arctanCenter_zero : (0 : Measure ℝ).arctanCenter = 0 := by
  unfold arctanCenter
  split_ifs with h
  · obtain ⟨m, -, hm⟩ := h
    exact absurd ((hm 1 (by simp)).trans (hm 0 (by simp)).symm) one_ne_zero
  · rfl

variable {μ}

/-- **Characterization of the arctan center.** For a finite nonzero measure, the arctan center is
the only zero of the arctan balance. -/
theorem arctanBalance_eq_zero_iff [IsFiniteMeasure μ] [NeZero μ] {m : ℝ} :
    μ.arctanBalance m = 0 ↔ m = μ.arctanCenter :=
  ⟨fun hm ↦ (strictAnti_arctanBalance μ).injective (hm.trans (arctanBalance_arctanCenter μ).symm),
    fun hm ↦ hm ▸ arctanBalance_arctanCenter μ⟩

/-- A point lies below the arctan center exactly when the balance there is positive. -/
theorem lt_arctanCenter_iff [IsFiniteMeasure μ] [NeZero μ] {m : ℝ} :
    m < μ.arctanCenter ↔ 0 < μ.arctanBalance m := by
  rw [← arctanBalance_arctanCenter μ]
  exact (strictAnti_arctanBalance μ).lt_iff_gt.symm

/-- A point lies above the arctan center exactly when the balance there is negative. -/
theorem arctanCenter_lt_iff [IsFiniteMeasure μ] [NeZero μ] {m : ℝ} :
    μ.arctanCenter < m ↔ μ.arctanBalance m < 0 := by
  rw [← arctanBalance_arctanCenter μ]
  exact (strictAnti_arctanBalance μ).lt_iff_gt.symm

/-- Translating a measure translates its arctan balance. -/
theorem arctanBalance_map_add (c m : ℝ) :
    (μ.map (· + c)).arctanBalance (m + c) = μ.arctanBalance m := by
  rw [arctanBalance_def, arctanBalance_def, integral_map (measurable_add_const c).aemeasurable
    (f := fun s ↦ arctan (s - (m + c)))
    (continuous_arctan.comp (continuous_sub_right (m + c))).aestronglyMeasurable]
  simp_rw [add_sub_add_right_eq_sub]

/-- **Translation equivariance of the arctan center.** Translating a finite nonzero measure by
`c` translates its arctan center by `c`. -/
theorem arctanCenter_map_add [IsFiniteMeasure μ] [NeZero μ] (c : ℝ) :
    (μ.map (· + c)).arctanCenter = μ.arctanCenter + c := by
  have : NeZero (μ.map (· + c)) :=
    ⟨(map_ne_zero_iff (measurable_add_const c).aemeasurable).2 (NeZero.ne μ)⟩
  rw [eq_comm, ← arctanBalance_eq_zero_iff, arctanBalance_map_add, arctanBalance_arctanCenter]

/-- Rescaling a finite nonzero measure by a positive finite factor does not change its arctan
center. -/
theorem arctanCenter_smul [IsFiniteMeasure μ] [NeZero μ] {r : ENNReal} (hr₀ : r ≠ 0)
    (hr : r ≠ ⊤) : (r • μ).arctanCenter = μ.arctanCenter := by
  have : NeZero (r • μ) := ⟨by simp [hr₀, NeZero.ne μ]⟩
  have : IsFiniteMeasure (r • μ) := μ.smul_finite hr
  rw [eq_comm, ← arctanBalance_eq_zero_iff, arctanBalance_def, integral_smul_measure,
    ← arctanBalance_def, arctanBalance_arctanCenter, smul_zero]

/-- The arctan center of a Dirac mass is its atom. -/
@[simp]
theorem arctanCenter_dirac (a : ℝ) : (dirac a).arctanCenter = a := by
  rw [eq_comm, ← arctanBalance_eq_zero_iff, arctanBalance_def, integral_dirac, sub_self,
    arctan_zero]

end Measure

namespace FiniteMeasure

/-- **Continuity of the arctan center.** If finite measures `μᵢ` converge weakly to a nonzero
finite measure `μ`, their arctan centers converge to the arctan center of `μ`. -/
theorem tendsto_arctanCenter {γ : Type*} {F : Filter γ} {μs : γ → FiniteMeasure ℝ}
    {μ : FiniteMeasure ℝ} (hμ : μ ≠ 0) (h : Tendsto μs F (𝓝 μ)) :
    Tendsto (fun i ↦ (μs i : Measure ℝ).arctanCenter) F (𝓝 (μ : Measure ℝ).arctanCenter) := by
  have : NeZero (μ : Measure ℝ) := ⟨fun h0 ↦ hμ (toMeasure_injective (h0.trans toMeasure_zero))⟩
  -- The balances converge pointwise, by weak convergence: `s ↦ arctan (s - m)` is bounded and
  -- continuous.
  have hbal (m : ℝ) :
      Tendsto (fun i ↦ (μs i : Measure ℝ).arctanBalance m) F
        (𝓝 ((μ : Measure ℝ).arctanBalance m)) :=
    by simpa only [coe_ofNormedAddCommGroup, Measure.arctanBalance_def] using
      tendsto_iff_forall_integral_tendsto.1 h (.ofNormedAddCommGroup (fun s ↦ arctan (s - m))
        (continuous_arctan.comp (continuous_sub_right m)) (π / 2)
        fun s ↦ (abs_arctan_lt_pi_div_two (s - m)).le)
  -- Eventually the balance of `μs i` is positive at `m - ε / 2` and negative at `m + ε / 2`,
  -- so `μs i ≠ 0` and its center lies strictly between these two points.
  rw [Metric.tendsto_nhds]
  intro ε hε
  set m := (μ : Measure ℝ).arctanCenter
  have h₁ : 0 < (μ : Measure ℝ).arctanBalance (m - ε / 2) :=
    Measure.lt_arctanCenter_iff.1 (by linarith)
  have h₂ : (μ : Measure ℝ).arctanBalance (m + ε / 2) < 0 :=
    Measure.arctanCenter_lt_iff.1 (by linarith)
  filter_upwards [(hbal _).eventually (lt_mem_nhds h₁), (hbal _).eventually (gt_mem_nhds h₂)]
    with i hi₁ hi₂
  have : NeZero (μs i : Measure ℝ) := ⟨fun h0 ↦ by simp [h0, Measure.arctanBalance_def] at hi₁⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [Measure.lt_arctanCenter_iff.2 hi₁]
  · linarith [Measure.arctanCenter_lt_iff.2 hi₂]

end FiniteMeasure

end MeasureTheory
