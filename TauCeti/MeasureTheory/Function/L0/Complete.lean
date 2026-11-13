/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.MeasureTheory.Function.L0.Convergence
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Completeness of real convergence in measure

The bounded integral metric on `TauCeti.L0 μ` is complete for every finite measure `μ`.
Thus Cauchy sequences of real random variables have limits without integrability assumptions
on the random variables themselves.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TauCeti.L0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Real random variables over a finite measure space are complete for convergence in measure. -/
instance instCompleteSpace : CompleteSpace (L0 μ) := by
  let a : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have ha : ∀ n, 0 < a n := fun n ↦ by dsimp [a]; positivity
  have hsum : Summable a := summable_geometric_two
  refine Metric.complete_of_convergent_controlled_sequences
    (fun n ↦ a n / (1 + a n) * a n) (fun n ↦ by
      have := ha n
      positivity) fun f hf ↦ ?_
  have hbound (n : ℕ) :
      μ {x | a n < dist (f n x) (f (n + 1) x)} ≤ ENNReal.ofReal (a n) := by
    have han := ha n
    have hmarkov := measureReal_ge_le_mul_dist (f n) (f (n + 1)) (ha n)
    have hcontrol := (hf n n (n + 1) le_rfl (Nat.le_succ n)).le
    have hcancel : (1 + a n) / a n * (a n / (1 + a n) * a n) = a n := by
      field_simp [ne_of_gt han, ne_of_gt (by positivity : 0 < 1 + a n)]
    have hr : μ.real {x | a n ≤ |f n x - f (n + 1) x|} ≤ a n :=
      hmarkov.trans ((mul_le_mul_of_nonneg_left hcontrol (by positivity)).trans_eq hcancel)
    have hcast := ENNReal.ofReal_le_ofReal hr
    rw [ofReal_measureReal (measure_ne_top μ _)] at hcast
    refine (measure_mono fun x hx ↦ ?_).trans hcast
    have hx' : a n < |f n x - f (n + 1) x| := by
      simpa only [Set.mem_ofPred_eq, Real.dist_eq] using hx
    exact hx'.le
  have hsum' : (∑' n, ENNReal.ofReal (a n)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ (ha n).le) hsum]
    exact ENNReal.ofReal_ne_top
  have hcauchy := TauCeti.MeasureTheory.ae_cauchySeq_of_summable_of_tsum_measure_lt_dist_ne_top hsum
    (ne_top_of_le_ne_top hsum' (tsum_le_tsum hbound))
  obtain ⟨g, hg, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae
    (fun n ↦ (f n).stronglyMeasurable.aestronglyMeasurable)
    (hcauchy.mono fun _ hx ↦ cauchySeq_tendsto_of_complete hx)
  refine ⟨ofFun g hg.aestronglyMeasurable, tendsto_iff_tendstoInMeasure.mpr ?_⟩
  exact (tendstoInMeasure_of_tendsto_ae
    (fun n ↦ (f n).stronglyMeasurable.aestronglyMeasurable) hlim).congr_right
      (coeFn_ofFun g hg.aestronglyMeasurable).symm

end TauCeti.L0
