/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Bounds for Mellin transforms on closed strips

Absolute convergence at the two real endpoints implies absolute convergence throughout
the strip and bounds the transform uniformly there, as needed for three-lines arguments.
-/

public section

open Complex Filter MeasureTheory Set

private theorem norm_mellinIntegrand_le_on_strip {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x : E) {a b u : ℝ} (hu : 0 < u) {s : ℂ} (hs : s.re ∈ Icc a b) :
    ‖(u : ℂ) ^ (s - 1) • x‖ ≤
      ‖(u : ℂ) ^ ((a : ℂ) - 1) • x‖ + ‖(u : ℂ) ^ ((b : ℂ) - 1) • x‖ := by
  simp only [norm_smul, ← add_mul, ← ofReal_one, ← ofReal_sub]
  refine mul_le_mul_of_nonneg_right (norm_ofReal_cpow_le_add_of_re_mem_Icc hu ?_) (norm_nonneg _)
  rw [sub_re, ofReal_re]
  exact ⟨sub_le_sub_right hs.1 1, sub_le_sub_right hs.2 1⟩

/-- Absolute convergence at both real edges gives absolute convergence at every point of the
closed vertical strip. -/
theorem MellinConvergent.of_re_mem_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} {a b : ℝ}
    (ha : MellinConvergent f a) (hb : MellinConvergent f b) {s : ℂ} (hs : s.re ∈ Icc a b) :
    MellinConvergent f s := by
  have ha' : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ ((a : ℂ) - 1) • f u) (Ioi 0) := ha
  have hm : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (s - a)) (Ioi 0) :=
    continuous_ofReal.continuousOn.cpow_const fun u hu ↦
      Or.inl (by simpa only [ofReal_re] using mem_Ioi.mp hu)
  refine (ha.norm.add hb.norm).mono' ?_ ?_
  · refine ((hm.aestronglyMeasurable measurableSet_Ioi).smul ha'.1).congr ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    -- The measurable scalar action is pointwise; expose the two factors at `u`.
    change (u : ℂ) ^ (s - a) • ((u : ℂ) ^ ((a : ℂ) - 1) • f u) = (u : ℂ) ^ (s - 1) • f u
    rw [← mul_smul, ← cpow_add _ _ (ofReal_ne_zero.mpr (mem_Ioi.mp hu).ne'), sub_add_sub_cancel]
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    exact norm_mellinIntegrand_le_on_strip (f u) hu hs

/-- Absolute convergence at `a` and `b` bounds the Mellin transform on the entire strip
`a ≤ Re s ≤ b`. -/
theorem MellinConvergent.exists_norm_mellin_le_on_strip {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} {a b : ℝ}
    (ha : MellinConvergent f a) (hb : MellinConvergent f b) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → ‖mellin f s‖ ≤ C := by
  let p (s : ℂ) (u : ℝ) := ‖(u : ℂ) ^ (s - 1) • f u‖
  refine ⟨∫ u in Ioi 0, p a u + p b u, fun s hs ↦ ?_⟩
  rw [mellin]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_ae (ha.of_re_mem_Icc hb hs).norm (ha.norm.add hb.norm) ?_)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  exact norm_mellinIntegrand_le_on_strip (f u) hu hs
