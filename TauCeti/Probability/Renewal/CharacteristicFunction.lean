/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Lattice
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The lattice obstruction for renewal laws

For a probability law `μ` on nonnegative times, the characteristic function of its real
pushforward equals one at `2π/a` exactly when the law is concentrated on `a ℕ`.
Consequently, a law is nonlattice precisely when zero is the only frequency where its
characteristic function equals one. No translation of the lattice is allowed.

This identifies the spectral obstruction in the convolution equation for limits of
translated renewal measures. It requires no moment assumption and permits an atom at zero,
including the law concentrated entirely at zero.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI.
-/

public section

open MeasureTheory Complex Set
open scoped NNReal

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

/-- At a positive reciprocal-span frequency, the characteristic function equals one
exactly when the interarrival law is concentrated on the corresponding nonnegative lattice. -/
theorem charFun_map_coe_eq_one_iff (a : ℝ≥0) (ha : 0 < a) :
    charFun (μ.map NNReal.toReal) (2 * Real.pi / a) = 1 ↔
      μ (range (fun n : ℕ => (n : ℝ≥0) * a))ᶜ = 0 := by
  rw [charFun_eq_one_iff, ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) measurable_const), ← mem_ae_iff]
  apply Filter.eventually_congr
  filter_upwards [] with x
  simp only [RCLike.inner_apply, conj_trivial]
  rw [exp_eq_one_iff_of_im_nonneg (by
    simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero]
    positivity)]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, NNReal.coe_injective ?_⟩
    have h : 2 * Real.pi / (a : ℝ) * x = n * (2 * Real.pi) := by
      simpa using congrArg Complex.im hn
    field_simp at h
    simpa [mul_comm] using h.symm
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
    push_cast
    field_simp

/-- A nonnegative probability law has a nonzero frequency fixed by its characteristic
function exactly when it is concentrated on an unshifted lattice of positive span. -/
theorem exists_ne_zero_charFun_map_coe_eq_one_iff :
    (∃ t : ℝ, t ≠ 0 ∧ charFun (μ.map NNReal.toReal) t = 1) ↔
      ∃ a : ℝ≥0, 0 < a ∧ μ (range (fun n : ℕ => (n : ℝ≥0) * a))ᶜ = 0 := by
  constructor
  · rintro ⟨t, ht, h⟩
    have habs : 0 < |t| := abs_pos.mpr ht
    have habs_eq : charFun (μ.map NNReal.toReal) |t| = 1 := by
      rcases le_total 0 t with ht' | ht'
      · simpa [abs_of_nonneg ht'] using h
      · simp [abs_of_nonpos ht', charFun_neg, h]
    let a : ℝ≥0 := ⟨2 * Real.pi / |t|, by positivity⟩
    have ha : 0 < a := (NNReal.coe_pos).mp (div_pos Real.two_pi_pos habs)
    refine ⟨a, ha, (charFun_map_coe_eq_one_iff μ a ha).mp ?_⟩
    have hfreq : 2 * Real.pi / (a : ℝ) = |t| := by
      have ha_coe : (a : ℝ) = 2 * Real.pi / |t| := rfl
      rw [ha_coe]
      field_simp
    rwa [hfreq]
  · rintro ⟨a, ha, h⟩
    exact ⟨2 * Real.pi / a, ne_of_gt (by positivity),
      (charFun_map_coe_eq_one_iff μ a ha).mpr h⟩

/-- The spectral nonlattice criterion: no positive-span lattice carries the law if and only
if the characteristic function differs from one at every nonzero frequency. -/
theorem forall_ne_zero_charFun_map_coe_ne_one_iff :
    (∀ t : ℝ, t ≠ 0 → charFun (μ.map NNReal.toReal) t ≠ 1) ↔
      ∀ a : ℝ≥0, 0 < a → μ (range (fun n : ℕ => (n : ℝ≥0) * a))ᶜ ≠ 0 := by
  simpa only [not_exists, not_and] using
    not_congr (exists_ne_zero_charFun_map_coe_eq_one_iff (μ := μ))

end MeasureTheory.Measure
