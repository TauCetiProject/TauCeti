/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import TauCeti.MeasureTheory.Measure.NatCast

/-!
# Complementing binomial counts

In `n` Bernoulli trials, replacing successes by failures sends the count `X` to `n - X`
and the success probability `p` to `1 - p`. We prove the native pushforward identity,
its cast reflection, and the corresponding random-variable laws. The identities
include zero trials and success probabilities zero and one.

Natural subtraction agrees with group subtraction on the almost-sure support `X ≤ n`.
The finite-sum reflection argument uses Mathlib's binomial mass formula and
`Finset.sum_range_reflect`, as in the hypergeometric complement API.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Counting failures instead of successes complements the binomial success probability. -/
@[simp]
theorem map_sub_binomial (n : ℕ) (p : unitInterval) :
    (binomial n p).map (fun k ↦ n - k) = binomial n (unitInterval.symm p) := by
  rw [binomial_eq_sum_dirac, binomial_eq_sum_dirac,
    Measure.map_finset_sum Measurable.of_discrete.aemeasurable]
  simp_rw [Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete]
  simp_rw [← Nat.range_succ_eq_Iic]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Finset.mem_range_succ_iff.mp hk
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkn, unitInterval.coe_symm_eq,
    sub_sub_cancel, Nat.choose_symm hkn]
  congr 2
  ring

/-- Reflection by `x ↦ n - x` complements the cast binomial law. -/
@[simp]
theorem map_sub_map_cast_binomial {R : Type*} [AddGroupWithOne R] [MeasurableSpace R]
    [MeasurableSub R] (n : ℕ) (p : unitInterval) :
    (Bin(R, n, p)).map (fun x ↦ (n : R) - x) =
      Bin(R, n, unitInterval.symm p) := by
  rw [Measure.map_sub_map_cast_of_ae_le _
    (ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))), map_sub_binomial]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- The failure count of binomially distributed trials has the complementary success
probability. -/
theorem sub_binomial {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} {n : ℕ} {p : unitInterval} (hX : HasLaw X (binomial n p) P) :
    HasLaw (fun ω ↦ n - X ω) (binomial n (unitInterval.symm p)) P := by
  exact (⟨Measurable.of_discrete.aemeasurable, map_sub_binomial n p⟩ :
    HasLaw (fun k ↦ n - k) (binomial n (unitInterval.symm p)) (binomial n p)).comp hX

/-- Reflecting a cast binomial variable by `x ↦ n - x` complements its success probability. -/
theorem sub_map_cast_binomial {R : Type*} [AddGroupWithOne R] [MeasurableSpace R]
    [MeasurableSub R] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → R} {n : ℕ} {p : unitInterval} (hX : HasLaw X Bin(R, n, p) P) :
    HasLaw (fun ω ↦ (n : R) - X ω) Bin(R, n, unitInterval.symm p) P := by
  exact (⟨by fun_prop, map_sub_map_cast_binomial n p⟩ :
    HasLaw (fun x : R ↦ (n : R) - x) Bin(R, n, unitInterval.symm p) Bin(R, n, p)).comp hX

end ProbabilityTheory.HasLaw
