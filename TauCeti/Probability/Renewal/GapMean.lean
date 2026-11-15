/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The mean positive lattice gap

For an interarrival probability law `F` supported on `a ℕ`, with `a > 0` and `F {0} < 1`,
remove zero increments and measure the remaining gaps in units of `a`. The resulting law is the
image of `F[|{0}ᶜ]` under `t ↦ ⌊t / a⌋₊`. It is concentrated on positive integers and its extended
mean is the original extended mean divided by `a * F {0}ᶜ`. For a probability law,
`F {0}ᶜ = 1 - F {0}`. These are the positive integer gaps used in the renewal countdown
chain; the normalization retains the effect of zero-increment clusters.

No finite-mean assumption is made: an infinite original mean gives an infinite gap mean.
The identities also apply to arbitrary measures, with Mathlib's totalized conditioning when
no positive mass remains. Probability normalization follows from `cond_isProbabilityMeasure`
and the image-measure instance. We use these existing measures rather than another law object.
The lattice support hypothesis is stated directly as almost-everywhere membership in `a ℕ`;
maximality of the spacing is not needed for the mean calculation.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, Chapter XI.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable (F : Measure ℝ≥0) {a : ℝ≥0}

/-- For a law supported on `a ℕ`, conditioning on a positive increment and counting its lattice
units gives a law concentrated on positive integers. -/
theorem ae_pos_floor_div_cond (ha : a ≠ 0)
    (hF : ∀ᵐ t ∂F, ∃ n : ℕ, t = n * a) :
    ∀ᵐ n ∂(F[|{0}ᶜ]).map (fun t ↦ ⌊t / a⌋₊), 0 < n := by
  rw [ae_map_iff (by fun_prop : AEMeasurable (fun t : ℝ≥0 ↦ ⌊t / a⌋₊) _)
    measurableSet_Ioi]
  filter_upwards [cond_absolutelyContinuous.ae_le hF,
    ae_cond_mem (measurableSet_singleton (0 : ℝ≥0)).compl] with t ht ht0
  obtain ⟨n, rfl⟩ := ht
  have hn : n ≠ 0 := by
    intro hn
    simp [hn] at ht0
  simpa [ha] using Nat.pos_of_ne_zero hn

/-- **The lattice mean-gap identity.** The mean of the positive integer gap law is
`μ / (a q)`, where `μ` is the original extended mean and `q` is the mass of positive
increments. The identity remains valid when the mean is infinite. -/
theorem lintegral_natCast_map_floor_div_cond (ha : a ≠ 0)
    (hF : ∀ᵐ t ∂F, ∃ n : ℕ, t = n * a) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(F[|{0}ᶜ]).map (fun t ↦ ⌊t / a⌋₊) =
      (∫⁻ t, (t : ℝ≥0∞) ∂F) / ((a : ℝ≥0∞) * F {0}ᶜ) := by
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  calc
    ∫⁻ t, (⌊t / a⌋₊ : ℝ≥0∞) ∂F[|{0}ᶜ] =
        ∫⁻ t, (t / a : ℝ≥0) ∂F[|{0}ᶜ] := by
      apply lintegral_congr_ae
      filter_upwards [cond_absolutelyContinuous.ae_le hF] with t ht
      obtain ⟨n, rfl⟩ := ht
      simp [ha]
    _ = _ := F.lintegral_div_cond_compl_zero ha

end MeasureTheory.Measure
