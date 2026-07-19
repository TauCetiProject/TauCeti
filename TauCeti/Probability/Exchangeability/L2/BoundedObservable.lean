module

public import TauCeti.Probability.Exchangeability.L2.Covariance
import TauCeti.Probability.Exchangeability.Map

/-!
# Bounded observables of processes in Lᵖ

This file supplies the bounded-observable entry point to the L² lane of the Exchangeability
roadmap.  On a finite measure space, composing every coordinate of a measurable process with a
bounded measurable observable gives an `Lᵖ` process for every exponent.  At exponent two, a
contractable process therefore has the uniform covariance structure established in
`TauCeti.Probability.Exchangeability.L2.Covariance`.

The result discharges the worked-example check in
`TauCetiRoadmap/Exchangeability/README.md`, "In the real-valued L² lane, bounded observables give
`MemLp 2` automatically."  The proof uses Mathlib's `MemLp.of_bound`; no material from
`cameronfreer/exchangeability` is used.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α E : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace E]
  [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]

/-- A bounded measurable observable, applied coordinatewise to a measurable process on a finite
measure space, belongs to every `Lᵖ`. -/
theorem memLp_comp_process_of_bound {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {f : α → E} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ)
    (C : ℝ) (hf_bound : ∀ x, ‖f x‖ ≤ C) (p : ENNReal) :
    ∀ i, MemLp (fun ω => f (X i ω)) p μ := by
  intro i
  exact MemLp.of_bound (hf.comp_aemeasurable (hX i)).aestronglyMeasurable C
    (ae_of_all μ fun ω => hf_bound (X i ω))

/-- A bounded real-valued observable of a contractable process has uniform means, variances, and
off-diagonal covariances.  This is `contractable_covariance_structure` with its coordinatewise
`L²` hypothesis discharged by boundedness. -/
theorem Contractable.covariance_structure_map_values_of_bound {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_contractable : Contractable μ X)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) {f : α → ℝ} (hf : Measurable f)
    (C : ℝ) (hf_bound : ∀ x, |f x| ≤ C) :
    (∀ i j, μ[fun ω => f (X i ω)] = μ[fun ω => f (X j ω)]) ∧
      (∀ i j, Var[fun ω => f (X i ω); μ] = Var[fun ω => f (X j ω); μ]) ∧
      (∀ i j k l, i ≠ j → k ≠ l →
        cov[fun ω => f (X i ω), fun ω => f (X j ω); μ] =
          cov[fun ω => f (X k ω), fun ω => f (X l ω); μ]) := by
  have hmap : Contractable μ (fun i ω => f (X i ω)) :=
    hX_contractable.map_values hf hX_meas
  exact contractable_covariance_structure hmap
    (memLp_comp_process_of_bound hf hX_meas C (by simpa only [Real.norm_eq_abs] using hf_bound) 2)

end Probability

end TauCeti
