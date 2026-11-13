/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.Process.HasIndepIncrements
public import TauCeti.Probability.Process.Restart
public import Mathlib.Probability.HasLaw

/-!
# Restarting stationary count increments at a stopping time

For a right-continuous count process with stationary independent increments, the increment
over a fixed duration after a stopping time has its original law, independently of the stopped
natural history, on the event of finiteness. Path regularity is required only almost surely,
and neither completeness nor right continuity of the natural filtration is assumed.

The filtration-relative result assumes independence of each fixed-duration increment from
the corresponding history. The natural-filtration specialization derives this independence
from independent increments. No independence from an arbitrary enlargement is asserted.
This scalar event identity determines the next waiting time at successive Poisson arrivals.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press (2018), Chapter 7, the exponential interarrival characterization.
-/

public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory.IsStoppingTime

open ProbabilityTheory

/-- A count increment with a fixed law independent of each deterministic history has that law
at a stopping time, independently of the stopped history on the finite-time event. The
filtration is arbitrary; right continuity of count paths is required only almost surely. -/
theorem measure_inter_stoppedValue_sub_preimage_eq_mul
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {N : ℝ≥0 → Ω → ℕ} {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hm : ∀ s, Measurable (N s))
    (hrc : ∀ᵐ ω ∂P, ∀ s, ContinuousWithinAt (fun u => N u ω) (Ici s) s)
    (t : ℝ≥0) {μ : Measure ℕ}
    (hindep : ∀ s, Indep
      (MeasurableSpace.comap (fun ω => N (s + t) ω - N s ω) inferInstance) (ℱ s) P)
    (hlaw : ∀ s, HasLaw (fun ω => N (s + t) ω - N s ω) μ P)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (B : Set ℕ) :
    P ((A ∩ {ω | τ ω ≠ ⊤}) ∩
      stoppedValue (fun s ω => N (s + t) ω - N s ω) τ ⁻¹' B) =
        P (A ∩ {ω | τ ω ≠ ⊤}) * μ B := by
  have hright : ∀ᵐ ω ∂P, τ ω ≠ ⊤ → ContinuousWithinAt
      (fun u => N (u + t) ω - N u ω) (Ici (τ ω).untopA) (τ ω).untopA := by
    filter_upwards [hrc] with ω hω _
    have hadd : Continuous (fun u : ℝ≥0 => u + t) := continuous_id.add continuous_const
    exact ((hω ((τ ω).untopA + t)).comp (f := fun u : ℝ≥0 => u + t)
      (s := Ici (τ ω).untopA) hadd.continuousWithinAt
      (fun u hu => add_le_add hu (le_refl t))).sub (hω _)
  have hB : MeasurableSet B := .of_discrete
  refine hτ.measure_inter_stoppedValue_preimage_eq_mul
    (U := fun s ω => N (s + t) ω - N s ω)
    (fun s => (hm _).sub (hm _)) hright hB (fun s C hC => ?_) hA
  rw [((hindep s).symm.indepSet_of_measurableSet hC
    ((comap_measurable _) hB)).measure_inter_eq_mul]
  exact congrArg (P C * ·) ((hlaw s).measure_eq hB)

end MeasureTheory.IsStoppingTime

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- **The stopping-time restart identity for stationary independent count increments.**
On the finite-time event, an increment of duration `t` after a stopping time has the same law
as `N t`, independently of the stopped history for any subfiltration of the natural one.
The stopping time may be infinite; no fallback value at infinity enters the assertion. -/
theorem HasIndepIncrements.measure_inter_stoppedValue_sub_preimage_eq_mul
    (hN : HasIndepIncrements N P) (hm : ∀ t, Measurable (N t))
    (h0 : ∀ᵐ ω ∂P, N 0 ω = 0) (hmono : ∀ᵐ ω ∂P, Monotone (fun t => N t ω))
    (hrc : ∀ᵐ ω ∂P, ∀ s, ContinuousWithinAt (fun u => N u ω) (Ici s) s)
    (t : ℝ≥0)
    (hstat : ∀ s, IdentDistrib (fun ω => N (s + t) ω - N s ω) (N t) P P)
    {ℱ : Filtration ℝ≥0 mΩ}
    (hle : ℱ ≤ Filtration.natural N (fun s => (hm s).stronglyMeasurable))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (B : Set ℕ) :
    P ((A ∩ {ω | τ ω ≠ ⊤}) ∩
      stoppedValue (fun s ω => N (s + t) ω - N s ω) τ ⁻¹' B) =
        P (A ∩ {ω | τ ω ≠ ⊤}) * P (N t ⁻¹' B) := by
  have : IsProbabilityMeasure P := hN.isProbabilityMeasure
  have hind (s : ℝ≥0) : Indep
      (MeasurableSpace.comap (fun ω => N (s + t) ω - N s ω) inferInstance) (ℱ s) P := by
    apply indep_of_indep_of_le_right (m₂ :=
      Filtration.natural N (fun s => (hm s).stronglyMeasurable) s) _ (hle s)
    have hi := (hN.indepFun_shift_nat hm h0 hmono s).comp
      (measurable_pi_apply t) measurable_id
    rw [Filtration.natural_eq_comap]
    simpa only [Function.comp_def, id_eq] using (IndepFun_iff_Indep _ _ _).mp hi
  have hlaw (s : ℝ≥0) : HasLaw (fun ω => N (s + t) ω - N s ω) (P.map (N t)) P :=
    ⟨(hstat s).aemeasurable_fst, (hstat s).map_eq⟩
  have h := hτ.measure_inter_stoppedValue_sub_preimage_eq_mul hm hrc t hind hlaw hA B
  simpa only [Measure.map_apply (hm t) .of_discrete] using h

end ProbabilityTheory
