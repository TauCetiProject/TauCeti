/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Integrating an independent random iid prefix

An independent natural-valued count selects a finite prefix of an iid sequence. Any measurable
nonnegative observable of that prefix can be integrated by first drawing the count and then
integrating against the corresponding finite product law. This permits finite-sample formulas
to be transferred to arbitrary realizations, including random finite configurations.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- Integrate an observable of a random iid prefix by mixing the finite product laws.
The count is independent of the entire sequence; almost-everywhere measurability suffices. -/
theorem IndepFun.lintegral_random_prefix {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure X} [IsProbabilityMeasure Q] {ρ : Measure ℕ}
    {N : Ω → ℕ} {Z : ℕ → Ω → X} (hNZ : IndepFun N (fun ω i ↦ Z i ω) P)
    (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) Q P) (hN : HasLaw N ρ P)
    {h : (n : ℕ) → (Fin n → X) → ℝ≥0∞} (hh : ∀ n, Measurable (h n)) :
    (∫⁻ ω, h (N ω) (fun i ↦ Z i ω) ∂P) =
      ∫⁻ n, ∫⁻ x, h n x ∂Measure.pi (fun _ : Fin n ↦ Q) ∂ρ := by
  have hseq : AEMeasurable (fun ω i ↦ Z i ω) P :=
    aemeasurable_pi_iff.2 fun i ↦ (hZ i).aemeasurable
  have hpair := hNZ.hasLaw_prod hN (hind.hasLaw_infinitePi hZ hseq)
  have hm : Measurable (fun z : ℕ × (ℕ → X) ↦ h z.1 (fun i ↦ z.2 i)) :=
    measurable_from_prod_countable_right fun n ↦ (hh n).comp (by fun_prop)
  rw [hpair.lintegral_comp hm.aemeasurable, lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro n
  rw [← lintegral_map (hh n) (by fun_prop)]
  have hprefix := TauCeti.MeasureTheory.map_prefixProj_infinitePi_const ⟨Q, inferInstance⟩ n
  simp only [ProbabilityMeasure.coe_mk] at hprefix
  rw [hprefix]

end ProbabilityTheory
