/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
import TauCeti.Analysis.Convex.MongeAmpere.Section
import TauCeti.Analysis.Convex.StrictConvexSpace

/-!
# The unit-density Monge–Ampère subsolution envelope

A shifted quadratic gives a unit-density subsolution on any bounded open convex domain.
The comparison principle bounds every subsolution by zero and the pointwise supremum is
a finite convex function, continuous in the open domain.

The construction is adapted from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/Dirichlet/Envelope.lean).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E)

/-- Convex potentials continuous on the closed domain, with nonpositive boundary values and
Aleksandrov measure at least the reference measure on the open domain. -/
def unitDensitySubsolutions (Ω : Set E) [DecidablePred (· ∈ Ω)] : Set (E → ℝ) :=
  {w | ConvexOn ℝ (closure Ω) w ∧ ContinuousOn w (closure Ω) ∧
    (∀ z ∈ frontier Ω, w z ≤ 0) ∧
    μ.restrict Ω ≤ mongeAmpereMeasure μ (fun x => if x ∈ Ω then (w x : EReal) else ⊤)}

variable {Ω : Set E} [DecidablePred (· ∈ Ω)]

/-- Characterize unit-density subsolutions by convexity, continuity, boundary values and measure. -/
theorem mem_unitDensitySubsolutions {w : E → ℝ} :
    w ∈ unitDensitySubsolutions μ Ω ↔
      ConvexOn ℝ (closure Ω) w ∧ ContinuousOn w (closure Ω) ∧
        (∀ z ∈ frontier Ω, w z ≤ 0) ∧
        μ.restrict Ω ≤ mongeAmpereMeasure μ (fun x => if x ∈ Ω then (w x : EReal) else ⊤) :=
  Iff.rfl

variable [μ.IsAddHaarMeasure]

/-- A sufficiently far downward translate of the unit quadratic belongs to the subsolution class. -/
theorem exists_quadratic_mem_unitDensitySubsolutions (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ R > (0 : ℝ), (fun x : E => (1 / 2 : ℝ) * ‖x‖ ^ 2 + (-R ^ 2 / 2)) ∈
      unitDensitySubsolutions μ Ω := by
  obtain ⟨R, hR, hbound⟩ := hb.closure.exists_pos_norm_le
  refine ⟨R, hR, convexOn_mul_norm_sq_add hΩc.closure (a := 1) zero_le_one _, ?_, ?_, ?_⟩
  · have hc : Continuous (fun x : E => (1 / 2 : ℝ) * ‖x‖ ^ 2 + (-R ^ 2 / 2)) := by fun_prop
    exact hc.continuousOn
  · intro z hz
    have hzbound := hbound z (frontier_subset_closure hz)
    nlinarith [norm_nonneg z]
  · rw [mongeAmpereMeasure_ite_mul_norm_sq_add μ hΩ hΩc (a := 1) zero_le_one,
      one_pow, ENNReal.ofReal_one, one_smul]

/-- The unit-density subsolution class is nonempty and its supremum is finite and convex
on the closure and continuous on the domain. -/
theorem exists_unitDensitySubsolutionEnvelope [Nontrivial E] (hΩ : IsOpen Ω)
    (hΩc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) :
    (unitDensitySubsolutions μ Ω).Nonempty ∧
      ∃ U : E → ℝ, (∀ x ∈ closure Ω, U x = sSup ((fun w => w x) ''
        unitDensitySubsolutions μ Ω)) ∧ ConvexOn ℝ (closure Ω) U ∧
        ContinuousOn U Ω ∧ (∀ x ∈ closure Ω, U x ≤ 0) ∧
        (∀ w ∈ unitDensitySubsolutions μ Ω, ∀ x ∈ closure Ω, w x ≤ U x) := by
  obtain ⟨R, _, hq⟩ := exists_quadratic_mem_unitDensitySubsolutions μ hΩ hΩc hb
  let S := unitDensitySubsolutions μ Ω
  have hSne : S.Nonempty := ⟨_, hq⟩
  have hzero : mongeAmpereMeasure μ (fun x => if x ∈ Ω then ((0 : ℝ) : EReal) else ⊤) = 0 := by
    have hdim : Module.finrank ℝ E ≠ 0 := (Module.finrank_pos (R := ℝ) (M := E)).ne'
    simpa only [zero_div, zero_mul, zero_add, zero_pow hdim, ENNReal.ofReal_zero, zero_smul] using
      mongeAmpereMeasure_ite_mul_norm_sq_add μ hΩ hΩc (a := 0) le_rfl 0
  have hcap (w : E → ℝ) (hw : w ∈ S) (x : E) (hx : x ∈ closure Ω) : w x ≤ 0 := by
    by_cases hxΩ : x ∈ Ω
    · exact le_of_mongeAmpereMeasure_le_of_le_frontier μ hΩ hb (convexOn_const 0 hΩc)
        (hw.1.subset subset_closure hΩc) continuousOn_const hw.2.1
        (by rw [hzero]; exact Measure.zero_le _) hw.2.2.1 hxΩ
    · exact hw.2.2.1 x (hΩ.frontier_eq.symm ▸ ⟨hx, hxΩ⟩)
  let U : E → ℝ := fun x => sSup ((fun w => w x) '' S)
  have hB (x : E) (hx : x ∈ closure Ω) : BddAbove ((fun w => w x) '' S) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hcap w hw x hx
  have hU : ConvexOn ℝ (closure Ω) U := by
    refine ⟨hΩc.closure, ?_⟩
    intro x hx y hy a b ha hb hab
    apply csSup_le (hSne.image _)
    rintro _ ⟨w, hw, rfl⟩
    exact ((hw.1).2 hx hy ha hb hab).trans <|
      add_le_add (smul_le_smul_of_nonneg_left (le_csSup (hB x hx) ⟨w, hw, rfl⟩) ha)
        (smul_le_smul_of_nonneg_left (le_csSup (hB y hy) ⟨w, hw, rfl⟩) hb)
  refine ⟨hSne, U, fun _ _ => rfl, hU, (hU.subset subset_closure hΩc).continuousOn hΩ, ?_, ?_⟩
  · intro x hx
    exact csSup_le (hSne.image _) (by rintro _ ⟨w, hw, rfl⟩; exact hcap w hw x hx)
  · intro w hw x hx
    exact le_csSup (hB x hx) ⟨w, hw, rfl⟩

end TauCeti
