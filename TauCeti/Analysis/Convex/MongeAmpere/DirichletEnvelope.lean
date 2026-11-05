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

/-- The pointwise supremum of the unit-density subsolution class. -/
def unitDensitySubsolutionEnvelope (Ω : Set E) [DecidablePred (· ∈ Ω)] : E → ℝ :=
  fun x => sSup ((fun w => w x) '' unitDensitySubsolutions μ Ω)

variable {Ω : Set E} [DecidablePred (· ∈ Ω)]

/-- Characterize unit-density subsolutions by convexity, continuity, boundary values and measure. -/
@[simp] theorem mem_unitDensitySubsolutions {w : E → ℝ} :
    w ∈ unitDensitySubsolutions μ Ω ↔
      ConvexOn ℝ (closure Ω) w ∧ ContinuousOn w (closure Ω) ∧
        (∀ z ∈ frontier Ω, w z ≤ 0) ∧
        μ.restrict Ω ≤ mongeAmpereMeasure μ (fun x => if x ∈ Ω then (w x : EReal) else ⊤) :=
  Iff.rfl

/-- Evaluate the unit-density subsolution envelope as a pointwise supremum. -/
theorem unitDensitySubsolutionEnvelope_apply (x : E) :
    unitDensitySubsolutionEnvelope μ Ω x =
      sSup ((fun w => w x) '' unitDensitySubsolutions μ Ω) := by
  rw [unitDensitySubsolutionEnvelope]

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

/-- The shifted quadratic supplies a unit-density subsolution on any bounded open convex set. -/
theorem unitDensitySubsolutions_nonempty (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) : (unitDensitySubsolutions μ Ω).Nonempty := by
  obtain ⟨R, _, hq⟩ := exists_quadratic_mem_unitDensitySubsolutions μ hΩ hΩc hb
  exact ⟨_, hq⟩

variable [Nontrivial E]

/-- Every unit-density subsolution is nonpositive on the closure of a bounded open convex set. -/
theorem nonpos_of_mem_unitDensitySubsolutions (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {w : E → ℝ} (hw : w ∈ unitDensitySubsolutions μ Ω)
    {x : E} (hx : x ∈ closure Ω) : w x ≤ 0 := by
  by_cases hxΩ : x ∈ Ω
  · exact le_of_mongeAmpereMeasure_le_of_le_frontier μ hΩ hb (convexOn_const 0 hΩc)
      (hw.1.subset subset_closure hΩc) continuousOn_const hw.2.1
      (by rw [mongeAmpereMeasure_ite_const μ hΩ hΩc]; exact Measure.zero_le _)
      hw.2.2.1 hxΩ
  · exact hw.2.2.1 x (hΩ.frontier_eq.symm ▸ ⟨hx, hxΩ⟩)

/-- The values of all unit-density subsolutions at a point in the closure are bounded above. -/
theorem bddAbove_image_unitDensitySubsolutions (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {x : E} (hx : x ∈ closure Ω) :
    BddAbove ((fun w => w x) '' unitDensitySubsolutions μ Ω) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact nonpos_of_mem_unitDensitySubsolutions μ hΩ hΩc hb hw hx

/-- Every unit-density subsolution lies below the envelope on the closure. -/
theorem le_unitDensitySubsolutionEnvelope (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {w : E → ℝ} (hw : w ∈ unitDensitySubsolutions μ Ω)
    {x : E} (hx : x ∈ closure Ω) : w x ≤ unitDensitySubsolutionEnvelope μ Ω x := by
  rw [unitDensitySubsolutionEnvelope_apply]
  exact le_csSup (bddAbove_image_unitDensitySubsolutions μ hΩ hΩc hb hx) ⟨w, hw, rfl⟩

/-- The unit-density subsolution envelope is nonpositive on the closure. -/
theorem unitDensitySubsolutionEnvelope_nonpos (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {x : E} (hx : x ∈ closure Ω) :
    unitDensitySubsolutionEnvelope μ Ω x ≤ 0 := by
  rw [unitDensitySubsolutionEnvelope_apply]
  apply csSup_le ((unitDensitySubsolutions_nonempty μ hΩ hΩc hb).image _)
  rintro _ ⟨w, hw, rfl⟩
  exact nonpos_of_mem_unitDensitySubsolutions μ hΩ hΩc hb hw hx

/-- The pointwise subsolution envelope is convex on the closure of the domain. -/
theorem convexOn_unitDensitySubsolutionEnvelope (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ConvexOn ℝ (closure Ω) (unitDensitySubsolutionEnvelope μ Ω) := by
  refine ⟨hΩc.closure, ?_⟩
  intro x hx y hy a b ha hbb hab
  rw [unitDensitySubsolutionEnvelope_apply]
  apply csSup_le ((unitDensitySubsolutions_nonempty μ hΩ hΩc hb).image _)
  rintro _ ⟨w, hw, rfl⟩
  exact (hw.1.2 hx hy ha hbb hab).trans <|
    add_le_add (smul_le_smul_of_nonneg_left
      (le_unitDensitySubsolutionEnvelope μ hΩ hΩc hb hw hx) ha)
      (smul_le_smul_of_nonneg_left
        (le_unitDensitySubsolutionEnvelope μ hΩ hΩc hb hw hy) hbb)

/-- The convex subsolution envelope is continuous in the open domain. -/
theorem continuousOn_unitDensitySubsolutionEnvelope (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) : ContinuousOn (unitDensitySubsolutionEnvelope μ Ω) Ω :=
  ((convexOn_unitDensitySubsolutionEnvelope μ hΩ hΩc hb).subset subset_closure hΩc).continuousOn hΩ

end TauCeti
