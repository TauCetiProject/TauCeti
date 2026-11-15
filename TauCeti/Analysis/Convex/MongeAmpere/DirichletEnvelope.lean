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
# The zero-boundary Monge–Ampère subsolution envelope

For a reference Haar measure `μ` and arbitrary data measure `ν`, the supremum of convex
subsolutions with nonpositive boundary values is the Perron candidate for the Monge–Ampère
Dirichlet problem with datum `ν` and zero boundary values. On a bounded open convex domain,
a shifted unit quadratic makes the class nonempty whenever `ν ≤ μ.restrict Ω`, in any dimension.
In positive dimension, comparison bounds every subsolution by zero; when the class is
nonempty, its pointwise supremum on the closure is finite and convex, and is continuous
in the open domain.
If the class is empty, the real supremum convention gives the zero function, so the same
nonpositivity, convexity and continuity conclusions still hold. The unit-density case is
`ν = μ.restrict Ω`. Boundary attainment and the measure identity are not asserted here.

The construction is adapted from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/Dirichlet/Envelope.lean).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ ν : Measure E)

/-- Convex potentials continuous on the closed domain, with nonpositive boundary values and
Aleksandrov measure at least the data measure `ν`. -/
def dirichletSubsolutions (Ω : Set E) [DecidablePred (· ∈ Ω)] : Set (E → ℝ) :=
  {w | ConvexOn ℝ (closure Ω) w ∧ ContinuousOn w (closure Ω) ∧
    (∀ z ∈ frontier Ω, w z ≤ 0) ∧
    ν ≤ mongeAmpereMeasure μ (fun x => if x ∈ Ω then (w x : EReal) else ⊤)}

/-- The pointwise supremum of the subsolution class for datum `ν` and zero boundary values.
It is the zero function if the class is empty, by the real supremum convention. -/
def dirichletSubsolutionEnvelope (Ω : Set E) [DecidablePred (· ∈ Ω)] : E → ℝ :=
  fun x => sSup ((fun w => w x) '' dirichletSubsolutions μ ν Ω)

variable {Ω : Set E} [DecidablePred (· ∈ Ω)]

/-- Characterize subsolutions by convexity, continuity, boundary values and measure. -/
@[simp] theorem mem_dirichletSubsolutions {w : E → ℝ} :
    w ∈ dirichletSubsolutions μ ν Ω ↔
      ConvexOn ℝ (closure Ω) w ∧ ContinuousOn w (closure Ω) ∧
        (∀ z ∈ frontier Ω, w z ≤ 0) ∧
        ν ≤ mongeAmpereMeasure μ (fun x => if x ∈ Ω then (w x : EReal) else ⊤) :=
  Iff.rfl

/-- Evaluate the zero-boundary subsolution envelope as a pointwise supremum. -/
theorem dirichletSubsolutionEnvelope_apply (x : E) :
    dirichletSubsolutionEnvelope μ ν Ω x =
      sSup ((fun w => w x) '' dirichletSubsolutions μ ν Ω) := by
  rw [dirichletSubsolutionEnvelope]

/-- The envelope of an empty subsolution class is the zero function, by the real supremum
convention. -/
theorem dirichletSubsolutionEnvelope_of_eq_empty (h : dirichletSubsolutions μ ν Ω = ∅) :
    dirichletSubsolutionEnvelope μ ν Ω = 0 := by
  funext x
  simp only [dirichletSubsolutionEnvelope_apply, h, image_empty, Real.sSup_empty, Pi.zero_apply]

/-- For a nonempty subsolution class, any common upper bound also bounds its envelope. -/
theorem dirichletSubsolutionEnvelope_le {x : E} {c : ℝ}
    (hne : (dirichletSubsolutions μ ν Ω).Nonempty)
    (h : ∀ w ∈ dirichletSubsolutions μ ν Ω, w x ≤ c) :
    dirichletSubsolutionEnvelope μ ν Ω x ≤ c := by
  rw [dirichletSubsolutionEnvelope_apply]
  apply csSup_le (hne.image _)
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

variable [μ.IsAddHaarMeasure]

/-- If the datum is bounded by the reference measure on the domain, a sufficiently far downward
translate of the unit quadratic belongs to the subsolution class, in every dimension. -/
theorem exists_quadratic_mem_dirichletSubsolutions (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hν : ν ≤ μ.restrict Ω) :
    ∃ R > (0 : ℝ), (fun x : E => (1 / 2 : ℝ) * ‖x‖ ^ 2 + (-R ^ 2 / 2)) ∈
      dirichletSubsolutions μ ν Ω := by
  obtain ⟨R, hR, hbound⟩ := hb.closure.exists_pos_norm_le
  refine ⟨R, hR, convexOn_mul_norm_sq_add hΩc.closure (a := 1) zero_le_one _, ?_, ?_, ?_⟩
  · have hc : Continuous (fun x : E => (1 / 2 : ℝ) * ‖x‖ ^ 2 + (-R ^ 2 / 2)) := by fun_prop
    exact hc.continuousOn
  · intro z hz
    have hzbound := hbound z (frontier_subset_closure hz)
    nlinarith [norm_nonneg z]
  · rw [mongeAmpereMeasure_ite_mul_norm_sq_add μ hΩ hΩc (a := 1) zero_le_one,
      one_pow, ENNReal.ofReal_one, one_smul]
    exact hν

/-- The shifted unit quadratic supplies a subsolution for any datum at most `μ.restrict Ω`,
on a bounded open convex set, in every dimension. -/
theorem dirichletSubsolutions_nonempty_of_le_restrict (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hν : ν ≤ μ.restrict Ω) :
    (dirichletSubsolutions μ ν Ω).Nonempty := by
  obtain ⟨R, _, hq⟩ := exists_quadratic_mem_dirichletSubsolutions μ ν hΩ hΩc hb hν
  exact ⟨_, hq⟩

variable [Nontrivial E]

/-- Every zero-boundary subsolution is nonpositive on the closure of a bounded open convex set. -/
theorem nonpos_of_mem_dirichletSubsolutions (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {w : E → ℝ} (hw : w ∈ dirichletSubsolutions μ ν Ω)
    {x : E} (hx : x ∈ closure Ω) : w x ≤ 0 := by
  by_cases hxΩ : x ∈ Ω
  · exact le_of_mongeAmpereMeasure_le_of_le_frontier μ hΩ hb (convexOn_const 0 hΩc)
      (hw.1.subset subset_closure hΩc) continuousOn_const hw.2.1
      (by rw [mongeAmpereMeasure_ite_const μ hΩ hΩc]; exact Measure.zero_le _)
      hw.2.2.1 hxΩ
  · exact hw.2.2.1 x (hΩ.frontier_eq.symm ▸ ⟨hx, hxΩ⟩)

/-- The values of all zero-boundary subsolutions at a point in the closure are bounded above. -/
theorem bddAbove_image_dirichletSubsolutions (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {x : E} (hx : x ∈ closure Ω) :
    BddAbove ((fun w => w x) '' dirichletSubsolutions μ ν Ω) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact nonpos_of_mem_dirichletSubsolutions μ ν hΩ hΩc hb hw hx

/-- Every zero-boundary subsolution lies below the envelope on the closure. -/
theorem le_dirichletSubsolutionEnvelope (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {w : E → ℝ} (hw : w ∈ dirichletSubsolutions μ ν Ω)
    {x : E} (hx : x ∈ closure Ω) : w x ≤ dirichletSubsolutionEnvelope μ ν Ω x := by
  rw [dirichletSubsolutionEnvelope_apply]
  exact le_csSup (bddAbove_image_dirichletSubsolutions μ ν hΩ hΩc hb hx) ⟨w, hw, rfl⟩

/-- At a point of the closure, the envelope of a nonempty class is at most `c` exactly when
every subsolution's value is at most `c`. -/
theorem dirichletSubsolutionEnvelope_le_iff (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hne : (dirichletSubsolutions μ ν Ω).Nonempty)
    {x : E} (hx : x ∈ closure Ω) {c : ℝ} :
    dirichletSubsolutionEnvelope μ ν Ω x ≤ c ↔
      ∀ w ∈ dirichletSubsolutions μ ν Ω, w x ≤ c :=
  ⟨fun h _ hw => (le_dirichletSubsolutionEnvelope μ ν hΩ hΩc hb hw hx).trans h,
    dirichletSubsolutionEnvelope_le μ ν hne⟩

/-- The zero-boundary subsolution envelope is nonpositive on the closure. -/
theorem dirichletSubsolutionEnvelope_nonpos (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {x : E} (hx : x ∈ closure Ω) :
    dirichletSubsolutionEnvelope μ ν Ω x ≤ 0 := by
  rw [dirichletSubsolutionEnvelope_apply]
  apply Real.sSup_nonpos
  rintro _ ⟨w, hw, rfl⟩
  exact nonpos_of_mem_dirichletSubsolutions μ ν hΩ hΩc hb hw hx

/-- The pointwise subsolution envelope is convex on the closure of the domain. -/
theorem convexOn_dirichletSubsolutionEnvelope (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ConvexOn ℝ (closure Ω) (dirichletSubsolutionEnvelope μ ν Ω) := by
  classical
  obtain hempty | hne := (dirichletSubsolutions μ ν Ω).eq_empty_or_nonempty
  · rw [dirichletSubsolutionEnvelope_of_eq_empty μ ν hempty]
    exact convexOn_const 0 hΩc.closure
  · refine ⟨hΩc.closure, ?_⟩
    intro x hx y hy a b ha hbb hab
    apply dirichletSubsolutionEnvelope_le μ ν hne
    intro w hw
    exact (hw.1.2 hx hy ha hbb hab).trans <|
      add_le_add (smul_le_smul_of_nonneg_left
        (le_dirichletSubsolutionEnvelope μ ν hΩ hΩc hb hw hx) ha)
        (smul_le_smul_of_nonneg_left
          (le_dirichletSubsolutionEnvelope μ ν hΩ hΩc hb hw hy) hbb)

/-- The convex subsolution envelope is continuous in the open domain. -/
theorem continuousOn_dirichletSubsolutionEnvelope (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) : ContinuousOn (dirichletSubsolutionEnvelope μ ν Ω) Ω :=
  ((convexOn_dirichletSubsolutionEnvelope μ ν hΩ hΩc hb).subset subset_closure hΩc).continuousOn hΩ

end TauCeti
