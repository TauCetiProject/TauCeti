/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Probability.Distributions.Gamma.CharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Weak continuity of gamma laws

The gamma law varies jointly weakly continuously with its positive shape and rate.
The statement uses `ProbabilityMeasure ℝ`, whose topology is weak convergence, and the
ordinary product topology on the two positive parameters.

Continuity of the principal complex power in `charFun_gammaMeasure` gives the result through
Mathlib's Lévy convergence theorem, `ProbabilityMeasure.tendsto_of_tendsto_charFun`.
The base has real part one, so varying the rate never crosses the branch cut.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- Gamma laws depend jointly weakly continuously on their positive shape and rate. -/
theorem continuous_gammaMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun p : Ioi (0 : ℝ) × Ioi (0 : ℝ) ↦
      (⟨gammaMeasure p.1 p.2,
        isProbabilityMeasure_gammaMeasure p.1.2 p.2.2⟩ : ProbabilityMeasure ℝ)) := by
  apply continuous_iff_seqContinuous.2
  intro p a hp
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    (μ := fun n ↦ ⟨gammaMeasure (p n).1 (p n).2,
      isProbabilityMeasure_gammaMeasure (p n).1.2 (p n).2.2⟩)
  intro t
  simp only [ProbabilityMeasure.coe_mk, charFun_gammaMeasure (p _).1.2 (p _).2.2,
    charFun_gammaMeasure a.1.2 a.2.2]
  have hr : Tendsto (fun n ↦ ((p n).2 : ℂ)) atTop (𝓝 (a.2 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_subtype_val.comp continuous_snd).tendsto a |>.comp hp)
  have ha : Tendsto (fun n ↦ ((p n).1 : ℂ)) atTop (𝓝 (a.1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_subtype_val.comp continuous_fst).tendsto a |>.comp hp)
  refine (tendsto_const_nhds.sub (tendsto_const_nhds.div hr ?_)).cpow ha.neg ?_
  · exact_mod_cast a.2.2.ne'
  · apply Complex.mem_slitPlane_iff.2
    left
    simp [Complex.div_re, Complex.normSq_ofReal]

end TauCeti.Probability
