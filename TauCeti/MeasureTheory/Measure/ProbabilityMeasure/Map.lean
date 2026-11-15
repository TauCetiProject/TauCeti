/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Continuous pushforwards of probability measures

A continuous measurable map induces a continuous pushforward for the weak topologies on
probability measures. Both spaces need measurable opens, but their sigma algebras may be finer
than the Borel sigma algebras. This applies in particular to measurable coordinate projections
when the product topology has measurable opens.

`MeasureTheory.ProbabilityMeasure.continuous_map_of_measurable` extends Mathlib's
`MeasureTheory.ProbabilityMeasure.continuous_map` by making the map's measurability explicit
instead of requiring the target's measurable space to be Borel. Its proof uses the same
bounded-continuous-test-function characterization of weak convergence.

`MeasureTheory.ProbabilityMeasure.continuous_map_of_ae_continuous`: the laws of a family of random
variables that depends continuously on a parameter, for almost every outcome, depend continuously
on that parameter. For example, the time marginals of a law on a space of continuous paths form a
continuous curve of probability measures.

`MeasureTheory.ProbabilityMeasure.continuous_map_of_continuous_uncurry` allows the input law
to vary together with the parameter of a jointly continuous map. It combines Mathlib's
`ProbabilityMeasure.continuous_prod` and `continuous_diracProba` by representing the
parameter as a Dirac factor.
-/

public section

namespace MeasureTheory.ProbabilityMeasure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]

/-- A continuous measurable map induces a continuous pushforward of probability measures for
the weak topologies, even when the target's measurable space is finer than its Borel space. -/
@[fun_prop]
lemma continuous_map_of_measurable {f : X → Y} (hf : Continuous f) (hm : Measurable f) :
    Continuous (fun μ : ProbabilityMeasure X ↦ μ.map f) := by
  rw [continuous_iff_forall_continuous_lintegral]
  intro g
  simpa [lintegral_map (by fun_prop : Measurable fun y ↦ (g y : ENNReal)) hm]
    using continuous_lintegral_boundedContinuousFunction (g.compContinuous ⟨f, hf⟩)

end MeasureTheory.ProbabilityMeasure

namespace MeasureTheory.ProbabilityMeasure

open TopologicalSpace

variable {T X Y : Type*} [TopologicalSpace T] [SecondCountableTopology T] [PseudoMetrizableSpace T]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] [PseudoMetrizableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Pushforward by a jointly continuous map depends weakly continuously on both its
parameter and its input probability law. -/
lemma continuous_map_of_continuous_uncurry {f : T → X → Y}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p : T × ProbabilityMeasure X ↦ p.2.map (f p.1)) := by
  -- The Borel σ-algebra of `T` is only used to view `T` as a space of Dirac masses.
  borelize T
  have h : Continuous fun p : T × ProbabilityMeasure X ↦
      ((diracProba p.1).prod p.2).map (Function.uncurry f) := by
    have := continuous_diracProba (X := T)
    fun_prop
  refine h.congr fun p ↦ toMeasure_injective ?_
  -- `diracProba` bundles `Measure.dirac` with its probability-measure instance.
  have hd : (diracProba p.1).toMeasure = Measure.dirac p.1 := (rfl)
  simp [hd, Measure.dirac_prod, Measure.map_map hf.measurable measurable_prodMk_left,
    Function.comp_def]

end MeasureTheory.ProbabilityMeasure

namespace MeasureTheory.ProbabilityMeasure

variable {T Ω E : Type*} [TopologicalSpace T] [SequentialSpace T] [MeasurableSpace Ω]
  [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- If `f t ω` depends continuously on `t` for almost every `ω`, then the laws `P.map (f t)`
depend continuously on `t` for the weak topology. For instance, the time marginals of a law on a
space of continuous paths form a continuous curve. -/
lemma continuous_map_of_ae_continuous (P : ProbabilityMeasure Ω) {f : T → Ω → E}
    (hf : ∀ t, AEMeasurable (f t) P) (hcont : ∀ᵐ ω ∂(P : Measure Ω), Continuous fun t ↦ f t ω) :
    Continuous fun t ↦ P.map (f t) :=
  continuous_iff_seqContinuous.2 fun _ t hx ↦ (tendstoInDistribution_of_ae_tendsto
    (fun _ ↦ hf _) (hf t) (hcont.mono fun _ h ↦ (h.tendsto t).comp hx)).tendsto

end MeasureTheory.ProbabilityMeasure
