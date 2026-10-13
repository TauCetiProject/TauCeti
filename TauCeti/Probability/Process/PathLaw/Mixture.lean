/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.ProductKernel
import TauCeti.MeasureTheory.Measure.GiryMonad
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Mixtures of i.i.d. path laws

The de Finetti barycenter of a measure `π` on `ProbabilityMeasure α` is the path-space measure
`∫ P^{⊗ℕ} dπ(P)`. This construction needs only a measurable state space and an arbitrary mixing
measure. It is useful independently of any representation theorem: draw a probability measure,
then draw an i.i.d. path from it.

This file supplies evaluation on measurable events, the point-mass and zero cases, preservation
of probability measures, additivity and homogeneity in the mixing measure, and compatibility with
coordinatewise measurable pushforwards. The symmetry and uniqueness properties of the mixture
belong in `TauCeti.Probability.DeFinetti.Barycenter`.

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, Theorem 1.1.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- The **de Finetti barycenter** of a mixing law `π` on `ProbabilityMeasure α`: the measure
`∫ P^{⊗ℕ} dπ(P)` on `ℕ → α` mixing the countable powers against `π`. For `π` a probability
measure this is the law of a sequence drawn i.i.d. from a `π`-random probability measure. -/
def deFinettiBarycenter (π : Measure (ProbabilityMeasure α)) : Measure (ℕ → α) :=
  π.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)

/-- The barycenter unfolded as a `Measure.bind` against the countable-power kernel. This is the
form used to evaluate mixtures and to compare their finite-dimensional marginals. -/
theorem deFinettiBarycenter_def (π : Measure (ProbabilityMeasure α)) :
    deFinettiBarycenter π = π.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  (rfl)

/-- The barycenter as the `Measure.join` of the pushforward of the mixing measure along
`P ↦ P^{⊗ℕ}`: the mixture representation read as a barycenter of measures on `ℕ → α` rather than
of measures on `α`. For `π` a probability measure this pushforward is the law of `P^{⊗ℕ}` under a
`π`-random `P`. -/
theorem deFinettiBarycenter_eq_join_map (π : Measure (ProbabilityMeasure α)) :
    deFinettiBarycenter π =
      (π.map fun P : ProbabilityMeasure α =>
        Measure.infinitePi fun _ : ℕ => (P : Measure α)).join :=
  (rfl)

/-- Evaluation of a barycenter on a measurable set: the `π`-average of the countable-power
masses. -/
theorem deFinettiBarycenter_apply (π : Measure (ProbabilityMeasure α)) {s : Set (ℕ → α)}
    (hs : MeasurableSet s) :
    deFinettiBarycenter π s =
      ∫⁻ P, (Measure.infinitePi fun _ : ℕ => (P : Measure α)) s ∂π :=
  Measure.bind_apply hs TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable

/-- A point mass mixing law has the corresponding i.i.d. law as its barycenter. -/
@[simp]
theorem deFinettiBarycenter_dirac (P : ProbabilityMeasure α) :
    deFinettiBarycenter (Measure.dirac P) = Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  Measure.dirac_bind TauCeti.MeasureTheory.measurable_infinitePi_const P

/-- The barycenter of a probability mixing law is a probability measure: every countable power of
a probability measure is one, so the mixture keeps the total mass of `π`. -/
instance isProbabilityMeasure_deFinettiBarycenter (π : Measure (ProbabilityMeasure α))
    [IsProbabilityMeasure π] : IsProbabilityMeasure (deFinettiBarycenter π) :=
  isProbabilityMeasure_bind TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable
    (.of_forall fun _ => inferInstance)

/-- **The zero mixing law has the zero barycenter.** -/
@[simp]
theorem deFinettiBarycenter_zero : deFinettiBarycenter (0 : Measure (ProbabilityMeasure α)) = 0 :=
  Measure.bind_zero_left _

/-- **The barycenter is additive in the mixing law.** -/
@[simp]
theorem deFinettiBarycenter_add (π₁ π₂ : Measure (ProbabilityMeasure α)) :
    deFinettiBarycenter (π₁ + π₂) = deFinettiBarycenter π₁ + deFinettiBarycenter π₂ := by
  simp only [deFinettiBarycenter_def]
  rw [← Measure.sum_cond π₁ π₂,
    Measure.bind_sum _ _ TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable,
    Measure.sum_bool]
  rfl

/-- **The barycenter is homogeneous in the mixing law.** -/
@[simp]
theorem deFinettiBarycenter_smul (c : ℝ≥0∞) (π : Measure (ProbabilityMeasure α)) :
    deFinettiBarycenter (c • π) = c • deFinettiBarycenter π :=
  Measure.bind_smul c π TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable

/-- **The barycenter is natural in the state space.** Pushing every coordinate of a barycenter
forward by a measurable `f : α → β` gives the barycenter of the mixing law pushed forward by
`P ↦ P.map f`: drawing `P` from `π` and then an i.i.d. `P`-sequence, and afterwards applying `f`
to each term, is the same as drawing `P.map f` and then an i.i.d. sequence from it. -/
theorem map_pi_deFinettiBarycenter {β : Type*} [MeasurableSpace β]
    (π : Measure (ProbabilityMeasure α)) {f : α → β} (hf : Measurable f) :
    (deFinettiBarycenter π).map (fun x i => f (x i))
      = deFinettiBarycenter (π.map fun P => P.map f) := by
  have hmap : Measurable fun P : ProbabilityMeasure α => P.map f :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map hf
  have hpi : Measurable fun x : ℕ → α => fun i => f (x i) :=
    Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)
  calc (deFinettiBarycenter π).map (fun x i => f (x i))
      = π.bind fun P => (Measure.infinitePi fun _ : ℕ => (P : Measure α)).map
          fun x i => f (x i) :=
        TauCeti.MeasureTheory.map_bind
          TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable hpi
    _ = π.bind fun P => Measure.infinitePi fun _ : ℕ => (P.map f : Measure β) :=
        congrArg (Measure.bind π) (funext fun P => by
          rw [Measure.infinitePi_map_pi (μ := fun _ : ℕ => (P : Measure α))
            (f := fun _ : ℕ => f) fun _ => hf]
          simp)
    _ = deFinettiBarycenter (π.map fun P => P.map f) := by
        rw [deFinettiBarycenter_def, TauCeti.MeasureTheory.bind_map hmap.aemeasurable
          TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable, Function.comp_def]

end MeasureTheory.Measure
