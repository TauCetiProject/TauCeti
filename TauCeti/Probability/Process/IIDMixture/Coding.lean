/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.IIDMixture.Basic
public import TauCeti.Probability.Process.PathLaw.Mixture
public import TauCeti.Probability.Kernel.Randomization
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Uniform coding of mixtures of i.i.d. path laws

Draw a probability measure `P` with law `π` and independently draw a sequence of uniform
variables on the unit interval. Applying `unitIntervalCoding α P` coordinatewise realizes
the mixture of the infinite powers of `P`. Retaining `P` as a coordinate realizes
`iidMixtureLaw π id`; forgetting it gives `Measure.deFinettiBarycenter π`.

These identities apply to an arbitrary measure `π` on probability measures, without a
symmetry assumption or a probability assumption on `π`. The state space is nonempty and
standard Borel, as required by the canonical uniform coding map. They provide functional
realizations of random product laws, including the joint law used in conditional-i.i.d.
and array representations.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22, for
  randomization by a uniform variable.
-/

public section

noncomputable section

open MeasureTheory unitInterval

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- Joint measurability of the canonical coordinatewise coding map. -/
theorem measurable_unitIntervalCodingPath :
    Measurable fun p : ProbabilityMeasure α × (ℕ → I) =>
      fun i => unitIntervalCoding α p.1 (p.2 i) :=
  measurable_pi_uncurry_prod fun _ => measurable_uncurry_unitIntervalCoding α

/-- **Coding a mixing law, keeping the parameter.** Retaining the drawn probability measure as a
coordinate, the same construction produces the canonical conditionally i.i.d. law `iidMixtureLaw`:
the parameter is not merely a mixing representative of the coded sequence but its directing
measure. -/
@[simp]
theorem map_prod_unitIntervalCoding_eq_iidMixtureLaw (π : Measure (ProbabilityMeasure α)) :
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)))
      = iidMixtureLaw π id :=
  map_prod_infinitePi_eq_iidMixtureLaw _ (measurable_uncurry_unitIntervalCoding α)
    map_volume_unitIntervalCoding

/-- **Coding a mixing law.** Drawing a probability measure from `π`, then coding an independent
i.i.d. uniform sequence by it, produces the de Finetti barycenter of `π`. -/
@[simp]
theorem map_prod_unitIntervalCoding_eq_deFinettiBarycenter (π : Measure (ProbabilityMeasure α)) :
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun p i => unitIntervalCoding α p.1 (p.2 i))
      = Measure.deFinettiBarycenter π := by
  have hG : Measurable fun p : ProbabilityMeasure α × (ℕ → I) =>
      (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)) :=
    measurable_fst.prodMk measurable_unitIntervalCodingPath
  calc
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          (fun p i => unitIntervalCoding α p.1 (p.2 i))
        = ((π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
            (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)))).map Prod.snd := by
              rw [Measure.map_map measurable_snd hG]
              rfl
    _ = (iidMixtureLaw π id).map Prod.snd := by
          rw [map_prod_unitIntervalCoding_eq_iidMixtureLaw]
    _ = Measure.deFinettiBarycenter π := by
          rw [iidMixtureLaw_def, TauCeti.MeasureTheory.map_bind
            (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const
              (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id).aemeasurable
            measurable_snd, Measure.deFinettiBarycenter_def]
          simp

end TauCeti.Probability
