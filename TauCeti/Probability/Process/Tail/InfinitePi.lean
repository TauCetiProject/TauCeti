/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Tail.Product
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.ZeroOne
import TauCeti.Probability.Independence.InfinitePi

/-!
# Kolmogorov's zero-one law for product measures

Over a countable index set `ι`, a product of probability measures (Mathlib's
`Measure.infinitePi`) is trivial on the tail σ-algebra `TauCeti.Probability.tailEvents`: every
tail event has measure `0` or `1`. Along an enumeration of `ι` the coordinates are independent and
the tail σ-algebra is that of the coordinate process
(`TauCeti.Probability.tailEvents_eq_tailProcess`). The ergodicity of Bernoulli product measures
under group actions, which follows from it, is in `TauCeti.Probability.Ergodic.Bernoulli.Action`.

## Main results

* `TauCeti.Probability.infinitePi_eq_zero_or_one_of_measurableSet_tailEvents`: Kolmogorov's
  zero-one law for a product measure over a countable index set.

## References

* H.-O. Georgii, *Gibbs measures and phase transitions* (2nd ed., 2011), Chapter 14.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {ι : Type*}

/-- **Kolmogorov's zero-one law** for a product measure: over a countable index set, every tail
event has measure `0` or `1` under a product of probability measures. -/
theorem infinitePi_eq_zero_or_one_of_measurableSet_tailEvents [Countable ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {P : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (P i)]
    {t : Set (∀ i, X i)} (ht : MeasurableSet[tailEvents] t) :
    Measure.infinitePi P t = 0 ∨ Measure.infinitePi P t = 1 := by
  rcases finite_or_infinite ι with hι | hι
  · rw [tailEvents_eq_bot, MeasurableSpace.measurableSet_bot_iff] at ht
    rcases ht with rfl | rfl <;> simp
  · obtain ⟨e⟩ : Nonempty (ℕ ≃ ι) := nonempty_equiv_of_countable
    rw [tailEvents_eq_tailProcess e, tailProcess_eq_limsup] at ht
    -- Along `e` the coordinates are independent under the product measure.
    have hind : iIndepFun (fun k (ω : ∀ i, X i) => ω (e k)) (Measure.infinitePi P) :=
      (iIndepFun_eval_infinitePi P).precomp e.injective
    exact measure_zero_or_one_of_measurableSet_limsup_atTop
      (fun k => (measurable_pi_apply (e k)).comap_le) hind.iIndep ht

end Probability

end TauCeti
