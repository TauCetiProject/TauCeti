/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Tail.ProperAction
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.ZeroOne

/-!
# Tail triviality and ergodicity of Bernoulli product measures

Over a countable index set `ι`, a product of probability measures (Mathlib's
`Measure.infinitePi`) is trivial on the tail σ-algebra `TauCeti.Probability.tailEvents`: every
tail event has measure `0` or `1`. This is Kolmogorov's zero-one law: along an enumeration of `ι`
the coordinates are independent and the tail σ-algebra is that of the coordinate process
(`TauCeti.Probability.tailEvents_eq_tailProcess`).

Let a group `Γ` act on `ι` and on configurations `ω : ι → S` by `(g • ω) i = ω (g⁻¹ • i)`
(Mathlib's `arrowAction`). The Bernoulli product measure `ν^{⊗ι}` of a probability
measure `ν` on `S` is invariant under this action, since each `g` permutes the coordinates. If
`Γ` is infinite and acts properly on the countable set `ι` (for finite `F, F' ⊆ ι`, only finitely
many `g` move a point of `F` into `F'`), then every almost invariant event is almost surely a tail
event (`TauCeti.Probability.exists_measurableSet_tailEvents_ae_eq_of_proper`), so it is null or
conull: the action is ergodic.

## Main results

* `TauCeti.Probability.measure_eq_zero_or_one_of_measurableSet_tailEvents`: Kolmogorov's zero-one
  law for a product measure over a countable index set.
* `TauCeti.Probability.eventuallyEmptyOrUniv_of_forall_preimage_ae_eq`: an almost invariant event
  is null or conull for a Bernoulli product measure under a proper action of an infinite group.
* `TauCeti.Probability.ergodicSMul_infinitePi`: the same statement as `ErgodicSMul` for the action
  `arrowAction`.

## References

* S. Sheffield, *Random surfaces*, Astérisque 304 (2005), Section 3.2, Lemma 3.2.1.
* H.-O. Georgii, *Gibbs measures and phase transitions* (2nd ed., 2011), Chapter 14.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {ι : Type*}

/-- **Kolmogorov's zero-one law** for a product measure: over a countable index set, every tail
event has measure `0` or `1` under a product of probability measures. -/
theorem measure_eq_zero_or_one_of_measurableSet_tailEvents [Countable ι] {X : ι → Type*}
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
      (iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id).precomp e.injective
    exact measure_zero_or_one_of_measurableSet_limsup_atTop
      (fun k => (measurable_pi_apply (e k)).comap_le) hind.iIndep ht

variable {Γ S : Type*} [Group Γ] [MulAction Γ ι] [MeasurableSpace S] {ν : Measure S}
  [IsProbabilityMeasure ν]

/-- **Bernoulli product measures are ergodic**, stated with almost invariant events. Let an
infinite group `Γ` act properly on a countable set `ι`, and on configurations by
`(g • ω) i = ω (g⁻¹ • i)`. For a probability measure `ν`, every null-measurable event that is
almost invariant under this action is null or conull for the product measure `ν^{⊗ι}`. -/
theorem eventuallyEmptyOrUniv_of_forall_preimage_ae_eq [Countable ι] [Infinite Γ]
    (hproper : ∀ F F' : Finset ι, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite) {A : Set (ι → S)}
    (hA : NullMeasurableSet A (Measure.infinitePi fun _ => ν))
    (hAg : ∀ g : Γ, (fun (ω : ι → S) i => ω (g⁻¹ • i)) ⁻¹' A =ᵐ[Measure.infinitePi fun _ => ν] A) :
    EventuallyEmptyOrUniv A (ae (Measure.infinitePi fun _ => ν)) := by
  have hμ (g : Γ) : MeasurePreserving (fun (ω : ι → S) i => ω (g⁻¹ • i))
      (Measure.infinitePi fun _ => ν) (Measure.infinitePi fun _ => ν) :=
    ⟨by fun_prop, Measure.map_infinitePi_infinitePi_of_inj (MulAction.injective g⁻¹)⟩
  obtain ⟨T, hT, hTA⟩ := exists_measurableSet_tailEvents_ae_eq_of_proper hproper hμ hA hAg
  refine (eventuallyEmptyOrUniv_iff.2 ?_).congr hTA
  rcases measure_eq_zero_or_one_of_measurableSet_tailEvents (P := fun _ => ν) hT with h | h
  · exact Or.inr (ae_iff.2 (by simpa using h))
  · exact Or.inl ((mem_ae_iff_prob_eq_one (tailEvents_le_pi _ hT)).2 h)

/-- **Bernoulli product measures are ergodic.** Let an infinite group `Γ` act properly on a
countable set `ι`: for finite `F, F' ⊆ ι`, only finitely many `g` move a point of `F` into `F'`.
For a probability measure `ν` on `S`, the action `(g • ω) i = ω (g⁻¹ • i)` of `Γ` on `ι → S`
(Mathlib's `arrowAction`) is ergodic for the product measure `ν^{⊗ι}`. -/
theorem ergodicSMul_infinitePi [Countable ι] [Infinite Γ]
    (hproper : ∀ F F' : Finset ι, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite) :
    letI := arrowAction (G := Γ) (A := ι) (B := S)
    ErgodicSMul Γ (ι → S) (Measure.infinitePi fun _ => ν) := by
  let := arrowAction (G := Γ) (A := ι) (B := S)
  exact
    { measure_preimage_smul g s hs :=
        (MeasurePreserving.mk (by fun_prop) (Measure.map_infinitePi_infinitePi_of_inj
          (P := fun _ : ι => ν) (MulAction.injective g⁻¹))).measure_preimage hs.nullMeasurableSet
      aeconst_of_forall_preimage_smul_ae_eq hs hsg :=
        eventuallyEmptyOrUniv_of_forall_preimage_ae_eq hproper hs.nullMeasurableSet hsg }

end Probability

end TauCeti
