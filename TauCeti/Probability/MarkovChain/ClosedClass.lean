/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ClosedClass
public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.MarkovChain.Recurrence

/-!
# Path laws on closed sets of states

Restricting a Markov kernel to a measurable closed set preserves the entire trajectory law
under the inclusion of paths, not just its finite-time transition probabilities. In particular,
entrance and positive-return times have the same laws and the same extended nonnegative means.
Recurrence and transience are therefore unchanged by restriction.

These identities allow results for chains on a finite closed communicating class to be used
in an ambient, possibly infinite state space. The initial law may be any finite measure on the
subtype. No countability or topology on the state space is needed. The Markov instance for the
restricted kernel is equivalent to closedness by
`Kernel.isMarkovKernel_subtype_iff_isClosedSet`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §§1.2 and 1.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open TauCeti.Probability
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] {s : Set S}
  (κ : Kernel S S) [IsMarkovKernel κ] (hs : MeasurableSet s)
  [hκs : IsMarkovKernel (κ.subtype hs)]

/-- Including paths of the restricted chain into the ambient space recovers the ambient
chain law, with the initial measure pushed forward by inclusion. -/
theorem markovChainLaw_map_subtype (ν : Measure s) [IsFiniteMeasure ν] :
    (markovChainLaw ν (κ.subtype hs)).map (fun ω n => (ω n).val) =
      markovChainLaw (ν.map Subtype.val) κ := by
  apply Measure.markovChainLaw_map_comp ν (κ.subtype hs) κ measurable_subtype_coe
  intro x
  have h := congrArg (fun η : Kernel s S => η x)
    (κ.map_subtype hs ((Kernel.isMarkovKernel_subtype_iff_isClosedSet hs).mp inferInstance))
  simpa only [Kernel.map_apply _ measurable_subtype_coe, Kernel.comap_apply] using h

include hs hκs in
/-- A chain whose initial measure is carried by a closed subtype stays in that set at all
natural times, on one event of full measure. -/
theorem ae_forall_mem_markovChainLaw_map_subtype (ν : Measure s) [IsFiniteMeasure ν] :
    ∀ᵐ ω ∂markovChainLaw (ν.map Subtype.val) κ, ∀ n, ω n ∈ s := by
  rw [← markovChainLaw_map_subtype κ hs ν]
  have hi : Measurable (fun ω : ℕ → s => fun n => (ω n).val) :=
    measurable_pi_iff.2 fun n => measurable_subtype_coe.comp (measurable_pi_apply n)
  exact (ae_map_iff hi.aemeasurable
    (by simpa only [ofPred_forall, preimage] using
      MeasurableSet.iInter fun n : ℕ => hs.preimage (measurable_pi_apply n))).2
      (ae_of_all _ fun ω n => (ω n).property)

/-- Entrance-time laws are preserved by restriction to a closed set. The target is pulled
back along inclusion; the lower index `m` may be zero (entrance) or one (positive return).
Nonentrance retains its value `⊤`. -/
theorem map_hittingAfter_markovChainLaw_subtype (ν : Measure s) [IsFiniteMeasure ν]
    {t : Set S} (ht : MeasurableSet t) (m : ℕ) :
    (markovChainLaw ν (κ.subtype hs)).map
        (hittingAfter (fun n ω => ω n) (Subtype.val ⁻¹' t) m) =
      (markovChainLaw (ν.map Subtype.val) κ).map
        (hittingAfter (fun n ω => ω n) t m) := by
  have hhit : Measurable (hittingAfter (fun n (ω : ℕ → S) => ω n) t m) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter ht).measurable'
  have hi : Measurable (fun ω : ℕ → s => fun n => (ω n).val) :=
    measurable_pi_iff.2 fun n => measurable_subtype_coe.comp (measurable_pi_apply n)
  rw [← markovChainLaw_map_subtype κ hs ν, Measure.map_map hhit hi]
  -- Both hitting times use exactly the same set of indices, by target preimage membership.
  congr 1

/-- Extended mean entrance times are preserved by restriction. In particular `m = 1` and
`t = {x.val}` compare positive-return means at `x`; nonreturn contributes infinite mean. -/
theorem lintegral_hittingAfter_markovChainLaw_subtype (ν : Measure s) [IsFiniteMeasure ν]
    {t : Set S} (ht : MeasurableSet t) (m : ℕ) :
    (∫⁻ ω, (hittingAfter (fun n ω => ω n) (Subtype.val ⁻¹' t) m ω).recTopCoe ⊤
      (fun n => (n : ℝ≥0∞)) ∂markovChainLaw ν (κ.subtype hs)) =
    ∫⁻ ω, (hittingAfter (fun n ω => ω n) t m ω).recTopCoe ⊤
      (fun n => (n : ℝ≥0∞)) ∂markovChainLaw (ν.map Subtype.val) κ := by
  have hhit : Measurable (hittingAfter (fun n (ω : ℕ → S) => ω n) t m) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter ht).measurable'
  have hhit' : Measurable (hittingAfter (fun n (ω : ℕ → s) => ω n)
      (Subtype.val ⁻¹' t) m) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (ht.preimage measurable_subtype_coe)).measurable'
  have hmean : Measurable (fun n : WithTop ℕ =>
      (n.recTopCoe ⊤ (fun k => (k : ℝ≥0∞)) : ℝ≥0∞)) := measurable_of_countable _
  rw [← MeasureTheory.lintegral_map hmean hhit',
    map_hittingAfter_markovChainLaw_subtype κ hs ν ht, MeasureTheory.lintegral_map hmean hhit]

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] {s : Set S}
  (κ : Kernel S S) [IsMarkovKernel κ] (hs : MeasurableSet s)
  [IsMarkovKernel (κ.subtype hs)]

/-- Restricting to a closed set preserves and reflects recurrence of each of its states. -/
@[simp]
theorem isRecurrent_subtype_iff (x : s) :
    (κ.subtype hs).IsRecurrent x ↔ κ.IsRecurrent x.val := by
  have hclosed := (isMarkovKernel_subtype_iff_isClosedSet hs).mp
    (inferInstance : IsMarkovKernel (κ.subtype hs))
  simp only [isRecurrent_iff_tsum_eq_top,
    subtype_pow_apply κ hs hclosed, image_singleton]

/-- Restricting to a closed set preserves and reflects transience of each of its states. -/
@[simp]
theorem isTransient_subtype_iff (x : s) :
    (κ.subtype hs).IsTransient x ↔ κ.IsTransient x.val := by
  simp only [isTransient_iff, isRecurrent_subtype_iff]

end ProbabilityTheory.Kernel
