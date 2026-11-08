/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.FiniteEntrance
public import TauCeti.Probability.MarkovChain.Reachability
public import TauCeti.Probability.Kernel.ClosedClass.Basic
public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.MarkovChain.Recurrence

/-!
# Entrance into closed communicating classes and restriction of path laws

Every finite-state Markov chain almost surely enters a closed communicating class.
More precisely, almost every path has a finite time after which it stays in one such
class. The class and entrance time may depend on the path, and no irreducibility
assumption is made. Both assertions hold for arbitrary initial measures and transfer
to processes on arbitrary measurable sample spaces through their path laws.

The structural accessibility theorem for finite kernels and the finite-state hitting
theorem supply entrance. Reachability along almost every chain path then supplies
permanence in the entered class; no stopping-time or conditional-law choice is needed.

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

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.2–1.3 and 1.5.
-/

public section

open MeasureTheory ProbabilityTheory Set TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] [Finite S] [MeasurableSingletonClass S]

private theorem exists_pow_apply_isClosedSet_communicatingClass_pos (κ : Kernel S S)
    (x : S) :
    ∃ n, 0 < (κ ^ n) x {y | κ.IsClosedSet (κ.communicatingClass y)} := by
  obtain ⟨y, hxy, hy⟩ := κ.exists_reaches_isClosedSet_communicatingClass x
  obtain ⟨n, hn⟩ := (reaches_def x y).mp hxy
  exact ⟨n, hn.trans_le (measure_mono (singleton_subset_iff.2 hy))⟩

/-- A finite-state chain almost surely enters the union of its closed communicating
classes. Entrance includes time zero, and the initial measure need not be finite. -/
theorem ae_hittingAfter_isClosedSet_communicatingClass_ne_top (κ : Kernel S S)
    [IsMarkovKernel κ] (ν : Measure S) :
    ∀ᵐ w ∂markovChainLaw ν κ,
      hittingAfter (fun n w => w n) {x | κ.IsClosedSet (κ.communicatingClass x)} 0 w ≠ ⊤ := by
  exact κ.ae_hittingAfter_ne_top_of_finite (Set.toFinite _).measurableSet
    (κ.exists_pow_apply_isClosedSet_communicatingClass_pos) ν

/-- Almost every path of a finite-state chain eventually stays in a single closed
communicating class. Both its representative and the time may depend on the path. -/
theorem ae_exists_forall_mem_isClosedSet_communicatingClass (κ : Kernel S S)
    [IsMarkovKernel κ] (ν : Measure S) :
    ∀ᵐ w ∂markovChainLaw ν κ, ∃ n,
      κ.IsClosedSet (κ.communicatingClass (w n)) ∧
        ∀ m, n ≤ m → w m ∈ κ.communicatingClass (w n) := by
  filter_upwards [κ.ae_hittingAfter_isClosedSet_communicatingClass_ne_top ν,
    κ.ae_forall_reaches ν] with w hhit hreach
  have hex : ∃ n, κ.IsClosedSet (κ.communicatingClass (w n)) := by
    simpa only [ne_eq, hittingAfter_eq_top_iff, zero_le, forall_const, mem_ofPred_eq,
      not_forall, not_not] using hhit
  obtain ⟨n, hn⟩ := hex
  refine ⟨n, hn, fun m hnm => ?_⟩
  exact isClosedSet_iff_forall_reaches_mem.mp hn (w n)
    (by simp) (w m) (hreach n m hnm)

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {S Ω : Type*} [MeasurableSpace S] [Finite S] [MeasurableSingletonClass S]
  [MeasurableSpace Ω] {κ : Kernel S S} [IsMarkovKernel κ]
  {ν : Measure S} {μ : Measure Ω} {X : ℕ → Ω → S}

/-- Every realization of a finite-state chain almost surely enters the union of its
closed communicating classes. The entrance time is zero if the initial state is in it. -/
theorem ae_hittingAfter_isClosedSet_communicatingClass_ne_top
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ) :
    ∀ᵐ ω ∂μ,
      hittingAfter X {x | κ.IsClosedSet (κ.communicatingClass x)} 0 ω ≠ ⊤ := by
  exact h.ae_hittingAfter_ne_top_of_finite (Set.toFinite _).measurableSet
    (κ.exists_pow_apply_isClosedSet_communicatingClass_pos)

/-- Almost every path of any realization of a finite-state chain eventually stays in
one closed communicating class. No canonical sample space is imposed. -/
theorem ae_exists_forall_mem_isClosedSet_communicatingClass
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ) :
    ∀ᵐ ω ∂μ, ∃ n,
      κ.IsClosedSet (κ.communicatingClass (X n ω)) ∧
        ∀ m, n ≤ m → X m ω ∈ κ.communicatingClass (X n ω) := by
  have hm : MeasurableSet {w : ℕ → S | ∃ n,
      κ.IsClosedSet (κ.communicatingClass (w n)) ∧
        ∀ m, n ≤ m → w m ∈ κ.communicatingClass (w n)} := by
    simp only [ofPred_exists, ofPred_and, ofPred_forall]
    measurability
  exact (h.ae_iff (measurableSet_setOfPred.1 hm)).2
    (κ.ae_exists_forall_mem_isClosedSet_communicatingClass ν)

end ProbabilityTheory.HasLaw

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
