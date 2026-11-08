/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.FiniteEntrance
public import TauCeti.Probability.MarkovChain.Reachability
public import TauCeti.Probability.Kernel.ClosedClass.Basic

/-!
# Eventual entrance into a closed communicating class

Every finite-state Markov chain almost surely enters a closed communicating class.
More precisely, almost every path has a finite time after which it stays in one such
class. The class and entrance time may depend on the path, and no irreducibility
assumption is made. Both assertions hold for arbitrary initial measures and transfer
to processes on arbitrary measurable sample spaces through their path laws.

The structural accessibility theorem for finite kernels and the finite-state hitting
theorem supply entrance. Reachability along almost every chain path then supplies
permanence in the entered class; no stopping-time or conditional-law choice is needed.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.2–1.3.
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
