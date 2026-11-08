/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.MarkovChain
public import TauCeti.Probability.Kernel.Reachability

/-!
# Reachability along Markov-chain paths

On a countable state space, almost every path of a Markov chain moves only along
positive-mass transitions. Consequently every later state is reachable from every earlier
state, simultaneously for all pairs of times. This connects the kernel's reachability
relation to pathwise arguments about closed sets and communicating classes.

The initial measure can be arbitrary. The assertion also transfers to any realization
with the same path law.
-/

public section

open MeasureTheory ProbabilityTheory Set TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

private theorem measurableSet_forall_reaches (κ : Kernel S S) :
    MeasurableSet {w : ℕ → S | ∀ m n, m ≤ n → κ.Reaches (w m) (w n)} := by
  simp only [ofPred_forall]
  measurability

/-- Almost every chain path respects reachability between all ordered pairs of times.
No finiteness or normalization of the initial measure is required. -/
theorem ae_forall_reaches_markovChainLaw (κ : Kernel S S) [IsMarkovKernel κ]
    (ν : Measure S) :
    ∀ᵐ w ∂markovChainLaw ν κ, ∀ m n, m ≤ n → κ.Reaches (w m) (w n) := by
  have hdirac (x : S) : ∀ᵐ w ∂markovChainLaw (Measure.dirac x) κ,
      ∀ m n, m ≤ n → κ.Reaches (w m) (w n) := by
    have hstep : ∀ᵐ w ∂markovChainLaw (Measure.dirac x) κ,
        ∀ n, κ.Reaches (w n) (w (n + 1)) := by
      refine ae_all_iff.2 fun n => ?_
      have hp : MeasurableSet {p : S × S | κ.Reaches p.1 p.2} :=
        (Set.to_countable _).measurableSet
      apply (ae_map_iff (μ := markovChainLaw (Measure.dirac x) κ)
        (p := fun p : S × S => κ.Reaches p.1 p.2)
        (f := fun w : ℕ → S => (w n, w (n + 1))) (by fun_prop) hp).1
      rw [markovChainLaw_map_pair_succ, Measure.ae_compProd_iff hp]
      exact ae_of_all _ fun y => ae_iff_of_countable.2 fun z hz =>
        reaches_of_pos (pos_iff_ne_zero.2 hz)
    filter_upwards [hstep] with w hw m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact Reaches.refl _
    | succ n _ ih => exact ih.trans (hw n)
  rw [Measure.markovChainLaw_eq_comp]
  exact Measure.ae_comp_of_ae_ae (κ.measurableSet_forall_reaches) (ae_of_all _ fun x => by
    simpa only [markovChainKernel_apply] using hdirac x)

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {S Ω : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace Ω] {κ : Kernel S S} [IsMarkovKernel κ]
  {ν : Measure S} {μ : Measure Ω} {X : ℕ → Ω → S}

/-- Reachability along all pairs of observation times holds in every realization of a
countable-state chain, not just on the canonical path space. -/
theorem ae_forall_reaches_markovChainLaw
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ) :
    ∀ᵐ ω ∂μ, ∀ m n, m ≤ n → κ.Reaches (X m ω) (X n ω) := by
  exact (h.ae_iff (measurableSet_setOfPred.1 (κ.measurableSet_forall_reaches))).2
    (κ.ae_forall_reaches_markovChainLaw ν)

end ProbabilityTheory.HasLaw
