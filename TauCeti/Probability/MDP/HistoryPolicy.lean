/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.Probability.Kernel.PMF

/-!
# History-dependent randomized policies

`TauCeti.HistoryPolicy S A` specifies an initial action kernel and an action kernel after
each finite history. At time `n + 1`, the history contains the state-action pairs at times
`0, …, n`, together with the current state. Both kernels are Markov kernels, so their rows
are probability measures.

`HistoryPolicy.ofMarkov` embeds time-dependent PMF policies, and `HistoryPolicy.ofStationary`
embeds stationary PMF policies. Only the state space needs to be countable with measurable
singletons: `Kernel.comap` pulls the state-indexed PMF kernel back along the current-state
projection.
The action space can be any measurable space.

The policy conventions follow M. L. Puterman, *Markov Decision Processes* (1994), §§2.1.6
and 5.3. The constructions reuse Tau Ceti's `Kernel.ofPMF` and Mathlib's `Kernel.comap`.
-/

public section

noncomputable section

open ProbabilityTheory

namespace TauCeti

variable (S A : Type*) [MeasurableSpace S] [MeasurableSpace A]

/-- A randomized policy whose action may depend measurably on the entire finite history.

The initial kernel uses the initial state. The kernel `next n` chooses the action at time
`n + 1`, given the state-action pairs through time `n` and the current state. -/
structure HistoryPolicy where
  /-- The initial action distribution, given the initial state. -/
  first : Kernel S A
  /-- The next action distribution, given the past state-action pairs and current state. -/
  next (n : ℕ) : Kernel ((Π _i : Finset.Iic n, S × A) × S) A
  /-- Every initial action distribution has total mass one. -/
  isMarkovKernel_first : IsMarkovKernel first
  /-- Every later action distribution has total mass one. -/
  isMarkovKernel_next : ∀ n, IsMarkovKernel (next n)

attribute [instance] HistoryPolicy.isMarkovKernel_first HistoryPolicy.isMarkovKernel_next

namespace HistoryPolicy

variable {S A}

/-- Policies are equal when their initial and subsequent action kernels agree. -/
@[ext]
theorem ext {π ρ : HistoryPolicy S A} (hfirst : π.first = ρ.first)
    (hnext : ∀ n, π.next n = ρ.next n) : π = ρ := by
  cases π
  cases ρ
  cases hfirst
  cases funext hnext
  rfl

variable [Countable S] [MeasurableSingletonClass S]

/-- A time-dependent Markov PMF policy viewed as a history-dependent policy.

The action at time `n + 1` uses only the current state, so the historical coordinates need
no countability or measurable-singleton assumptions. -/
def ofMarkov (π : ℕ → S → PMF A) : HistoryPolicy S A where
  first := Kernel.ofPMF (π 0)
  next n := (Kernel.ofPMF (π (n + 1))).comap Prod.snd measurable_snd
  isMarkovKernel_first := inferInstance
  isMarkovKernel_next _ := inferInstance

/-- The initial kernel of a Markov policy is its time-zero PMF kernel. -/
theorem ofMarkov_first (π : ℕ → S → PMF A) :
    (ofMarkov π).first = Kernel.ofPMF (π 0) := by rfl

/-- A Markov policy discards the past and applies the PMF kernel at the next time. -/
theorem ofMarkov_next (π : ℕ → S → PMF A) (n : ℕ) :
    (ofMarkov π).next n = (Kernel.ofPMF (π (n + 1))).comap Prod.snd measurable_snd := by rfl

/-- The initial action measure of a Markov policy. -/
@[simp]
theorem ofMarkov_first_apply (π : ℕ → S → PMF A) (s : S) :
    (ofMarkov π).first s = (π 0 s).toMeasure := by
  rw [ofMarkov_first, Kernel.ofPMF_apply]

/-- The next action measure of a Markov policy depends only on the current state. -/
@[simp]
theorem ofMarkov_next_apply (π : ℕ → S → PMF A) (n : ℕ)
    (h : (Π _i : Finset.Iic n, S × A) × S) :
    (ofMarkov π).next n h = (π (n + 1) h.2).toMeasure := by
  rw [ofMarkov_next, Kernel.comap_apply, Kernel.ofPMF_apply]

/-- A stationary PMF policy viewed as a history-dependent policy. -/
def ofStationary (π : S → PMF A) : HistoryPolicy S A := ofMarkov fun _ => π

/-- A stationary policy is the Markov policy with constant time dependence. -/
theorem ofStationary_eq_ofMarkov (π : S → PMF A) :
    ofStationary π = ofMarkov (fun _ => π) := by rfl

/-- The initial action measure of a stationary policy. -/
@[simp]
theorem ofStationary_first_apply (π : S → PMF A) (s : S) :
    (ofStationary π).first s = (π s).toMeasure := by
  rw [ofStationary_eq_ofMarkov, ofMarkov_first_apply]

/-- The next action measure of a stationary policy depends only on the current state. -/
@[simp]
theorem ofStationary_next_apply (π : S → PMF A) (n : ℕ)
    (h : (Π _i : Finset.Iic n, S × A) × S) :
    (ofStationary π).next n h = (π h.2).toMeasure := by
  rw [ofStationary_eq_ofMarkov, ofMarkov_next_apply]

end HistoryPolicy

end TauCeti
