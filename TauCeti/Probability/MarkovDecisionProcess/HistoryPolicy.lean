/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
public import TauCeti.Probability.Kernel.IonescuTulcea.Traj
public import TauCeti.Probability.Kernel.PMF
import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# History-dependent policies and their trajectory laws

A controller of a Markov decision process with states `S` and actions `A` observes, at each time,
the current state and the whole past, and draws an action at random. Such a
**history-dependent randomized policy** `π : HistoryPolicy S A` is a Markov kernel `π.first`
choosing the action at time `0` from the initial state, and Markov kernels `π.next n` choosing the
action at time `n + 1` from the state-action history up to time `n` and the state at time `n + 1`.
Markov policies `π : ℕ → S → PMF A` and randomized stationary policies `π : S → PMF A` are the
special cases `ofMarkov π` and `ofStationary π`, which look only at the current state.

Given the law of the next state as a Markov kernel `τ : Kernel (S × A) S` of the current state and
action, a policy `π` and an initial state `s`, the **trajectory law** `π.trajLaw τ s` is the law
on `ℕ → S × A` of the state-action process. It is the Ionescu-Tulcea measure
`Kernel.trajMeasure` started from `dirac s ⊗ₘ π.first` whose step from the history up to time `n`
is `π.stepKernel τ n`: the next state is drawn from `τ` at the last state-action pair, then the
next action from `π.next n`. The construction needs no countability; for a Markov decision process
with transition laws `trans : S → A → PMF S` on countable state and action spaces with measurable
singletons, `τ` is `Kernel.ofPMF (fun p ↦ trans p.1 p.2)`.

## Main statements

* `HistoryPolicy.trajLaw_map_eval_zero`: the pair at time `0` has law `dirac s ⊗ₘ π.first`, so
  the state at time `0` is `s` and the action at time `0` has law `π.first s`
  (`trajLaw_ae_fst_zero`, `trajLaw_map_snd_zero`);
* `HistoryPolicy.trajLaw_map_frestrictLe_fst_succ`: given the history up to time `n`, the state at
  time `n + 1` has law `τ (sₙ, aₙ)`;
* `HistoryPolicy.trajLaw_map_frestrictLe_snd_succ`: given the history up to time `n` and the
  state at time `n + 1`, the action at time `n + 1` has law `π.next n`;
* `HistoryPolicy.condDistrib_fst_succ_trajLaw`, `HistoryPolicy.condDistrib_snd_succ_trajLaw`:
  the same two statements for Mathlib's regular conditional distributions;
* `HistoryPolicy.trajLaw_ofMarkov_map_eval_succ`: under a Markov policy `π`, the action at time
  `n + 1` has conditional law `π (n + 1) sₙ₊₁` given the state `sₙ₊₁`.

## References

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley,
  1994, Sections 2.1.5 and 2.1.6.
-/

public section

noncomputable section

open Finset MeasureTheory ProbabilityTheory Preorder

namespace TauCeti

/-- A history-dependent randomized policy with states `S` and actions `A`: the Markov kernel
`first` draws the action at time `0` from the initial state, and the Markov kernel `next n` draws
the action at time `n + 1` from the state-action history up to time `n` and the state at time
`n + 1`. -/
@[ext]
structure HistoryPolicy (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  /-- The kernel drawing the action at time `0` from the initial state. -/
  first : Kernel S A
  /-- The kernel drawing the action at time `n + 1` from the history up to time `n` and the state
  at time `n + 1`. -/
  next (n : ℕ) : Kernel ((Π _ : Iic n, S × A) × S) A
  /-- The action at time `0` is drawn from a probability measure. -/
  isMarkovKernel_first : IsMarkovKernel first
  /-- The action at each later time is drawn from a probability measure. -/
  isMarkovKernel_next (n : ℕ) : IsMarkovKernel (next n)

namespace HistoryPolicy

attribute [instance] isMarkovKernel_first isMarkovKernel_next

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

section Markov

variable [Countable S] [MeasurableSingletonClass S]

/-- The history-dependent policy of a Markov policy `π : ℕ → S → PMF A`, which draws the action at
time `n` from `π n` at the current state and ignores the rest of the history. -/
def ofMarkov (π : ℕ → S → PMF A) : HistoryPolicy S A where
  first := Kernel.ofPMF (π 0)
  next n := (Kernel.ofPMF (π (n + 1))).comap Prod.snd measurable_snd
  isMarkovKernel_first := inferInstance
  isMarkovKernel_next _ := inferInstance

/-- Under a Markov policy, the action at time `0` is drawn from `π 0` at the initial state. -/
@[simp]
theorem ofMarkov_first (π : ℕ → S → PMF A) : (ofMarkov π).first = Kernel.ofPMF (π 0) := (rfl)

/-- Under a Markov policy, the kernel choosing the action at time `n + 1` reads only the state at
time `n + 1`. -/
@[simp]
theorem ofMarkov_next (π : ℕ → S → PMF A) (n : ℕ) :
    (ofMarkov π).next n = (Kernel.ofPMF (π (n + 1))).comap Prod.snd measurable_snd := (rfl)

/-- Under a Markov policy, the action at time `n + 1` is drawn from `π (n + 1)` at the state at
time `n + 1`, whatever the history. -/
theorem ofMarkov_next_apply (π : ℕ → S → PMF A) (n : ℕ) (h : Π _ : Iic n, S × A) (s : S) :
    (ofMarkov π).next n (h, s) = (π (n + 1) s).toMeasure := by
  simp [Kernel.comap_apply, Kernel.ofPMF_apply]

/-- The history-dependent policy of a randomized stationary policy `π : S → PMF A`, which draws
every action from `π` at the current state. -/
def ofStationary (π : S → PMF A) : HistoryPolicy S A :=
  ofMarkov fun _ ↦ π

/-- `ofStationary π` is the Markov policy that plays `π` at every time. -/
theorem ofStationary_def (π : S → PMF A) : ofStationary π = ofMarkov fun _ ↦ π := (rfl)

/-- Under a stationary policy, the action at time `0` is drawn from `π` at the initial state. -/
@[simp]
theorem ofStationary_first (π : S → PMF A) : (ofStationary π).first = Kernel.ofPMF π := (rfl)

/-- Under a stationary policy, every later action is drawn from `π` at the current state. -/
@[simp]
theorem ofStationary_next (π : S → PMF A) (n : ℕ) :
    (ofStationary π).next n = (Kernel.ofPMF π).comap Prod.snd measurable_snd := (rfl)

end Markov

section Traj

variable (τ : Kernel (S × A) S) (π : HistoryPolicy S A)

/-- One step of the trajectory under the policy `π`: from the state-action history up to time
`n`, draw the next state from `τ` at the last pair, then the next action from `π.next n`. -/
def stepKernel (n : ℕ) : Kernel (Π _ : Iic n, S × A) (S × A) :=
  τ.comap (fun h ↦ h ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) ⊗ₖ π.next n

/-- The defining formula of `stepKernel`. -/
theorem stepKernel_def (n : ℕ) :
    π.stepKernel τ n =
      τ.comap (fun h ↦ h ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) ⊗ₖ π.next n := (rfl)

variable [IsMarkovKernel τ]

instance (n : ℕ) : IsMarkovKernel (π.stepKernel τ n) := by
  rw [stepKernel_def]
  infer_instance

/-- The trajectory law of the policy `π` from the initial state `s`, for the law `τ` of the next
state given the current state and action: the law on `ℕ → S × A` of the state-action process. -/
def trajLaw (s : S) : Measure (ℕ → S × A) :=
  Kernel.trajMeasure (Measure.dirac s ⊗ₘ π.first) (π.stepKernel τ)

/-- The defining formula of `trajLaw`. -/
theorem trajLaw_def (s : S) :
    π.trajLaw τ s = Kernel.trajMeasure (Measure.dirac s ⊗ₘ π.first) (π.stepKernel τ) := (rfl)

instance (s : S) : IsProbabilityMeasure (π.trajLaw τ s) := by
  rw [trajLaw_def]
  infer_instance

variable {τ π} {s : S}

/-- The state-action pair at time `0` has law `dirac s ⊗ₘ π.first`. -/
@[simp]
theorem trajLaw_map_eval_zero : (π.trajLaw τ s).map (fun ω ↦ ω 0) = Measure.dirac s ⊗ₘ π.first :=
  Kernel.map_eval_zero_trajMeasure

/-- The state at time `0` has law `dirac s`. -/
@[simp]
theorem trajLaw_map_fst_zero : (π.trajLaw τ s).map (fun ω ↦ (ω 0).1) = Measure.dirac s := by
  have h := congrArg (Measure.map Prod.fst) (trajLaw_map_eval_zero (τ := τ) (π := π) (s := s))
  rwa [Measure.map_map measurable_fst (measurable_pi_apply 0), ← Measure.fst,
    Measure.fst_compProd] at h

/-- The trajectory starts at `s`. -/
theorem trajLaw_ae_fst_zero [MeasurableSingletonClass S] : ∀ᵐ ω ∂π.trajLaw τ s, (ω 0).1 = s :=
  HasLaw.ae_eq_of_dirac ⟨(measurable_fst.comp (measurable_pi_apply 0)).aemeasurable,
    trajLaw_map_fst_zero⟩

/-- The action at time `0` has law `π.first s`. -/
@[simp]
theorem trajLaw_map_snd_zero : (π.trajLaw τ s).map (fun ω ↦ (ω 0).2) = π.first s := by
  have h := congrArg (Measure.map Prod.snd) (trajLaw_map_eval_zero (τ := τ) (π := π) (s := s))
  rwa [Measure.map_map measurable_snd (measurable_pi_apply 0), ← Measure.snd,
    Measure.snd_compProd, Measure.dirac_bind π.first.measurable] at h

variable (π τ s) in
/-- The joint law of the history up to time `n` and the pair at time `n + 1` is the law of the
history followed by one step of `π.stepKernel τ n`. -/
theorem trajLaw_map_frestrictLe_succ (n : ℕ) :
    (π.trajLaw τ s).map (fun ω ↦ (frestrictLe n ω, ω (n + 1))) =
      (π.trajLaw τ s).map (frestrictLe n) ⊗ₘ π.stepKernel τ n :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

/-- **The state transition.** Given the history up to time `n`, the state at time `n + 1` has law
`τ (sₙ, aₙ)`: the joint law of the history and that state is the law of the history followed by
`τ` at its last pair. -/
theorem trajLaw_map_frestrictLe_fst_succ (n : ℕ) :
    (π.trajLaw τ s).map (fun ω ↦ (frestrictLe n ω, (ω (n + 1)).1)) =
      (π.trajLaw τ s).map (frestrictLe n) ⊗ₘ
        τ.comap (fun h ↦ h ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) := by
  have hmeas : Measurable fun ω : ℕ → S × A ↦ (frestrictLe n ω, ω (n + 1)) := by fun_prop
  rw [← Measure.fst_compProd ((π.trajLaw τ s).map (frestrictLe n) ⊗ₘ _) (π.next n),
    ← Measure.compProd_assoc, ← stepKernel_def, ← trajLaw_map_frestrictLe_succ,
    Measure.map_map (by fun_prop) hmeas, Measure.fst, Measure.map_map measurable_fst (by fun_prop)]
  -- The two maps agree pointwise by the definition of `MeasurableEquiv.prodAssoc`, which has no
  -- apply lemma.
  rfl

/-- **The action choice.** Given the history up to time `n` and the state at time `n + 1`, the
action at time `n + 1` has law `π.next n`. -/
theorem trajLaw_map_frestrictLe_snd_succ (n : ℕ) :
    (π.trajLaw τ s).map (fun ω ↦ ((frestrictLe n ω, (ω (n + 1)).1), (ω (n + 1)).2)) =
      (π.trajLaw τ s).map (fun ω ↦ (frestrictLe n ω, (ω (n + 1)).1)) ⊗ₘ π.next n := by
  have hmeas : Measurable fun ω : ℕ → S × A ↦ (frestrictLe n ω, ω (n + 1)) := by fun_prop
  rw [trajLaw_map_frestrictLe_fst_succ, ← Measure.compProd_assoc, ← stepKernel_def,
    ← trajLaw_map_frestrictLe_succ, Measure.map_map (by fun_prop) hmeas]
  -- The two maps agree pointwise by the definition of `MeasurableEquiv.prodAssoc`, which has no
  -- apply lemma.
  rfl

/-- **The state transition from the last pair.** The joint law of the pair at time `n` and the
state at time `n + 1` is the law of that pair followed by `τ`. -/
theorem trajLaw_map_eval_fst_succ (n : ℕ) :
    (π.trajLaw τ s).map (fun ω ↦ (ω n, (ω (n + 1)).1)) =
      (π.trajLaw τ s).map (fun ω ↦ ω n) ⊗ₘ τ := by
  have hlast : Measurable fun h : Π _ : Iic n, S × A ↦ h ⟨n, mem_Iic.2 le_rfl⟩ :=
    measurable_pi_apply _
  have h := congrArg (Measure.map (Prod.map (fun h : Π _ : Iic n, S × A ↦ h ⟨n, mem_Iic.2 le_rfl⟩)
    (id : S → S))) (trajLaw_map_frestrictLe_fst_succ (τ := τ) (π := π) (s := s) n)
  rwa [Measure.map_map (hlast.prodMap measurable_id) (by fun_prop),
    Measure.map_prodMap_compProd_comap _ _ hlast,
    Measure.map_map hlast (measurable_frestrictLe n)] at h

/-- **The state transition, as a conditional distribution.** Given the history up to time `n`,
the state at time `n + 1` has regular conditional distribution `τ` at the last pair of the
history. -/
theorem condDistrib_fst_succ_trajLaw [StandardBorelSpace S] [Nonempty S] (n : ℕ) :
    condDistrib (fun ω ↦ (ω (n + 1)).1) (frestrictLe n) (π.trajLaw τ s)
      =ᵐ[(π.trajLaw τ s).map (frestrictLe n)]
        τ.comap (fun h ↦ h ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
    (trajLaw_map_frestrictLe_fst_succ n)

/-- **The action choice, as a conditional distribution.** Given the history up to time `n` and
the state at time `n + 1`, the action at time `n + 1` has regular conditional distribution
`π.next n`. -/
theorem condDistrib_snd_succ_trajLaw [StandardBorelSpace A] [Nonempty A] (n : ℕ) :
    condDistrib (fun ω ↦ (ω (n + 1)).2) (fun ω ↦ (frestrictLe n ω, (ω (n + 1)).1))
      (π.trajLaw τ s) =ᵐ[(π.trajLaw τ s).map fun ω ↦ (frestrictLe n ω, (ω (n + 1)).1)]
        π.next n :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
    (trajLaw_map_frestrictLe_snd_succ n)

/-- **The action choice of a Markov policy.** Under `ofMarkov π`, the pair at time `n + 1` has the
law of the state at time `n + 1` followed by `π (n + 1)`: given that state, the action at time
`n + 1` is drawn from `π (n + 1)` at it. -/
theorem trajLaw_ofMarkov_map_eval_succ [Countable S] [MeasurableSingletonClass S]
    {π : ℕ → S → PMF A} (n : ℕ) :
    ((ofMarkov π).trajLaw τ s).map (fun ω ↦ ω (n + 1)) =
      ((ofMarkov π).trajLaw τ s).map (fun ω ↦ (ω (n + 1)).1) ⊗ₘ Kernel.ofPMF (π (n + 1)) := by
  have hmeas : Measurable
      fun ω : ℕ → S × A ↦ ((frestrictLe n ω, (ω (n + 1)).1), (ω (n + 1)).2) := by
    fun_prop
  have h := congrArg (Measure.map (Prod.map Prod.snd id)) (trajLaw_map_frestrictLe_snd_succ
    (τ := τ) (π := ofMarkov π) (s := s) n)
  rwa [Measure.map_map (measurable_snd.prodMap measurable_id) hmeas, ofMarkov_next,
    Measure.map_prodMap_compProd_comap _ _ measurable_snd,
    Measure.map_map measurable_snd (by fun_prop)] at h

end Traj

end HistoryPolicy

end TauCeti
