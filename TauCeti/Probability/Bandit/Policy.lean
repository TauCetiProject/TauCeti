/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.IonescuTulcea.Traj
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Bandit policies and the law of their interaction with an environment

A bandit learner chooses, in each round `t : ℕ`, an arm in a measurable space `ι` and then
observes a real reward. A trajectory is `ω : ℕ → ι × ℝ`, with arm `(ω t).1` and reward
`(ω t).2` in round `t`; the history through round `n` is `Preorder.frestrictLe n ω`.

* `TauCeti.Bandit.Policy ι` is a history-dependent randomized policy: the law `first` of the arm
  of round `0` and Markov kernels `next n` choosing the arm of round `n + 1` from the history
  through round `n`.
* An environment is a sequence `ρ : ℕ → Kernel ι ℝ` of Markov kernels: the reward of round `t` is
  drawn from `ρ t` at the arm played.
* `TauCeti.Bandit.envLaw ρ π` is the law on trajectories of the interaction of `π` with `ρ`,
  built by Mathlib's Ionescu–Tulcea construction `ProbabilityTheory.Kernel.trajMeasure` from the
  joint step `TauCeti.Bandit.envStep ρ π n`, which draws the next arm from the policy and then
  its reward from the environment.
* `TauCeti.Bandit.Policy.PlaysIn π S` says that the policy chooses, at every history, an arm in
  the prescribed set `S t ω`. When `ι` is countable with measurable singletons, under it the arm
  of every round lies in its set almost surely (`TauCeti.Bandit.ae_forall_mem_of_playsIn`).

We prove the joint and conditional laws of the next arm and reward given the history, and their
integral form; that these identities characterize `envLaw ρ π` (`TauCeti.Bandit.eq_envLaw`); and
that the law depends on the kernels of the policy only almost everywhere
(`TauCeti.Bandit.envLaw_congr`). Deterministic policies (`TauCeti.Bandit.Policy.deterministic`)
play in the sets containing their choices.

The policy of a Markov decision process, `TauCeti.HistoryPolicy`, conditions each action on the
current state; a bandit has no state, and its reward is drawn after the arm, so its trajectory
pairs each arm with the reward that follows it.

See T. Lattimore and C. Szepesvári, *Bandit Algorithms* (2020), Definition 4.7 for policies and
Sections 4.6–4.7 and Proposition 4.8 for the law of the interaction and its uniqueness.
-/

public section

noncomputable section

open Finset MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Bandit

variable (ι : Type*) [MeasurableSpace ι]

/-- A history-dependent randomized bandit policy on the arms `ι` with real rewards: the law
`first` of the arm of round `0` and, for each `n`, a Markov kernel `next n` choosing the arm of
round `n + 1` from the arms and rewards of rounds `0, …, n`. -/
structure Policy where
  /-- The law of the arm of round `0`. -/
  first : Measure ι
  /-- The law of the arm of round `n + 1`, given the arms and rewards of rounds `0, …, n`. -/
  next (n : ℕ) : Kernel ((_ : Iic n) → ι × ℝ) ι
  /-- The law of the first arm is a probability measure. -/
  isProbabilityMeasure_first : IsProbabilityMeasure first
  /-- Every later arm distribution has total mass one. -/
  isMarkovKernel_next : ∀ n, IsMarkovKernel (next n)

attribute [instance] Policy.isProbabilityMeasure_first Policy.isMarkovKernel_next

variable {ι}

namespace Policy

/-- Policies are equal when their first laws and their kernels agree. -/
@[ext]
theorem ext {π π' : Policy ι} (hfirst : π.first = π'.first) (hnext : ∀ n, π.next n = π'.next n) :
    π = π' := by
  cases π
  cases π'
  cases hfirst
  cases funext hnext
  rfl

end Policy

section Law

variable (ρ : ℕ → Kernel ι ℝ) (π : Policy ι)

/-- The joint step of the interaction after round `n`: the arm of round `n + 1` is drawn from the
policy at the history through round `n`, and its reward from `ρ (n + 1)` at that arm. -/
def envStep (n : ℕ) : Kernel ((_ : Iic n) → ι × ℝ) (ι × ℝ) :=
  π.next n ⊗ₖ (ρ (n + 1)).prodMkLeft ((_ : Iic n) → ι × ℝ)

/-- The joint step is the composition-product of the policy's kernel and the environment. -/
theorem envStep_def (n : ℕ) :
    envStep ρ π n = π.next n ⊗ₖ (ρ (n + 1)).prodMkLeft ((_ : Iic n) → ι × ℝ) := (rfl)

instance (n : ℕ) [IsMarkovKernel (ρ (n + 1))] : IsMarkovKernel (envStep ρ π n) := by
  rw [envStep_def]
  infer_instance

/-- The arm marginal of the joint step is the policy's kernel. -/
@[simp]
theorem fst_envStep (n : ℕ) [IsMarkovKernel (ρ (n + 1))] : (envStep ρ π n).fst = π.next n := by
  rw [envStep_def, Kernel.fst_compProd]

variable [∀ t, IsMarkovKernel (ρ t)]

/-- The law on trajectories `ℕ → ι × ℝ` of the interaction of the policy `π` with the environment
`ρ`: the first arm is drawn from `π.first` and its reward from `ρ 0`, and after round `n` the next
arm and reward are drawn from the joint step `envStep ρ π n`. -/
def envLaw : Measure (ℕ → ι × ℝ) :=
  Kernel.trajMeasure (X := fun _ ↦ ι × ℝ) (π.first ⊗ₘ ρ 0) (envStep ρ π)

/-- The law of the interaction is the trajectory measure of the joint steps. -/
theorem envLaw_def :
    envLaw ρ π = Kernel.trajMeasure (X := fun _ ↦ ι × ℝ) (π.first ⊗ₘ ρ 0) (envStep ρ π) := (rfl)

instance : IsProbabilityMeasure (envLaw ρ π) := by
  rw [envLaw_def]
  infer_instance

/-- In round `0`, the arm and reward have law `π.first ⊗ₘ ρ 0`. -/
@[simp]
theorem envLaw_map_eval_zero : (envLaw ρ π).map (fun ω ↦ ω 0) = π.first ⊗ₘ ρ 0 := by
  rw [envLaw_def, Kernel.trajMeasure_map_eval_zero]

/-- The arm of round `0` has law `π.first`. -/
@[simp]
theorem envLaw_map_arm_zero : (envLaw ρ π).map (fun ω ↦ (ω 0).1) = π.first := by
  calc
    _ = ((envLaw ρ π).map (fun ω ↦ ω 0)).fst :=
      (Measure.map_map measurable_fst (measurable_pi_apply 0)).symm
    _ = _ := by rw [envLaw_map_eval_zero, Measure.fst_compProd]

/-- The law of the history through round `n` and the arm and reward of round `n + 1` is the law of
the history followed by the joint step. -/
theorem envLaw_map_history_succ (n : ℕ) :
    (envLaw ρ π).map (fun ω ↦ (frestrictLe n ω, ω (n + 1))) =
      (envLaw ρ π).map (frestrictLe n) ⊗ₘ envStep ρ π n := by
  rw [envLaw_def]
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

/-- The law of the history through round `n` and the arm of round `n + 1` is the law of the
history followed by the policy's kernel. -/
theorem envLaw_map_history_arm_succ (n : ℕ) :
    (envLaw ρ π).map (fun ω ↦ (frestrictLe n ω, (ω (n + 1)).1)) =
      (envLaw ρ π).map (frestrictLe n) ⊗ₘ π.next n := by
  have h := congrArg (fun μ : Measure (((_ : Iic n) → ι × ℝ) × (ι × ℝ)) ↦
    μ.map (Prod.map id Prod.fst)) (envLaw_map_history_succ ρ π n)
  rw [Measure.map_map (measurable_id.prodMap measurable_fst) (by fun_prop),
    ← Measure.compProd_map measurable_fst, ← Kernel.fst_eq, fst_envStep] at h
  exact h

/-- The law of the history through round `n`, the arm of round `n + 1` and its reward is the law
of the history and the arm followed by the environment at that arm. -/
theorem envLaw_map_history_arm_reward_succ (n : ℕ) :
    (envLaw ρ π).map (fun ω ↦ ((frestrictLe n ω, (ω (n + 1)).1), (ω (n + 1)).2)) =
      (envLaw ρ π).map (fun ω ↦ (frestrictLe n ω, (ω (n + 1)).1)) ⊗ₘ
        (ρ (n + 1)).prodMkLeft ((_ : Iic n) → ι × ℝ) := by
  have h := congrArg (fun μ : Measure (((_ : Iic n) → ι × ℝ) × (ι × ℝ)) ↦
    μ.map MeasurableEquiv.prodAssoc.symm) (envLaw_map_history_succ ρ π n)
  rw [Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop), envStep_def,
    Measure.compProd_assoc, ← envLaw_map_history_arm_succ] at h
  exact h

/-- In round `0`, a function of the arm and reward integrates as the reward integral at each arm,
averaged over the law of the first arm. -/
theorem lintegral_envLaw_zero {f : ι × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (ω 0) ∂envLaw ρ π = ∫⁻ a, ∫⁻ x, f (a, x) ∂ρ 0 a ∂π.first := by
  rw [← lintegral_map hf (measurable_pi_apply 0), envLaw_map_eval_zero,
    Measure.lintegral_compProd hf]

/-- The integral form of `envLaw_map_history_succ`: a function of the history through round `n`
and of the arm and reward of round `n + 1` integrates as the reward integral at each arm, averaged
over the policy's choice at the history. -/
theorem lintegral_envLaw_succ (n : ℕ) {f : ((_ : Iic n) → ι × ℝ) → ι × ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ ω, f (frestrictLe n ω) (ω (n + 1)) ∂envLaw ρ π =
      ∫⁻ ω, ∫⁻ a, ∫⁻ x, f (frestrictLe n ω) (a, x) ∂ρ (n + 1) a
        ∂π.next n (frestrictLe n ω) ∂envLaw ρ π := by
  have hstep (h : (_ : Iic n) → ι × ℝ) :
      ∫⁻ p, f h p ∂envStep ρ π n h = ∫⁻ a, ∫⁻ x, f h (a, x) ∂ρ (n + 1) a ∂π.next n h := by
    rw [envStep_def, Kernel.lintegral_compProd _ _ _ (f := f h) (hf.comp measurable_prodMk_left)]
    simp
  calc ∫⁻ ω, f (frestrictLe n ω) (ω (n + 1)) ∂envLaw ρ π
      = ∫⁻ q, Function.uncurry f q ∂(envLaw ρ π).map (fun ω ↦ (frestrictLe n ω, ω (n + 1))) := by
        rw [lintegral_map hf (by fun_prop)]
        simp only [Function.uncurry_apply_pair]
    _ = ∫⁻ h, ∫⁻ p, f h p ∂envStep ρ π n h ∂(envLaw ρ π).map (frestrictLe n) := by
        rw [envLaw_map_history_succ, Measure.lintegral_compProd hf]
        simp
    _ = ∫⁻ ω, ∫⁻ p, f (frestrictLe n ω) p ∂envStep ρ π n (frestrictLe n ω) ∂envLaw ρ π :=
        lintegral_map hf.lintegral_kernel_prod_right' (measurable_frestrictLe n)
    _ = _ := by simp_rw [hstep]

/-- Given the history through round `n`, the arm and reward of round `n + 1` have the conditional
law `envStep ρ π n`. -/
theorem condDistrib_envLaw_succ [StandardBorelSpace ι] [Nonempty ι] (n : ℕ) :
    condDistrib (fun ω ↦ ω (n + 1)) (frestrictLe n) (envLaw ρ π)
      =ᵐ[(envLaw ρ π).map (frestrictLe n)] envStep ρ π n :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
    (envLaw_map_history_succ ρ π n)

/-- Given the history through round `n`, the arm of round `n + 1` has the conditional law
`π.next n`. -/
theorem condDistrib_arm_succ [StandardBorelSpace ι] [Nonempty ι] (n : ℕ) :
    condDistrib (fun ω ↦ (ω (n + 1)).1) (frestrictLe n) (envLaw ρ π)
      =ᵐ[(envLaw ρ π).map (frestrictLe n)] π.next n :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
    (envLaw_map_history_arm_succ ρ π n)

/-- Given the history through round `n` and the arm of round `n + 1`, the reward of round `n + 1`
has the conditional law `ρ (n + 1)` at that arm. -/
theorem condDistrib_reward_succ (n : ℕ) :
    condDistrib (fun ω ↦ (ω (n + 1)).2) (fun ω ↦ (frestrictLe n ω, (ω (n + 1)).1)) (envLaw ρ π)
      =ᵐ[(envLaw ρ π).map (fun ω ↦ (frestrictLe n ω, (ω (n + 1)).1))]
        (ρ (n + 1)).prodMkLeft ((_ : Iic n) → ι × ℝ) :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
    (envLaw_map_history_arm_reward_succ ρ π n)

/-- Given the arm of round `0`, the reward of round `0` has the conditional law `ρ 0` at that
arm. -/
theorem condDistrib_reward_zero :
    condDistrib (fun ω ↦ (ω 0).2) (fun ω ↦ (ω 0).1) (envLaw ρ π) =ᵐ[π.first] ρ 0 := by
  rw [← envLaw_map_arm_zero ρ π]
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop) ?_
  rw [envLaw_map_arm_zero, ← envLaw_map_eval_zero]

/-- **Uniqueness of the law of the interaction.** A measure on trajectories under which the arm
and reward of round `0` have law `π.first ⊗ₘ ρ 0`, and under which the history through each round
`n` is followed by the joint step `envStep ρ π n`, is `envLaw ρ π`. -/
theorem eq_envLaw {P : Measure (ℕ → ι × ℝ)} (h₀ : P.map (fun ω ↦ ω 0) = π.first ⊗ₘ ρ 0)
    (hsucc : ∀ n, P.map (fun ω ↦ (frestrictLe n ω, ω (n + 1))) =
      P.map (frestrictLe n) ⊗ₘ envStep ρ π n) :
    P = envLaw ρ π :=
  Kernel.eq_trajMeasure (X := fun _ ↦ ι × ℝ) h₀ hsucc

/-- **Congruence of the law of the interaction.** Two policies with the same first law, whose
kernels agree at almost every history of the interaction of the first, have the same law of the
interaction. -/
theorem envLaw_congr {π π' : Policy ι} (hfirst : π.first = π'.first)
    (hnext : ∀ n, π.next n =ᵐ[(envLaw ρ π).map (frestrictLe n)] π'.next n) :
    envLaw ρ π = envLaw ρ π' := by
  have hstep (n : ℕ) : envStep ρ π n =ᵐ[(envLaw ρ π).map (frestrictLe n)] envStep ρ π' n := by
    filter_upwards [hnext n] with h hh
    ext s hs
    rw [envStep_def, envStep_def, Kernel.compProd_apply hs, Kernel.compProd_apply hs, hh]
  rw [envLaw_def, Kernel.trajMeasure_congr hstep, envLaw_def, hfirst]

end Law

namespace Policy

/-- The policy `π` plays in the sets `S`: its arm of round `0` lies in `S 0 ω`, and its arm of
round `n + 1` after the history `frestrictLe n ω` lies in `S (n + 1) ω`, with probability one, for
every trajectory `ω`. The condition is imposed at every history, whether or not the interaction
reaches it. -/
def PlaysIn (π : Policy ι) (S : ℕ → (ℕ → ι × ℝ) → Set ι) : Prop :=
  (∀ ω, π.first (S 0 ω) = 1) ∧ ∀ n ω, π.next n (frestrictLe n ω) (S (n + 1) ω) = 1

/-- Unfolding `Policy.PlaysIn`. -/
theorem playsIn_iff {π : Policy ι} {S : ℕ → (ℕ → ι × ℝ) → Set ι} :
    π.PlaysIn S ↔
      (∀ ω, π.first (S 0 ω) = 1) ∧ ∀ n ω, π.next n (frestrictLe n ω) (S (n + 1) ω) = 1 :=
  Iff.rfl

/-- A policy that plays in the sets `S` plays in any larger sets. -/
theorem PlaysIn.mono {π : Policy ι} {S S' : ℕ → (ℕ → ι × ℝ) → Set ι} (hπ : π.PlaysIn S)
    (hSS' : ∀ t ω, S t ω ⊆ S' t ω) : π.PlaysIn S' := by
  have h {μ : Measure ι} [IsProbabilityMeasure μ] {s s' : Set ι} (hs : μ s = 1) (hss' : s ⊆ s') :
      μ s' = 1 :=
    le_antisymm prob_le_one (hs ▸ measure_mono hss')
  exact ⟨fun ω ↦ h (hπ.1 ω) (hSS' 0 ω), fun n ω ↦ h (hπ.2 n ω) (hSS' (n + 1) ω)⟩

/-- The deterministic policy that plays `a₀` in round `0` and `f n` of the history through round
`n` in round `n + 1`. -/
def deterministic (a₀ : ι) (f : (n : ℕ) → ((_ : Iic n) → ι × ℝ) → ι)
    (hf : ∀ n, Measurable (f n)) : Policy ι where
  first := Measure.dirac a₀
  next n := Kernel.deterministic (f n) (hf n)
  isProbabilityMeasure_first := inferInstance
  isMarkovKernel_next _ := inferInstance

variable {a₀ : ι} {f : (n : ℕ) → ((_ : Iic n) → ι × ℝ) → ι} {hf : ∀ n, Measurable (f n)}

/-- The law of the first arm of a deterministic policy is the point mass at `a₀`. -/
@[simp]
theorem deterministic_first : (deterministic a₀ f hf).first = Measure.dirac a₀ := (rfl)

/-- The kernel of round `n + 1` of a deterministic policy is the deterministic kernel of `f n`. -/
@[simp]
theorem deterministic_next (n : ℕ) :
    (deterministic a₀ f hf).next n = Kernel.deterministic (f n) (hf n) := (rfl)

/-- A deterministic policy plays in every family of sets containing its choices. -/
theorem deterministic_playsIn {S : ℕ → (ℕ → ι × ℝ) → Set ι} (h₀ : ∀ ω, a₀ ∈ S 0 ω)
    (hsucc : ∀ n ω, f n (frestrictLe n ω) ∈ S (n + 1) ω) : (deterministic a₀ f hf).PlaysIn S :=
  ⟨fun ω ↦ by simp [Measure.dirac_apply_of_mem (h₀ ω)],
    fun n ω ↦ by simp [Kernel.deterministic_apply, Measure.dirac_apply_of_mem (hsucc n ω)]⟩

/-- With measurable singletons, a deterministic policy plays in the sets `S` exactly when they
contain its choices. -/
theorem deterministic_playsIn_iff [MeasurableSingletonClass ι] {S : ℕ → (ℕ → ι × ℝ) → Set ι} :
    (deterministic a₀ f hf).PlaysIn S ↔
      (∀ ω, a₀ ∈ S 0 ω) ∧ ∀ n ω, f n (frestrictLe n ω) ∈ S (n + 1) ω := by
  refine ⟨fun h ↦ ⟨fun ω ↦ ?_, fun n ω ↦ ?_⟩, fun h ↦ deterministic_playsIn h.1 h.2⟩
  · by_contra hω
    simpa [Measure.dirac_apply, hω] using h.1 ω
  · by_contra hω
    simpa [Kernel.deterministic_apply, Measure.dirac_apply, hω] using h.2 n ω

end Policy

variable [Countable ι] [MeasurableSingletonClass ι]

/-- If the policy `π` plays in the sets `S` then, almost surely for the law of its interaction with
any environment, the arm of every round `t` lies in `S t ω`. No measurability of `S` is needed. -/
theorem ae_forall_mem_of_playsIn (ρ : ℕ → Kernel ι ℝ) [∀ t, IsMarkovKernel (ρ t)] {π : Policy ι}
    {S : ℕ → (ℕ → ι × ℝ) → Set ι} (hπ : π.PlaysIn S) :
    ∀ᵐ ω ∂(envLaw ρ π), ∀ t, (ω t).1 ∈ S t ω := by
  -- In each round the arm played is almost surely an atom of the policy's law at the history,
  -- and an atom lies in every set of full mass, all sets of arms being measurable.
  have hmem {μ : Measure ι} [IsProbabilityMeasure μ] {s : Set ι} {a : ι} (hs : μ s = 1)
      (ha : μ {a} ≠ 0) : a ∈ s :=
    ae_iff_of_countable.1 ((mem_ae_iff_prob_eq_one (Set.to_countable s).measurableSet).2 hs) a ha
  refine ae_all_iff.2 fun t ↦ ?_
  cases t with
  | zero =>
    have h : ∀ᵐ a ∂(envLaw ρ π).map (fun ω ↦ (ω 0).1), π.first {a} ≠ 0 := by
      rw [envLaw_map_arm_zero]
      exact ae_iff_of_countable.2 fun _ ↦ id
    filter_upwards [ae_of_ae_map (measurable_fst.comp (measurable_pi_apply 0)).aemeasurable h]
      with ω hω
    exact hmem (hπ.1 ω) hω
  | succ n =>
    have h := Measure.ae_compProd_measure_singleton_ne_zero
      ((envLaw ρ π).map (frestrictLe n)) (π.next n)
    rw [← envLaw_map_history_arm_succ ρ π n] at h
    filter_upwards [ae_of_ae_map (by fun_prop) h] with ω hω
    exact hmem (hπ.2 n ω) hω

end TauCeti.Bandit
