/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.MarkovProperty

/-!
# Finite-time cylinders of Markov chains

For nondecreasing observation times, finite-dimensional singleton probabilities are products
of transition masses over the intervening time gaps. Observation need not begin at zero,
and repeated times are allowed: the corresponding factor is the identity kernel.
The formulas also transfer to any process with the specified path law.

The multistep event identity expresses the transition law after an arbitrary deterministic
time gap on an event of the history, without a countability assumption on the state space.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.1.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability

namespace MeasureTheory.Measure

variable {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] (κ : Kernel S S) [IsMarkovKernel κ]

/-- On an event of the history through time `n`, the state at time `n + k` has the
`k`-step transition law from the current state. -/
theorem markovChainLaw_inter_preimage_eval_add (n k : ℕ) {A : Set (ℕ → S)}
    (hA : MeasurableSet[Filtration.piLE n] A) {B : Set S} (hB : MeasurableSet B) :
    markovChainLaw ν κ (A ∩ (fun ω => ω (n + k)) ⁻¹' B) =
      ∫⁻ ω in A, (κ ^ k) (ω n) B ∂markovChainLaw ν κ := by
  rw [Filtration.piLE_eq_comap_prefix, MeasurableSpace.measurableSet_comap] at hA
  obtain ⟨C, hC, rfl⟩ := hA
  have hmap := congrArg (fun μ : Measure (ℕ → S) => μ.map (fun ω => ω k))
    (markovChainLaw_restrict_map_shift_iterate ν κ n hC)
  rw [map_map (measurable_pi_apply k) (measurable_shift_iterate n),
    markovChainLaw_map_eval] at hmap
  have heval : (fun ω : ℕ → S => ω k) ∘ (shift S)^[n] = fun ω => ω (n + k) := by
    funext ω
    simp [Nat.add_comm]
  rw [heval] at hmap
  have h := congrArg (fun μ : Measure S => μ B) hmap
  rw [map_apply (measurable_pi_apply _) hB, restrict_apply (hB.preimage (measurable_pi_apply _)),
    Measure.bind_apply hB (Kernel.aemeasurable _), lintegral_map (Kernel.measurable_coe _ hB)
      (measurable_pi_apply n)] at h
  simpa only [Set.inter_comm] using h

variable [MeasurableSingletonClass S]

/-- The singleton cylinder formula at arbitrary nondecreasing observation times. The initial
factor is the marginal at the first observation; each later factor uses the elapsed time.
Repeated observations contribute an identity-kernel factor, so inconsistent states have mass
zero. Neither countability of the state space nor probability normalization is needed. -/
theorem markovChainLaw_finiteTime_singleton {n : ℕ} (t : Fin (n + 1) → ℕ)
    (ht : Monotone t) (w : Fin (n + 1) → S) :
    markovChainLaw ν κ {ω | ∀ i, ω (t i) = w i} =
      ((κ ^ t 0) ∘ₘ ν) {w 0} *
        ∏ i : Fin n, (κ ^ (t i.succ - t i.castSucc)) (w i.castSucc) {w i.succ} := by
  induction n with
  | zero =>
    have hevent : {ω : ℕ → S | ∀ i : Fin 1, ω (t i) = w i} =
        (fun ω => ω (t 0)) ⁻¹' {w 0} := by
      ext ω
      simp [Fin.forall_fin_one]
    rw [hevent, ← map_apply (measurable_pi_apply _) (measurableSet_singleton _),
      markovChainLaw_map_eval]
    simp
  | succ n ih =>
    let A : Set (ℕ → S) := {ω | ∀ i : Fin (n + 1), ω (t i.castSucc) = w i.castSucc}
    have hA : MeasurableSet[Filtration.piLE (t (Fin.last n).castSucc)] A := by
      have hcoord (i : Fin (n + 1)) :
          Measurable[Filtration.piLE (t (Fin.last n).castSucc)]
            (fun ω : ℕ → S => ω (t i.castSucc)) :=
        (Filtration.adapted_piLE (t i.castSucc)).mono
          ((Filtration.piLE).mono (ht (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i)))) le_rfl
      have hevent : A = ⋂ i : Fin (n + 1), (fun ω : ℕ → S => ω (t i.castSucc)) ⁻¹'
          {w i.castSucc} := by
        ext ω
        simp [A]
      rw [hevent]
      exact MeasurableSet.iInter fun i => (measurableSet_singleton _).preimage (hcoord i)
    have hA' : MeasurableSet A := (Filtration.piLE.le _) _ hA
    have hevent : {ω : ℕ → S | ∀ i, ω (t i) = w i} =
        A ∩ (fun ω => ω (t (Fin.last (n + 1)))) ⁻¹' {w (Fin.last (n + 1))} := by
      ext ω
      simp [A, Fin.forall_iff_castSucc, and_comm, and_left_comm]
    have hle : t (Fin.last n).castSucc ≤ t (Fin.last (n + 1)) := ht (Fin.le_last _)
    rw [hevent, ← Nat.add_sub_of_le hle,
      markovChainLaw_inter_preimage_eval_add ν κ _ _ hA (measurableSet_singleton _)]
    rw [setLIntegral_congr_fun hA' (fun ω hω => by rw [hω (Fin.last n)]),
      setLIntegral_const, mul_comm, ih (fun i => t i.castSucc)
        (fun i j hij => ht (Fin.castSucc_le_castSucc_iff.mpr hij)) (fun i => w i.castSucc),
      Fin.prod_univ_castSucc]
    simp [mul_assoc]

/-- On a countable state space, the probability of any finite-dimensional event is the sum
of its singleton path weights. In particular, take `C` to be a rectangle for cylinder events
with arbitrary prescribed sets at the observation times. -/
theorem markovChainLaw_finiteTime [Countable S] {n : ℕ} (t : Fin (n + 1) → ℕ)
    (ht : Monotone t) (C : Set (Fin (n + 1) → S)) :
    markovChainLaw ν κ ((fun ω i => ω (t i)) ⁻¹' C) =
      ∑' w : Fin (n + 1) → S, C.indicator (fun w =>
        ((κ ^ t 0) ∘ₘ ν) {w 0} *
          ∏ i : Fin n, (κ ^ (t i.succ - t i.castSucc)) (w i.castSucc) {w i.succ}) w := by
  have hmeas : Measurable (fun (ω : ℕ → S) i => ω (t i)) := by fun_prop
  rw [← map_apply hmeas (Set.to_countable C).measurableSet,
    ← tsum_indicator_apply_singleton _ C (Set.to_countable C).measurableSet]
  have hmass (w : Fin (n + 1) → S) :
      ((markovChainLaw ν κ).map (fun ω i => ω (t i))) {w} =
        ((κ ^ t 0) ∘ₘ ν) {w 0} *
          ∏ i : Fin n, (κ ^ (t i.succ - t i.castSucc)) (w i.castSucc) {w i.succ} := by
    rw [map_apply hmeas (measurableSet_singleton _)]
    simpa only [Set.preimage_singleton, funext_iff] using
      markovChainLaw_finiteTime_singleton ν κ t ht w
  simp_rw [hmass]

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure S} [IsFiniteMeasure ν]
    {κ : Kernel S S} [IsMarkovKernel κ] {X : ℕ → Ω → S}

/-- A process with the Markov path law has the same finite-time singleton probabilities,
independently of its sample space. -/
theorem finiteTime_singleton_markovChainLaw
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    {n : ℕ} (t : Fin (n + 1) → ℕ) (ht : Monotone t) (w : Fin (n + 1) → S) :
    P {ω | ∀ i, X (t i) ω = w i} =
      ((κ ^ t 0) ∘ₘ ν) {w 0} *
        ∏ i : Fin n, (κ ^ (t i.succ - t i.castSucc)) (w i.castSucc) {w i.succ} := by
  have hm : MeasurableSet {ω : ℕ → S | ∀ i, ω (t i) = w i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => (measurableSet_singleton _).preimage (measurable_pi_apply _)
  exact (h.measure_eq hm).trans (ν.markovChainLaw_finiteTime_singleton κ t ht w)

/-- Finite-dimensional event probabilities transfer through equality with the Markov path
law. No canonical sample space or additional coordinate measurability assumption is imposed. -/
theorem finiteTime_markovChainLaw [Countable S]
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    {n : ℕ} (t : Fin (n + 1) → ℕ) (ht : Monotone t) (C : Set (Fin (n + 1) → S)) :
    P ((fun ω i => X (t i) ω) ⁻¹' C) =
      ∑' w : Fin (n + 1) → S, C.indicator (fun w =>
        ((κ ^ t 0) ∘ₘ ν) {w 0} *
          ∏ i : Fin n, (κ ^ (t i.succ - t i.castSucc)) (w i.castSucc) {w i.succ}) w := by
  exact (h.measure_eq ((Set.to_countable C).measurableSet.preimage (by fun_prop))).trans
    (ν.markovChainLaw_finiteTime κ t ht C)

end ProbabilityTheory.HasLaw
