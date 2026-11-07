/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.Kernel.Composition.Power
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Data.Fintype.Lattice

/-!
# Entrance into accessible sets on finite state spaces

For a finite-state Markov chain, a measurable set that can be reached with positive
probability from every state is entered almost surely, from every initial measure.
The set need not be a singleton, and neither irreducibility nor closedness is required.
The result also transfers to any process with the same path law.
This is the probabilistic ingredient for eventual entrance into the closed classes
of a finite chain.

The argument uses the maximum of the probabilities of never entering the set.
If this maximum were positive, a positive transition probability into the set would
strictly decrease it, contradicting the Markov property. In particular, no uniform
bound on the lengths of the paths into the set is assumed.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.3.
-/

public section

open MeasureTheory ProbabilityTheory Set
open TauCeti.Probability
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]

/-- The set of paths that never visit a measurable set is measurable. -/
private theorem measurableSet_forall_notMem {A : Set S} (hA : MeasurableSet A) :
    MeasurableSet {w : ℕ → S | ∀ n, w n ∉ A} := by
  convert MeasurableSet.iInter (fun n : ℕ => hA.compl.preimage (measurable_pi_apply n)) using 1
  ext w
  simp

/-- Starting in the target rules out never entering it, since entrance includes time zero. -/
private theorem markovChainKernel_forall_notMem_eq_zero_of_mem {A : Set S} (hA : MeasurableSet A)
    {x : S} (hx : x ∈ A) : κ.markovChainKernel x {w : ℕ → S | ∀ n, w n ∉ A} = 0 := by
  have hsub : {w : ℕ → S | ∀ n, w n ∉ A} ⊆ (fun w : ℕ → S => w 0) ⁻¹' Aᶜ := fun w hw => hw 0
  apply le_antisymm _ bot_le
  calc κ.markovChainKernel x _ ≤ κ.markovChainKernel x ((fun w => w 0) ⁻¹' Aᶜ) :=
        measure_mono hsub
    _ = 0 := by
      rw [← Measure.map_apply (measurable_pi_apply 0) hA.compl,
        ← Kernel.map_apply _ (measurable_pi_apply 0), markovChainKernel_map_eval]
      simp [one_def, id_apply, hA, hx]

/-- Never entering implies never entering after any deterministic shift. The Markov
property therefore bounds the failure probability by its average at time `n`. -/
private theorem markovChainKernel_forall_notMem_le_lintegral {A : Set S}
    (hA : MeasurableSet A) (x : S) (n : ℕ) :
    κ.markovChainKernel x {w : ℕ → S | ∀ n, w n ∉ A} ≤
      ∫⁻ y, κ.markovChainKernel y {w : ℕ → S | ∀ n, w n ∉ A} ∂(κ ^ n) x := by
  have hB := measurableSet_forall_notMem hA
  calc _ ≤ markovChainLaw (Measure.dirac x) κ
        ((shift S)^[n] ⁻¹' {w : ℕ → S | ∀ n, w n ∉ A}) := by
        rw [← markovChainKernel_apply]
        exact measure_mono fun w hw k => by simpa using hw (k + n)
    _ = _ := by
        rw [← Measure.map_apply (measurable_shift_iterate n) hB,
          Measure.markovChainLaw_map_shift_iterate, Measure.dirac_bind (Kernel.measurable _),
          Measure.markovChainLaw_eq_comp, Measure.bind_apply hB (Kernel.aemeasurable _)]

/-- At a maximizer, positive mass entering the target forces a strict decrease unless
the maximum is zero. Finiteness is used only to obtain this maximizer. -/
private theorem markovChainKernel_forall_notMem_eq_zero [Finite S] {A : Set S}
    (hA : MeasurableSet A) (hreach : ∀ x, ∃ n, 0 < (κ ^ n) x A) (x : S) :
    κ.markovChainKernel x {w : ℕ → S | ∀ n, w n ∉ A} = 0 := by
  set q : S → ℝ≥0∞ := fun x => κ.markovChainKernel x {w : ℕ → S | ∀ n, w n ∉ A} with hqdef
  have hzero : ∀ x ∈ A, q x = 0 := fun x hx => markovChainKernel_forall_notMem_eq_zero_of_mem hA hx
  have hq : ∀ x, q x = 0 := by
    cases isEmpty_or_nonempty S with
    | inl h => exact fun x => isEmptyElim x
    | inr h =>
      obtain ⟨x, hx⟩ := Finite.exists_max q
      have hfin : q x ≠ ∞ := measure_ne_top _ _
      have hxzero : q x = 0 := by
        by_contra hpos
        obtain ⟨n, hn⟩ := hreach x
        have hbound : q x ≤ q x * (κ ^ n) x Aᶜ := calc
          q x ≤ ∫⁻ y, q y ∂(κ ^ n) x := markovChainKernel_forall_notMem_le_lintegral hA x n
          _ ≤ ∫⁻ y, Aᶜ.indicator (fun _ => q x) y ∂(κ ^ n) x := by
            apply lintegral_mono
            intro y
            by_cases hy : y ∈ A
            · simp [hy, hzero y hy]
            · simpa [hy] using hx y
          _ = q x * (κ ^ n) x Aᶜ := by simp [lintegral_indicator hA.compl, mul_comm]
        have hmass : (κ ^ n) x Aᶜ = 1 := by
          apply le_antisymm (prob_le_one)
          exact (ENNReal.mul_le_mul_iff_right hpos hfin).1 (by simpa using hbound)
        exact hn.ne' ((prob_compl_eq_one_iff hA).1 hmass)
      exact fun y => le_antisymm (hx y |>.trans_eq hxzero) bot_le
  exact hq x

/-- A finite-state chain enters a measurable set almost surely if every state has
positive probability of being in that set at some finite time. The initial measure
need not be a probability measure, or even finite. -/
theorem ae_hittingAfter_ne_top_of_finite [Finite S] (κ : Kernel S S) [IsMarkovKernel κ]
    {A : Set S} (hA : MeasurableSet A) (hreach : ∀ x, ∃ n, 0 < (κ ^ n) x A)
    (ν : Measure S) :
    ∀ᵐ w ∂markovChainLaw ν κ, hittingAfter (fun n w => w n) A 0 w ≠ ⊤ := by
  have hB := measurableSet_forall_notMem hA
  -- Mix the point-started conclusions over the arbitrary initial measure.
  rw [Measure.markovChainLaw_eq_comp]
  apply Measure.ae_comp_of_ae_ae
    (by
      convert hB.compl using 1
      ext w
      simp [hittingAfter_eq_top_iff])
  exact ae_of_all _ fun x => by
    simpa [ae_iff, hittingAfter_eq_top_iff] using
      markovChainKernel_forall_notMem_eq_zero hA hreach x

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] [Finite S]
    {κ : Kernel S S} [IsMarkovKernel κ] {ν : Measure S} {μ : Measure Ω}
    {X : ℕ → Ω → S}

/-- Any realization of a finite-state chain almost surely enters a measurable set
that is accessible with positive probability from every state. -/
theorem ae_hittingAfter_ne_top_of_finite
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) μ)
    {A : Set S} (hA : MeasurableSet A) (hreach : ∀ x, ∃ n, 0 < (κ ^ n) x A) :
    ∀ᵐ ω ∂μ, hittingAfter X A 0 ω ≠ ⊤ := by
  have hm : MeasurableSet {w : ℕ → S | hittingAfter (fun n w => w n) A 0 w ≠ ⊤} := by
    convert MeasurableSet.iUnion (fun n : ℕ => hA.preimage (measurable_pi_apply n)) using 1
    ext w
    simp [hittingAfter_eq_top_iff]
  simpa only [ne_eq, hittingAfter_eq_top_iff] using
    (h.ae_iff (measurableSet_setOfPred.1 hm)).2
      (κ.ae_hittingAfter_ne_top_of_finite hA hreach ν)

end ProbabilityTheory.HasLaw
