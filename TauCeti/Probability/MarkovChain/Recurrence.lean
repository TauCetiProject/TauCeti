/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.MarkovChain.Visits
public import TauCeti.Probability.Kernel.ClosedClass

/-!
# Recurrence and communicating classes

A state of a Markov kernel is recurrent if the chain started there returns at a positive
time almost surely, and transient otherwise. Recurrence is equivalent to divergence of
the diagonal Green function, and is constant on communicating classes.

Every state reachable from a recurrent state is recurrent and hits the original state
almost surely. Consequently a recurrent communicating class is closed. In an irreducible
chain with a recurrent state, every state is hit almost surely from every initial law.
These results supply the state-classification input to coupling arguments.

The first entrance and first return use `hittingAfter` starting at zero and one,
respectively. The class-property and hitting results need only measurable singletons;
countability is used for closedness of the communicating class.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.5, in particular
  Theorem 1.5.4.
-/

public section

open MeasureTheory TauCeti.Probability

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]
  {κ : Kernel S S} [IsMarkovKernel κ] {x y : S}

/-- A state is recurrent if the chain started there returns at a positive time almost surely. -/
def IsRecurrent (κ : Kernel S S) [IsMarkovKernel κ] (x : S) : Prop :=
  markovChainLaw (Measure.dirac x) κ
    {ω | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} = 1

/-- The first return in the definition of recurrence starts at time one. -/
theorem isRecurrent_iff : κ.IsRecurrent x ↔
    markovChainLaw (Measure.dirac x) κ
      {ω | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} = 1 := Iff.rfl

/-- A state is transient if it is not recurrent. -/
def IsTransient (κ : Kernel S S) [IsMarkovKernel κ] (x : S) : Prop :=
  ¬ κ.IsRecurrent x

/-- Transience is the failure of almost-sure return. -/
theorem isTransient_iff : κ.IsTransient x ↔ ¬ κ.IsRecurrent x := Iff.rfl

/-- The return probability of a transient state is strictly less than one. -/
theorem isTransient_iff_return_probability_lt_one : κ.IsTransient x ↔
    markovChainLaw (Measure.dirac x) κ
      {ω | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} < 1 := by
  rw [isTransient_iff, isRecurrent_iff]
  exact ⟨fun h => lt_of_le_of_ne prob_le_one h, fun h => h.ne⟩

variable [MeasurableSingletonClass S]

/-- A state is recurrent exactly when its diagonal Green function is infinite. -/
theorem isRecurrent_iff_tsum_eq_top :
    κ.IsRecurrent x ↔ ∑' n : ℕ, (κ ^ n) x {x} = ∞ :=
  (κ.tsum_pow_apply_singleton_self_eq_top_iff x).symm

/-- Recurrence is constant on communicating classes. -/
theorem Communicates.isRecurrent_iff (hxy : κ.Communicates x y) :
    κ.IsRecurrent x ↔ κ.IsRecurrent y := by
  suffices h : ∀ {x y : S}, κ.Communicates x y → κ.IsRecurrent x → κ.IsRecurrent y from
    ⟨h hxy, h hxy.symm⟩
  intro x y hxy hx
  obtain ⟨hxy, hyx⟩ := (communicates_def x y).mp hxy
  obtain ⟨a, ha⟩ := (reaches_def y x).mp hyx
  obtain ⟨b, hb⟩ := (reaches_def x y).mp hxy
  rw [isRecurrent_iff_tsum_eq_top] at hx ⊢
  have hbound : (κ ^ a) y {x} * (∑' n : ℕ, (κ ^ n) x {x}) * (κ ^ b) x {y} ≤
      ∑' n : ℕ, (κ ^ n) y {y} := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    refine (tsum_le_tsum fun n => ?_).trans
      (tsum_comp_le_tsum_of_injective (f := fun n : ℕ => a + n + b)
        (by intro m n h; dsimp only at h; omega) (fun n => (κ ^ n) y {y}))
    exact (mul_le_mul_left
      (pow_apply_singleton_mul_le_pow_add_apply κ a n y x (measurableSet_singleton x))
      ((κ ^ b) x {y})).trans
      (pow_apply_singleton_mul_le_pow_add_apply κ (a + n) b y x
        (measurableSet_singleton y))
  simpa [hx, ha.ne', hb.ne'] using hbound

/-- Transience is constant on communicating classes. -/
theorem Communicates.isTransient_iff (hxy : κ.Communicates x y) :
    κ.IsTransient x ↔ κ.IsTransient y := by
  rw [ProbabilityTheory.Kernel.isTransient_iff, ProbabilityTheory.Kernel.isTransient_iff]
  exact not_congr hxy.isRecurrent_iff

/-- From a state reachable from a recurrent state, the chain hits the recurrent state
almost surely. The entrance may occur at time zero. -/
theorem IsRecurrent.ae_hittingAfter_ne_top_of_reaches (hx : κ.IsRecurrent x)
    (hxy : κ.Reaches x y) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac y) κ,
      hittingAfter (fun n ω => ω n) {x} 0 ω ≠ ⊤ := by
  obtain ⟨n, hn⟩ := (reaches_def x y).mp hxy
  have hE : MeasurableSet {ω : ℕ → S | hittingAfter (fun n ω => ω n) {x} 0 ω ≠ ⊤} :=
    ((measurableSet_singleton ⊤).preimage
      (Filtration.adapted_piLE.isStoppingTime_hittingAfter
        (f := Filtration.piLE (X := fun _ : ℕ => S)) (measurableSet_singleton x)).measurable').compl
  -- Infinitely many visits imply a visit after time `n`. Disintegrating the future law then
  -- gives almost-sure entrance from `y`, since `y` has positive mass at time `n`.
  have hshift : ∀ᵐ ω ∂(markovChainLaw (Measure.dirac x) κ).map (shift S)^[n],
      hittingAfter (fun n ω => ω n) {x} 0 ω ≠ ⊤ := by
    rw [ae_map_iff (measurable_shift_iterate n).aemeasurable hE]
    filter_upwards [κ.ae_infinite_setOf_eq_markovChainLaw_dirac (isRecurrent_iff.mp hx)]
      with ω hω
    obtain ⟨k, hk, hnk⟩ := hω.exists_gt n
    have hmem : ((shift S)^[n] ω) (k - n) ∈ ({x} : Set S) := by
      simpa [shift_iterate_apply, Nat.sub_add_cancel hnk.le] using hk
    exact ne_top_of_le_ne_top WithTop.coe_ne_top
      (hittingAfter_le_of_mem (Nat.zero_le _) hmem)
  rw [Measure.markovChainLaw_map_shift_iterate, Measure.dirac_bind (κ ^ n).measurable,
    Measure.markovChainLaw_eq_comp] at hshift
  have hrows := Measure.ae_ae_of_ae_comp hshift
  simp only [markovChainKernel_apply] at hrows
  by_contra hy
  exact hn.ne' (measure_mono_null (Set.singleton_subset_iff.mpr hy) (ae_iff.mp hrows))

/-- Every state reachable from a recurrent state can reach it back. -/
theorem IsRecurrent.reaches_of_reaches (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    κ.Reaches y x := by
  by_contra hyx
  have hzero : ∀ n : ℕ, markovChainLaw (Measure.dirac y) κ {ω | ω n = x} = 0 := by
    intro n
    rw [Measure.markovChainLaw_setOf_apply_eq_comp, Measure.dirac_bind (κ ^ n).measurable]
    exact nonpos_iff_eq_zero.mp (not_lt.mp fun h => hyx ((reaches_def y x).mpr ⟨n, h⟩))
  have havoid : ∀ᵐ ω ∂markovChainLaw (Measure.dirac y) κ, ∀ n, ω n ≠ x :=
    ae_all_iff.mpr fun n => ae_iff.mpr (by simpa using hzero n)
  have hhit := hx.ae_hittingAfter_ne_top_of_reaches hxy
  have : ∀ᵐ ω ∂markovChainLaw (Measure.dirac y) κ, False := by
    filter_upwards [havoid, hhit] with ω hω hH
    exact hH (hittingAfter_eq_top_iff.mpr fun n _ => hω n)
  exact (Filter.Eventually.exists this).elim fun _ h => h

/-- Every state reachable from a recurrent state is recurrent. -/
theorem IsRecurrent.of_reaches (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    κ.IsRecurrent y :=
  (Communicates.isRecurrent_iff
    ((communicates_def x y).mpr ⟨hxy, hx.reaches_of_reaches hxy⟩)).mp hx

/-- A recurrent state hits every state reachable from it almost surely. -/
theorem IsRecurrent.ae_hittingAfter_ne_top (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) κ,
      hittingAfter (fun n ω => ω n) {y} 0 ω ≠ ⊤ :=
  (hx.of_reaches hxy).ae_hittingAfter_ne_top_of_reaches (hx.reaches_of_reaches hxy)

/-- A communicating class containing a recurrent state is closed under transitions. -/
theorem IsRecurrent.isClosedSet_communicatingClass [Countable S] (hx : κ.IsRecurrent x) :
    κ.IsClosedSet (κ.communicatingClass x) := by
  rw [isClosedSet_iff_forall_reaches_mem]
  intro y hy z hyz
  rw [mem_communicatingClass_iff, communicates_def] at hy ⊢
  have hxz := hy.1.trans hyz
  exact ⟨hxz, hx.reaches_of_reaches hxz⟩

/-- In an irreducible chain with a recurrent state, every state is hit almost surely
from any initial measure. In particular this holds for any initial probability law. -/
theorem IsRecurrent.ae_hittingAfter_ne_top_of_isIrreducible [IsIrreducible Measure.count κ]
    (hx : κ.IsRecurrent x) (ν : Measure S) (y : S) :
    ∀ᵐ ω ∂markovChainLaw ν κ, hittingAfter (fun n ω => ω n) {y} 0 ω ≠ ⊤ := by
  have hreaches := (isIrreducible_count_iff_forall_reaches.mp inferInstance :
    ∀ a b : S, κ.Reaches a b)
  rw [Measure.markovChainLaw_eq_comp]
  apply Measure.ae_comp_of_ae_ae
    (((measurableSet_singleton ⊤).preimage
      (Filtration.adapted_piLE.isStoppingTime_hittingAfter
        (f := Filtration.piLE (X := fun _ : ℕ => S))
        (measurableSet_singleton y)).measurable').compl)
  exact Filter.Eventually.of_forall fun z => by
    rw [markovChainKernel_apply]
    exact (hx.of_reaches (hreaches x z)).ae_hittingAfter_ne_top (hreaches z y)

end ProbabilityTheory.Kernel
