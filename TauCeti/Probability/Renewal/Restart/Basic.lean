/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Basic

/-!
# Restarting a renewal path at an observation time

At time `t`, the first waiting time of the future counting process is the excess at `t`,
not the entire increment straddling `t`. Subsequent waiting times are the unused original
increments. `renewalRestart` forms this sequence. On a nonexplosive path its positive-index
arrivals are exactly the original arrivals strictly after `t`, translated by `-t`.
Consequently its count at `s` is `N (t + s) - N t`.

These are pathwise identities: no independence or distributional assumption is needed.
They retain zero increments and arrivals exactly at the observation time. In particular,
the restarted count starts at zero even when the original count at zero is positive.
Measurability and a process-law transfer theorem allow a law for the restarted increment
sequence to be transferred to the entire future counting process. This separates the
pathwise inversion from the probabilistic memorylessness argument for exponential gaps.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} (T : ℕ → Ω → ℝ≥0)

/-- The waiting times after observation at `t`: first the residual waiting time, then the
increments strictly after the straddling increment. On explosive paths the count uses its
exceptional value zero, just as in `renewalExcess`. -/
def renewalRestart (t : ℝ≥0) : ℕ → Ω → ℝ≥0
  | 0 => renewalExcess T t
  | n + 1 => fun ω ↦ T (renewalCountNat T t ω + n + 1) ω

@[simp]
lemma renewalRestart_zero (t : ℝ≥0) : renewalRestart T t 0 = renewalExcess T t := (rfl)

@[simp]
lemma renewalRestart_succ (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    renewalRestart T t (n + 1) ω = T (renewalCountNat T t ω + n + 1) ω := (rfl)

/-- Restarting commutes with a change of sample space. -/
@[simp]
lemma renewalRestart_comp {Ω' : Type*} (f : Ω' → Ω) (t : ℝ≥0) (n : ℕ) (ω : Ω') :
    renewalRestart (fun n ω ↦ T n (f ω)) t n ω = renewalRestart T t n (f ω) := by
  cases n <;> simp [renewalExcess_def, arrival_def]

variable {T}

/-- Positive-index arrivals of the restarted sequence are the original future arrivals,
with the observation time subtracted. The additive form avoids truncated subtraction. -/
lemma add_arrival_renewalRestart {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) (n : ℕ) :
    t + arrival (renewalRestart T t) (n + 1) ω =
      arrival T (renewalCountNat T t ω + n + 1) ω := by
  induction n with
  | zero => simpa [arrival_succ] using add_renewalExcess hω t
  | succ n ih =>
    rw [arrival_succ, ← add_assoc, ih, renewalRestart_succ]
    simpa [Nat.add_assoc] using
      (arrival_succ T (renewalCountNat T t ω + n + 1) ω).symm

/-- The future waiting-time sequence of a nonexplosive path is nonexplosive. -/
lemma tendsto_arrival_renewalRestart {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    Tendsto (fun n ↦ arrival (renewalRestart T t) n ω) atTop atTop := by
  apply (tendsto_add_atTop_iff_nat 1).1
  refine tendsto_atTop.2 fun b ↦ ?_
  have hlim := hω.comp ((tendsto_add_atTop_nat (renewalCountNat T t ω)).comp
    (tendsto_add_atTop_nat 1))
  filter_upwards [(tendsto_atTop.1 hlim) (t + b)] with n hn
  have hle : t + b ≤ t + arrival (renewalRestart T t) (n + 1) ω := by
    simpa [add_arrival_renewalRestart hω, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hn
  exact le_of_add_le_add_left hle

/-- Restarting at `t` removes precisely the arrivals counted at `t`. The count on the
right includes arrivals at `t + s` and excludes all arrivals at `t`, with multiplicity. -/
theorem renewalCountNat_renewalRestart {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t s : ℝ≥0) :
    renewalCountNat (renewalRestart T t) s ω =
      renewalCountNat T (t + s) ω - renewalCountNat T t ω := by
  have hr := tendsto_arrival_renewalRestart hω t
  have hmono : renewalCountNat T t ω ≤ renewalCountNat T (t + s) ω :=
    monotone_renewalCountNat T ω le_self_add
  apply (renewalCountNat_eq_iff hr).2
  constructor
  · by_cases hz : renewalCountNat T (t + s) ω - renewalCountNat T t ω = 0
    · simp [hz]
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
      rw [hn]
      apply le_of_add_le_add_left (a := t)
      rw [add_arrival_renewalRestart hω]
      have hi : renewalCountNat T t ω + n + 1 = renewalCountNat T (t + s) ω := by omega
      rw [hi]
      exact arrival_renewalCountNat_le hω (t + s)
  · apply lt_of_add_lt_add_left (a := t)
    rw [add_arrival_renewalRestart hω]
    have hi : renewalCountNat T t ω +
        (renewalCountNat T (t + s) ω - renewalCountNat T t ω) + 1 =
        renewalCountNat T (t + s) ω + 1 := by omega
    rw [hi]
    exact lt_arrival_renewalCountNat_succ hω (t + s)

/-- There are no restarted arrivals at time zero, even when the original increments have
zeros: the residual first waiting time is strictly positive. -/
@[simp]
lemma renewalCountNat_renewalRestart_zero {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) (t : ℝ≥0) :
    renewalCountNat (renewalRestart T t) 0 ω = 0 := by
  simp [renewalCountNat_renewalRestart hω]

variable [MeasurableSpace Ω]

/-- Each restarted increment is measurable, including its random original index. -/
@[fun_prop]
lemma measurable_renewalRestart (hT : ∀ n, Measurable (T n)) (t : ℝ≥0) (n : ℕ) :
    Measurable (renewalRestart T t n) := by
  cases n with
  | zero => exact measurable_renewalExcess hT t
  | succ n =>
    exact (measurable_pi_iff.2 hT).eval_index
      (((measurable_renewalCountNat hT t).add_const n).add_const 1)

variable {P : Measure Ω}

/-- For nondegenerate i.i.d. increments, the restart identity holds on one event of full
measure, simultaneously at every observation time and future time. -/
theorem ae_renewalCountNat_renewalRestart (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) :
    ∀ᵐ ω ∂P, ∀ t s, renewalCountNat (renewalRestart T t) s ω =
      renewalCountNat T (t + s) ω - renewalCountNat T t ω := by
  filter_upwards [ae_tendsto_arrival_atTop hindep hid hzero] with ω hω t s
  exact renewalCountNat_renewalRestart hω t s

/-- Transfer the law of the entire restarted increment sequence to the future count
process. Only almost-sure nonexplosion is required; the restarted law need not be i.i.d. -/
theorem hasLaw_renewalCountNat_sub_of_hasLaw_renewalRestart
    (hP : ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop)
    (t : ℝ≥0) {Q : Measure (ℕ → ℝ≥0)}
    (hQ : HasLaw (fun ω n ↦ renewalRestart T t n ω) Q P) :
    HasLaw (fun ω s ↦ renewalCountNat T (t + s) ω - renewalCountNat T t ω)
      (Q.map (fun w s ↦ renewalCountNat (fun n w ↦ w n) s w)) P := by
  have hc : Measurable (fun (w : ℕ → ℝ≥0) s ↦
      renewalCountNat (fun n w ↦ w n) s w) :=
    measurable_pi_iff.2 fun s ↦ measurable_renewalCountNat (fun n ↦ measurable_pi_apply n) s
  refine ((hasLaw_map hc.aemeasurable).comp hQ).congr ?_
  filter_upwards [hP] with ω hω
  funext s
  exact (renewalCountNat_renewalRestart hω t s).symm.trans
    (renewalCountNat_comp (fun n (w : ℕ → ℝ≥0) ↦ w n)
      (fun ω n ↦ renewalRestart T t n ω) s ω)

end TauCeti.Probability
