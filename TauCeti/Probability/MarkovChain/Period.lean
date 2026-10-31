/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Probability.Kernel.Irreducible
public import TauCeti.NumberTheory.FrobeniusNumber
public import TauCeti.Probability.Kernel.Composition.Power

/-!
# The period of a state of a Markov chain

For a transition kernel `κ : Kernel α α` and a state `x`, the *return lengths* of `x` are the
times `n ≥ 1` at which the chain started at `x` is back at `x` with positive probability,
`0 < (κ ^ n) x {x}`. The *period* `κ.period x` is their gcd, computed with Mathlib's
`Nat.setGcd`, so a state with no return length has period zero. The kernel is *aperiodic* when
every state has period one.

By Chapman–Kolmogorov the return lengths are closed under addition. Hence every sufficiently
large multiple of the period is a return length, and a state of period one returns with positive
probability at every sufficiently large time. Mutually reachable states have the same period, so
the period is constant on each communicating class. For an irreducible aperiodic kernel on a
space with measurable singletons, every transition mass `(κ ^ n) x {y}` is positive for all
sufficiently large `n`; this is the input to the coupling proof of convergence to equilibrium.

Irreducibility is Mathlib's `Kernel.IsIrreducible` with respect to counting measure, which on a
space with measurable singletons says that every state reaches every other state.

As a check of the definition, the period of a state under the deterministic kernel of a map `f`
is the minimal period `Function.minimalPeriod f x` of `x` under `f`.

## Main definitions

* `ProbabilityTheory.Kernel.returnLengths κ x`: the positive return lengths of `x`.
* `ProbabilityTheory.Kernel.period κ x`: their gcd.
* `ProbabilityTheory.Kernel.IsAperiodic κ`: every state has period one.

## Main statements

* `ProbabilityTheory.Kernel.eventually_pos_pow_period_mul_apply_singleton`: the chain returns to
  `x` with positive probability at every sufficiently large multiple of the period.
* `ProbabilityTheory.Kernel.period_eq_period_of_pos`: mutually reachable states have the same
  period.
* `ProbabilityTheory.Kernel.eventually_pos_pow_apply_singleton_of_period_eq_one`: from a state of
  period one, every reachable state is reached with positive probability at every sufficiently
  large time.
* `ProbabilityTheory.Kernel.IsAperiodic.eventually_pos_pow_apply_singleton`: the same for every
  pair of states of an irreducible aperiodic kernel.
* `ProbabilityTheory.Kernel.period_deterministic`: the period under a deterministic kernel is the
  minimal period.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8.
-/

public section

open MeasureTheory Filter

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] {κ : Kernel α α} {x y : α} {n : ℕ}

variable (κ) in
/-- The positive return lengths of a state `x`: the times `n ≥ 1` with `0 < (κ ^ n) x {x}`. -/
def returnLengths (x : α) : Set ℕ := {n | 0 < n ∧ 0 < (κ ^ n) x {x}}

@[simp]
theorem mem_returnLengths : n ∈ κ.returnLengths x ↔ 0 < n ∧ 0 < (κ ^ n) x {x} := Iff.rfl

/-- The return lengths of a state are closed under addition. -/
theorem add_mem_returnLengths [MeasurableSingletonClass α] {m : ℕ}
    (hm : m ∈ κ.returnLengths x) (hn : n ∈ κ.returnLengths x) : m + n ∈ κ.returnLengths x :=
  ⟨by have := hm.1; lia, pow_add_apply_pos (measurableSet_singleton x) hm.2 hn.2⟩

variable (κ) in
/-- The period of a state `x`: the gcd of its positive return lengths. A state that the chain
never revisits with positive probability has period zero. -/
noncomputable def period (x : α) : ℕ := Nat.setGcd (κ.returnLengths x)

/-- The defining equation of the period: the gcd of the return lengths. -/
theorem period_def : κ.period x = Nat.setGcd (κ.returnLengths x) := (rfl)

/-- The period divides every return length. -/
theorem period_dvd_of_mem_returnLengths (h : n ∈ κ.returnLengths x) : κ.period x ∣ n :=
  Nat.setGcd_dvd_of_mem h

/-- The characterizing property of the period: it is the greatest common divisor of the return
lengths. -/
theorem dvd_period_iff {d : ℕ} : d ∣ κ.period x ↔ ∀ n ∈ κ.returnLengths x, d ∣ n :=
  Nat.dvd_setGcd_iff

/-- A state has period zero exactly when it has no return length. -/
theorem period_eq_zero_iff : κ.period x = 0 ↔ κ.returnLengths x = ∅ := by
  rw [period_def, Nat.setGcd_eq_zero_iff, Set.eq_empty_iff_forall_notMem]
  refine ⟨fun h n hn ↦ hn.1.ne' (h hn), fun h n hn ↦ (h n hn).elim⟩

/-- A state that the chain can revisit in one step has period one. -/
theorem period_eq_one_of_pos_apply (h : 0 < κ x {x}) : κ.period x = 1 :=
  Nat.dvd_one.mp (period_dvd_of_mem_returnLengths ⟨one_pos, by rwa [pow_one]⟩)

variable (κ) in
/-- A kernel is aperiodic when every state has period one. -/
def IsAperiodic : Prop := ∀ x, κ.period x = 1

theorem isAperiodic_iff : κ.IsAperiodic ↔ ∀ x, κ.period x = 1 := Iff.rfl

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

/-- The chain returns to `x` with positive probability at every sufficiently large multiple of
the period of `x`. For a state of period zero this only says `0 < (κ ^ 0) x {x}`. -/
theorem eventually_pos_pow_period_mul_apply_singleton (κ : Kernel α α) (x : α) :
    ∀ᶠ k in atTop, 0 < (κ ^ (κ.period x * k)) x {x} := by
  rcases Nat.eq_zero_or_pos (κ.period x) with h0 | hpos
  · simp [h0, one_def, id_apply]
  have hmem := Nat.eventually_mem_of_setGcd_dvd (s := κ.returnLengths x)
    fun a ha b hb ↦ add_mem_returnLengths ha hb
  rw [eventually_atTop] at hmem ⊢
  obtain ⟨N, hN⟩ := hmem
  exact ⟨N, fun k hk ↦ (hN _ (hk.trans (Nat.le_mul_of_pos_left k hpos))
    (dvd_mul_right _ _)).2⟩

/-- A state of period one is revisited with positive probability at every sufficiently large
time. -/
theorem eventually_pos_pow_apply_singleton_self_of_period_eq_one (h : κ.period x = 1) :
    ∀ᶠ n in atTop, 0 < (κ ^ n) x {x} := by
  simpa [h] using eventually_pos_pow_period_mul_apply_singleton κ x

/-- If `x` reaches `y` and `y` reaches `x`, then the period of `x` divides the period of `y`. -/
theorem period_dvd_period_of_pos {a b : ℕ} (hxy : 0 < (κ ^ a) x {y})
    (hyx : 0 < (κ ^ b) y {x}) : κ.period x ∣ κ.period y := by
  -- A round trip `x → y → x` of length `a + b` has positive probability, and inserting a return
  -- to `y` of length `n` gives one of length `a + n + b`; the period of `x` divides both.
  have hround : 0 < (κ ^ (a + b)) x {x} := pow_add_apply_pos (measurableSet_singleton x) hxy hyx
  have hdvd_ab : κ.period x ∣ a + b := by
    rcases Nat.eq_zero_or_pos (a + b) with h | h
    · simp [h]
    · exact period_dvd_of_mem_returnLengths ⟨h, hround⟩
  refine dvd_period_iff.mpr fun n hn ↦ ?_
  have hlong : a + n + b ∈ κ.returnLengths x :=
    ⟨by have := hn.1; lia, pow_add_apply_pos (measurableSet_singleton x)
      (pow_add_apply_pos (measurableSet_singleton y) hxy hn.2) hyx⟩
  have h := period_dvd_of_mem_returnLengths hlong
  rw [show a + n + b = n + (a + b) by lia] at h
  exact (Nat.dvd_add_left hdvd_ab).mp h

/-- **The period is a class property.** Mutually reachable states have the same period. -/
theorem period_eq_period_of_pos {a b : ℕ} (hxy : 0 < (κ ^ a) x {y})
    (hyx : 0 < (κ ^ b) y {x}) : κ.period x = κ.period y :=
  Nat.dvd_antisymm (period_dvd_period_of_pos hxy hyx) (period_dvd_period_of_pos hyx hxy)

/-- If `x` has period one and reaches `y`, then `(κ ^ n) x {y}` is positive for every
sufficiently large `n`. -/
theorem eventually_pos_pow_apply_singleton_of_period_eq_one {a : ℕ} (hx : κ.period x = 1)
    (hxy : 0 < (κ ^ a) x {y}) : ∀ᶠ n in atTop, 0 < (κ ^ n) x {y} := by
  have h := eventually_pos_pow_apply_singleton_self_of_period_eq_one hx
  rw [eventually_atTop] at h ⊢
  obtain ⟨N, hN⟩ := h
  refine ⟨N + a, fun n hn ↦ ?_⟩
  rw [show n = (n - a) + a by lia]
  exact pow_add_apply_pos (measurableSet_singleton y) (hN _ (by lia)) hxy

/-- Under counting-measure irreducibility every state reaches every other state. -/
theorem exists_pos_pow_apply_singleton [IsIrreducible Measure.count κ] (x y : α) :
    ∃ n, 0 < (κ ^ n) x {y} :=
  IsIrreducible.irreducible (φ := Measure.count) (measurableSet_singleton y) (by simp) x

/-- All states of an irreducible kernel have the same period. -/
theorem period_eq_period [IsIrreducible Measure.count κ] (x y : α) :
    κ.period x = κ.period y :=
  have ⟨_, hxy⟩ := exists_pos_pow_apply_singleton (κ := κ) x y
  have ⟨_, hyx⟩ := exists_pos_pow_apply_singleton (κ := κ) y x
  period_eq_period_of_pos hxy hyx

/-- An irreducible kernel is aperiodic as soon as one state has period one. -/
theorem isAperiodic_iff_period_eq_one [IsIrreducible Measure.count κ] (x : α) :
    κ.IsAperiodic ↔ κ.period x = 1 :=
  ⟨fun h ↦ h x, fun h y ↦ (period_eq_period y x).trans h⟩

/-- For an irreducible aperiodic kernel, every transition mass `(κ ^ n) x {y}` is positive for all
sufficiently large `n`. -/
theorem IsAperiodic.eventually_pos_pow_apply_singleton [IsIrreducible Measure.count κ]
    (h : κ.IsAperiodic) (x y : α) : ∀ᶠ n in atTop, 0 < (κ ^ n) x {y} :=
  have ⟨_, hxy⟩ := exists_pos_pow_apply_singleton (κ := κ) x y
  eventually_pos_pow_apply_singleton_of_period_eq_one (h x) hxy

/-- The return lengths of `x` under a deterministic kernel are the positive periods of `x`. -/
@[simp]
theorem returnLengths_deterministic {f : α → α} (hf : Measurable f) (x : α) :
    (deterministic f hf).returnLengths x = {n | 0 < n ∧ Function.IsPeriodicPt f n x} := by
  ext n
  simp [deterministic_pow, deterministic_apply, pos_iff_ne_zero,
    Set.indicator_apply_eq_zero, Function.IsPeriodicPt, Function.IsFixedPt]

/-- The period of `x` under the deterministic kernel of `f` is the minimal period of `x`
under `f`. In particular a point that is not periodic has period zero. -/
@[simp]
theorem period_deterministic {f : α → α} (hf : Measurable f) (x : α) :
    (deterministic f hf).period x = Function.minimalPeriod f x := by
  refine Nat.dvd_antisymm ?_ (dvd_period_iff.mpr fun n hn ↦ ?_)
  · rcases Nat.eq_zero_or_pos (Function.minimalPeriod f x) with h | h
    · simp [h]
    · exact period_dvd_of_mem_returnLengths <| (returnLengths_deterministic hf x).symm ▸
        ⟨h, Function.isPeriodicPt_minimalPeriod f x⟩
  · rw [returnLengths_deterministic] at hn
    exact Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hn.2

end MeasurableSingletonClass

end ProbabilityTheory.Kernel
