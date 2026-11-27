/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.MeasureTheory.Measure.TotalVariation.Countable
public import TauCeti.Probability.Kernel.Invariance
public import TauCeti.Probability.MarkovChain.Examples.Absorbing
public import TauCeti.Probability.MarkovChain.Invariant

/-!
# The general two-state chain

`twoStateChain a b` is the Markov kernel on `Bool` that moves from `false` to `true` with
probability `a` and from `true` to `false` with probability `b`, staying put otherwise. Every
quantity of the equilibrium theory is explicit for it, which makes it the basic test case for
invariance, detailed balance, Kac's formula and convergence in total variation.

* The one-step transition probabilities are `a`, `1 - a`, `b` and `1 - b`
  (`twoStateChain_false_real_true`, `twoStateChain_false_real_false`,
  `twoStateChain_true_real_false`, `twoStateChain_true_real_true`).
* After one step the mass at `true` is `a` times the mass at `false` plus `1 - b` times the mass
  at `true` (`twoStateChain_comp_real_true`). Hence, for two initial measures of the same total
  mass, the difference of the masses at `true` is multiplied by `1 - a - b` at every step
  (`twoStateChain_pow_comp_real_true_sub`), and the total variation distance is multiplied by
  exactly `|1 - a - b|` (`tvDist_twoStateChain_pow_comp`).
* A finite measure `π` satisfies detailed balance exactly when `π {false} * a = π {true} * b`
  (`twoStateChain_isReversible_iff`). The law `twoStateEquilibrium a b`, with mass `a / (a + b)` at
  `true`, satisfies it and is invariant; when `a + b ≠ 0` it is the only invariant probability
  (`twoStateChain_invariant_iff`). When `a = b = 0` the kernel is the identity, every probability
  is invariant, and `twoStateEquilibrium 0 0` is the point mass at `false`.
* The law at time `n` has mass `a / (a + b) + (1 - a - b) ^ n * (ν {true} - a / (a + b))` at `true`
  (`twoStateChain_pow_comp_real_true`), and started at `false` its total variation distance to
  equilibrium is `2 * a / (a + b) * |1 - a - b| ^ n`
  (`tvDist_twoStateChain_pow_false_twoStateEquilibrium`).
* The chain is irreducible exactly when `a` and `b` are nonzero
  (`twoStateChain_isIrreducible_iff`). Kac's formula then gives the mean return times
  `(a + b) / b` to `false` and `(a + b) / a` to `true`, with no aperiodicity assumption; the same
  formulas hold when the target state is absorbing (`twoStateChain_meanReturnTime_false`,
  `twoStateChain_meanReturnTime_true`).

The absorbing chain `absorbingChain p` is the case `a = 1 - p`, `b = 0`
(`absorbingChain_eq_twoStateChain`). For `a = b = 1` the chain always switches: its invariant law
is uniform, yet started at `false` the distance to equilibrium is `1` at every time, so the
aperiodicity hypothesis of the convergence theorem cannot be dropped.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Example 1.1.4 and §§1.7–1.8.
* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, §1.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable (a b : unitInterval)

/-- The two-state chain on `Bool` that moves from `false` to `true` with probability `a` and from
`true` to `false` with probability `b`, staying put otherwise. -/
def twoStateChain : Kernel Bool Bool :=
  Kernel.ofFunOfCountable fun x =>
    if x then bernoulliMeasure false true b else bernoulliMeasure true false a

/-- From `false` the chain moves to `true` with probability `a`. -/
@[simp] theorem twoStateChain_false : twoStateChain a b false = bernoulliMeasure true false a :=
  (rfl)

/-- From `true` the chain moves to `false` with probability `b`. -/
@[simp] theorem twoStateChain_true : twoStateChain a b true = bernoulliMeasure false true b :=
  (rfl)

instance : IsMarkovKernel (twoStateChain a b) :=
  ⟨fun x => by cases x <;> simp only [twoStateChain_false, twoStateChain_true] <;> infer_instance⟩

/-- From `false` the chain moves to `true` with probability `a`. -/
theorem twoStateChain_false_real_true : (twoStateChain a b false).real {true} = a := by
  simp

/-- From `false` the chain stays at `false` with probability `1 - a`. -/
theorem twoStateChain_false_real_false : (twoStateChain a b false).real {false} = 1 - a := by
  simp

/-- From `true` the chain moves to `false` with probability `b`. -/
theorem twoStateChain_true_real_false : (twoStateChain a b true).real {false} = b := by
  simp

/-- From `true` the chain stays at `true` with probability `1 - b`. -/
theorem twoStateChain_true_real_true : (twoStateChain a b true).real {true} = 1 - b := by
  simp

/-- From `false` the chain moves to `true` with probability `a`, as an extended real. -/
theorem twoStateChain_false_singleton_true :
    twoStateChain a b false {true} = ENNReal.ofReal a := by
  rw [← ofReal_measureReal, twoStateChain_false_real_true]

/-- From `true` the chain moves to `false` with probability `b`, as an extended real. -/
theorem twoStateChain_true_singleton_false :
    twoStateChain a b true {false} = ENNReal.ofReal b := by
  rw [← ofReal_measureReal, twoStateChain_true_real_false]

/-- The absorbing chain `absorbingChain p` is the two-state chain that leaves `false` with
probability `1 - p` and never leaves `true`. -/
theorem absorbingChain_eq_twoStateChain (p : unitInterval) :
    absorbingChain p = twoStateChain (unitInterval.symm p) 0 := by
  refine Kernel.ext fun x => ?_
  cases x
  · simp [bernoulliMeasure_def, add_comm]
  · simp

/-- **One step of the two-state chain.** The new mass at `true` is the flow `a` out of `false`
plus the mass `1 - b` that stays at `true`. -/
theorem twoStateChain_comp_real_true (ν : Measure Bool) [IsFiniteMeasure ν] :
    (twoStateChain a b ∘ₘ ν).real {true} = a * ν.real {false} + (1 - b) * ν.real {true} := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton true)
    (twoStateChain a b).aemeasurable, lintegral_fintype, Fintype.sum_bool,
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [← measureReal_def, twoStateChain_false_real_true, twoStateChain_true_real_true]
  ring

/-- **Geometric contraction.** For two finite initial measures of the same total mass, the
difference of the masses at `true` after `n` steps is `(1 - a - b) ^ n` times the initial
difference. -/
theorem twoStateChain_pow_comp_real_true_sub (n : ℕ) {ν ν' : Measure Bool} [IsFiniteMeasure ν]
    (h : ν Set.univ = ν' Set.univ) :
    ((twoStateChain a b ^ n) ∘ₘ ν).real {true} - ((twoStateChain a b ^ n) ∘ₘ ν').real {true} =
      (1 - a - b) ^ n * (ν.real {true} - ν'.real {true}) := by
  have : IsFiniteMeasure ν' := ⟨h ▸ measure_lt_top ν Set.univ⟩
  induction n with
  | zero => simp [Kernel.one_def]
  | succ n ih =>
    rw [pow_succ', Kernel.mul_def, ← Measure.comp_assoc, ← Measure.comp_assoc,
      twoStateChain_comp_real_true, twoStateChain_comp_real_true, pow_succ', mul_assoc, ← ih]
    -- The masses at `false` are determined by the common total mass.
    have huniv : ((twoStateChain a b ^ n) ∘ₘ ν).real Set.univ =
        ((twoStateChain a b ^ n) ∘ₘ ν').real Set.univ := by
      simp only [measureReal_def, Measure.comp_apply_univ, h]
    rw [measureReal_singleton_false (μ := (twoStateChain a b ^ n : Kernel Bool Bool) ∘ₘ ν),
      measureReal_singleton_false (μ := (twoStateChain a b ^ n : Kernel Bool Bool) ∘ₘ ν'), huniv]
    ring

/-- **Exact contraction in total variation.** For two finite initial measures of the same total
mass, `n` steps of the two-state chain multiply their total variation distance by
`|1 - a - b| ^ n`. -/
theorem tvDist_twoStateChain_pow_comp (n : ℕ) {ν ν' : Measure Bool} [IsFiniteMeasure ν]
    (h : ν Set.univ = ν' Set.univ) :
    tvDist ((twoStateChain a b ^ n : Kernel Bool Bool) ∘ₘ ν)
        ((twoStateChain a b ^ n : Kernel Bool Bool) ∘ₘ ν') =
      |1 - (a : ℝ) - b| ^ n * tvDist ν ν' := by
  rw [tvDist_eq_two_mul_abs_measureReal_true (by simp only [Measure.comp_apply_univ, h]),
    twoStateChain_pow_comp_real_true_sub a b n h, tvDist_eq_two_mul_abs_measureReal_true h,
    abs_mul, abs_pow]
  ring

/-- The weight `a / (a + b)` of `true` at equilibrium, as a point of the unit interval. It is zero
when `a = b = 0`. -/
private def equilibriumWeight : unitInterval :=
  have ha := unitInterval.nonneg a
  have hb := unitInterval.nonneg b
  ⟨a / (a + b), div_nonneg ha (add_nonneg ha hb),
    div_le_one_of_le₀ (le_add_of_nonneg_right hb) (add_nonneg ha hb)⟩

/-- The equilibrium law of `twoStateChain a b`: mass `a / (a + b)` at `true` and the rest at
`false`. When `a = b = 0` it is the point mass at `false`. -/
def twoStateEquilibrium : Measure Bool :=
  bernoulliMeasure true false (equilibriumWeight a b)

instance : IsProbabilityMeasure (twoStateEquilibrium a b) := by
  unfold twoStateEquilibrium; infer_instance

/-- The equilibrium mass of `true` is `a / (a + b)`. -/
@[simp] theorem twoStateEquilibrium_real_true :
    (twoStateEquilibrium a b).real {true} = a / (a + b) := by
  simp [twoStateEquilibrium, equilibriumWeight, bernoulliMeasure_real_apply_of_mem_of_notMem]

/-- The equilibrium mass of `false` is `1 - a / (a + b)`. -/
@[simp] theorem twoStateEquilibrium_real_false :
    (twoStateEquilibrium a b).real {false} = 1 - a / (a + b) := by
  simp [twoStateEquilibrium, equilibriumWeight, bernoulliMeasure_real_apply_of_notMem_of_mem]

/-- When `a + b ≠ 0`, the equilibrium mass of `false` is `b / (a + b)`. -/
theorem twoStateEquilibrium_real_false_of_add_ne_zero (hab : (a : ℝ) + b ≠ 0) :
    (twoStateEquilibrium a b).real {false} = b / (a + b) := by
  rw [twoStateEquilibrium_real_false]
  field_simp
  ring

/-- **Detailed balance for two states.** A finite measure is reversible for the two-state chain
exactly when the flow `π {false} * a` from `false` to `true` equals the flow `π {true} * b` back. -/
theorem twoStateChain_isReversible_iff (π : Measure Bool) [IsFiniteMeasure π] :
    (twoStateChain a b).IsReversible π ↔ π.real {false} * a = π.real {true} * b := by
  rw [Kernel.isReversible_iff_singleton]
  have hflow : π {false} * twoStateChain a b false {true} =
      π {true} * twoStateChain a b true {false} ↔ π.real {false} * a = π.real {true} * b := by
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ← measureReal_def, twoStateChain_false_real_true,
      twoStateChain_true_real_false]
  refine ⟨fun h => hflow.mp (h false true), fun h x y => ?_⟩
  cases x <;> cases y
  · rfl
  · exact hflow.mpr h
  · exact (hflow.mpr h).symm
  · rfl

/-- The equilibrium law satisfies detailed balance. -/
theorem twoStateChain_isReversible_twoStateEquilibrium :
    (twoStateChain a b).IsReversible (twoStateEquilibrium a b) := by
  rw [twoStateChain_isReversible_iff, twoStateEquilibrium_real_false,
    twoStateEquilibrium_real_true]
  by_cases hab : (a : ℝ) + b = 0
  · have ha : (a : ℝ) = 0 := by linarith [unitInterval.nonneg a, unitInterval.nonneg b]
    simp [ha]
  · field_simp
    ring

/-- The equilibrium law is invariant. -/
theorem twoStateChain_invariant_twoStateEquilibrium :
    (twoStateChain a b).Invariant (twoStateEquilibrium a b) :=
  (twoStateChain_isReversible_twoStateEquilibrium a b).invariant

/-- **Uniqueness of the invariant probability.** Unless the chain is the identity (`a = b = 0`),
a probability on `Bool` is invariant exactly when it is the equilibrium law. -/
theorem twoStateChain_invariant_iff (hab : (a : ℝ) + b ≠ 0) (π : Measure Bool)
    [IsProbabilityMeasure π] :
    (twoStateChain a b).Invariant π ↔ π = twoStateEquilibrium a b := by
  refine ⟨fun hπ => ?_, fun h => h ▸ twoStateChain_invariant_twoStateEquilibrium a b⟩
  have h1 := twoStateChain_pow_comp_real_true_sub a b 1
    (ν := π) (ν' := twoStateEquilibrium a b) (measure_univ.trans measure_univ.symm)
  rw [hπ.pow_comp, (twoStateChain_invariant_twoStateEquilibrium a b).pow_comp, pow_one] at h1
  have hzero : π.real {true} - (twoStateEquilibrium a b).real {true} = 0 := by
    have : ((a : ℝ) + b) * (π.real {true} - (twoStateEquilibrium a b).real {true}) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left hab
  rw [← tvDist_eq_zero_iff,
    tvDist_eq_two_mul_abs_measureReal_true (measure_univ.trans measure_univ.symm), hzero,
    abs_zero, mul_zero]

/-- **The law at time `n`.** From a probability `ν`, the mass at `true` after `n` steps is
`a / (a + b) + (1 - a - b) ^ n * (ν {true} - a / (a + b))`. -/
theorem twoStateChain_pow_comp_real_true (n : ℕ) (ν : Measure Bool) [IsProbabilityMeasure ν] :
    ((twoStateChain a b ^ n) ∘ₘ ν).real {true} =
      a / (a + b) + (1 - a - b) ^ n * (ν.real {true} - a / (a + b)) := by
  have h := twoStateChain_pow_comp_real_true_sub a b n
    (ν := ν) (ν' := twoStateEquilibrium a b) (measure_univ.trans measure_univ.symm)
  rw [(twoStateChain_invariant_twoStateEquilibrium a b).pow_comp,
    twoStateEquilibrium_real_true] at h
  linear_combination h

/-- Started at `false`, the mass at `true` after `n` steps is
`a / (a + b) * (1 - (1 - a - b) ^ n)`. -/
theorem twoStateChain_pow_false_real_true (n : ℕ) :
    ((twoStateChain a b ^ n) false).real {true} = a / (a + b) * (1 - (1 - a - b) ^ n) := by
  rw [← Measure.dirac_bind (twoStateChain a b ^ n).measurable, twoStateChain_pow_comp_real_true,
    Measure.dirac_real_apply, Set.indicator_of_notMem (by simp)]
  ring

/-- Started at `true`, the mass at `true` after `n` steps is
`a / (a + b) + (1 - a - b) ^ n * (1 - a / (a + b))`. -/
theorem twoStateChain_pow_true_real_true (n : ℕ) :
    ((twoStateChain a b ^ n) true).real {true} =
      a / (a + b) + (1 - a - b) ^ n * (1 - a / (a + b)) := by
  rw [← Measure.dirac_bind (twoStateChain a b ^ n).measurable, twoStateChain_pow_comp_real_true,
    Measure.dirac_real_apply_of_mem rfl]

/-- **Distance to equilibrium.** From a probability `ν`, the total variation distance to the
equilibrium law after `n` steps is `|1 - a - b| ^ n` times the initial distance. -/
theorem tvDist_twoStateChain_pow_comp_twoStateEquilibrium (n : ℕ) (ν : Measure Bool)
    [IsProbabilityMeasure ν] :
    tvDist ((twoStateChain a b ^ n : Kernel Bool Bool) ∘ₘ ν) (twoStateEquilibrium a b) =
      |1 - (a : ℝ) - b| ^ n * tvDist ν (twoStateEquilibrium a b) := by
  conv_lhs => rw [← (twoStateChain_invariant_twoStateEquilibrium a b).pow_comp n]
  exact tvDist_twoStateChain_pow_comp a b n (measure_univ.trans measure_univ.symm)

/-- Started at `false`, the total variation distance to equilibrium after `n` steps is
`2 * a / (a + b) * |1 - a - b| ^ n`. -/
theorem tvDist_twoStateChain_pow_false_twoStateEquilibrium (n : ℕ) :
    tvDist ((twoStateChain a b ^ n) false) (twoStateEquilibrium a b) =
      2 * (a / (a + b)) * |1 - (a : ℝ) - b| ^ n := by
  rw [← Measure.dirac_bind (twoStateChain a b ^ n).measurable,
    tvDist_twoStateChain_pow_comp_twoStateEquilibrium, tvDist_dirac_left,
    twoStateEquilibrium_real_false]
  ring

/-- Started at `true`, the total variation distance to equilibrium after `n` steps is
`2 * (1 - a / (a + b)) * |1 - a - b| ^ n`. -/
theorem tvDist_twoStateChain_pow_true_twoStateEquilibrium (n : ℕ) :
    tvDist ((twoStateChain a b ^ n) true) (twoStateEquilibrium a b) =
      2 * (1 - a / (a + b)) * |1 - (a : ℝ) - b| ^ n := by
  rw [← Measure.dirac_bind (twoStateChain a b ^ n).measurable,
    tvDist_twoStateChain_pow_comp_twoStateEquilibrium, tvDist_dirac_left,
    twoStateEquilibrium_real_true]
  ring

/-- **Irreducibility.** The two-state chain is irreducible exactly when both switching
probabilities are nonzero. -/
theorem twoStateChain_isIrreducible_iff :
    Kernel.IsIrreducible Measure.count (twoStateChain a b) ↔ a ≠ 0 ∧ b ≠ 0 := by
  rw [Kernel.isIrreducible_count_iff_forall_reaches]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨ha, hb⟩ x y => ?_⟩
  · -- If `a = 0`, the chain never leaves `false`.
    rintro rfl
    obtain ⟨n, hn⟩ := (Kernel.reaches_def _ _).mp (h false true)
    have hreal := twoStateChain_pow_false_real_true 0 b n
    simp only [Set.Icc.coe_zero, zero_div, zero_mul] at hreal
    rw [measureReal_eq_zero_iff] at hreal
    exact hn.ne' hreal
  · -- If `b = 0`, the chain never leaves `true`.
    rintro rfl
    obtain ⟨n, hn⟩ := (Kernel.reaches_def _ _).mp (h true false)
    have hreal : ((twoStateChain a 0 ^ n) true).real {false} = 0 := by
      rw [measureReal_singleton_false, probReal_univ, twoStateChain_pow_true_real_true]
      by_cases ha : (a : ℝ) = 0 <;> simp [ha]
    rw [measureReal_eq_zero_iff] at hreal
    exact hn.ne' hreal
  · cases x <;> cases y
    · exact Kernel.Reaches.refl _
    · refine Kernel.reaches_of_pos ?_
      rw [twoStateChain_false_singleton_true]
      exact ENNReal.ofReal_pos.mpr (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr ha))
    · refine Kernel.reaches_of_pos ?_
      rw [twoStateChain_true_singleton_false]
      exact ENNReal.ofReal_pos.mpr (unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hb))
    · exact Kernel.Reaches.refl _

/-- **Mean return time to `false`.** If `b ≠ 0`, the mean return time to `false` is
`(a + b) / b`. For `a ≠ 0` this is Kac's formula for the irreducible chain, with no aperiodicity
needed; for `a = 0` the state `false` is absorbing and the mean return time is `1`. -/
theorem twoStateChain_meanReturnTime_false (hb : b ≠ 0) :
    (twoStateChain a b).meanReturnTime false = ENNReal.ofReal ((a + b) / b) := by
  have hb' : (0 : ℝ) < b := unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hb)
  by_cases ha : a = 0
  · subst ha
    rw [Kernel.meanReturnTime_eq_one_of_apply_singleton_self (by simp), Set.Icc.coe_zero,
      zero_add, div_self hb'.ne', ENNReal.ofReal_one]
  have := (twoStateChain_isIrreducible_iff a b).mpr ⟨ha, hb⟩
  have hab : (0 : ℝ) < a + b := by linarith [unitInterval.nonneg a]
  rw [← inv_inv ((twoStateChain a b).meanReturnTime false),
    ← (twoStateChain_invariant_twoStateEquilibrium a b).apply_singleton_eq_inv_meanReturnTime false,
    ← ofReal_measureReal, twoStateEquilibrium_real_false_of_add_ne_zero a b hab.ne',
    ← ENNReal.ofReal_inv_of_pos (div_pos hb' hab), inv_div]

/-- **Mean return time to `true`.** If `a ≠ 0`, the mean return time to `true` is `(a + b) / a`.
For `b ≠ 0` this is Kac's formula for the irreducible chain, with no aperiodicity needed; for
`b = 0` the state `true` is absorbing and the mean return time is `1`. -/
theorem twoStateChain_meanReturnTime_true (ha : a ≠ 0) :
    (twoStateChain a b).meanReturnTime true = ENNReal.ofReal ((a + b) / a) := by
  have ha' : (0 : ℝ) < a := unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr ha)
  by_cases hb : b = 0
  · subst hb
    rw [Kernel.meanReturnTime_eq_one_of_apply_singleton_self (by simp), Set.Icc.coe_zero,
      add_zero, div_self ha'.ne', ENNReal.ofReal_one]
  have := (twoStateChain_isIrreducible_iff a b).mpr ⟨ha, hb⟩
  have hab : (0 : ℝ) < a + b := by linarith [unitInterval.nonneg b]
  rw [← inv_inv ((twoStateChain a b).meanReturnTime true),
    ← (twoStateChain_invariant_twoStateEquilibrium a b).apply_singleton_eq_inv_meanReturnTime true,
    ← ofReal_measureReal, twoStateEquilibrium_real_true,
    ← ENNReal.ofReal_inv_of_pos (div_pos ha' hab), inv_div]

end TauCeti.Probability
