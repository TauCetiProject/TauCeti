/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.UniformOn
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.Kernel.Reachability
public import TauCeti.Probability.MarkovChain.Period

/-!
# A deterministic finite-cycle chain

`cycleKernel n` moves from `x : Fin n` to `x + 1`, with addition modulo the positive
integer `n`. Its transition powers are point masses at `x + k`, every state reaches every
other state, its period is exactly `n`, and the uniform probability is invariant.

Despite this invariant probability, starting from a point mass does not approach equilibrium
unless `n = 1`: at every time the total variation distance is `2 * (1 - 1 / n)`.
This example distinguishes stationarity from convergence and exhibits the role of aperiodicity.
The formulas include the one-state chain, whose period is one and whose distance is zero.

For the cycle example and the aperiodicity requirement, see J. R. Norris, *Markov Chains*
(Cambridge University Press, 1997), §1.8. The construction uses Mathlib's deterministic
kernel and uniform measure, not a separate representation of transition matrices.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Fin.NatCast

namespace TauCeti.Probability

variable (n : ℕ) [NeZero n]

/-- The deterministic chain on `Fin n` that advances by one modulo `n`. -/
def cycleKernel : Kernel (Fin n) (Fin n) :=
  Kernel.deterministic (fun x => x + 1) (measurable_of_countable _)

/-- Every row of the finite-cycle transition kernel is a probability measure. -/
instance : IsMarkovKernel (cycleKernel n) := by
  unfold cycleKernel
  infer_instance

/-- The one-step law is the point mass at the next state. -/
@[simp] theorem cycleKernel_apply (x : Fin n) :
    cycleKernel n x = Measure.dirac (x + 1) :=
  Kernel.deterministic_apply _ _

/-- After `k` steps the cycle is at `x + k`, with addition modulo `n`. -/
@[simp] theorem cycleKernel_pow_apply (k : ℕ) (x : Fin n) :
    (cycleKernel n ^ k) x = Measure.dirac (x + (k : Fin n)) := by
  simp [cycleKernel, Kernel.deterministic_pow, Kernel.deterministic_apply,
    add_right_iterate, nsmul_one]

/-- The elementary transition probabilities of the finite cycle. -/
theorem cycleKernel_pow_apply_singleton (k : ℕ) (x y : Fin n) :
    (cycleKernel n ^ k) x {y} = if x + (k : Fin n) = y then 1 else 0 := by
  rw [cycleKernel_pow_apply, Measure.dirac_apply' _ (measurableSet_singleton _)]
  simp [Set.indicator, eq_comm]

-- The row formula already supplies the simp normal form of this left-hand side.
/-- The return probability is one at multiples of the cycle length, and zero otherwise. -/
theorem cycleKernel_pow_apply_singleton_self (k : ℕ) (x : Fin n) :
    (cycleKernel n ^ k) x {x} = if n ∣ k then 1 else 0 := by
  rw [cycleKernel_pow_apply_singleton]
  simp [Fin.natCast_eq_zero]

/-- From a point mass, the time-`k` distribution is again a point mass. -/
@[simp] theorem cycleKernel_pow_comp_dirac (k : ℕ) (x : Fin n) :
    (cycleKernel n ^ k) ∘ₘ Measure.dirac x = Measure.dirac (x + (k : Fin n)) := by
  rw [Measure.dirac_bind (Kernel.measurable _)]
  exact cycleKernel_pow_apply n k x

/-- Any state can be reached in fewer than `n` steps. -/
theorem cycleKernel_exists_pos_pow_apply_singleton (x y : Fin n) :
    ∃ k < n, 0 < (cycleKernel n ^ k) x {y} := by
  refine ⟨(y - x).val, (y - x).isLt, ?_⟩
  rw [cycleKernel_pow_apply_singleton]
  simp

/-- The finite-cycle chain is irreducible with respect to counting measure. -/
instance : Kernel.IsIrreducible Measure.count (cycleKernel n) := by
  rw [Kernel.isIrreducible_count_iff_forall_reaches]
  intro x y
  obtain ⟨k, _, hk⟩ := cycleKernel_exists_pos_pow_apply_singleton n x y
  exact (Kernel.reaches_def x y).mpr ⟨k, hk⟩

/-- The positive return lengths are exactly the positive multiples of `n`. -/
@[simp] theorem cycleKernel_returnLengths (x : Fin n) :
    (cycleKernel n).returnLengths x = {k | 0 < k ∧ n ∣ k} := by
  ext k
  simp only [Kernel.mem_returnLengths, Set.mem_ofPred_eq,
    cycleKernel_pow_apply_singleton_self]
  by_cases h : n ∣ k <;> simp [h]

/-- Every state of the finite cycle has period exactly the cycle length. -/
@[simp] theorem cycleKernel_period (x : Fin n) : (cycleKernel n).period x = n := by
  apply Nat.dvd_antisymm
  · exact Kernel.period_dvd_of_mem_returnLengths (by simp [NeZero.pos n])
  · exact Kernel.dvd_period_iff.mpr fun k hk => by
      simpa using ((cycleKernel_returnLengths n x) ▸ hk).2

/-- The finite cycle is aperiodic exactly in the one-state case. -/
@[simp] theorem cycleKernel_isAperiodic_iff : (cycleKernel n).IsAperiodic ↔ n = 1 := by
  simp [Kernel.isAperiodic_iff]

/-- The uniform law is stationary for the deterministic finite cycle. -/
theorem cycleKernel_invariant_uniformOn :
    (cycleKernel n).Invariant (uniformOn (Set.univ : Set (Fin n))) := by
  rw [Kernel.Invariant, cycleKernel, Measure.deterministic_comp_eq_map]
  apply Measure.ext_iff_singleton.mpr
  intro y
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (fun x : Fin n => x + 1) ⁻¹' {y} = {y - 1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact eq_sub_iff_add_eq.symm
  rw [hpre]
  simp [uniformOn_univ]

/-- At every time, the distance from a point-started cycle to its invariant uniform law is
`2 * (1 - 1 / n)`, with Mathlib's total variation normalization. -/
theorem cycleKernel_tvDist_uniformOn (k : ℕ) (x : Fin n) :
    tvDist ((cycleKernel n ^ k) ∘ₘ Measure.dirac x)
        (uniformOn (Set.univ : Set (Fin n))) = 2 * (1 - (n : ℝ)⁻¹) := by
  rw [cycleKernel_pow_comp_dirac, tvDist_dirac_left]
  simp [Measure.real, uniformOn_univ]

/-- Convergence to the invariant uniform probability from a point mass occurs exactly for
the one-state cycle. In particular, stationarity alone does not imply convergence. -/
theorem cycleKernel_tendsto_tvDist_uniformOn_iff (x : Fin n) :
    Tendsto (fun k : ℕ => tvDist ((cycleKernel n ^ k) ∘ₘ Measure.dirac x)
      (uniformOn (Set.univ : Set (Fin n)))) atTop (nhds 0) ↔ n = 1 := by
  simp only [cycleKernel_tvDist_uniformOn]
  rw [tendsto_const_nhds_iff]
  constructor
  · intro h
    have hi : (n : ℝ)⁻¹ = 1 := by linarith
    have : (n : ℝ) = 1 := (inv_eq_one).mp hi
    exact_mod_cast this
  · rintro rfl
    norm_num

end TauCeti.Probability
