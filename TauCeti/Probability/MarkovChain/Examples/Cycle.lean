/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Probability.UniformOn
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Probability.Kernel.Reachability
public import TauCeti.Probability.MarkovChain.Invariant
public import TauCeti.Probability.MarkovChain.Occupation
public import TauCeti.Probability.MarkovChain.Period

/-!
# A deterministic finite-cycle chain

`cycleKernel n` moves from `x : Fin n` to `x + 1`, with addition modulo the positive
integer `n`. Its transition powers are point masses at `x + k`, every state reaches every
other state, its period is `n`, its mean return time at every state is `n`, every state is
positive recurrent (hence recurrent and neither transient nor null recurrent), and the
uniform probability is invariant.

Started at `x`, the path law is the point mass on the periodic trajectory `k ↦ x + k`.
Consequently the first entrance time to `y` is almost surely `(y - x).val` (in particular `0`
when `y = x`), while the first positive return time to `x` is almost surely `n` (and the first
positive passage time to `y ≠ x` is `(y - x).val`). At `n = 1`, the recurrent one-state chain
therefore has entrance time `0` and first positive return time `1`. Every state has mean return
time `n`, is positive recurrent (hence recurrent and not transient), and has infinite Green
function. Its cycle occupation measure is counting measure on `Fin n`, whose normalization by
`1 / n` recovers the uniform invariant probability.

Despite this invariant probability, starting from a point mass does not approach equilibrium in
total variation unless `n = 1`: at every time the total variation distance is `2 * (1 - 1 / n)`.
In contrast, the empirical positive-time occupation frequency of every state converges almost
surely (for every initial measure) and in expectation (for every initial probability measure) to
`1 / n`. The point-started trajectory, first entrance, and positive-time hitting evaluations, as
well as the empirical occupation limits, also transfer to realizations on arbitrary measurable
sample spaces via `ProbabilityTheory.HasLaw`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §§1.5, 1.7–1.8, and 1.10.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Fin.NatCast

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

/-! ### Path laws, entrance times, and positive return times -/

/-- Started at `x`, the path law of the finite cycle is the point mass on the periodic trajectory
`k ↦ x + k`. -/
@[simp] theorem markovChainLaw_dirac_cycleKernel (x : Fin n) :
    markovChainLaw (Measure.dirac x) (cycleKernel n) =
      Measure.dirac (fun k : ℕ => x + (k : Fin n)) := by
  have hlaw : markovChainLaw (Measure.dirac x) (cycleKernel n) =
      markovChainLaw (Measure.dirac x)
        (Kernel.deterministic (fun y : Fin n => y + 1) (measurable_of_countable _)) := by
    unfold cycleKernel
    congr!
  rw [hlaw, markovChainLaw_dirac_deterministic]
  simp [add_right_iterate, nsmul_one]

/-- The path-law kernel of `cycleKernel n` sends each initial state `x` deterministically to its
periodic trajectory `k ↦ x + k`. -/
@[simp] theorem markovChainKernel_cycleKernel :
    (cycleKernel n).markovChainKernel =
      Kernel.deterministic (fun (x : Fin n) (k : ℕ) => x + (k : Fin n))
        (measurable_pi_iff.2 fun _ => measurable_of_countable _) := by
  ext1 x
  rw [Kernel.markovChainKernel_apply, markovChainLaw_dirac_cycleKernel,
    Kernel.deterministic_apply]

/-- For any initial measure `ν`, the path law of `cycleKernel n` is the pushforward of `ν` along
the trajectory map `x ↦ (k ↦ x + k)`. -/
theorem markovChainLaw_cycleKernel (ν : Measure (Fin n)) :
    markovChainLaw ν (cycleKernel n) = ν.map (fun (x : Fin n) (k : ℕ) => x + (k : Fin n)) := by
  rw [Measure.markovChainLaw_eq_comp, markovChainKernel_cycleKernel,
    Measure.deterministic_comp_eq_map]

/-- Started at `x`, almost every trajectory of `cycleKernel n` follows `k ↦ x + k` at every time
simultaneously. -/
theorem ae_forall_eq_add_cycleKernel (x : Fin n) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) (cycleKernel n),
      ∀ k : ℕ, ω k = x + (k : Fin n) := by
  simp

/-- Started at `x`, the first entrance time to `y` (allowing time zero) is almost surely
`(y - x).val`. In particular, at `y = x` the entrance time is `0`. -/
theorem ae_hittingAfter_zero_cycleKernel (x y : Fin n) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) (cycleKernel n),
      hittingAfter (fun k ω => ω k) {y} 0 ω = ((y - x).val : WithTop ℕ) := by
  simp

/-- Under `cycleKernel n` started at `x`, the first entrance time to `y` has point-mass law at
`(y - x).val`. -/
theorem hasLaw_hittingAfter_zero_cycleKernel (x y : Fin n) :
    HasLaw (hittingAfter (fun k (ω : ℕ → Fin n) => ω k) {y} 0)
      (Measure.dirac ((y - x).val : WithTop ℕ))
      (markovChainLaw (Measure.dirac x) (cycleKernel n)) :=
  hasLaw_dirac_of_ae_eq (ae_hittingAfter_zero_cycleKernel n x y)

/-- Started at `x`, the first positive-time visit to `y` occurs almost surely at time `n` when
`y = x`, and at time `(y - x).val` when `y ≠ x`. In particular, at `n = 1` the recurrent
one-state chain enters `{x}` at time `0` (`ae_hittingAfter_zero_cycleKernel`) and first returns at
positive time `1`. -/
theorem ae_hittingAfter_one_cycleKernel (x y : Fin n) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) (cycleKernel n),
      hittingAfter (fun k ω => ω k) {y} 1 ω =
        if y = x then (n : WithTop ℕ) else ((y - x).val : WithTop ℕ) := by
  simp

/-- Under `cycleKernel n` started at `x`, the first positive-time visit to `y` has point-mass law
at `n` when `y = x` and at `(y - x).val` when `y ≠ x`. -/
theorem hasLaw_hittingAfter_one_cycleKernel (x y : Fin n) :
    HasLaw (hittingAfter (fun k (ω : ℕ → Fin n) => ω k) {y} 1)
      (Measure.dirac (if y = x then (n : WithTop ℕ) else ((y - x).val : WithTop ℕ)))
      (markovChainLaw (Measure.dirac x) (cycleKernel n)) :=
  hasLaw_dirac_of_ae_eq (ae_hittingAfter_one_cycleKernel n x y)

/-! ### Positive recurrence, cycle occupation, and empirical occupation limits -/

/-- Every state of `cycleKernel n` has mean return time `n`. -/
@[simp] theorem cycleKernel_meanReturnTime (x : Fin n) :
    (cycleKernel n).meanReturnTime x = n := by
  rw [Kernel.meanReturnTime_def, markovChainLaw_dirac_cycleKernel, lintegral_dirac,
    hittingAfter_one_add_natCast, ite_eq_left rfl]
  exact ENat.toENNReal_coe n

/-- Every state of the finite cycle is positive recurrent. -/
@[simp] theorem cycleKernel_isPositiveRecurrent (x : Fin n) :
    (cycleKernel n).IsPositiveRecurrent x := by
  rw [Kernel.isPositiveRecurrent_iff, cycleKernel_meanReturnTime]
  exact ENNReal.natCast_lt_top n

/-- Every state of the finite cycle is recurrent. -/
@[simp] theorem cycleKernel_isRecurrent (x : Fin n) :
    (cycleKernel n).IsRecurrent x :=
  (cycleKernel_isPositiveRecurrent n x).isRecurrent

/-- No state of the finite cycle is transient. -/
@[simp] theorem not_cycleKernel_isTransient (x : Fin n) :
    ¬ (cycleKernel n).IsTransient x := by
  simp [Kernel.isTransient_iff]

/-- From any initial measure, almost every trajectory of `cycleKernel n` enters `y` in finite
time. -/
theorem ae_hittingAfter_zero_ne_top_cycleKernel (ν : Measure (Fin n)) (y : Fin n) :
    ∀ᵐ ω ∂markovChainLaw ν (cycleKernel n),
      hittingAfter (fun k ω => ω k) {y} 0 ω ≠ ⊤ :=
  (cycleKernel_isRecurrent n y).ae_hittingAfter_ne_top_of_isIrreducible ν y

-- `cycleKernel_pow_apply` already reduces the summand on the left-hand side.
/-- The Green function of `cycleKernel n` is infinite between every pair of states. -/
theorem cycleKernel_tsum_pow_apply_singleton (x y : Fin n) :
    ∑' k : ℕ, (cycleKernel n ^ k) x {y} = ∞ := by
  have hdiag : ∑' k : ℕ, (cycleKernel n ^ k) y {y} = ∞ :=
    (cycleKernel_isPositiveRecurrent n y).tsum_pow_apply_singleton_self_eq_top
  have hhit : markovChainLaw (Measure.dirac x) (cycleKernel n)
      {ω | hittingAfter (fun k ω => ω k) {y} 0 ω ≠ ⊤} = 1 :=
    (mem_ae_iff_prob_eq_one
      (measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton y) 0)).mp
      (ae_hittingAfter_zero_ne_top_cycleKernel n (Measure.dirac x) y)
  have hcomp := (cycleKernel n).tsum_pow_comp_apply_singleton (Measure.dirac x) y
  simp_rw [Measure.dirac_bind (Kernel.measurable _)] at hcomp
  rw [hcomp, hhit, hdiag, one_mul]

/-- Normalizing the cycle occupation measure of `cycleKernel n` by the reciprocal mean return time
recovers the uniform invariant probability on `Fin n`. -/
theorem cycleKernel_inv_meanReturnTime_smul_cycleOccupation (x : Fin n) :
    ((cycleKernel n).meanReturnTime x)⁻¹ • (cycleKernel n).cycleOccupation x =
      uniformOn (Set.univ : Set (Fin n)) :=
  ((cycleKernel_invariant_uniformOn n).eq_inv_meanReturnTime_smul_cycleOccupation x).symm

/-- The cycle occupation measure of `cycleKernel n` around any state `x` is counting measure on
`Fin n`: every state is visited exactly once during one return cycle of length `n`. -/
@[simp] theorem cycleKernel_cycleOccupation (x : Fin n) :
    (cycleKernel n).cycleOccupation x = Measure.count := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h := congrArg ((n : ℝ≥0∞) • ·)
    (cycleKernel_inv_meanReturnTime_smul_cycleOccupation n x)
  rw [cycleKernel_meanReturnTime, smul_smul,
    ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top n), one_smul] at h
  rw [h]
  apply Measure.ext_iff_singleton.mpr
  intro y
  simp [uniformOn_univ, ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top n)]

/-- **Almost-sure empirical occupation limit of the finite cycle.** From any initial measure, the
fraction of positive times `1, …, m` spent at `y` converges almost surely to `1 / n`, even when
`n > 1` prevents total-variation convergence of the marginal laws. -/
theorem ae_tendsto_visitCount_div_cycleKernel (ν : Measure (Fin n)) (y : Fin n) :
    ∀ᵐ ω ∂markovChainLaw ν (cycleKernel n),
      Tendsto (fun m : ℕ => (visitCount (fun k => ω (k + 1)) y m : ℝ) / m)
        atTop (𝓝 (n : ℝ)⁻¹) := by
  filter_upwards [Measure.ae_tendsto_visitCount_div_markovChainLaw ν (cycleKernel n) y,
    ae_hittingAfter_zero_ne_top_cycleKernel n ν y] with ω hlim hhit
  simpa [hhit, cycleKernel_meanReturnTime, ENNReal.toReal_inv] using hlim

/-- **Expected empirical occupation limit of the finite cycle.** From any initial probability
measure, the expected fraction of positive times `1, …, m` spent at `y` converges to `1 / n`. -/
theorem tendsto_integral_visitCount_div_cycleKernel (ν : Measure (Fin n))
    [IsProbabilityMeasure ν] (y : Fin n) :
    Tendsto (fun m : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) y m : ℝ) / m
        ∂markovChainLaw ν (cycleKernel n))
      atTop (𝓝 (n : ℝ)⁻¹) := by
  have h1 : markovChainLaw ν (cycleKernel n)
      {ω | hittingAfter (fun k ω => ω k) {y} 0 ω ≠ ⊤} = 1 :=
    (mem_ae_iff_prob_eq_one
      (measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton y) 0)).mp
      (ae_hittingAfter_zero_ne_top_cycleKernel n ν y)
  have hprob : (markovChainLaw ν (cycleKernel n)).real
      {ω | hittingAfter (fun k ω => ω k) {y} 0 ω ≠ ⊤} = 1 := by
    simp [Measure.real, h1]
  simpa [hprob, cycleKernel_meanReturnTime, ENNReal.toReal_inv] using
    Measure.tendsto_integral_visitCount_div_markovChainLaw ν (cycleKernel n) y

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} [NeZero n]
  {X : Ω → ℕ → Fin n} {x : Fin n}

/-- Every realization of the finite cycle started at `x` follows `k ↦ x + k` at every time almost
surely. -/
theorem ae_forall_eq_add_cycleKernel
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (cycleKernel n)) P) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, X ω k = x + (k : Fin n) := by
  have h := TauCeti.Probability.ae_forall_eq_add_cycleKernel n x
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- Every realization of the finite cycle started at `x` enters `y` at time `(y - x).val` almost
surely. -/
theorem ae_hittingAfter_zero_cycleKernel
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (cycleKernel n)) P) (y : Fin n) :
    ∀ᵐ ω ∂P, hittingAfter (fun k ω => X ω k) {y} 0 ω = ((y - x).val : WithTop ℕ) := by
  have h := TauCeti.Probability.ae_hittingAfter_zero_cycleKernel n x y
  rw [← hX.map_eq] at h
  simpa only [hittingAfter_def] using ae_of_ae_map hX.aemeasurable h

/-- Transfer the point-mass first-entrance law of `cycleKernel n` to any realization of its path
law. -/
theorem hittingAfter_zero_cycleKernel
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (cycleKernel n)) P) (y : Fin n) :
    HasLaw (hittingAfter (fun k ω => X ω k) {y} 0)
      (Measure.dirac ((y - x).val : WithTop ℕ)) P :=
  (hasLaw_hittingAfter_zero_cycleKernel n x y).fun_comp hX

/-- Every realization of the finite cycle started at `x` has extended mean first entrance time
`(y - x).val` to `y`. -/
theorem lintegral_hittingAfter_zero_cycleKernel
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (cycleKernel n)) P) (y : Fin n) :
    (∫⁻ ω, ENat.toENNReal (hittingAfter (fun k ω => X ω k) {y} 0 ω) ∂P) =
      ((y - x).val : ℝ≥0∞) := by
  rw [(hX.hittingAfter_zero_cycleKernel y).lintegral_comp
    (f := fun t : WithTop ℕ => ENat.toENNReal t) aemeasurable_dirac,
    lintegral_dirac (f := fun t : WithTop ℕ => ENat.toENNReal t)]
  exact ENat.toENNReal_coe _

/-- Every realization of the finite cycle started at `x` first visits `y` at positive time `n` when
`y = x`, and at positive time `(y - x).val` when `y ≠ x`, almost surely. -/
theorem ae_hittingAfter_one_cycleKernel
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (cycleKernel n)) P) (y : Fin n) :
    ∀ᵐ ω ∂P, hittingAfter (fun k ω => X ω k) {y} 1 ω =
      if y = x then (n : WithTop ℕ) else ((y - x).val : WithTop ℕ) := by
  have h := TauCeti.Probability.ae_hittingAfter_one_cycleKernel n x y
  rw [← hX.map_eq] at h
  simpa only [hittingAfter_def] using ae_of_ae_map hX.aemeasurable h

/-- Transfer the point-mass positive hitting-time law of `cycleKernel n` to any realization of its
path law. -/
theorem hittingAfter_one_cycleKernel
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (cycleKernel n)) P) (y : Fin n) :
    HasLaw (hittingAfter (fun k ω => X ω k) {y} 1)
      (Measure.dirac (if y = x then (n : WithTop ℕ) else ((y - x).val : WithTop ℕ))) P :=
  (hasLaw_hittingAfter_one_cycleKernel n x y).fun_comp hX

/-- Every realization of the finite cycle started at `x` has extended mean first positive-time
visit `n` when `y = x`, and `(y - x).val` when `y ≠ x`. -/
theorem lintegral_hittingAfter_one_cycleKernel
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (cycleKernel n)) P) (y : Fin n) :
    (∫⁻ ω, ENat.toENNReal (hittingAfter (fun k ω => X ω k) {y} 1 ω) ∂P) =
      if y = x then (n : ℝ≥0∞) else ((y - x).val : ℝ≥0∞) := by
  rw [(hX.hittingAfter_one_cycleKernel y).lintegral_comp
    (f := fun t : WithTop ℕ => ENat.toENNReal t) aemeasurable_dirac,
    lintegral_dirac (f := fun t : WithTop ℕ => ENat.toENNReal t)]
  split_ifs <;> exact ENat.toENNReal_coe _

/-- Almost-sure empirical occupation convergence to `1 / n` transfers to any realization of
`cycleKernel n` on an arbitrary measurable sample space. -/
theorem ae_tendsto_visitCount_div_cycleKernel {ν : Measure (Fin n)}
    (hX : HasLaw X (markovChainLaw ν (cycleKernel n)) P) (y : Fin n) :
    ∀ᵐ ω ∂P,
      Tendsto (fun m : ℕ => (visitCount (fun k => X ω (k + 1)) y m : ℝ) / m)
        atTop (𝓝 (n : ℝ)⁻¹) := by
  have h := TauCeti.Probability.ae_tendsto_visitCount_div_cycleKernel n ν y
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- Expected empirical occupation convergence to `1 / n` transfers to any realization of
`cycleKernel n` from an initial probability measure. -/
theorem tendsto_integral_visitCount_div_cycleKernel {ν : Measure (Fin n)}
    [IsProbabilityMeasure ν]
    (hX : HasLaw X (markovChainLaw ν (cycleKernel n)) P) (y : Fin n) :
    Tendsto (fun m : ℕ => ∫ ω, (visitCount (fun k => X ω (k + 1)) y m : ℝ) / m ∂P)
      atTop (𝓝 (n : ℝ)⁻¹) := by
  have hm (m : ℕ) : Measurable (fun w : ℕ → Fin n =>
      (visitCount (fun k => w (k + 1)) y m : ℝ) / m) :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_visitCount_comp y m (measurableSet_singleton y)
        (fun i _ => measurable_pi_apply (i + 1)))).div_const m
  have hint (m : ℕ) : (∫ ω, (visitCount (fun k => X ω (k + 1)) y m : ℝ) / m ∂P) =
      ∫ w, (visitCount (fun k => w (k + 1)) y m : ℝ) / m
        ∂markovChainLaw ν (cycleKernel n) :=
    hX.integral_comp (hm m).aestronglyMeasurable
  simp_rw [hint]
  exact TauCeti.Probability.tendsto_integral_visitCount_div_cycleKernel n ν y

end ProbabilityTheory.HasLaw
