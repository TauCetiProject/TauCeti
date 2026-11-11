/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Lebesgue.Encard
public import TauCeti.Probability.MarkovChain.StrongMarkov.Basic
public import TauCeti.Probability.Process.SuccessiveVisits

/-!
# The number of visits of a Markov chain to a state

Let `X` be the coordinate process on path space `ℕ → α` under the path law `markovChainLaw ν κ`,
write `ℙ_y = markovChainLaw (dirac y) κ` for the law of the chain started at `y`, and fix a state
`y`. Write `H_y = hittingAfter X {y} 0` for the first entrance time of `y`, which may be time zero,
and `T_y⁺ = hittingAfter X {y} 1` for the first return time, which is positive. The *return
probability* of `y` is `ρ_y = ℙ_y(T_y⁺ < ∞)`.

The visits of the path to `y`, counted from the first entrance as visit zero, occur at the
stopping times `successiveVisit X y k`. At each existing visit the chain is at `y`, so by the
strong Markov property the path after that visit is a fresh chain started at `y`; the next visit
exists exactly when this fresh chain returns. Hence the number of visits has a geometric tail:

```text
ℙ_ν(visit k exists) = ℙ_ν(H_y < ∞) · ρ_y ^ k.
```

This gives the recurrence/transience dichotomy for the visits of a single state.

* If `ρ_y = 1`, then almost surely every path that reaches `y` visits it infinitely often. Started
  at `y`, the chain returns to `y` infinitely often almost surely, which is the hypothesis of the
  excursion decomposition `TauCeti.Probability.markovChainLaw_eq_map_pathOfExcursions`.
* If `ρ_y < 1`, then from every initial law the chain visits `y` only finitely often almost
  surely.

Summing the tail gives the mean number of visits. Since the chain is at `y` at time `n` with
probability `((κ ^ n) ∘ₘ ν) {y}`, this mean is the Green function
`G(ν, y) = ∑ n, ((κ ^ n) ∘ₘ ν) {y}`, and

```text
G(y, y) = ∑ n, (κ ^ n) y {y} = (1 - ρ_y)⁻¹,      G(ν, y) = ℙ_ν(H_y < ∞) · G(y, y)
```

in `ℝ≥0∞`. In particular `y` satisfies `ρ_y = 1` exactly when `∑ n, (κ ^ n) y {y} = ∞`.

## Main results

* `MeasureTheory.Measure.markovChainLaw_setOf_successiveVisit_ne_top`: the geometric tail
  `ℙ_ν(visit k exists) = ℙ_ν(H_y < ∞) · ρ_y ^ k`.
* `MeasureTheory.Measure.ae_infinite_setOf_eq_of_hittingAfter_ne_top` and
  `ProbabilityTheory.Kernel.ae_infinite_setOf_eq_markovChainLaw_dirac`: if `ρ_y = 1`, a path that
  reaches `y` visits it infinitely often almost surely.
* `MeasureTheory.Measure.markovChainLaw_setOf_infinite_setOf_eq_eq_zero`: if `ρ_y < 1`, the chain
  visits `y` infinitely often with probability zero.
* `MeasureTheory.Measure.lintegral_encard_setOf_eq_markovChainLaw`: the mean number of visits is
  `ℙ_ν(H_y < ∞) · (1 - ρ_y)⁻¹`.
* `ProbabilityTheory.Kernel.tsum_pow_comp_apply_singleton` and
  `ProbabilityTheory.Kernel.tsum_pow_apply_singleton_self`: the Green-function identities.
* `ProbabilityTheory.Kernel.tsum_pow_apply_singleton_self_eq_top_iff`: the return probability of
  `y` is one exactly when `∑ n, (κ ^ n) y {y} = ∞`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Lemma 1.5.1 and Theorem 1.5.3.
-/

public section

open ProbabilityTheory TauCeti.Probability

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*}

/-- After a finite visit to `y` at time `n`, the next visit exists exactly when the path seen from
time `n` returns to `y` at a positive time. -/
private theorem setOf_successiveVisit_succ_ne_top (y : α) (k : ℕ) :
    {x : ℕ → α | successiveVisit (fun n x => x n) y k x ≠ ⊤} ∩
        stoppedValue (fun n => (shift α)^[n]) (successiveVisit (fun n x => x n) y k) ⁻¹'
          {z | hittingAfter (fun n z => z n) {y} 1 z ≠ ⊤} =
      {x | successiveVisit (fun n x => x n) y (k + 1) x ≠ ⊤} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  induction h : successiveVisit (fun n (x : ℕ → α) => x n) y k x using WithTop.recTopCoe with
  | top =>
    have hle := successiveVisit_monotone (fun n (x : ℕ → α) => x n) y x (Nat.le_succ k)
    simp only [h, top_le_iff] at hle
    simp [hle]
  | coe n =>
    rw [successiveVisit_succ_eq_hittingAfter h]
    simp only [ne_eq, WithTop.coe_ne_top, not_false_eq_true, true_and, stoppedValue, h,
      WithTop.untopD_coe, hittingAfter_eq_top_iff, shift_iterate_apply, not_forall,
      Set.mem_singleton_iff, not_not, exists_prop]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j + n, by omega, hx⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j - n, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩

variable [MeasurableSpace α] [MeasurableSingletonClass α] (ν : Measure α) (κ : Kernel α α)
  [IsMarkovKernel κ]

/-- At the visit to `y` indexed by `k`, the stopped future has the law of a chain started at `y`,
scaled by the mass of paths on which that visit exists. The first entrance is visit zero. -/
theorem markovChainLaw_restrict_map_successiveVisit_eq_smul
    (y : α) (k : ℕ) :
    ((markovChainLaw ν κ).restrict
      {x | successiveVisit (fun n x => x n) y k x ≠ ⊤}).map
        (stoppedValue (fun n => (shift α)^[n]) (successiveVisit (fun n x => x n) y k)) =
      markovChainLaw ν κ {x | successiveVisit (fun n x => x n) y k x ≠ ⊤} •
        markovChainLaw (dirac y) κ := by
  have hσ := Filtration.adapted_piLE.isStoppingTime_successiveVisit
    (X := fun n (x : ℕ → α) => x n) (measurableSet_singleton y) k
  have hlaw := markovChainLaw_restrict_map_stoppedValue_shift_iterate_eq_smul ν κ hσ
    MeasurableSet.univ (y := y) fun x hx => by
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hx.2
      simp only [stoppedValue, ← hn, WithTop.untopD_coe]
      exact (successiveVisit_eq_coe_iff.mp hn.symm).1
  simpa only [Set.univ_inter] using hlaw

/-- **The visits of a chain to a state have a geometric tail.** The visit to `y` indexed by `k`,
counting the first entrance as visit zero, exists with probability
`ℙ_ν(H_y < ∞) · ρ_y ^ k`, where `ρ_y = ℙ_y(T_y⁺ < ∞)` is the return probability of `y`. -/
theorem markovChainLaw_setOf_successiveVisit_ne_top (y : α) (k : ℕ) :
    markovChainLaw ν κ {x | successiveVisit (fun n x => x n) y k x ≠ ⊤} =
      markovChainLaw ν κ {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} *
        markovChainLaw (dirac y) κ {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    set σ := successiveVisit (fun n (x : ℕ → α) => x n) y k
    have hσ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) σ :=
      Filtration.adapted_piLE.isStoppingTime_successiveVisit (measurableSet_singleton y) k
    have hθ : Measurable (stoppedValue (fun n => (shift α)^[n]) σ) :=
      measurable_stoppedValue_of_countable (fun n => measurable_shift_iterate n) hσ.measurable'
    have hB : MeasurableSet {z : ℕ → α | hittingAfter (fun n z => z n) {y} 1 z ≠ ⊤} :=
      measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton y) 1
    rw [← setOf_successiveVisit_succ_ne_top, Set.inter_comm, ← restrict_apply (hB.preimage hθ),
      ← map_apply hθ hB, markovChainLaw_restrict_map_successiveVisit_eq_smul,
      smul_apply, smul_eq_mul, ih, pow_succ, mul_assoc]

/-- **A state that is returned to almost surely is visited infinitely often.** If the chain started
at `y` returns to `y` almost surely, then for every initial measure, almost every path that
reaches `y` visits it infinitely often. -/
theorem ae_infinite_setOf_eq_of_hittingAfter_ne_top {y : α}
    (hy : markovChainLaw (dirac y) κ {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = 1) :
    ∀ᵐ x ∂markovChainLaw ν κ,
      hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤ → {n | x n = y}.Infinite := by
  -- The statement for a finite initial measure, used at Dirac starts below.
  have key : ∀ (ν : Measure α) [IsFiniteMeasure ν], ∀ᵐ x ∂markovChainLaw ν κ,
      hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤ → {n | x n = y}.Infinite := by
    intro ν _
    have hσ : ∀ k, MeasurableSet {x : ℕ → α | successiveVisit (fun n x => x n) y k x ≠ ⊤} :=
      measurableSet_setOf_successiveVisit_ne_top (fun n => measurable_pi_apply n)
        (measurableSet_singleton y)
    -- Each visit exists exactly on the event that `y` is reached, up to a null set.
    have hk : ∀ k, ∀ᵐ x ∂markovChainLaw ν κ, hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤ →
        successiveVisit (fun n x => x n) y k x ≠ ⊤ := fun k => by
      have hsub : {x : ℕ → α | successiveVisit (fun n x => x n) y k x ≠ ⊤} ⊆
          {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} := fun x hx => by
        have hle : successiveVisit (fun n (x : ℕ → α) => x n) y 0 x ≤
            successiveVisit (fun n x => x n) y k x :=
          successiveVisit_monotone _ y x (Nat.zero_le k)
        rw [successiveVisit_zero] at hle
        exact ne_top_of_le_ne_top hx hle
      have heq := ae_eq_of_subset_of_measure_ge hsub
        (by rw [markovChainLaw_setOf_successiveVisit_ne_top ν κ y k, hy, one_pow, mul_one])
        (hσ k).nullMeasurableSet (measure_ne_top _ _)
      filter_upwards [heq] with x hx hH
      exact (iff_of_eq hx).2 hH
    filter_upwards [ae_all_iff.mpr hk] with x hx hH
    exact forall_successiveVisit_lt_top_iff.mp fun k => lt_top_iff_ne_top.mpr (hx k hH)
  have hH : MeasurableSet {x : ℕ → α | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} :=
    measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton y) 0
  have hI : MeasurableSet {x : ℕ → α | {n | x n = y}.Infinite} :=
    measurableSet_setOf_infinite_setOf_eq (fun n => measurable_pi_apply n)
      (measurableSet_singleton y)
  have hS := hH.imp hI
  rw [markovChainLaw_eq_comp]
  refine ae_comp_of_ae_ae hS (Filter.Eventually.of_forall fun a => ?_)
  rw [Kernel.markovChainKernel_apply]
  exact key (dirac a)

/-- **A state that is not returned to almost surely is visited finitely often.** If the return
probability of `y` is less than one, then for every initial measure the chain visits `y`
infinitely often with probability zero. -/
theorem markovChainLaw_setOf_infinite_setOf_eq_eq_zero {y : α}
    (hy : markovChainLaw (dirac y) κ {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} < 1) :
    markovChainLaw ν κ {x | {n | x n = y}.Infinite} = 0 := by
  -- The statement for a finite initial measure, used at Dirac starts below.
  have key : ∀ (ν : Measure α) [IsFiniteMeasure ν],
      markovChainLaw ν κ {x | {n | x n = y}.Infinite} = 0 := by
    intro ν _
    have ht := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hy)
      (Or.inr (measure_ne_top (markovChainLaw ν κ) {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤}))
    rw [mul_zero] at ht
    refine nonpos_iff_eq_zero.mp (ge_of_tendsto' ht fun k => ?_)
    rw [← markovChainLaw_setOf_successiveVisit_ne_top]
    exact measure_mono fun x hx =>
      lt_top_iff_ne_top.mp (forall_successiveVisit_lt_top_iff.mpr hx k)
  rw [markovChainLaw_eq_comp, bind_apply (measurableSet_setOf_infinite_setOf_eq
    (fun n => measurable_pi_apply n) (measurableSet_singleton y)) (Kernel.aemeasurable _)]
  simp [Kernel.markovChainKernel_apply, key]

/-- **The mean number of visits.** For any initial measure, the mean number of times the
chain is at `y` is `ℙ_ν(H_y < ∞) · (1 - ρ_y)⁻¹`, where `ρ_y` is the return probability of `y`.
It is infinite when `y` is reached with positive probability and `ρ_y = 1`. -/
theorem lintegral_encard_setOf_eq_markovChainLaw (y : α) :
    ∫⁻ x, ({n | x n = y}.encard : ℝ≥0∞) ∂markovChainLaw ν κ =
      markovChainLaw ν κ {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} *
        (1 - markovChainLaw (dirac y) κ {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤})⁻¹ := by
  -- The number of visits is the number of indices `k` whose visit exists.
  simp_rw [← encard_setOf_successiveVisit_ne_top (X := fun n (x : ℕ → α) => x n)]
  rw [lintegral_encard_setOf_eq_tsum _ (measurableSet_setOf_successiveVisit_ne_top
    (fun n => measurable_pi_apply n) (measurableSet_singleton y))]
  simp_rw [markovChainLaw_setOf_successiveVisit_ne_top ν κ y, ENNReal.tsum_mul_left,
    ENNReal.tsum_geometric]

/-- The probability that the chain is at `y` at time `n`, summed over `n`, is the mean number of
visits `ℙ_ν(H_y < ∞) · (1 - ρ_y)⁻¹`. -/
private theorem tsum_markovChainLaw_setOf_apply_eq (y : α) :
    ∑' n, markovChainLaw ν κ {x | x n = y} =
      markovChainLaw ν κ {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} *
        (1 - markovChainLaw (dirac y) κ {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤})⁻¹ := by
  rw [← lintegral_encard_setOf_eq_tsum (P := fun n (x : ℕ → α) => x n = y) _ fun n =>
    (measurableSet_singleton y).preimage (measurable_pi_apply n),
    lintegral_encard_setOf_eq_markovChainLaw]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (κ : Kernel α α)
  [IsMarkovKernel κ]

/-- Started at `y`, the chain enters `y` at time zero. -/
theorem ae_hittingAfter_zero_ne_top_markovChainLaw_dirac (y : α) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ, hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤ := by
  filter_upwards [markovChainLaw_dirac_ae_apply_zero κ y] with x hx
  exact ne_top_of_le_ne_top WithTop.coe_ne_top
    (hittingAfter_le_of_mem le_rfl (Set.mem_singleton_iff.mpr hx))

/-- Started at `y`, the chain reaches `y` with probability one. -/
theorem markovChainLaw_dirac_setOf_hittingAfter_zero_ne_top (y : α) :
    markovChainLaw (Measure.dirac y) κ {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} = 1 := by
  rw [measure_congr (ae_eq_univ.mpr (mem_ae_iff.mp
    (ae_hittingAfter_zero_ne_top_markovChainLaw_dirac κ y))), measure_univ]

/-- Started at `y`, the visit to `y` indexed by `k` (visit zero being time zero) exists with
probability `ρ_y ^ k`. -/
theorem markovChainLaw_dirac_setOf_successiveVisit_ne_top (y : α) (k : ℕ) :
    markovChainLaw (Measure.dirac y) κ {x | successiveVisit (fun n x => x n) y k x ≠ ⊤} =
      markovChainLaw (Measure.dirac y) κ {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} ^ k := by
  rw [Measure.markovChainLaw_setOf_successiveVisit_ne_top,
    markovChainLaw_dirac_setOf_hittingAfter_zero_ne_top, one_mul]

/-- **A chain started at a state it returns to almost surely returns infinitely often.** This is
the hypothesis of the excursion decomposition
`TauCeti.Probability.markovChainLaw_eq_map_pathOfExcursions`. -/
theorem ae_infinite_setOf_eq_markovChainLaw_dirac {y : α}
    (hy : markovChainLaw (Measure.dirac y) κ {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = 1) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ, {n | x n = y}.Infinite := by
  filter_upwards [Measure.ae_infinite_setOf_eq_of_hittingAfter_ne_top (Measure.dirac y) κ hy,
    ae_hittingAfter_zero_ne_top_markovChainLaw_dirac κ y] with x hx h0
  exact hx h0

/-- **The Green function at the diagonal.** The mean number of visits to `y` of the chain started
at `y`, `∑ n, (κ ^ n) y {y}`, is `(1 - ρ_y)⁻¹`, where `ρ_y = ℙ_y(T_y⁺ < ∞)` is the return
probability of `y`. -/
theorem tsum_pow_apply_singleton_self (y : α) :
    ∑' n : ℕ, (κ ^ n) y {y} =
      (1 - markovChainLaw (Measure.dirac y) κ
        {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤})⁻¹ := by
  have hn : ∀ n, (κ ^ n) y {y} = markovChainLaw (Measure.dirac y) κ {x | x n = y} := fun n => by
    rw [Measure.markovChainLaw_setOf_apply_eq_comp, Measure.dirac_bind (κ ^ n).measurable]
  simp_rw [hn, Measure.tsum_markovChainLaw_setOf_apply_eq,
    markovChainLaw_dirac_setOf_hittingAfter_zero_ne_top, one_mul]

/-- **The Green function.** For an initial measure `ν`, the mean number of visits to `y`,
`∑ n, ((κ ^ n) ∘ₘ ν) {y}`, is the probability `ℙ_ν(H_y < ∞)` of reaching `y` times the mean
number of visits `∑ n, (κ ^ n) y {y}` of the chain started at `y`. -/
theorem tsum_pow_comp_apply_singleton (ν : Measure α) (y : α) :
    ∑' n : ℕ, ((κ ^ n) ∘ₘ ν) {y} =
      markovChainLaw ν κ {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} *
        ∑' n : ℕ, (κ ^ n) y {y} := by
  rw [tsum_pow_apply_singleton_self, ← Measure.tsum_markovChainLaw_setOf_apply_eq]
  simp_rw [Measure.markovChainLaw_setOf_apply_eq_comp]

/-- **The recurrence criterion.** The chain started at `y` returns to `y` almost surely exactly when
the mean number of visits `∑ n, (κ ^ n) y {y}` is infinite. -/
theorem tsum_pow_apply_singleton_self_eq_top_iff (y : α) :
    ∑' n : ℕ, (κ ^ n) y {y} = ∞ ↔
      markovChainLaw (Measure.dirac y) κ {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = 1 := by
  rw [tsum_pow_apply_singleton_self, ENNReal.inv_eq_top, tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm prob_le_one h, fun h => h.ge⟩

end ProbabilityTheory.Kernel
