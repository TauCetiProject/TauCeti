/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.StrongMarkov.Basic
public import TauCeti.Probability.Process.SuccessiveVisits
public import TauCeti.Probability.Process.Excursion.MarkovChain

/-!
# Returns of a homogeneous chain to a state

Let `X` be the coordinate process on path space `ℕ → α` under the path law
`markovChainLaw ν κ`, and write `ℙₓ = markovChainLaw (dirac x) κ`. For a state `y`, the first
entrance `H_y = hittingAfter X {y} 0` may occur at time zero, while the first return
`T_y⁺ = hittingAfter X {y} 1` only looks at positive times; both are infinite when the visit
does not occur. The *return probability* of `y` is `ρ_y = ℙ_y(T_y⁺ < ∞)`.

The visits to `y` are enumerated by the stopping times `successiveVisit X y k`, with visit zero the
first entrance. By the strong Markov property at the visit indexed by `k`, the chain then starts
afresh from `y`, so the next visit exists with probability `ρ_y`, independently of the past.
Iterating gives

`ℙ(the visit indexed by k exists) = ℙ(H_y < ∞) * ρ_y ^ k`

for every initial law (`MeasureTheory.Measure.markovChainLaw_successiveVisit_ne_top`), and in
particular `ℙ_y(the visit indexed by k exists) = ρ_y ^ k`
(`ProbabilityTheory.Kernel.markovChainLaw_dirac_successiveVisit_ne_top`).

This yields the dichotomy between recurrent and transient states.

* If `ρ_y = 1`, then almost surely a chain that visits `y` at all visits it infinitely often,
  whatever its initial law
  (`MeasureTheory.Measure.ae_infinite_setOf_eq_of_exists_eq_markovChainLaw`).
* If `ρ_y < 1`, then almost surely the chain visits `y` only finitely often, whatever its initial
  law (`MeasureTheory.Measure.ae_finite_setOf_eq_markovChainLaw`).
* Started at `y`, the chain visits `y` infinitely often almost surely exactly when `ρ_y = 1`
  (`ProbabilityTheory.Kernel.ae_infinite_setOf_eq_markovChainLaw_dirac_iff`). This supplies the
  hypothesis of the excursion decomposition `TauCeti.Probability.iIndepFun_excursionProcess` and
  `TauCeti.Probability.markovChainLaw_eq_map_pathOfExcursions` at a state with `ρ_y = 1`.

No countability of the state space is needed: measurable singletons suffice.

Two path-space facts about hitting times of the coordinate process are used along the way: the
event that a hitting time is finite is measurable
(`TauCeti.Probability.measurableSet_hittingAfter_coord_ne_top`), and the path enters a set after
time `m + n` exactly when the path shifted by `n` enters it after time `m`
(`TauCeti.Probability.hittingAfter_shift_iterate_ne_top_iff`).

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.5, Lemma 1.5.1 and
  Theorem 1.5.3.
-/

public section

open Filter MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped ENNReal Topology

namespace TauCeti.Probability

variable {α : Type*}

/-- The coordinate process enters `s` at some time at least `m + n` exactly when the path shifted
by `n` enters `s` at some time at least `m`. -/
theorem hittingAfter_shift_iterate_ne_top_iff (s : Set α) (m n : ℕ) (x : ℕ → α) :
    hittingAfter (fun k (x : ℕ → α) => x k) s (m + n) x ≠ ⊤ ↔
      hittingAfter (fun k (x : ℕ → α) => x k) s m ((shift α)^[n] x) ≠ ⊤ := by
  simp only [ne_eq, not_iff_not, hittingAfter_eq_top_iff, shift_iterate_apply]
  exact ⟨fun h j hj => h (j + n) (by omega), fun h j hj => by
    simpa [Nat.sub_add_cancel (show n ≤ j by omega)] using h (j - n) (by omega)⟩

/-- The event that the coordinate process enters a measurable set `s` at some time at least `m`
is measurable. -/
theorem measurableSet_hittingAfter_coord_ne_top [MeasurableSpace α] {s : Set α}
    (hs : MeasurableSet s) (m : ℕ) :
    MeasurableSet {x : ℕ → α | hittingAfter (fun k (x : ℕ → α) => x k) s m x ≠ ⊤} :=
  ((measurableSet_singleton ⊤).preimage
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter (n := m) hs).measurable').compl

end TauCeti.Probability

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]

/-- **One more visit costs a factor `ρ_y`.** By the strong Markov property at the visit to `y`
indexed by `k`, the probability that the next visit exists is the probability that the visit
indexed by `k` exists times the return probability `ρ_y = ℙ_y(T_y⁺ < ∞)`. -/
theorem markovChainLaw_successiveVisit_succ_ne_top [IsFiniteMeasure ν] (y : α) (k : ℕ) :
    markovChainLaw ν κ {x | successiveVisit (fun n (x : ℕ → α) => x n) y (k + 1) x ≠ ⊤} =
      markovChainLaw ν κ {x | successiveVisit (fun n (x : ℕ → α) => x n) y k x ≠ ⊤} *
        markovChainLaw (dirac y) κ
          {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 1 x ≠ ⊤} := by
  set X : ℕ → (ℕ → α) → α := fun n x => x n
  set τ := successiveVisit X y k
  set θ := stoppedValue (fun n => (shift α)^[n]) τ
  set B := {x : ℕ → α | hittingAfter X {y} 1 x ≠ ⊤}
  have hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ :=
    Filtration.adapted_piLE.isStoppingTime_successiveVisit (measurableSet_singleton y) k
  have hθ : Measurable θ :=
    measurable_stoppedValue_of_countable (fun n => measurable_shift_iterate n) hτ.measurable'
  have hB : MeasurableSet B := measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton y) 1
  -- On `{τ = n}` the next visit is the first entrance after `n + 1`, that is, the first return of
  -- the path seen from time `n`; off `{τ < ∞}` there is no next visit either.
  have hset : {x | successiveVisit X y (k + 1) x ≠ ⊤} = Set.univ ∩ {x | τ x ≠ ⊤} ∩ θ ⁻¹' B := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage, B]
    by_cases hx : τ x = ⊤
    · simp only [hx, ne_eq, not_true_eq_false, false_and, iff_false, not_not]
      exact top_le_iff.1 (hx ▸ successiveVisit_monotone X y x k.le_succ)
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hx
      have hθx : θ x = (shift α)^[n] x := by
        simp only [θ, stoppedValue, ← hn, WithTop.untopD_coe]
      rw [successiveVisit_succ_eq_hittingAfter (n := n) (by simp [τ, ← hn]), hθx, add_comm n 1]
      simpa only [hx, ne_eq, not_false_eq_true, true_and] using
        hittingAfter_shift_iterate_ne_top_iff {y} 1 n x
  have hy : ∀ x ∈ Set.univ ∩ {x | τ x ≠ ⊤}, stoppedValue X τ x = y := by
    rintro x ⟨-, hx⟩
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hx
    have := (successiveVisit_eq_coe_iff (X := X) (a := y) (k := k) (ω := x) (n := n)).1
      (by simp [τ, ← hn])
    simpa only [stoppedValue, ← hn, WithTop.untopD_coe] using this.1
  have h := markovChainLaw_restrict_map_stoppedValue_shift_iterate_eq_smul ν κ hτ
    MeasurableSet.univ hy
  rw [hset, Set.inter_comm, ← Measure.restrict_apply (hB.preimage hθ), ← Measure.map_apply hθ hB, h]
  simp

/-- **The probability that the visit to `y` indexed by `k` exists.** Under every finite initial law
it is `ℙ(H_y < ∞) * ρ_y ^ k`, where `H_y` is the first entrance to `y` and
`ρ_y = ℙ_y(T_y⁺ < ∞)` is the return probability of `y`. -/
theorem markovChainLaw_successiveVisit_ne_top [IsFiniteMeasure ν] (y : α) (k : ℕ) :
    markovChainLaw ν κ {x | successiveVisit (fun n (x : ℕ → α) => x n) y k x ≠ ⊤} =
      markovChainLaw ν κ {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 0 x ≠ ⊤} *
        markovChainLaw (dirac y) κ
          {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 1 x ≠ ⊤} ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [markovChainLaw_successiveVisit_succ_ne_top, ih, pow_succ, mul_assoc]

/-- **Return with probability one gives infinitely many visits.** If the chain started at `y`
returns to `y` almost surely, then under every finite initial law, almost surely the chain visits
`y` infinitely often as soon as it visits `y` at all. -/
theorem ae_infinite_setOf_eq_of_exists_eq_markovChainLaw [IsFiniteMeasure ν] {y : α}
    (h : markovChainLaw (dirac y) κ
      {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 1 x ≠ ⊤} = 1) :
    ∀ᵐ x ∂markovChainLaw ν κ, (∃ n, x n = y) → {n | x n = y}.Infinite := by
  set X : ℕ → (ℕ → α) → α := fun n x => x n
  -- Each visit exists with the same probability as the first entrance, and its existence implies
  -- that of the first entrance, so the two events agree almost surely.
  have hk : ∀ k, ∀ᵐ x ∂markovChainLaw ν κ,
      hittingAfter X {y} 0 x ≠ ⊤ → successiveVisit X y k x ≠ ⊤ := by
    intro k
    have hsub : {x | successiveVisit X y k x ≠ ⊤} ⊆ {x | hittingAfter X {y} 0 x ≠ ⊤} :=
      fun x hx => by
        have h₀ : successiveVisit X y 0 x ≠ ⊤ :=
          ne_top_of_le_ne_top hx (successiveVisit_monotone X y x (Nat.zero_le k))
        rwa [successiveVisit_zero] at h₀
    have heq := ae_eq_of_subset_of_measure_ge hsub
      ((markovChainLaw_successiveVisit_ne_top ν κ y k).trans (by rw [h, one_pow, mul_one])).ge
      ((measurable_successiveVisit (fun n => measurable_pi_apply n) (measurableSet_singleton y)
        k (measurableSet_singleton ⊤)).compl.nullMeasurableSet) (measure_ne_top _ _)
    filter_upwards [heq.mem_iff] with x hx hH
    exact hx.2 hH
  filter_upwards [ae_all_iff.2 hk] with x hx ⟨n, hn⟩
  refine (forall_successiveVisit_lt_top_iff (X := X)).1 fun k => lt_top_iff_ne_top.2 (hx k ?_)
  exact fun htop => hittingAfter_eq_top_iff.1 htop n (Nat.zero_le n) hn

/-- **Return with probability less than one gives finitely many visits.** If the chain started at
`y` fails to return to `y` with positive probability, then under every finite initial law the
chain almost surely visits `y` only finitely often. -/
theorem ae_finite_setOf_eq_markovChainLaw [IsFiniteMeasure ν] {y : α}
    (h : markovChainLaw (dirac y) κ
      {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 1 x ≠ ⊤} < 1) :
    ∀ᵐ x ∂markovChainLaw ν κ, {n | x n = y}.Finite := by
  set X : ℕ → (ℕ → α) → α := fun n x => x n
  set P := markovChainLaw ν κ
  -- Infinitely many visits force every visit to exist, an event of probability
  -- `ℙ(H_y < ∞) * ρ_y ^ k`, which tends to zero.
  have hlim : Tendsto (fun k => P {x | hittingAfter X {y} 0 x ≠ ⊤} *
      markovChainLaw (dirac y) κ {x | hittingAfter X {y} 1 x ≠ ⊤} ^ k) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h)
      (Or.inr (measure_ne_top P _))
  have hle : ∀ k, P {x | ¬{n | x n = y}.Finite} ≤
      P {x | hittingAfter X {y} 0 x ≠ ⊤} *
        markovChainLaw (dirac y) κ {x | hittingAfter X {y} 1 x ≠ ⊤} ^ k := fun k => by
    refine (measure_mono fun x hx => ?_).trans (markovChainLaw_successiveVisit_ne_top ν κ y k).le
    exact ((forall_successiveVisit_lt_top_iff (X := X)).2 hx k).ne
  rw [ae_iff]
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim hle)

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ]

/-- **The probability of `k` returns.** Started at `y`, the chain makes its visit to `y` indexed by
`k`, that is, returns to `y` at least `k` times, with probability `ρ_y ^ k`, where
`ρ_y = ℙ_y(T_y⁺ < ∞)` is the return probability of `y`. -/
theorem markovChainLaw_dirac_successiveVisit_ne_top (y : α) (k : ℕ) :
    markovChainLaw (Measure.dirac y) κ
        {x | successiveVisit (fun n (x : ℕ → α) => x n) y k x ≠ ⊤} =
      markovChainLaw (Measure.dirac y) κ
        {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 1 x ≠ ⊤} ^ k := by
  -- The chain started at `y` enters `y` at time zero.
  have h₀ : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 0 x ≠ ⊤} = 1 := by
    refine (mem_ae_iff_prob_eq_one
      (measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton y) 0)).1 ?_
    filter_upwards [markovChainLaw_dirac_ae_apply_zero κ y] with x hx htop
    exact hittingAfter_eq_top_iff.1 htop 0 le_rfl hx
  rw [Measure.markovChainLaw_successiveVisit_ne_top (Measure.dirac y) κ, h₀, one_mul]

/-- **Recurrence dichotomy at a state.** The chain started at `y` almost surely visits `y`
infinitely often exactly when it returns to `y` almost surely; otherwise it almost surely visits
`y` only finitely often (`MeasureTheory.Measure.ae_finite_setOf_eq_markovChainLaw`). -/
theorem ae_infinite_setOf_eq_markovChainLaw_dirac_iff (y : α) :
    (∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ, {n | x n = y}.Infinite) ↔
      markovChainLaw (Measure.dirac y) κ
        {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 1 x ≠ ⊤} = 1 := by
  refine ⟨fun hinf => ?_, fun h => ?_⟩
  · by_contra hne
    have hfin := Measure.ae_finite_setOf_eq_markovChainLaw (Measure.dirac y) κ
      (lt_of_le_of_ne prob_le_one hne)
    obtain ⟨x, h₁, h₂⟩ := (hinf.and hfin).exists
    exact h₁ h₂
  · filter_upwards [Measure.ae_infinite_setOf_eq_of_exists_eq_markovChainLaw (Measure.dirac y) κ h,
      markovChainLaw_dirac_ae_apply_zero κ y] with x hx h₀
    exact hx ⟨0, h₀⟩

end ProbabilityTheory.Kernel
