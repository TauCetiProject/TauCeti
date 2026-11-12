/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Visits
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

for every initial law (`MeasureTheory.Measure.markovChainLaw_setOf_successiveVisit_ne_top`, in
`TauCeti.Probability.MarkovChain.Visits`), and in particular
`ℙ_y(the visit indexed by k exists) = ρ_y ^ k`
(`ProbabilityTheory.Kernel.markovChainLaw_dirac_setOf_successiveVisit_ne_top`).

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

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.5, Lemma 1.5.1 and
  Theorem 1.5.3.
-/

public section

open Filter MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped ENNReal Topology

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]

/-- **Return with probability one gives infinitely many visits.** If the chain started at `y`
returns to `y` almost surely, then under every initial law, almost surely the chain visits
`y` infinitely often as soon as it visits `y` at all. -/
theorem ae_infinite_setOf_eq_of_exists_eq_markovChainLaw {y : α}
    (h : markovChainLaw (dirac y) κ
      {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 1 x ≠ ⊤} = 1) :
    ∀ᵐ x ∂markovChainLaw ν κ, (∃ n, x n = y) → {n | x n = y}.Infinite := by
  filter_upwards [ae_infinite_setOf_eq_of_hittingAfter_ne_top ν κ h] with x hx ⟨n, hn⟩
  exact hx fun htop => hittingAfter_eq_top_iff.1 htop n (Nat.zero_le n) hn

/-- **Return with probability less than one gives finitely many visits.** If the chain started at
`y` fails to return to `y` with positive probability, then under every initial law the
chain almost surely visits `y` only finitely often. -/
theorem ae_finite_setOf_eq_markovChainLaw {y : α}
    (h : markovChainLaw (dirac y) κ
      {x | hittingAfter (fun n (x : ℕ → α) => x n) {y} 1 x ≠ ⊤} < 1) :
    ∀ᵐ x ∂markovChainLaw ν κ, {n | x n = y}.Finite := by
  rw [ae_iff]
  exact markovChainLaw_setOf_infinite_setOf_eq_eq_zero ν κ h

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ]

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
