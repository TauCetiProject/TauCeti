/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.SeededRegularization
public import Mathlib.Order.PartialSups
import Mathlib.Tactic.Linarith

/-!
# Strong seeded regularization for pair-color systems

Iterating seeded equitable pair-color regularity
(`PairColorSystem.exists_refining_equipartition_sum_irregularPairs_le`) produces a nested pair of
equipartitions `Q ≤ P ≤ P₀` below any prescribed equitable seed `P₀` such that:

* the fine partition `Q` is `η #P.parts`-regular up to irregular vertex mass `η #P.parts |V|²`, for
  an arbitrary positive schedule `η : ℕ → ℝ` evaluated at the coarse complexity `#P.parts`;
* the pair-color energy rises by at most `γ` from `P` to `Q`, i.e. `S.energy Q - S.energy P ≤ γ`;
* both `#P.parts` and `#Q.parts` are bounded by
  `TauCeti.strongPairColorRegularityBound γ η #P₀.parts`, independently of `|V|`.

Combined with `PairColorSystem.sum_card_mul_abs_pairColorDensity_sub_le`, the energy-gap bound
`S.energy Q - S.energy P ≤ γ` controls the `L¹` deviation between fine and coarse block densities
when coupling `S` on each fine block `A' ×ˢ B'` to the coarse block distribution on `A ×ˢ B`.

## Main definitions

* `TauCeti.strongPairColorRegularityStep`: complexity bound for one round of seeded pair-color
  regularization under a schedule `η`.
* `TauCeti.strongPairColorRegularityBound`: host-independent complexity bound for strong seeded
  pair-color regularization.

## Main results

* `TauCeti.PairColorSystem.exists_strong_refining_equipartition`: existence of nested equipartitions
  `Q ≤ P ≤ P₀` with scheduled fine regularity and energy gap at most `γ`.

## References

* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Finpartition Function

namespace TauCeti

/-- The complexity bound for one round of strong pair-color regularization under a schedule `η`,
starting from a partition with at most `m` parts: the supremum of
`equitablePairColorRegularityBound (η j) j` over `j ≤ m`, making the step bound monotone in `m`
even when `η` is not monotone. -/
noncomputable def strongPairColorRegularityStep (η : ℕ → ℝ) (m : ℕ) : ℕ :=
  partialSups (fun j ↦ equitablePairColorRegularityBound (η j) j) m

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityStep`. -/
theorem strongPairColorRegularityStep_def (η : ℕ → ℝ) (m : ℕ) :
    strongPairColorRegularityStep η m =
      partialSups (fun j ↦ equitablePairColorRegularityBound (η j) j) m :=
  (rfl)

/-- `TauCeti.strongPairColorRegularityStep` as a supremum over `Finset.range (m + 1)`. -/
theorem strongPairColorRegularityStep_eq_sup_range (η : ℕ → ℝ) (m : ℕ) :
    strongPairColorRegularityStep η m =
      (range (m + 1)).sup fun j ↦ equitablePairColorRegularityBound (η j) j :=
  partialSups_eq_sup_range _ m

/-- One round of `TauCeti.strongPairColorRegularityStep` dominates the single-round bound from any
smaller partition size `j ≤ m`. -/
theorem equitablePairColorRegularityBound_le_strongPairColorRegularityStep {η : ℕ → ℝ} {j m : ℕ}
    (h : j ≤ m) :
    equitablePairColorRegularityBound (η j) j ≤ strongPairColorRegularityStep η m :=
  le_partialSups_of_le (fun j ↦ equitablePairColorRegularityBound (η j) j) h

/-- `TauCeti.strongPairColorRegularityStep` is monotone in the starting complexity. -/
theorem strongPairColorRegularityStep_mono (η : ℕ → ℝ) :
    Monotone (strongPairColorRegularityStep η) :=
  (partialSups fun j ↦ equitablePairColorRegularityBound (η j) j).monotone

/-- When `η` is positive everywhere, `TauCeti.strongPairColorRegularityStep` is at least its
input. -/
theorem le_strongPairColorRegularityStep {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (m : ℕ) :
    m ≤ strongPairColorRegularityStep η m :=
  (le_equitablePairColorRegularityBound (hη m) m).trans
    (equitablePairColorRegularityBound_le_strongPairColorRegularityStep le_rfl)

/-- Host-independent complexity bound for strong seeded pair-color regularization with energy-gap
tolerance `γ` and schedule `η`, starting from `l₀` parts: `⌊1 / γ⌋₊ + 1` iterations of
`TauCeti.strongPairColorRegularityStep η`. -/
noncomputable def strongPairColorRegularityBound (γ : ℝ) (η : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  (strongPairColorRegularityStep η)^[⌊1 / γ⌋₊ + 1] l₀

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityBound`. -/
theorem strongPairColorRegularityBound_def (γ : ℝ) (η : ℕ → ℝ) (l₀ : ℕ) :
    strongPairColorRegularityBound γ η l₀ =
      (strongPairColorRegularityStep η)^[⌊1 / γ⌋₊ + 1] l₀ :=
  (rfl)

/-- `TauCeti.strongPairColorRegularityBound` is monotone in the starting complexity `l₀`. -/
theorem strongPairColorRegularityBound_mono (γ : ℝ) (η : ℕ → ℝ) :
    Monotone (strongPairColorRegularityBound γ η) :=
  (strongPairColorRegularityStep_mono η).iterate _

/-- When `η` is positive everywhere, `TauCeti.strongPairColorRegularityBound` is at least `l₀`. -/
theorem le_strongPairColorRegularityBound (γ : ℝ) {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (l₀ : ℕ) :
    l₀ ≤ strongPairColorRegularityBound γ η l₀ :=
  id_le_iterate_of_id_le (le_strongPairColorRegularityStep hη) _ _

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)

/-- **Strong seeded pair-color regularization.** Given an equipartition `P₀`, an energy-gap
tolerance `γ > 0`, and a positive schedule `η : ℕ → ℝ`, there exist equipartitions `Q ≤ P ≤ P₀`
such that `Q` has irregular vertex mass at most `η #P.parts * |V|²` at tolerance `η #P.parts`, the
energy rises by at most `γ` from `P` to `Q`, and `#Q.parts` (hence also `#P.parts`) is bounded by
`strongPairColorRegularityBound γ η #P₀.parts`. -/
theorem exists_strong_refining_equipartition
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition)
    {γ : ℝ} (hγ : 0 < γ) {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    ∃ P Q : Finpartition (univ : Finset V),
      P ≤ P₀ ∧ Q ≤ P ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
      #Q.parts ≤ equitablePairColorRegularityBound (η #P.parts) #P.parts ∧
      #Q.parts ≤ strongPairColorRegularityBound γ η #P₀.parts ∧
      ∑ AB ∈ S.irregularPairs (η #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        η #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      S.energy Q - S.energy P ≤ γ := by
  set g := strongPairColorRegularityStep η
  -- After `i + 1` rounds, either the energy gap is at most `γ` or `S.energy Q > γ * (i + 1)`.
  have key (i : ℕ) : ∃ P Q : Finpartition (univ : Finset V),
      P ≤ P₀ ∧ Q ≤ P ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
      #Q.parts ≤ equitablePairColorRegularityBound (η #P.parts) #P.parts ∧
      #Q.parts ≤ g^[i + 1] #P₀.parts ∧
      ∑ AB ∈ S.irregularPairs (η #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        η #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      (S.energy Q - S.energy P ≤ γ ∨ γ * (i + 1) < S.energy Q) := by
    induction i with
    | zero =>
      obtain ⟨Q, hQP₀, hQ, hQeb, hQreg⟩ :=
        S.exists_refining_equipartition_sum_irregularPairs_le P₀ hP₀ (hη #P₀.parts)
      refine ⟨P₀, Q, le_rfl, hQP₀, hP₀, hQ, hQeb,
        hQeb.trans (equitablePairColorRegularityBound_le_strongPairColorRegularityStep le_rfl),
        hQreg, (le_or_gt _ γ).imp id fun h ↦ ?_⟩
      have := S.energy_nonneg P₀
      push_cast
      linarith
    | succ i ih =>
      obtain ⟨P, Q, hPP₀, hQP, hP, hQ, hQeb, hQg, hQreg, hgap⟩ := ih
      have hgi : g^[i + 1] #P₀.parts ≤ g^[i + 1 + 1] #P₀.parts := by
        rw [iterate_succ_apply' g (i + 1)]
        exact le_strongPairColorRegularityStep hη _
      by_cases hclose : S.energy Q - S.energy P ≤ γ
      · exact ⟨P, Q, hPP₀, hQP, hP, hQ, hQeb, hQg.trans hgi, hQreg, Or.inl hclose⟩
      replace hgap := hgap.resolve_left hclose
      obtain ⟨R, hRQ, hR, hReb, hRreg⟩ :=
        S.exists_refining_equipartition_sum_irregularPairs_le Q hQ (hη #Q.parts)
      refine ⟨Q, R, hQP.trans hPP₀, hRQ, hQ, hR, hReb, ?_, hRreg,
        (le_or_gt _ γ).imp id fun h ↦ ?_⟩
      · rw [iterate_succ_apply' g (i + 1)]
        exact (hReb.trans
          (equitablePairColorRegularityBound_le_strongPairColorRegularityStep le_rfl)).trans
          (strongPairColorRegularityStep_mono η hQg)
      · push_cast
        linarith
  obtain ⟨P, Q, hPP₀, hQP, hP, hQ, hQeb, hQg, hQreg, hgap⟩ := key ⌊1 / γ⌋₊
  refine ⟨P, Q, hPP₀, hQP, hP, hQ, hQeb, hQg, hQreg, hgap.resolve_right fun h ↦ ?_⟩
  have hN : 1 / γ < ⌊1 / γ⌋₊ + 1 := Nat.lt_floor_add_one _
  have h1 : 1 < γ * (⌊1 / γ⌋₊ + 1) := by rwa [div_lt_iff₀ hγ, mul_comm] at hN
  linarith [S.energy_le_one Q]

end PairColorSystem

end TauCeti
