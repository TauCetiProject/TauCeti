/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.SeededRegularization
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Order.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Strong equitable regularity for pair-color systems

Equitable pair-color regularity
(`PairColorSystem.exists_refining_equipartition_sum_irregularPairs_le`) produces an equipartition
whose irregular cell pairs cover at most `ε |V|²` vertex pairs at a tolerance `ε` chosen in
advance. Because the returned number of cells depends on `ε`, that theorem cannot directly achieve
a tolerance scheduled as a function of the returned number of cells.

This file proves the strong (Alon–Fischer–Krivelevich–Szegedy) form for pair-color systems. Given
an energy-gap bound `g > 0` and a positive tolerance schedule `η : ℕ → ℝ`, iterating seeded
equitable regularization produces nested equipartitions `P₀ ≥ P₁ ≥ P₂ ≥ …`, where `P_{i+1}`
regularizes `P_i` at tolerance `η #P_i.parts`. Because the pair-color energy lies in `[0, 1]` and
is nondecreasing under refinement, some consecutive pair `(P, Q) = (P_i, P_{i+1})` with
`i ≤ ⌊1 / g⌋₊` satisfies `S.energy Q - S.energy P ≤ g`. The fine equipartition `Q` is then
`η #P.parts`-regular outside an `η #P.parts`-fraction of the vertex pairs, while `#P.parts` is
bounded independently of `|V|` by `strongPairColorRegularityBound g η #P₀.parts`.

Combined with the `L¹` density-deviation bound across a small energy gap
(`PairColorSystem.sum_card_mul_abs_pairColorDensity_sub_refinementParent_le`) and coupled
low-discrepancy recoloring on the fine cell pairs, this yields regular approximations of lower
skeletons at arbitrary complexity schedules.

## Main definitions

* `TauCeti.strongPairColorRegularityStep`: upper bound on the cell count after one round of strong
  equitable regularization from at most `m` cells.
* `TauCeti.strongPairColorRegularityBound`: upper bound on the coarse cell count in the seeded and
  unseeded strong equitable regularity lemmas.

## Main results

* `TauCeti.PairColorSystem.exists_strong_refining_equipartition_sum_irregularPairs_le`: strong
  equitable regularity refining a prescribed equipartition.
* `TauCeti.PairColorSystem.exists_strong_equipartition_sum_irregularPairs_le`: unseeded strong
  equitable regularity with at least `l` coarse cells.

## References

* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.1 (the strong regularity lemma).
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Finpartition

namespace TauCeti

/-- Upper bound on the number of cells after one round of strong equitable pair-color
regularization from at most `m` cells at schedule `η`. -/
noncomputable def strongPairColorRegularityStep (η : ℕ → ℝ) (m : ℕ) : ℕ :=
  max m ((range (m + 1)).sup fun k ↦ equitablePairColorRegularityBound (η k) k)

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityStep`. -/
theorem strongPairColorRegularityStep_def (η : ℕ → ℝ) (m : ℕ) :
    strongPairColorRegularityStep η m =
      max m ((range (m + 1)).sup fun k ↦ equitablePairColorRegularityBound (η k) k) :=
  (rfl)

/-- `strongPairColorRegularityStep` never decreases the cell count. -/
theorem le_strongPairColorRegularityStep (η : ℕ → ℝ) (m : ℕ) :
    m ≤ strongPairColorRegularityStep η m :=
  le_max_left _ _

/-- `strongPairColorRegularityStep` is monotone in the cell count. -/
theorem monotone_strongPairColorRegularityStep (η : ℕ → ℝ) :
    Monotone (strongPairColorRegularityStep η) := fun _ _ h ↦
  max_le_max h (Finset.sup_mono (range_mono (Nat.succ_le_succ h)))

/-- Equitable regularization from `k ≤ m` cells at tolerance `η k` produces at most
`strongPairColorRegularityStep η m` cells. -/
theorem equitablePairColorRegularityBound_le_strongPairColorRegularityStep (η : ℕ → ℝ) {k m : ℕ}
    (hk : k ≤ m) :
    equitablePairColorRegularityBound (η k) k ≤ strongPairColorRegularityStep η m :=
  le_max_of_le_right (le_sup (f := fun k ↦ equitablePairColorRegularityBound (η k) k)
    (mem_range.2 (Nat.lt_succ_of_le hk)))

/-- Upper bound on the number of coarse cells in strong equitable pair-color regularization,
starting from `max l 1` cells with energy-gap threshold `g` and schedule `η`. -/
noncomputable def strongPairColorRegularityBound (g : ℝ) (η : ℕ → ℝ) (l : ℕ) : ℕ :=
  (strongPairColorRegularityStep η)^[⌊1 / g⌋₊] (max l 1)

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityBound`. -/
theorem strongPairColorRegularityBound_def (g : ℝ) (η : ℕ → ℝ) (l : ℕ) :
    strongPairColorRegularityBound g η l =
      (strongPairColorRegularityStep η)^[⌊1 / g⌋₊] (max l 1) :=
  (rfl)

/-- `strongPairColorRegularityBound` is at least the requested lower bound `l`. -/
theorem le_strongPairColorRegularityBound (g : ℝ) (η : ℕ → ℝ) (l : ℕ) :
    l ≤ strongPairColorRegularityBound g η l :=
  (le_max_left l 1).trans
    (Function.monotone_iterate_of_id_le (le_strongPairColorRegularityStep η) (Nat.zero_le _) _)

/-- `strongPairColorRegularityBound` is always positive. -/
theorem strongPairColorRegularityBound_pos (g : ℝ) (η : ℕ → ℝ) (l : ℕ) :
    0 < strongPairColorRegularityBound g η l :=
  Nat.lt_of_lt_of_le (by positivity : 0 < max l 1)
    (Function.monotone_iterate_of_id_le (le_strongPairColorRegularityStep η) (Nat.zero_le _) _)

/-- `strongPairColorRegularityBound` is monotone in the initial cell count `l`. -/
theorem monotone_strongPairColorRegularityBound (g : ℝ) (η : ℕ → ℝ) :
    Monotone (strongPairColorRegularityBound g η) := fun _ _ h ↦
  (monotone_strongPairColorRegularityStep η).iterate _ (max_le_max h le_rfl)

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V] (S : PairColorSystem κ V)

/-- Run `j` rounds of strong equitable regularization below `P₀`: either an earlier round already
achieved energy gap at most `g`, or the energy has reached at least `j * g`. -/
private theorem exists_strong_refining_equipartition_iterate [Fintype κ]
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {g : ℝ}
    {η : ℕ → ℝ} (hη : ∀ m, 0 < η m) (j : ℕ) :
    (∃ P Q : Finpartition (univ : Finset V),
      Q ≤ P ∧ P ≤ P₀ ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
      #P.parts ≤ (strongPairColorRegularityStep η)^[j] #P₀.parts ∧
      #Q.parts ≤ equitablePairColorRegularityBound (η #P.parts) #P.parts ∧
      ∑ AB ∈ S.irregularPairs (η #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        η #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      S.energy Q - S.energy P ≤ g) ∨
    ∃ P : Finpartition (univ : Finset V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ (strongPairColorRegularityStep η)^[j] #P₀.parts ∧
      j * g ≤ S.energy P := by
  let step := strongPairColorRegularityStep η
  induction j with
  | zero => exact Or.inr ⟨P₀, le_rfl, hP₀, le_rfl, by simpa using S.energy_nonneg P₀⟩
  | succ j ih =>
    have hle : step^[j] #P₀.parts ≤ step^[j + 1] #P₀.parts := by
      rw [Function.iterate_succ_apply']
      exact le_strongPairColorRegularityStep η _
    obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard, hreg, hgap⟩ | ⟨P, hPP₀, hP, hPcard, hE⟩ := ih
    · exact Or.inl ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard.trans hle, hQcard, hreg, hgap⟩
    obtain ⟨Q, hQP, hQ, hQcard, hreg⟩ :=
      S.exists_refining_equipartition_sum_irregularPairs_le P hP (hη #P.parts)
    by_cases hgap : S.energy Q - S.energy P ≤ g
    · exact Or.inl ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard.trans hle, hQcard, hreg, hgap⟩
    refine Or.inr ⟨Q, hQP.trans hPP₀, hQ, ?_, ?_⟩
    · rw [Function.iterate_succ_apply']
      exact hQcard.trans (equitablePairColorRegularityBound_le_strongPairColorRegularityStep η
        hPcard)
    · push_cast
      linarith

/-- **Strong equitable pair-color regularity refining a seed.** Given `g > 0`, a positive schedule
`η : ℕ → ℝ`, and an equipartition `P₀` of `V`, there exist nested equipartitions `Q ≤ P ≤ P₀` such
that `#P.parts ≤ strongPairColorRegularityBound g η #P₀.parts`, `#Q.parts` is bounded by equitable
regularization at `(η #P.parts, #P.parts)`, the `η #P.parts`-irregular cell pairs of `Q` cover at
most `η #P.parts |V|²` ordered vertex pairs, and `S.energy Q - S.energy P ≤ g`. -/
theorem exists_strong_refining_equipartition_sum_irregularPairs_le [Fintype κ]
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {g : ℝ} (hg : 0 < g)
    {η : ℕ → ℝ} (hη : ∀ m, 0 < η m) :
    ∃ P Q : Finpartition (univ : Finset V),
      Q ≤ P ∧ P ≤ P₀ ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
      #P.parts ≤ strongPairColorRegularityBound g η #P₀.parts ∧
      #Q.parts ≤ equitablePairColorRegularityBound (η #P.parts) #P.parts ∧
      ∑ AB ∈ S.irregularPairs (η #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        η #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      S.energy Q - S.energy P ≤ g := by
  have hbound : (strongPairColorRegularityStep η)^[⌊1 / g⌋₊] #P₀.parts ≤
      strongPairColorRegularityBound g η #P₀.parts := by
    rw [strongPairColorRegularityBound_def]
    exact (monotone_strongPairColorRegularityStep η).iterate _ (le_max_left _ _)
  obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard, hreg, hgap⟩ | ⟨P, hPP₀, hP, hPcard, hE⟩ :=
    S.exists_strong_refining_equipartition_iterate P₀ hP₀ hη ⌊1 / g⌋₊
  · exact ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard.trans hbound, hQcard, hreg, hgap⟩
  obtain ⟨Q, hQP, hQ, hQcard, hreg⟩ :=
    S.exists_refining_equipartition_sum_irregularPairs_le P hP (hη #P.parts)
  refine ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard.trans hbound, hQcard, hreg, ?_⟩
  by_contra! hgap
  have hK : 1 < (⌊1 / g⌋₊ + 1 : ℕ) * g := by
    rw [← div_lt_iff₀ hg, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  push_cast at hK
  linarith [S.energy_le_one Q]

/-- **Strong equitable pair-color regularity.** Given `g > 0`, a positive schedule `η : ℕ → ℝ`, and
`l ≤ |V|`, there exist nested equipartitions `Q ≤ P` of `V` with
`l ≤ #P.parts ≤ strongPairColorRegularityBound g η l` such that `Q` is `η #P.parts`-regular outside
at most `η #P.parts |V|²` vertex pairs and `S.energy Q - S.energy P ≤ g`. -/
theorem exists_strong_equipartition_sum_irregularPairs_le [Fintype κ] {g : ℝ} (hg : 0 < g)
    {η : ℕ → ℝ} (hη : ∀ m, 0 < η m) {l : ℕ} (hl : l ≤ Fintype.card V) :
    ∃ P Q : Finpartition (univ : Finset V),
      Q ≤ P ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
      l ≤ #P.parts ∧ #P.parts ≤ strongPairColorRegularityBound g η l ∧
      #Q.parts ≤ equitablePairColorRegularityBound (η #P.parts) #P.parts ∧
      ∑ AB ∈ S.irregularPairs (η #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        η #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      S.energy Q - S.energy P ≤ g := by
  by_cases hsize : max l 1 ≤ Fintype.card V
  · obtain ⟨P₀, hP₀, hcard⟩ := exists_equipartition_card_eq (univ : Finset V)
      (by positivity : max l 1 ≠ 0) (by rwa [card_univ])
    obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard, hreg, hgap⟩ :=
      S.exists_strong_refining_equipartition_sum_irregularPairs_le P₀ hP₀ hg hη
    refine ⟨P, Q, hQP, hP, hQ, (le_max_left l 1).trans (hcard ▸ card_mono hPP₀), ?_, hQcard,
      hreg, hgap⟩
    simpa [hcard, strongPairColorRegularityBound_def, max_assoc] using hPcard
  · have hn : Fintype.card V = 0 := by omega
    have hl0 : l = 0 := by omega
    obtain ⟨P, Q, hQP, -, hP, hQ, hPcard, hQcard, hreg, hgap⟩ :=
      S.exists_strong_refining_equipartition_sum_irregularPairs_le ⊥ (bot_isEquipartition _) hg hη
    refine ⟨P, Q, hQP, hP, hQ, by omega, ?_, hQcard, hreg, hgap⟩
    simpa [card_bot, card_univ, hn, hl0] using hPcard

end PairColorSystem

end TauCeti
