/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.SeededRegularization
public import TauCeti.Order.Partition.Finpartition
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.PartialSups
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.BigOperators.Finset.WeightedCauchySchwarz

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

Because the energy gap `S.energy Q - S.energy P` equals the mean squared density deviation between
`Q` and `P` across all colors (`PairColorSystem.sum_sq_pairColorDensity_sub_div_eq_energy_sub`),
weighted Cauchy–Schwarz converts `S.energy Q - S.energy P ≤ γ` into an `L¹` bound on how far the
fine block densities deviate from the coarse block densities
(`PairColorSystem.sum_abs_pairColorDensity_sub_le` and
`PairColorSystem.sum_card_mul_abs_pairColorDensity_sub_le`). In the strong regular approximation of
lower skeletons, this `L¹` bound controls the total variation edit cost of coupling `S` on each fine
block `A' ×ˢ B'` to the coarse block distribution on `A ×ˢ B`.

## Main definitions

* `TauCeti.strongPairColorRegularityStep`: complexity bound for one round of seeded pair-color
  regularization under a schedule `η`.
* `TauCeti.strongPairColorRegularityBound`: host-independent complexity bound for strong seeded
  pair-color regularization.

## Main results

* `TauCeti.PairColorSystem.exists_strong_refining_equipartition`: existence of nested equipartitions
  `Q ≤ P ≤ P₀` with scheduled fine regularity and energy gap at most `γ`.
* `TauCeti.PairColorSystem.sum_abs_pairColorDensity_sub_le`: `L¹` density-deviation bound over all
  ordered distinct pairs from an energy-gap bound.
* `TauCeti.PairColorSystem.sum_card_mul_abs_pairColorDensity_sub_le`: blockwise `L¹`
  density-deviation bound over fine blocks lying in distinct coarse cells.

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

section DensityDeviation

variable {P Q : Finpartition (univ : Finset V)}

/-- **`L¹` density deviation from an energy gap.** If `Q ≤ P` and `S.energy Q - S.energy P ≤ γ`,
then for each color `c`, the absolute deviations between the fine and coarse block densities of `c`
sum over all ordered distinct vertex pairs to at most `√γ * #(univ : Finset V).offDiag`. -/
theorem sum_abs_pairColorDensity_sub_le (hQP : Q ≤ P) {γ : ℝ} (hγ : S.energy Q - S.energy P ≤ γ)
    (c : κ) :
    ∑ p ∈ (univ : Finset V).offDiag,
        |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
          pairColorDensity S c (P.part p.1) (P.part p.2)| ≤
      √γ * #(univ : Finset V).offDiag := by
  set U := (univ : Finset V).offDiag
  let f : V × V → ℝ := fun p ↦
    (pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
      pairColorDensity S c (P.part p.1) (P.part p.2)
  rcases eq_or_ne #U 0 with hU0 | hU
  · rw [card_eq_zero.1 hU0, sum_empty, card_empty, Nat.cast_zero, mul_zero]
  · have hUpos : (0 : ℝ) < #U := Nat.cast_pos.2 (Nat.pos_of_ne_zero hU)
    have hw0 : ∀ p ∈ U, 0 ≤ (1 : ℝ) / #U := fun _ _ ↦ by positivity
    have hw1 : ∑ _p ∈ U, (1 : ℝ) / #U ≤ 1 := by
      rw [sum_const, nsmul_eq_mul, mul_one_div, div_self hUpos.ne']
    have hsq : ∑ p ∈ U, ((1 : ℝ) / #U) * f p ^ 2 ≤ γ := by
      rw [← mul_sum, one_div_mul_eq_div]
      refine (div_le_div_of_nonneg_right ?_ hUpos.le).trans
        ((S.sum_sq_pairColorDensity_sub_div_eq_energy_sub hQP).trans_le hγ)
      exact sum_le_sum fun p _ ↦
        single_le_sum (f := fun k ↦ ((pairColorDensity S k (Q.part p.1) (Q.part p.2) : ℝ) -
          pairColorDensity S k (P.part p.1) (P.part p.2)) ^ 2)
          (fun _ _ ↦ sq_nonneg _) (mem_univ c)
    have hcs := U.weighted_sum_abs_le_sqrt (fun _ ↦ (1 : ℝ) / #U) f hw0 hw1 hsq
    rw [← mul_sum, one_div_mul_eq_div, div_le_iff₀ hUpos] at hcs
    exact hcs

/-- **Blockwise `L¹` density deviation across distinct coarse cells.** If `Q ≤ P` and
`S.energy Q - S.energy P ≤ γ`, then summing `(#A' * #B') * |d_c(A', B') - d_c(A, B)|` over all pairs
of fine cells `(A', B')` whose coarse parents `A = refinementParent hQP A'` and
`B = refinementParent hQP B'` are distinct gives at most `√γ * #(univ : Finset V).offDiag`. -/
theorem sum_card_mul_abs_pairColorDensity_sub_le (hQP : Q ≤ P) {γ : ℝ}
    (hγ : S.energy Q - S.energy P ≤ γ) (c : κ) :
    ∑ AB ∈ (univ : Finset (Q.parts × Q.parts)) with
        refinementParent hQP AB.1 ≠ refinementParent hQP AB.2,
        (#AB.1.1 * #AB.2.1 : ℝ) *
          |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| ≤
      √γ * #(univ : Finset V).offDiag := by
  let f : V × V → ℝ := fun p ↦
    |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
      pairColorDensity S c (P.part p.1) (P.part p.2)|
  set I := (univ : Finset (Q.parts × Q.parts)).filter fun AB ↦
    refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  have hterm (AB : Q.parts × Q.parts) :
      (#AB.1.1 * #AB.2.1 : ℝ) *
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| =
        ∑ p ∈ AB.1.1 ×ˢ AB.2.1, f p := by
    have hcongr : ∀ p ∈ AB.1.1 ×ˢ AB.2.1, f p =
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| := by
      intro p hp
      obtain ⟨hp₁, hp₂⟩ := mem_product.1 hp
      simp only [f, Q.part_eq_of_mem AB.1.2 hp₁, Q.part_eq_of_mem AB.2.2 hp₂,
        part_eq_refinementParent hQP AB.1 hp₁, part_eq_refinementParent hQP AB.2 hp₂]
    rw [sum_congr rfl hcongr, sum_const, card_product, nsmul_eq_mul, Nat.cast_mul]
  have hdisj : (I : Set (Q.parts × Q.parts)).PairwiseDisjoint fun AB ↦ AB.1.1 ×ˢ AB.2.1 := by
    intro AB _ CD _ hne
    refine disjoint_product.2 ?_
    by_cases h₁ : AB.1 = CD.1
    · exact Or.inr (Q.disjoint AB.2.2 CD.2.2 <| Subtype.coe_injective.ne fun h₂ ↦
        hne (Prod.ext h₁ h₂))
    · exact Or.inl (Q.disjoint AB.1.2 CD.1.2 (Subtype.coe_injective.ne h₁))
  have hsub : I.biUnion (fun AB ↦ AB.1.1 ×ˢ AB.2.1) ⊆ (univ : Finset V).offDiag := by
    intro p hp
    obtain ⟨AB, hAB, hpAB⟩ := mem_biUnion.1 hp
    obtain ⟨hp₁, hp₂⟩ := mem_product.1 hpAB
    have hne_parent : (refinementParent hQP AB.1).1 ≠ (refinementParent hQP AB.2).1 :=
      Subtype.coe_injective.ne (mem_filter.1 hAB).2
    have hdisjP := P.disjoint (refinementParent hQP AB.1).2 (refinementParent hQP AB.2).2 hne_parent
    refine mem_offDiag.2 ⟨mem_univ _, mem_univ _, fun heq ↦ ?_⟩
    exact disjoint_left.1 hdisjP (le_refinementParent hQP AB.1 hp₁)
      (heq ▸ le_refinementParent hQP AB.2 hp₂)
  calc ∑ AB ∈ I, (#AB.1.1 * #AB.2.1 : ℝ) *
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|
      = ∑ AB ∈ I, ∑ p ∈ AB.1.1 ×ˢ AB.2.1, f p := sum_congr rfl fun AB _ ↦ hterm AB
    _ = ∑ p ∈ I.biUnion (fun AB ↦ AB.1.1 ×ˢ AB.2.1), f p := (sum_biUnion hdisj).symm
    _ ≤ ∑ p ∈ (univ : Finset V).offDiag, f p :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ abs_nonneg _
    _ ≤ √γ * #(univ : Finset V).offDiag := S.sum_abs_pairColorDensity_sub_le hQP hγ c

end DensityDeviation

end PairColorSystem

end TauCeti
