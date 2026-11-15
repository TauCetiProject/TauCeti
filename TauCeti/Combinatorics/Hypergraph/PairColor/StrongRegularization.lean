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
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Iterate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Data.Finset.Basic

/-!
# Strong regularity and refinement amalgamation for pair-color systems

Equitable pair-color regularity
(`PairColorSystem.exists_refining_equipartition_sum_irregularPairs_le`) controls irregular cell
pairs at a fixed tolerance `ε`, producing a vertex partition whose cell count depends on `ε`. When a
construction requires regularity at a scale `η #P.parts` that depends on the number of cells of a
coarse partition `P`, a single regularization pass is circular.

This file resolves that dependence via a two-scale strong regularity iteration and supplies the two
companion transfer lemmas needed to pass back from the fine partition `Q` to the coarse partition
`P`:

1. **Energy-gap `L¹` drift** (`PairColorSystem.sum_offDiag_abs_pairColorDensity_sub_le` and
   `PairColorSystem.sum_refinementParent_ne_abs_pairColorDensity_sub_le`): if `Q ≤ P` has pair-color
   energy gap `S.energy Q - S.energy P ≤ g`, Cauchy–Schwarz on the refinement defect identity bounds
   the size-weighted `ℓ¹` palette distance between fine block densities and their coarse parent
   densities by `√(card κ * g) * |V|²`.
2. **Coarse regularity from fine regular blocks** (`PairColorSystem.isRegularPair_of_refinement`):
   if `Q ≤ P` and every fine block `(A', B')` inside an off-diagonal coarse block `(A, B)` is
   `η`-regular for `T` with color densities within `η` of `p`, then `(A, B)` has color densities
   within `2 * η` of `p` and is `δ`-regular whenever `4 * η ≤ δ ^ 3`.
3. **Strong equitable pair-color regularity** (`PairColorSystem.exists_strong_equipartition`):
   iterating seeded equitable regularity along any positive schedule `η : ℕ → ℝ` finds
   equipartitions `Q ≤ P ≤ P₀` with energy gap at most `g`, fine irregular mass at scale
   `η #P.parts`, and coarse cell count bounded independently of `V` by
   `strongPairColorRegularityBound g η #P₀.parts`.

## Main definitions

* `TauCeti.strongPairColorRegularityStep`: monotone cell-count bound for one seeded regularity step.
* `TauCeti.strongPairColorRegularityBound`: cell-count bound for the coarse partition in strong
  pair-color regularity.

## Main results

* `TauCeti.PairColorSystem.sum_offDiag_abs_pairColorDensity_sub_le`: `L¹` density drift over
  ordered distinct vertex pairs from a small energy gap.
* `TauCeti.PairColorSystem.sum_refinementParent_ne_abs_pairColorDensity_sub_le`: block-summed `L¹`
  density drift across fine blocks in distinct coarse cells.
* `TauCeti.PairColorSystem.abs_pairColorDensity_sub_le_of_refinement`: coarse block density
  accuracy from fine regular blocks.
* `TauCeti.PairColorSystem.isRegularPair_of_refinement`: coarse pair regularity from fine regular
  blocks.
* `TauCeti.PairColorSystem.exists_strong_equipartition`: strong equitable regularity refining a
  seed equipartition.

## References

* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), 451–476.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), §4.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
-/

public section

open Finset Finpartition Function

namespace TauCeti

/-- Cell-count bound for one round of strong pair-color regularity from at most `m` coarse cells:
the maximum of `equitablePairColorRegularityBound (η j) j` over `j ≤ m`, making the step bound
monotone for an arbitrary schedule `η`. -/
noncomputable def strongPairColorRegularityStep (η : ℕ → ℝ) (m : ℕ) : ℕ :=
  partialSups (fun j ↦ equitablePairColorRegularityBound (η j) j) m

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityStep`. -/
theorem strongPairColorRegularityStep_def (η : ℕ → ℝ) (m : ℕ) :
    strongPairColorRegularityStep η m =
      partialSups (fun j ↦ equitablePairColorRegularityBound (η j) j) m :=
  (rfl)

/-- `strongPairColorRegularityStep` dominates the seeded regularity bound at every `j ≤ m`. -/
theorem equitablePairColorRegularityBound_le_strongPairColorRegularityStep {η : ℕ → ℝ} {j m : ℕ}
    (h : j ≤ m) :
    equitablePairColorRegularityBound (η j) j ≤ strongPairColorRegularityStep η m :=
  le_partialSups_of_le (fun j ↦ equitablePairColorRegularityBound (η j) j) h

/-- `strongPairColorRegularityStep` is monotone in the starting cell count. -/
theorem strongPairColorRegularityStep_mono (η : ℕ → ℝ) :
    Monotone (strongPairColorRegularityStep η) :=
  (partialSups fun j ↦ equitablePairColorRegularityBound (η j) j).monotone

/-- One step of strong pair-color regularity along a positive schedule does not decrease the number
of cells. -/
theorem le_strongPairColorRegularityStep {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (m : ℕ) :
    m ≤ strongPairColorRegularityStep η m := by
  have hle : max m 1 ≤ equitablePairColorRegularityBound (η m) m := by
    rw [equitablePairColorRegularityBound_def]
    exact id_le_iterate_of_id_le (le_ceil_mul_mul_four_pow_sq (hη m)) _ _
  exact (le_max_left m 1).trans
    (hle.trans (equitablePairColorRegularityBound_le_strongPairColorRegularityStep le_rfl))

/-- Bound on the coarse cell count in `PairColorSystem.exists_strong_equipartition`, starting from
`m₀` cells: at most `⌊1 / g⌋₊` failed energy-gap rounds occur before `S.energy Q - S.energy P ≤ g`.
-/
noncomputable def strongPairColorRegularityBound (g : ℝ) (η : ℕ → ℝ) (m₀ : ℕ) : ℕ :=
  (strongPairColorRegularityStep η)^[⌊1 / g⌋₊] m₀

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityBound`. -/
theorem strongPairColorRegularityBound_def (g : ℝ) (η : ℕ → ℝ) (m₀ : ℕ) :
    strongPairColorRegularityBound g η m₀ = (strongPairColorRegularityStep η)^[⌊1 / g⌋₊] m₀ :=
  (rfl)

/-- `strongPairColorRegularityBound` is monotone in the initial cell count. -/
theorem strongPairColorRegularityBound_mono (g : ℝ) (η : ℕ → ℝ) :
    Monotone (strongPairColorRegularityBound g η) :=
  (strongPairColorRegularityStep_mono η).iterate _

/-- For a positive schedule, `strongPairColorRegularityBound` is at least the initial cell count. -/
theorem le_strongPairColorRegularityBound (g : ℝ) {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) (m₀ : ℕ) :
    m₀ ≤ strongPairColorRegularityBound g η m₀ :=
  id_le_iterate_of_id_le (le_strongPairColorRegularityStep hη) _ _

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V]

section EnergyDrift

variable [Fintype κ] (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}

/-- **Energy gap bounds `L¹` density drift.** If `Q ≤ P` has pair-color energy gap at most `g`, then
the sum over ordered distinct vertex pairs and over all palette colors of the absolute density
difference between the fine and coarse blocks is at most `√(card κ * g) * |V|²`. -/
theorem sum_offDiag_abs_pairColorDensity_sub_le (h : Q ≤ P) {g : ℝ}
    (hgap : S.energy Q - S.energy P ≤ g) :
    ∑ p ∈ (univ : Finset V).offDiag, ∑ c : κ,
        |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
          pairColorDensity S c (P.part p.1) (P.part p.2)| ≤
      √(Fintype.card κ * g) * (Fintype.card V : ℝ) ^ 2 := by
  let D := (univ : Finset V).offDiag
  let f (p : V × V) (c : κ) : ℝ :=
    (pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
      pairColorDensity S c (P.part p.1) (P.part p.2)
  have hg : 0 ≤ g := (sub_nonneg.2 (S.energy_mono_of_refines h)).trans hgap
  have hsq : ∑ p ∈ D, ∑ c : κ, f p c ^ 2 ≤ g * #D := by
    rcases (#D).eq_zero_or_pos with hD0 | hDpos
    · rw [card_eq_zero.1 hD0]
      simp
    · have hDpos' : (0 : ℝ) < #D := Nat.cast_pos.2 hDpos
      exact (div_le_iff₀ hDpos').1
        ((S.sum_sq_pairColorDensity_sub_div_eq_energy_sub h).trans_le hgap)
  have hDle : (#D : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast (card_offDiag_le_sq (univ : Finset V)).trans_eq (by rw [card_univ])
  have hcs := sum_mul_sq_le_sq_mul_sq (D ×ˢ (univ : Finset κ)) (fun _ ↦ (1 : ℝ))
    (fun pc ↦ |f pc.1 pc.2|)
  simp only [one_mul, one_pow, sum_const, card_product, card_univ, nsmul_eq_mul, mul_one,
    sq_abs, sum_product] at hcs
  have hrhs : ((#D * Fintype.card κ : ℕ) : ℝ) * ∑ p ∈ D, ∑ c : κ, f p c ^ 2 ≤
      (√(Fintype.card κ * g) * (Fintype.card V : ℝ) ^ 2) ^ 2 := by
    calc ((#D * Fintype.card κ : ℕ) : ℝ) * ∑ p ∈ D, ∑ c : κ, f p c ^ 2
        ≤ (#D * Fintype.card κ : ℝ) * (g * #D) := by
          push_cast; exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (Fintype.card κ * g) * (#D : ℝ) ^ 2 := by ring
      _ ≤ (Fintype.card κ * g) * ((Fintype.card V : ℝ) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hDle 2) (by positivity)
      _ = (√(Fintype.card κ * g) * (Fintype.card V : ℝ) ^ 2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact (sq_le_sq₀ (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
    (by positivity)).1 (hcs.trans hrhs)

/-- **Block-summed `L¹` density drift.** If `Q ≤ P` has energy gap at most `g`, then summing
`(#A' * #B') * ∑ c, |d_c(A', B') - d_c(A, B)|` over all fine block pairs `(A', B')` lying in
distinct coarse parent cells `(A, B)` gives at most `√(card κ * g) * |V|²`. -/
theorem sum_refinementParent_ne_abs_pairColorDensity_sub_le (h : Q ≤ P) {g : ℝ}
    (hgap : S.energy Q - S.energy P ≤ g) :
    ∑ AB ∈ univ.filter (fun AB : Q.parts × Q.parts ↦
        refinementParent h AB.1 ≠ refinementParent h AB.2),
      (#AB.1.1 * #AB.2.1 : ℝ) * ∑ c : κ,
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent h AB.1).1 (refinementParent h AB.2).1| ≤
      √(Fintype.card κ * g) * (Fintype.card V : ℝ) ^ 2 := by
  let F := univ.filter fun AB : Q.parts × Q.parts ↦
    refinementParent h AB.1 ≠ refinementParent h AB.2
  let d (p : V × V) : ℝ := ∑ c : κ,
    |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
      pairColorDensity S c (P.part p.1) (P.part p.2)|
  have hblock (AB : Q.parts × Q.parts) :
      (#AB.1.1 * #AB.2.1 : ℝ) * ∑ c : κ,
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent h AB.1).1 (refinementParent h AB.2).1| =
      ∑ p ∈ AB.1.1 ×ˢ AB.2.1, d p := by
    rw [← Nat.cast_mul, ← card_product, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun p hp ↦ sum_congr rfl fun c _ ↦ ?_
    obtain ⟨hp₁, hp₂⟩ := mem_product.1 hp
    rw [Q.part_eq_of_mem AB.1.2 hp₁, Q.part_eq_of_mem AB.2.2 hp₂,
      part_eq_refinementParent h AB.1 hp₁, part_eq_refinementParent h AB.2 hp₂]
  have hdisj : (F : Set (Q.parts × Q.parts)).PairwiseDisjoint (fun AB ↦ AB.1.1 ×ˢ AB.2.1) := by
    intro AB _ CD _ hne
    refine disjoint_product.2 ?_
    by_cases h₁ : AB.1 = CD.1
    · exact Or.inr (Q.pairwiseDisjoint_subtype_val Set.univ (Set.mem_univ _) (Set.mem_univ _)
        fun h₂ ↦ hne (Prod.ext h₁ h₂))
    · exact Or.inl (Q.pairwiseDisjoint_subtype_val Set.univ (Set.mem_univ _) (Set.mem_univ _) h₁)
  have hsub : F.biUnion (fun AB ↦ AB.1.1 ×ˢ AB.2.1) ⊆ (univ : Finset V).offDiag := by
    intro p hp
    obtain ⟨AB, hAB, hpAB⟩ := mem_biUnion.1 hp
    obtain ⟨hp₁, hp₂⟩ := mem_product.1 hpAB
    have hneP : (refinementParent h AB.1).1 ≠ (refinementParent h AB.2).1 :=
      Subtype.coe_injective.ne (mem_filter.1 hAB).2
    have hdisjP := P.disjoint (refinementParent h AB.1).2 (refinementParent h AB.2).2 hneP
    exact mem_offDiag.2 ⟨mem_univ _, mem_univ _, hdisjP.forall_ne_finset
      (le_refinementParent h AB.1 hp₁) (le_refinementParent h AB.2 hp₂)⟩
  calc ∑ AB ∈ F, (#AB.1.1 * #AB.2.1 : ℝ) * ∑ c : κ,
          |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
            pairColorDensity S c (refinementParent h AB.1).1 (refinementParent h AB.2).1|
      = ∑ AB ∈ F, ∑ p ∈ AB.1.1 ×ˢ AB.2.1, d p := sum_congr rfl fun AB _ ↦ hblock AB
    _ = ∑ p ∈ F.biUnion (fun AB ↦ AB.1.1 ×ˢ AB.2.1), d p := (sum_biUnion hdisj).symm
    _ ≤ ∑ p ∈ (univ : Finset V).offDiag, d p :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _
    _ ≤ √(Fintype.card κ * g) * (Fintype.card V : ℝ) ^ 2 :=
        S.sum_offDiag_abs_pairColorDensity_sub_le h hgap

end EnergyDrift

section RefinementAmalgamation

variable {P Q : Finpartition (univ : Finset V)}

/-- Partition the `c`-colored pairs in a subrectangle `X ×ˢ Y ⊆ A ×ˢ B` across the fine children
of `A` and `B` in `Q`. -/
private theorem card_filter_colorOfPair_eq_sum_refinement [DecidableEq κ]
    (T : PairColorSystem κ V) (hQP : Q ≤ P) {A B : Finset V} (hA : A ∈ P.parts)
    (hB : B ∈ P.parts) {X Y : Finset V} (hXA : X ⊆ A) (hYB : Y ⊆ B) (c : κ) :
    (#{q ∈ X ×ˢ Y | T.colorOfPair q.1 q.2 = some c} : ℝ) =
      ∑ A' ∈ univ.filter (fun A' : Q.parts ↦ refinementParent hQP A' = ⟨A, hA⟩),
        ∑ B' ∈ univ.filter (fun B' : Q.parts ↦ refinementParent hQP B' = ⟨B, hB⟩),
          (#{q ∈ (X ∩ A'.1) ×ˢ (Y ∩ B'.1) | T.colorOfPair q.1 q.2 = some c} : ℝ) := by
  classical
  let FA := univ.filter fun A' : Q.parts ↦ refinementParent hQP A' = ⟨A, hA⟩
  let FB := univ.filter fun B' : Q.parts ↦ refinementParent hQP B' = ⟨B, hB⟩
  have hprod : X ×ˢ Y = (FA ×ˢ FB).biUnion fun AB ↦ (X ∩ AB.1.1) ×ˢ (Y ∩ AB.2.1) := by
    have hXeq : X = FA.biUnion fun A' ↦ X ∩ A'.1 := by
      rw [← inter_biUnion, biUnion_filter_refinementParent_eq hQP ⟨A, hA⟩, inter_eq_left.2 hXA]
    have hYeq : Y = FB.biUnion fun B' ↦ Y ∩ B'.1 := by
      rw [← inter_biUnion, biUnion_filter_refinementParent_eq hQP ⟨B, hB⟩, inter_eq_left.2 hYB]
    conv_lhs => rw [hXeq, hYeq]
    ext q
    simp only [mem_product, mem_biUnion, Prod.exists]
    exact ⟨fun ⟨⟨A', hA', hq₁⟩, ⟨B', hB', hq₂⟩⟩ ↦ ⟨A', B', ⟨hA', hB'⟩, hq₁, hq₂⟩,
      fun ⟨A', B', ⟨hA', hB'⟩, hq₁, hq₂⟩ ↦ ⟨⟨A', hA', hq₁⟩, ⟨B', hB', hq₂⟩⟩⟩
  rw [hprod, filter_biUnion, card_biUnion, Nat.cast_sum, sum_product]
  intro AB _ CD _ hne
  refine disjoint_filter_filter (disjoint_product.2 ?_)
  by_cases h₁ : AB.1 = CD.1
  · exact Or.inr <|
      (Q.pairwiseDisjoint_subtype_val Set.univ (Set.mem_univ _) (Set.mem_univ _)
        fun h₂ ↦ hne (Prod.ext h₁ h₂)).mono inter_subset_right inter_subset_right
  · exact Or.inl <|
      (Q.pairwiseDisjoint_subtype_val Set.univ (Set.mem_univ _) (Set.mem_univ _) h₁).mono
        inter_subset_right inter_subset_right

/-- Summing fine rectangle discrepancies over the fine blocks partitioning `(A, B)` bounds the color
count deviation on any subrectangle `X ×ˢ Y ⊆ A ×ˢ B` by `2 * η * #A * #B`. -/
private theorem abs_card_filter_colorOfPair_sub_le_of_refinement [DecidableEq κ]
    (T : PairColorSystem κ V) (hQP : Q ≤ P) {A B : Finset V} (hA : A ∈ P.parts)
    (hB : B ∈ P.parts) (hAB : A ≠ B) {p : κ → ℝ} {η : ℝ}
    (hreg : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B → T.IsRegularPair η A' B')
    (hdens : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
      ∀ c, |(pairColorDensity T c A' B' : ℝ) - p c| ≤ η)
    {X Y : Finset V} (hXA : X ⊆ A) (hYB : Y ⊆ B) (c : κ) :
    |(#{q ∈ X ×ˢ Y | T.colorOfPair q.1 q.2 = some c} : ℝ) - p c * #X * #Y| ≤
      2 * η * #A * #B := by
  classical
  have hdisjAB : Disjoint A B := P.disjoint hA hB hAB
  let FA := univ.filter fun A' : Q.parts ↦ refinementParent hQP A' = ⟨A, hA⟩
  let FB := univ.filter fun B' : Q.parts ↦ refinementParent hQP B' = ⟨B, hB⟩
  have hpXY : p c * #X * #Y =
      ∑ A' ∈ FA, ∑ B' ∈ FB, p c * #(X ∩ A'.1) * #(Y ∩ B'.1) := by
    have hXsum : (#X : ℝ) = ∑ A' ∈ FA, (#(X ∩ A'.1) : ℝ) := by
      rw [← Nat.cast_sum, sum_card_inter_filter_refinementParent_eq hQP ⟨A, hA⟩ X,
        inter_eq_left.2 hXA]
    have hYsum : (#Y : ℝ) = ∑ B' ∈ FB, (#(Y ∩ B'.1) : ℝ) := by
      rw [← Nat.cast_sum, sum_card_inter_filter_refinementParent_eq hQP ⟨B, hB⟩ Y,
        inter_eq_left.2 hYB]
    simp_rw [hXsum, hYsum, mul_sum, sum_mul]
    exact sum_comm
  have hABsum : 2 * η * #A * #B = ∑ A' ∈ FA, ∑ B' ∈ FB, 2 * η * #A'.1 * #B'.1 := by
    have hAsum : (#A : ℝ) = ∑ A' ∈ FA, (#A'.1 : ℝ) := by
      rw [← Nat.cast_sum, sum_card_filter_refinementParent_eq hQP ⟨A, hA⟩]
    have hBsum : (#B : ℝ) = ∑ B' ∈ FB, (#B'.1 : ℝ) := by
      rw [← Nat.cast_sum, sum_card_filter_refinementParent_eq hQP ⟨B, hB⟩]
    simp_rw [hAsum, hBsum, mul_sum, sum_mul]
    exact sum_comm
  rw [card_filter_colorOfPair_eq_sum_refinement T hQP hA hB hXA hYB c, hpXY, hABsum,
    ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun A' hA' ↦ ?_)
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun B' hB' ↦ ?_)
  have hA'A : A'.1 ⊆ A := (refinementParent_eq_iff hQP).1 (mem_filter.1 hA').2
  have hB'B : B'.1 ⊆ B := (refinementParent_eq_iff hQP).1 (mem_filter.1 hB').2
  have hreg' := hreg A'.1 A'.2 hA'A B'.1 B'.2 hB'B
  have hη : 0 ≤ η := haveI : Nonempty κ := ⟨c⟩; hreg'.nonneg
  have hdisc := hreg'.abs_card_filter_colorOfPair_sub_le (c := c)
    (hdisjAB.mono hA'A hB'B) (inter_subset_right (s₁ := X)) (inter_subset_right (s₁ := Y))
  have hs : (#(X ∩ A'.1) : ℝ) ≤ #A'.1 := mod_cast card_le_card inter_subset_right
  have ht : (#(Y ∩ B'.1) : ℝ) ≤ #B'.1 := mod_cast card_le_card inter_subset_right
  have hshift : |(pairColorDensity T c A'.1 B'.1 : ℝ) * #(X ∩ A'.1) * #(Y ∩ B'.1) -
      p c * #(X ∩ A'.1) * #(Y ∩ B'.1)| ≤ η * #A'.1 * #B'.1 := by
    calc |(pairColorDensity T c A'.1 B'.1 : ℝ) * #(X ∩ A'.1) * #(Y ∩ B'.1) -
            p c * #(X ∩ A'.1) * #(Y ∩ B'.1)|
        = |(pairColorDensity T c A'.1 B'.1 : ℝ) - p c| * (#(X ∩ A'.1) * #(Y ∩ B'.1)) := by
          rw [mul_assoc (pairColorDensity T c A'.1 B'.1 : ℝ), mul_assoc (p c), ← sub_mul,
            abs_mul, abs_of_nonneg (a := (#(X ∩ A'.1) : ℝ) * #(Y ∩ B'.1)) (by positivity)]
      _ ≤ η * (#A'.1 * #B'.1) := mul_le_mul (hdens A'.1 A'.2 hA'A B'.1 B'.2 hB'B c)
          (mul_le_mul hs ht (by positivity) (by positivity)) (by positivity) hη
      _ = η * #A'.1 * #B'.1 := by ring
  exact (abs_sub_le _ ((pairColorDensity T c A'.1 B'.1 : ℝ) * #(X ∩ A'.1) * #(Y ∩ B'.1)) _).trans
    (by linarith)

/-- **Coarse density from fine regular blocks.** If `Q ≤ P` and every fine block `(A', B')` inside
an off-diagonal coarse block `(A, B)` is `η`-regular for `T` with color densities within `η` of
`p`, then `(A, B)` has color densities within `2 * η` of `p`. -/
theorem abs_pairColorDensity_sub_le_of_refinement (T : PairColorSystem κ V) (hQP : Q ≤ P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) {p : κ → ℝ} {η : ℝ}
    (hreg : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B → T.IsRegularPair η A' B')
    (hdens : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
      ∀ c, |(pairColorDensity T c A' B' : ℝ) - p c| ≤ η)
    (c : κ) :
    |(pairColorDensity T c A B : ℝ) - p c| ≤ 2 * η := by
  classical
  have hABpos : (0 : ℝ) < #A * #B :=
    mul_pos (Nat.cast_pos.2 (P.nonempty_of_mem_parts hA).card_pos)
      (Nat.cast_pos.2 (P.nonempty_of_mem_parts hB).card_pos)
  have hcard : (#{q ∈ A ×ˢ B | T.colorOfPair q.1 q.2 = some c} : ℝ) =
      pairColorDensity T c A B * (#A * #B) :=
    mod_cast (pairColorDensity_mul_card_of_disjoint T c (P.disjoint hA hB hAB)).symm
  have hbound := abs_card_filter_colorOfPair_sub_le_of_refinement T hQP hA hB hAB hreg hdens
    subset_rfl subset_rfl c
  rw [hcard, mul_assoc (p c), ← sub_mul, abs_mul, abs_of_pos hABpos] at hbound
  exact le_of_mul_le_mul_right (by linarith) hABpos

/-- **Coarse regularity from fine regular blocks.** Under the hypotheses of
`PairColorSystem.abs_pairColorDensity_sub_le_of_refinement`, if `0 < δ` and `4 * η ≤ δ ^ 3`, then
`(A, B)` is `δ`-regular for `T`. -/
theorem isRegularPair_of_refinement (T : PairColorSystem κ V) (hQP : Q ≤ P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) {p : κ → ℝ} {η δ : ℝ}
    (hδ : 0 < δ) (hηδ : 4 * η ≤ δ ^ 3)
    (hreg : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B → T.IsRegularPair η A' B')
    (hdens : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
      ∀ c, |(pairColorDensity T c A' B' : ℝ) - p c| ≤ η) :
    T.IsRegularPair δ A B := by
  classical
  obtain hδ1 | hδ1 := le_or_gt 1 δ
  · exact isRegularPair_of_one_le hδ1
  rw [isRegularPair_iff]
  intro c X hXA Y hYB hX hY
  obtain ⟨A', hA', hA'A⟩ := exists_le_of_le hQP hA
  obtain ⟨B', hB', hB'B⟩ := exists_le_of_le hQP hB
  have hη : 0 ≤ η := haveI : Nonempty κ := ⟨c⟩; (hreg A' hA' hA'A B' hB' hB'B).nonneg
  have hApos : (0 : ℝ) < #A := Nat.cast_pos.2 (P.nonempty_of_mem_parts hA).card_pos
  have hBpos : (0 : ℝ) < #B := Nat.cast_pos.2 (P.nonempty_of_mem_parts hB).card_pos
  have hXYle : δ ^ 2 * (#A * #B) ≤ #X * #Y := by
    calc δ ^ 2 * (#A * #B) = (δ * #A) * (δ * #B) := by ring
      _ ≤ #X * #Y := mul_le_mul hX hY (by positivity) (by positivity)
  have hXYpos : (0 : ℝ) < #X * #Y := lt_of_lt_of_le (by positivity) hXYle
  have hcard : (#{q ∈ X ×ˢ Y | T.colorOfPair q.1 q.2 = some c} : ℝ) =
      pairColorDensity T c X Y * (#X * #Y) :=
    mod_cast (pairColorDensity_mul_card_of_disjoint T c ((P.disjoint hA hB hAB).mono hXA hYB)).symm
  have hXYbound := abs_card_filter_colorOfPair_sub_le_of_refinement T hQP hA hB hAB hreg hdens
    hXA hYB c
  rw [hcard, mul_assoc (p c), ← sub_mul, abs_mul, abs_of_pos hXYpos] at hXYbound
  have hsub : |(pairColorDensity T c X Y : ℝ) - p c| ≤ 2 * η / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_right (a := (#A * #B : ℝ)) ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hXYle (abs_nonneg ((pairColorDensity T c X Y : ℝ) - p c))
    linarith
  have hfull := abs_pairColorDensity_sub_le_of_refinement T hQP hA hB hAB hreg hdens c
  have hbudget : 2 * η / δ ^ 2 + 2 * η ≤ δ := by
    rw [← le_sub_iff_add_le, div_le_iff₀ (by positivity)]
    have hsq1 : δ ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq1 hη]
  exact (abs_sub_le _ (p c) _).trans (by rw [abs_sub_comm (p c)]; linarith)

end RefinementAmalgamation

section StrongEquipartition

/-- **Strong equitable regularity for pair-color systems.** Given an equipartition `P₀`, an energy
gap tolerance `g > 0`, and a positive schedule `η : ℕ → ℝ`, there exist equipartitions `Q ≤ P ≤ P₀`
such that `P` has at most `strongPairColorRegularityBound g η #P₀.parts` cells, `Q` has at most
`strongPairColorRegularityStep η #P.parts` cells, `S.energy Q - S.energy P ≤ g`, and the irregular
distinct-cell pairs of `Q` at parameter `η #P.parts` cover at most `η #P.parts * |V|²` ordered
vertex pairs. -/
theorem exists_strong_equipartition [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {g : ℝ} (hg : 0 < g)
    {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    ∃ P Q : Finpartition (univ : Finset V), Q ≤ P ∧ P ≤ P₀ ∧
      P.IsEquipartition ∧ Q.IsEquipartition ∧
      #P.parts ≤ strongPairColorRegularityBound g η #P₀.parts ∧
      #Q.parts ≤ strongPairColorRegularityStep η #P.parts ∧
      S.energy Q - S.energy P ≤ g ∧
      ∑ AB ∈ S.irregularPairs (η #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        η #P.parts * (Fintype.card V : ℝ) ^ 2 := by
  let step := strongPairColorRegularityStep η
  have hround (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition) :
      ∃ Q : Finpartition (univ : Finset V), Q ≤ P ∧ Q.IsEquipartition ∧
        #Q.parts ≤ step #P.parts ∧
        ∑ AB ∈ S.irregularPairs (η #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
          η #P.parts * (Fintype.card V : ℝ) ^ 2 := by
    obtain ⟨Q, hQP, hQ, hQcard, hQreg⟩ :=
      S.exists_refining_equipartition_sum_irregularPairs_le P hP (hη #P.parts)
    exact ⟨Q, hQP, hQ,
      hQcard.trans (equitablePairColorRegularityBound_le_strongPairColorRegularityStep le_rfl),
      hQreg⟩
  have hiter (i : ℕ) : ∃ P Q : Finpartition (univ : Finset V), Q ≤ P ∧ P ≤ P₀ ∧
      P.IsEquipartition ∧ Q.IsEquipartition ∧
      #P.parts ≤ step^[i] #P₀.parts ∧ #Q.parts ≤ step #P.parts ∧
      ∑ AB ∈ S.irregularPairs (η #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
        η #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      (S.energy Q - S.energy P ≤ g ∨ g * (i + 1 : ℝ) < S.energy Q) := by
    induction i with
    | zero =>
      obtain ⟨Q, hQP, hQ, hQcard, hQreg⟩ := hround P₀ hP₀
      refine ⟨P₀, Q, hQP, le_rfl, hP₀, hQ, le_rfl, hQcard, hQreg, (le_or_gt _ g).imp id fun h ↦ ?_⟩
      push_cast
      linarith [S.energy_nonneg P₀]
    | succ i ih =>
      obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard, hQreg, hgap⟩ := ih
      by_cases hclose : S.energy Q - S.energy P ≤ g
      · have hgrow : step^[i] #P₀.parts ≤ step^[i + 1] #P₀.parts := by
          rw [iterate_succ_apply' step i]
          exact le_strongPairColorRegularityStep hη _
        exact ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard.trans hgrow, hQcard, hQreg, Or.inl hclose⟩
      · obtain ⟨R, hRQ, hR, hRcard, hRreg⟩ := hround Q hQ
        have hQgrow : #Q.parts ≤ step^[i + 1] #P₀.parts := by
          rw [iterate_succ_apply' step i]
          exact hQcard.trans (strongPairColorRegularityStep_mono η hPcard)
        refine ⟨Q, R, hRQ, hQP.trans hPP₀, hQ, hR, hQgrow, hRcard, hRreg,
          (le_or_gt _ g).imp id fun h ↦ ?_⟩
        have hprev := hgap.resolve_left hclose
        push_cast
        linarith
  obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard, hQreg, hgap⟩ := hiter ⌊1 / g⌋₊
  refine ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard, hgap.resolve_right fun h ↦ ?_, hQreg⟩
  have h1 : 1 < g * (⌊1 / g⌋₊ + 1 : ℝ) := by
    have hlt : 1 / g < (⌊1 / g⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rwa [div_lt_iff₀ hg, mul_comm] at hlt
  linarith [S.energy_le_one Q]

end StrongEquipartition

end PairColorSystem

end TauCeti
