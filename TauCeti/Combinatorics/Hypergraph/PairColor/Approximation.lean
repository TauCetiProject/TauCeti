/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Option
public import TauCeti.Combinatorics.Hypergraph.PairColor.Diagonal
public import TauCeti.Combinatorics.Hypergraph.PairColor.Energy
public import TauCeti.Combinatorics.Hypergraph.PairColor.Recoloring
public import TauCeti.Combinatorics.Hypergraph.PairColor.StrongRegularization
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.GCongr
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import TauCeti.Data.Finset.Basic
import TauCeti.Order.Partition.Finpartition

/-!
# Strong regular approximation of pair-color systems

Given a pair-color system `S` with a finite palette `κ`, an equitable vertex partition `P₀`, an
edit tolerance `α > 0`, and a positive error schedule `G : ℕ → ℝ`, this file first constructs an
exact equitable refinement `P ≤ P₀` of bounded size together with a recolored pair-color system
`T` over the same palette `κ` preserving `S.rev` and all within-cell colors such that every pair
of distinct cells of `P` is `G #P.parts`-regular and `T` disagrees with `S` on at most `α |V|²`
ordered distinct pairs (`PairColorSystem.exists_refining_equipartition_regular_offDiag`).
Pre-refining `P₀` to make the diagonal blocks small and applying `PairColorSystem.fillDiagonal`
then yields a pair-color system over `Option κ` whose lower skeleton `⟨P, T⟩` is `F`-regular at
its own lower complexity (`PairColorSystem.exists_refining_equipartition_lowerSkeletonRegular`),
along with unseeded versions with a prescribed minimum part count `l`
(`PairColorSystem.exists_equipartition_regular_offDiag`,
`PairColorSystem.exists_equipartition_lowerSkeletonRegular`).

Unlike single-scale cleanup (`PairColorSystem.exists_recoloring_isPairColorRegular`), which takes
a constant tolerance `ε` and cannot refine `P` without shrinking `F (#P.parts + card κ + 1)`,
schedule-governed regular approximation uses two-scale strong regularity
(`PairColorSystem.exists_strong_refining_equipartitions`) to obtain nested equipartitions
`Q ≤ P ≤ P₀` with bounded energy gap `S.energy Q - S.energy P` and `Q` regular at a fine
tolerance governed by `G #P.parts`. By `PairColorSystem.sum_abs_pairColorDensity_sub_le`, the
fine block densities of `S` are close in `L¹` to the coarse block densities on `P`. On each
canonical off-diagonal fine block `A' ×ˢ B'`,
`PairColorSystem.exists_coupled_recoloring_abs_card_filter_sub_le` adjusts regular fine blocks
toward `pairColorDensity S · A B` while editing few pairs and replaces irregular fine blocks by
quasi-random colorings. Summing rectangle discrepancies across the fine subblocks via
`PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines` and
`PairColorSystem.isRegularPair_of_abs_card_filter_colorOfPair_sub_le` makes every off-diagonal
coarse pair regular, and `PairColorSystem.fillDiagonal` cleans up within-cell pairs.

## Main definitions

* `TauCeti.pairOffDiagTolerance`: fine regularity tolerance for off-diagonal strong approximation.
* `TauCeti.pairOffDiagPartsBound`: part-count bound for off-diagonal strong approximation.
* `TauCeti.pairOffDiagBound`: host-size threshold for off-diagonal strong approximation.
* `TauCeti.pairApproximationTolerance`: fine regularity tolerance for lower-skeleton approximation.
* `TauCeti.pairApproximationPartsBound`: part-count bound for lower-skeleton approximation.
* `TauCeti.pairApproximationBound`: host-size threshold for lower-skeleton approximation.

## Main results

* `TauCeti.PairColorSystem.exists_refining_equipartition_regular_offDiag`: seeded off-diagonal
  strong regular approximation preserving the palette `κ` and within-cell colors.
* `TauCeti.PairColorSystem.exists_equipartition_regular_offDiag`: unseeded off-diagonal strong
  regular approximation with at least `l` parts.
* `TauCeti.PairColorSystem.exists_refining_equipartition_lowerSkeletonRegular`: seeded strong
  regular approximation of a pair-color system over `Option κ`.
* `TauCeti.PairColorSystem.exists_equipartition_lowerSkeletonRegular`: unseeded strong regular
  approximation of a pair-color system over `Option κ` with at least `l` parts.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2 / Theorem 2.5.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000).
-/

public section

open Finset Finpartition Real

namespace TauCeti

/-! ### Quantitative bounds -/

/-- The fine pair-regularity tolerance requested over a coarse partition with `t` cells in
off-diagonal strong pair-color approximation, for a palette of `q` colors, edit budget `α`, and
off-diagonal schedule `G`. -/
noncomputable def pairOffDiagTolerance (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (t : ℕ) : ℝ :=
  min (α / (4 * ((max q 1 : ℕ) + 1))) ((min (1 / 2) (G t)) ^ 3 / (4 * (max q 1 : ℕ)))

/-- Unfolding lemma for `TauCeti.pairOffDiagTolerance`. -/
theorem pairOffDiagTolerance_def (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (t : ℕ) :
    pairOffDiagTolerance q α G t =
      min (α / (4 * ((max q 1 : ℕ) + 1))) ((min (1 / 2) (G t)) ^ 3 / (4 * (max q 1 : ℕ))) :=
  (rfl)

/-- For positive `α` and a positive schedule `G`, `pairOffDiagTolerance` is positive. -/
theorem pairOffDiagTolerance_pos (q : ℕ) {α : ℝ} (hα : 0 < α) {G : ℕ → ℝ}
    (hG : ∀ n, 0 < G n) (t : ℕ) :
    0 < pairOffDiagTolerance q α G t := by
  rw [pairOffDiagTolerance_def]
  have hδ : 0 < min (1 / 2) (G t) := lt_min (by norm_num) (hG _)
  exact lt_min (by positivity) (by positivity)

/-- `pairOffDiagTolerance` never exceeds `1 / 32`. -/
theorem pairOffDiagTolerance_le_one_div_32 (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (t : ℕ) :
    pairOffDiagTolerance q α G t ≤ 1 / 32 := by
  have hq : (1 : ℝ) ≤ (max q 1 : ℕ) := by exact_mod_cast le_max_right q 1
  have hcube : (min (1 / 2) (G t)) ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
    (by decide : Odd 3).strictMono_pow.monotone (min_le_left _ _)
  calc pairOffDiagTolerance q α G t
      ≤ (min (1 / 2) (G t)) ^ 3 / (4 * (max q 1 : ℕ)) := min_le_right _ _
    _ ≤ (1 / 2 : ℝ) ^ 3 / (4 * 1) :=
        div_le_div₀ (by norm_num) hcube (by norm_num) (by linarith)
    _ = 1 / 32 := by norm_num

/-- Upper bound on the number of cells of the coarse equipartition in off-diagonal strong
pair-color approximation, starting from an equipartition with `l₀` cells. -/
noncomputable def pairOffDiagPartsBound (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  strongPairColorRegularityBound ((α / (4 * (max q 1 : ℕ))) ^ 2)
    (pairOffDiagTolerance q α G) l₀

/-- Unfolding lemma for `TauCeti.pairOffDiagPartsBound`. -/
theorem pairOffDiagPartsBound_def (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) :
    pairOffDiagPartsBound q α G l₀ =
      strongPairColorRegularityBound ((α / (4 * (max q 1 : ℕ))) ^ 2)
        (pairOffDiagTolerance q α G) l₀ :=
  (rfl)

/-- `pairOffDiagPartsBound` is monotone in the starting cell count `l₀`. -/
theorem pairOffDiagPartsBound_mono (q : ℕ) (α : ℝ) (G : ℕ → ℝ) :
    Monotone (pairOffDiagPartsBound q α G) :=
  strongPairColorRegularityBound_mono _ _

/-- For positive parameters, `pairOffDiagPartsBound` is at least `l₀`. -/
theorem le_pairOffDiagPartsBound (q : ℕ) {α : ℝ} (hα : 0 < α) {G : ℕ → ℝ}
    (hG : ∀ n, 0 < G n) (l₀ : ℕ) :
    l₀ ≤ pairOffDiagPartsBound q α G l₀ :=
  le_strongPairColorRegularityBound _ (pairOffDiagTolerance_pos q hα hG) _

/-- Minimum host size `|V|` above which off-diagonal strong pair-color approximation succeeds:
each cell of the fine equipartition contains enough vertices for the union bound over
subrectangles to beat one. -/
noncomputable def pairOffDiagBound (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  let M := pairOffDiagPartsBound q α G l₀
  max 1 (strongPairColorStepBound (pairOffDiagTolerance q α G) M) *
    ((range (M + 1)).sup
      (fun t ↦ ⌈(q + 3 : ℝ) / (pairOffDiagTolerance q α G t) ^ 2⌉₊) + 1)

/-- Unfolding lemma for `TauCeti.pairOffDiagBound`. -/
theorem pairOffDiagBound_def (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) :
    pairOffDiagBound q α G l₀ =
      max 1 (strongPairColorStepBound (pairOffDiagTolerance q α G)
          (pairOffDiagPartsBound q α G l₀)) *
        ((range (pairOffDiagPartsBound q α G l₀ + 1)).sup
          (fun t ↦ ⌈(q + 3 : ℝ) / (pairOffDiagTolerance q α G t) ^ 2⌉₊) + 1) :=
  (rfl)

/-- `pairOffDiagBound` is always positive. -/
theorem pairOffDiagBound_pos (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) :
    0 < pairOffDiagBound q α G l₀ :=
  Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (Nat.succ_pos _)

/-- `pairOffDiagBound` is monotone in `l₀`. -/
theorem pairOffDiagBound_mono (q : ℕ) (α : ℝ) (G : ℕ → ℝ) :
    Monotone (pairOffDiagBound q α G) := fun _ _ h ↦ by
  have hM := pairOffDiagPartsBound_mono q α G h
  refine Nat.mul_le_mul (max_le_max le_rfl (strongPairColorStepBound_mono _ hM))
    (Nat.succ_le_succ (sup_mono (range_mono (Nat.succ_le_succ hM))))

/-- For positive parameters, `pairOffDiagBound` bounds `pairOffDiagPartsBound`. -/
theorem pairOffDiagPartsBound_le_pairOffDiagBound (q : ℕ) {α : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ} (hG : ∀ n, 0 < G n) (l₀ : ℕ) :
    pairOffDiagPartsBound q α G l₀ ≤ pairOffDiagBound q α G l₀ :=
  calc pairOffDiagPartsBound q α G l₀
      ≤ strongPairColorStepBound (pairOffDiagTolerance q α G)
          (pairOffDiagPartsBound q α G l₀) :=
        le_strongPairColorStepBound (pairOffDiagTolerance_pos q hα hG) _
    _ ≤ max 1 (strongPairColorStepBound (pairOffDiagTolerance q α G)
          (pairOffDiagPartsBound q α G l₀)) :=
        le_max_right _ _
    _ ≤ pairOffDiagBound q α G l₀ :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- The fine pair-regularity tolerance requested over a coarse partition with `t` cells, for a
palette of `q` colors, edit budget `α`, and schedule `F`. The `t + q + 1` argument accounts for
the fresh diagonal color added by `PairColorSystem.fillDiagonal`. -/
noncomputable def pairApproximationTolerance (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (t : ℕ) : ℝ :=
  pairOffDiagTolerance q α (fun t ↦ F (t + q + 1)) t

/-- Unfolding lemma for `TauCeti.pairApproximationTolerance`. -/
theorem pairApproximationTolerance_def (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (t : ℕ) :
    pairApproximationTolerance q α F t =
      pairOffDiagTolerance q α (fun t ↦ F (t + q + 1)) t :=
  (rfl)

/-- For positive `α` and a positive schedule `F`, `pairApproximationTolerance` is positive. -/
theorem pairApproximationTolerance_pos (q : ℕ) {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (t : ℕ) :
    0 < pairApproximationTolerance q α F t :=
  pairOffDiagTolerance_pos q hα (fun _ ↦ hF _) t

/-- `pairApproximationTolerance` never exceeds `1 / 32`. -/
theorem pairApproximationTolerance_le_one_div_32 (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (t : ℕ) :
    pairApproximationTolerance q α F t ≤ 1 / 32 :=
  pairOffDiagTolerance_le_one_div_32 q α (fun t ↦ F (t + q + 1)) t

/-- Upper bound on the number of cells of the coarse equipartition in strong pair-color
approximation, starting from an equipartition with `l₀` cells. -/
noncomputable def pairApproximationPartsBound (q : ℕ) (α : ℝ) (F : ℕ → ℝ)
    (l₀ : ℕ) : ℕ :=
  pairOffDiagPartsBound q α (fun t ↦ F (t + q + 1)) (max 1 ⌈4 / α⌉₊ * l₀)

/-- Unfolding lemma for `TauCeti.pairApproximationPartsBound`. -/
theorem pairApproximationPartsBound_def (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    pairApproximationPartsBound q α F l₀ =
      pairOffDiagPartsBound q α (fun t ↦ F (t + q + 1)) (max 1 ⌈4 / α⌉₊ * l₀) :=
  (rfl)

/-- `pairApproximationPartsBound` is monotone in the starting cell count `l₀`. -/
theorem pairApproximationPartsBound_mono (q : ℕ) (α : ℝ) (F : ℕ → ℝ) :
    Monotone (pairApproximationPartsBound q α F) := fun _ _ h ↦
  pairOffDiagPartsBound_mono q α (fun t ↦ F (t + q + 1)) (Nat.mul_le_mul_left _ h)

/-- For positive parameters, `pairApproximationPartsBound` is at least
`max 1 ⌈4 / α⌉₊ * l₀`. -/
theorem mul_le_pairApproximationPartsBound (q : ℕ) {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (l₀ : ℕ) :
    max 1 ⌈4 / α⌉₊ * l₀ ≤ pairApproximationPartsBound q α F l₀ :=
  le_pairOffDiagPartsBound q hα (fun _ ↦ hF _) _

/-- For positive parameters, `pairApproximationPartsBound` is at least `l₀`. -/
theorem le_pairApproximationPartsBound (q : ℕ) {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (l₀ : ℕ) :
    l₀ ≤ pairApproximationPartsBound q α F l₀ :=
  (Nat.le_mul_of_pos_left l₀ (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))).trans
    (mul_le_pairApproximationPartsBound q hα hF l₀)

/-- Minimum host size `|V|` above which strong pair-color approximation succeeds: each cell of
the fine equipartition contains enough vertices for the union bound over subrectangles to beat
one. -/
noncomputable def pairApproximationBound (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  pairOffDiagBound q α (fun t ↦ F (t + q + 1)) (max 1 ⌈4 / α⌉₊ * l₀)

/-- Unfolding lemma for `TauCeti.pairApproximationBound`. -/
theorem pairApproximationBound_def (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    pairApproximationBound q α F l₀ =
      pairOffDiagBound q α (fun t ↦ F (t + q + 1)) (max 1 ⌈4 / α⌉₊ * l₀) :=
  (rfl)

/-- `pairApproximationBound` is always positive. -/
theorem pairApproximationBound_pos (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    0 < pairApproximationBound q α F l₀ :=
  pairOffDiagBound_pos q α _ _

/-- `pairApproximationBound` is monotone in `l₀`. -/
theorem pairApproximationBound_mono (q : ℕ) (α : ℝ) (F : ℕ → ℝ) :
    Monotone (pairApproximationBound q α F) := fun _ _ h ↦
  pairOffDiagBound_mono q α (fun t ↦ F (t + q + 1)) (Nat.mul_le_mul_left _ h)

/-- For positive parameters, `pairApproximationBound` bounds `pairApproximationPartsBound`. -/
theorem pairApproximationPartsBound_le_pairApproximationBound (q : ℕ) {α : ℝ} (hα : 0 < α)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (l₀ : ℕ) :
    pairApproximationPartsBound q α F l₀ ≤ pairApproximationBound q α F l₀ :=
  pairOffDiagPartsBound_le_pairOffDiagBound q hα (fun _ ↦ hF _) _

namespace PairColorSystem

/-! ### Assembling coarse regularity and bounding edits -/

section Assembly

/-- Fine cell pairs `(A', B')` in `Q.parts ×ˢ Q.parts` whose `P`-parents are strictly ordered
under `eP`. -/
private noncomputable def canonicalFineBlocks {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    (eP : P.parts ≃ Fin (Fintype.card P.parts)) : Finset (Finset V × Finset V) :=
  let parentIdx (C : Finset V) : ℕ :=
    if hC : C ∈ Q.parts then (eP (refinementParent hQP ⟨C, hC⟩)).val else 0
  (Q.parts ×ˢ Q.parts).filter fun uv ↦ parentIdx uv.1 < parentIdx uv.2

private theorem mem_canonicalFineBlocks_elim {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} {hQP : Q ≤ P}
    {eP : P.parts ≃ Fin (Fintype.card P.parts)} {uv : Finset V × Finset V}
    (huv : uv ∈ canonicalFineBlocks hQP eP) :
    uv.1 ∈ Q.parts ∧ uv.2 ∈ Q.parts ∧
      eP (refinementParent hQP ⟨uv.1, (mem_product.1 (mem_filter.1 huv).1).1⟩) <
        eP (refinementParent hQP ⟨uv.2, (mem_product.1 (mem_filter.1 huv).1).2⟩) := by
  obtain ⟨hprod, hlt⟩ := mem_filter.1 huv
  obtain ⟨h1, h2⟩ := mem_product.1 hprod
  exact ⟨h1, h2, by simpa only [h1, h2, ↓reduceDIte, Fin.lt_def] using hlt⟩

/-- Distinct canonical fine blocks have disjoint Cartesian products. -/
private theorem pairwiseDisjoint_canonicalFineBlocks {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    (eP : P.parts ≃ Fin (Fintype.card P.parts)) :
    ((canonicalFineBlocks hQP eP : Finset _) : Set _).PairwiseDisjoint
      (fun uv : Finset V × Finset V ↦ uv.1 ×ˢ uv.2) := by
  intro u hu v hv huv
  obtain ⟨h1u, h2u, -⟩ := mem_canonicalFineBlocks_elim hu
  obtain ⟨h1v, h2v, -⟩ := mem_canonicalFineBlocks_elim hv
  refine disjoint_product.2 ?_
  by_cases h1 : u.1 = v.1
  · exact Or.inr (Q.disjoint h2u h2v fun h2 ↦ huv (Prod.ext h1 h2))
  · exact Or.inl (Q.disjoint h1u h1v h1)

/-- Every vertex pair in a canonical fine block lies in `(univ : Finset V).offDiag`. -/
private theorem biUnion_canonicalFineBlocks_subset_offDiag {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    (eP : P.parts ≃ Fin (Fintype.card P.parts)) :
    (canonicalFineBlocks hQP eP).biUnion (fun uv ↦ uv.1 ×ˢ uv.2) ⊆ (univ : Finset V).offDiag := by
  intro x hx
  obtain ⟨uv, huv, hxuv⟩ := mem_biUnion.1 hx
  obtain ⟨h1, h2, hlt⟩ := mem_canonicalFineBlocks_elim huv
  obtain ⟨hx1, hx2⟩ := mem_product.1 hxuv
  have hpAB : (refinementParent hQP ⟨uv.1, h1⟩).1 ≠ (refinementParent hQP ⟨uv.2, h2⟩).1 :=
    fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
  exact mem_offDiag.2 ⟨mem_univ _, mem_univ _,
    (P.disjoint (refinementParent hQP ⟨uv.1, h1⟩).2
      (refinementParent hQP ⟨uv.2, h2⟩).2 hpAB).forall_ne_finset
      (le_refinementParent hQP ⟨uv.1, h1⟩ hx1) (le_refinementParent hQP ⟨uv.2, h2⟩ hx2)⟩

open Classical in
/-- Twice the pair mass of irregular canonical fine blocks is at most the `Q`-irregular pair
budget `η |V|²`. -/
private theorem sum_irregular_canonicalFineBlocks_le
    {κ V : Type*} [Fintype V] [DecidableEq V]
    (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (eP : P.parts ≃ Fin (Fintype.card P.parts)) {η : ℝ}
    (hQirreg : ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) ≤
      η * (Fintype.card V : ℝ) ^ 2) :
    ∑ uv ∈ (canonicalFineBlocks hQP eP).filter (fun uv ↦ ¬ S.IsRegularPair η uv.1 uv.2),
      2 * (#uv.1 * #uv.2 : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set FB_irr := (canonicalFineBlocks hQP eP).filter fun uv ↦ ¬ S.IsRegularPair η uv.1 uv.2
  have hdisj_irr : Disjoint FB_irr (FB_irr.image Prod.swap) := by
    rw [disjoint_left]
    intro uv huv hswap
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hswap
    exact lt_asymm (mem_filter.1 (mem_filter.1 huv).1).2 (mem_filter.1 (mem_filter.1 hw).1).2
  have hsub_irr : FB_irr ∪ FB_irr.image Prod.swap ⊆ S.irregularPairs η Q := by
    intro uv huv
    rcases mem_union.1 huv with huv | huv
    · obtain ⟨hFB, hirr⟩ := mem_filter.1 huv
      obtain ⟨h1, h2, hlt⟩ := mem_canonicalFineBlocks_elim hFB
      exact S.mem_irregularPairs.2 ⟨h1, h2,
        fun heq ↦ (ne_of_lt hlt) (by congr 2; exact Subtype.ext heq), hirr⟩
    · obtain ⟨w, hw, rfl⟩ := mem_image.1 huv
      obtain ⟨hFB, hirr⟩ := mem_filter.1 hw
      obtain ⟨h1, h2, hlt⟩ := mem_canonicalFineBlocks_elim hFB
      exact S.mem_irregularPairs.2 ⟨h2, h1,
        fun heq ↦ (ne_of_lt hlt) (by congr 2; exact Subtype.ext heq.symm),
        fun hr ↦ hirr hr.symm⟩
  calc ∑ uv ∈ FB_irr, 2 * (#uv.1 * #uv.2 : ℝ)
      = ∑ uv ∈ FB_irr ∪ FB_irr.image Prod.swap, (#uv.1 * #uv.2 : ℝ) := by
        rw [sum_union hdisj_irr, sum_image (fun _ _ _ _ h ↦ Prod.swap_injective h),
          ← sum_add_distrib]
        exact sum_congr rfl fun _ _ ↦ by simp; ring
    _ ≤ ∑ uv ∈ S.irregularPairs η Q, (#uv.1 * #uv.2 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub_irr fun _ _ _ ↦ by positivity
    _ ≤ η * (Fintype.card V : ℝ) ^ 2 := hQirreg

open Classical in
/-- The `L¹` density discrepancy between `Q` and `P` summed over any subset of canonical fine
blocks is bounded by `(α / 4) |V|²` when `S.energy Q - S.energy P` is small. -/
private theorem sum_L1_canonicalFineBlocks_le
    {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (eP : P.parts ≃ Fin (Fintype.card P.parts))
    {FB' : Finset (Finset V × Finset V)} (hFB' : FB' ⊆ canonicalFineBlocks hQP eP)
    {α : ℝ} (hα : 0 < α)
    (hgap : S.energy Q - S.energy P ≤ (α / (4 * (max (Fintype.card κ) 1 : ℕ))) ^ 2) :
    ∑ uv ∈ FB', ∑ x ∈ uv.1 ×ˢ uv.2, ∑ c : κ,
        |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
          pairColorDensity S c (P.part x.1) (P.part x.2)| ≤
      α / 4 * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set q := Fintype.card κ
  set q' : ℕ := max q 1
  set g₂ := (α / (4 * (q' : ℝ))) ^ 2
  have hg₂_sqrt : √g₂ = α / (4 * (q' : ℝ)) := sqrt_sq (by positivity)
  have hFB_disj := (pairwiseDisjoint_canonicalFineBlocks hQP eP).subset hFB'
  have hFB_off : FB'.biUnion (fun uv ↦ uv.1 ×ˢ uv.2) ⊆ (univ : Finset V).offDiag :=
    (biUnion_subset_biUnion_of_subset_left _ hFB').trans
      (biUnion_canonicalFineBlocks_subset_offDiag hQP eP)
  have hoff_le : (#(univ : Finset V).offDiag : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have : #(univ : Finset V).offDiag ≤ Fintype.card V * Fintype.card V := by simp
    exact_mod_cast this.trans_eq (sq _).symm
  calc ∑ uv ∈ FB', ∑ x ∈ uv.1 ×ˢ uv.2, ∑ c : κ,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)|
      = ∑ x ∈ FB'.biUnion (fun uv ↦ uv.1 ×ˢ uv.2), ∑ c : κ,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)| := (sum_biUnion hFB_disj).symm
    _ ≤ ∑ x ∈ (univ : Finset V).offDiag, ∑ c : κ,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)| :=
        sum_le_sum_of_subset_of_nonneg hFB_off fun _ _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _
    _ = ∑ c : κ, ∑ x ∈ (univ : Finset V).offDiag,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)| := sum_comm
    _ ≤ ∑ _c : κ, √g₂ * #(univ : Finset V).offDiag :=
        sum_le_sum fun c _ ↦ S.sum_abs_pairColorDensity_sub_le hQP hgap c
    _ = q * (α / (4 * (q' : ℝ))) * #(univ : Finset V).offDiag := by
        rw [sum_const, card_univ, nsmul_eq_mul, hg₂_sqrt, mul_assoc]
    _ ≤ α / 4 * (Fintype.card V : ℝ) ^ 2 := by
        have hqq' : (q : ℝ) * (α / (4 * (q' : ℝ))) ≤ α / 4 := by
          have hle : (q : ℝ) ≤ q' := by exact_mod_cast le_max_left q 1
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith [mul_le_mul_of_nonneg_left hle hα.le]
        exact mul_le_mul hqq' hoff_le (Nat.cast_nonneg _) (by positivity)

open Classical in
/-- Twice the edits of `T_off` across `η`-regular canonical fine blocks is bounded by the `L¹`
energy-gap term `(α / 4) |V|²` plus the coupling slack `2 |κ| η |V|²`. -/
private theorem sum_regular_canonicalFineBlocks_le
    {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    (S T_off : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (eP : P.parts ≃ Fin (Fintype.card P.parts))
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (hgap : S.energy Q - S.energy P ≤ (α / (4 * (max (Fintype.card κ) 1 : ℕ))) ^ 2)
    (hreg_edit : ∀ A' B' : Q.parts,
      eP (refinementParent hQP A') < eP (refinementParent hQP B') →
      S.IsRegularPair η A'.1 B'.1 →
        (#{x ∈ A'.1 ×ˢ B'.1 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
          (∑ c : κ, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1| *
            (#A'.1 * #B'.1)) / 2 + Fintype.card κ * η * (#A'.1 * #B'.1)) :
    ∑ uv ∈ (canonicalFineBlocks hQP eP).filter (fun uv ↦ S.IsRegularPair η uv.1 uv.2),
      2 * (#{x ∈ uv.1 ×ˢ uv.2 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
      (α / 4 + 2 * Fintype.card κ * η) * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set q := Fintype.card κ
  set FB_reg := (canonicalFineBlocks hQP eP).filter fun uv ↦ S.IsRegularPair η uv.1 uv.2
  have hFB_sub : FB_reg ⊆ canonicalFineBlocks hQP eP := filter_subset _ _
  have hlocal (uv : Finset V × Finset V) (huv : uv ∈ FB_reg) :
      2 * (#{x ∈ uv.1 ×ˢ uv.2 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
        (∑ x ∈ uv.1 ×ˢ uv.2, ∑ c : κ,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)|) +
          2 * q * η * (#uv.1 * #uv.2 : ℝ) := by
    obtain ⟨hFB, hreg⟩ := mem_filter.1 huv
    obtain ⟨h1, h2, hlt⟩ := mem_canonicalFineBlocks_elim hFB
    set pA := refinementParent hQP ⟨uv.1, h1⟩
    set pB := refinementParent hQP ⟨uv.2, h2⟩
    have hspec := hreg_edit ⟨uv.1, h1⟩ ⟨uv.2, h2⟩ hlt hreg
    have hconst : ∑ c : κ, |(pairColorDensity S c uv.1 uv.2 : ℝ) -
          pairColorDensity S c pA.1 pB.1| * (#uv.1 * #uv.2) =
        ∑ x ∈ uv.1 ×ˢ uv.2, ∑ c : κ,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)| := by
      rw [sum_comm]
      refine sum_congr rfl fun c _ ↦ ?_
      have hpt : ∀ x ∈ uv.1 ×ˢ uv.2,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)| =
          |(pairColorDensity S c uv.1 uv.2 : ℝ) - pairColorDensity S c pA.1 pB.1| :=
        fun x hx ↦ by
          obtain ⟨hx1, hx2⟩ := mem_product.1 hx
          rw [Q.part_eq_of_mem h1 hx1, Q.part_eq_of_mem h2 hx2,
            part_eq_refinementParent hQP ⟨uv.1, h1⟩ hx1,
            part_eq_refinementParent hQP ⟨uv.2, h2⟩ hx2]
      rw [sum_congr rfl hpt, sum_const, card_product, nsmul_eq_mul]
      push_cast; ring
    linarith
  have hFB_disj := (pairwiseDisjoint_canonicalFineBlocks hQP eP).subset hFB_sub
  have hmass_FB : ∑ uv ∈ FB_reg, (#uv.1 * #uv.2 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have hle : ∑ uv ∈ FB_reg, (#uv.1 * #uv.2) ≤ Fintype.card V * Fintype.card V := by
      have hc1 : #(FB_reg.biUnion fun uv ↦ uv.1 ×ˢ uv.2) = ∑ uv ∈ FB_reg, #uv.1 * #uv.2 := by
        rw [card_biUnion hFB_disj]; exact sum_congr rfl fun _ _ ↦ card_product _ _
      simpa [hc1, Fintype.card_prod] using card_le_univ (FB_reg.biUnion fun uv ↦ uv.1 ×ˢ uv.2)
    rw [sq]; exact_mod_cast hle
  calc ∑ uv ∈ FB_reg, 2 * (#{x ∈ uv.1 ×ˢ uv.2 |
          T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ)
      ≤ (∑ uv ∈ FB_reg, ∑ x ∈ uv.1 ×ˢ uv.2, ∑ c : κ,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)|) +
        ∑ uv ∈ FB_reg, 2 * q * η * (#uv.1 * #uv.2 : ℝ) := by
        rw [← sum_add_distrib]; exact sum_le_sum hlocal
    _ ≤ α / 4 * (Fintype.card V : ℝ) ^ 2 + 2 * q * η * (Fintype.card V : ℝ) ^ 2 := by
        rw [← mul_sum]
        exact add_le_add (sum_L1_canonicalFineBlocks_le S hQP eP hFB_sub hα hgap)
          (mul_le_mul_of_nonneg_left hmass_FB (by positivity))
    _ = (α / 4 + 2 * q * η) * (Fintype.card V : ℝ) ^ 2 := by ring

open Classical in
/-- Orientation reduction: if `T_off` preserves `S.rev` and within-cell colors of `P`, then the
total number of edited ordered distinct pairs is at most twice the number edited on pairs
strictly ordered under `eP`. -/
private theorem card_edit_le_two_mul_pos {κ V : Type*} [Fintype V] [DecidableEq V]
    (S T_off : PairColorSystem κ V) {P : Finpartition (univ : Finset V)}
    (eP : P.parts ≃ Fin (Fintype.card P.parts)) (hrev : T_off.rev = S.rev)
    (hdiag : ∀ u v, P.part u = P.part v → T_off.colorOfPair u v = S.colorOfPair u v) :
    #{p : {p : V × V // p.1 ≠ p.2} | T_off.color p ≠ S.color p} ≤
      2 * #{x ∈ (univ : Finset V).offDiag |
        eP ⟨P.part x.1, P.part_mem.2 (mem_univ x.1)⟩ <
          eP ⟨P.part x.2, P.part_mem.2 (mem_univ x.2)⟩ ∧
        T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} := by
  classical
  set E_all : Finset {p : V × V // p.1 ≠ p.2} := {p | T_off.color p ≠ S.color p}
  set E_pos : Finset (V × V) :=
    {x ∈ (univ : Finset V).offDiag |
      eP ⟨P.part x.1, P.part_mem.2 (mem_univ x.1)⟩ <
        eP ⟨P.part x.2, P.part_mem.2 (mem_univ x.2)⟩ ∧
      T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2}
  have hswap_ne {x : V × V}
      (hne : T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2) :
      T_off.colorOfPair x.2 x.1 ≠ S.colorOfPair x.2 x.1 := fun heq ↦
    hne <| by rw [T_off.colorOfPair_swap x.2 x.1, hrev, heq, ← S.colorOfPair_swap x.2 x.1]
  have hsub : E_all.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ E_pos ∪ E_pos.image Prod.swap := by
    intro x hx
    obtain ⟨⟨y, hy⟩, hmem, rfl⟩ := mem_map.1 hx
    have hoff_ne : T_off.colorOfPair y.1 y.2 ≠ S.colorOfPair y.1 y.2 := by
      simpa only [colorOfPair_of_ne _ hy, ne_eq, Option.some.injEq] using (mem_filter.1 hmem).2
    have hsame : P.part y.1 ≠ P.part y.2 := fun h ↦ hoff_ne (hdiag y.1 y.2 h)
    have hne_eP : eP ⟨P.part y.1, P.part_mem.2 (mem_univ y.1)⟩ ≠
        eP ⟨P.part y.2, P.part_mem.2 (mem_univ y.2)⟩ := fun h ↦
      hsame (Subtype.ext_iff.1 (eP.injective h))
    rcases lt_or_gt_of_ne hne_eP with hlt | hgt
    · exact mem_union_left _ (mem_filter.2 ⟨mem_offDiag.2 ⟨mem_univ _, mem_univ _, hy⟩, hlt,
        hoff_ne⟩)
    · exact mem_union_right _ (mem_image.2 ⟨y.swap,
        mem_filter.2 ⟨mem_offDiag.2 ⟨mem_univ _, mem_univ _, hy.symm⟩, hgt, hswap_ne hoff_ne⟩,
        Prod.swap_swap y⟩)
  calc #E_all = #(E_all.map ⟨Subtype.val, Subtype.val_injective⟩) := (card_map _).symm
    _ ≤ #(E_pos ∪ E_pos.image Prod.swap) := card_le_card hsub
    _ ≤ #E_pos + #(E_pos.image Prod.swap) := card_union_le _ _
    _ ≤ #E_pos + #E_pos := Nat.add_le_add_left card_image_le _
    _ = 2 * #E_pos := (two_mul _).symm

open Classical in
/-- Bound the edited ordered distinct pairs of an off-diagonal recoloring `T_off` by
`(3 / 4) * α |V|²` using the `L¹` energy-gap, regular-coupling, and irregular-pair budgets. -/
private theorem card_edit_offDiag_le
    {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    (S T_off : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (eP : P.parts ≃ Fin (Fintype.card P.parts))
    (hrev : T_off.rev = S.rev)
    (hdiag : ∀ u v, P.part u = P.part v → T_off.colorOfPair u v = S.colorOfPair u v)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (hQirreg : ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) ≤
      η * (Fintype.card V : ℝ) ^ 2)
    (hgap : S.energy Q - S.energy P ≤ (α / (4 * (max (Fintype.card κ) 1 : ℕ))) ^ 2)
    (hη_α : (2 * (Fintype.card κ : ℝ) + 1) * η ≤ α / 2)
    (hreg_edit : ∀ A' B' : Q.parts,
      eP (refinementParent hQP A') < eP (refinementParent hQP B') →
      S.IsRegularPair η A'.1 B'.1 →
        (#{x ∈ A'.1 ×ˢ B'.1 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
          (∑ c : κ, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1| *
            (#A'.1 * #B'.1)) / 2 + Fintype.card κ * η * (#A'.1 * #B'.1)) :
    (#{p : {p : V × V // p.1 ≠ p.2} | T_off.color p ≠ S.color p} : ℝ) ≤
      3 / 4 * α * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set E_pos : Finset (V × V) :=
    {x ∈ (univ : Finset V).offDiag |
      eP ⟨P.part x.1, P.part_mem.2 (mem_univ x.1)⟩ <
        eP ⟨P.part x.2, P.part_mem.2 (mem_univ x.2)⟩ ∧
      T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2}
  set FB := canonicalFineBlocks hQP eP
  have hE_pos_sub : E_pos ⊆ FB.biUnion (fun uv ↦
      {x ∈ uv.1 ×ˢ uv.2 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2}) := by
    intro x hx
    obtain ⟨_, hlt, hne⟩ := mem_filter.1 hx
    have hQ1 : Q.part x.1 ∈ Q.parts := Q.part_mem.2 (mem_univ x.1)
    have hQ2 : Q.part x.2 ∈ Q.parts := Q.part_mem.2 (mem_univ x.2)
    have hp1 : refinementParent hQP ⟨Q.part x.1, hQ1⟩ =
        ⟨P.part x.1, P.part_mem.2 (mem_univ x.1)⟩ :=
      Subtype.ext (part_eq_refinementParent hQP ⟨Q.part x.1, hQ1⟩
        (Q.mem_part_self.2 (mem_univ x.1))).symm
    have hp2 : refinementParent hQP ⟨Q.part x.2, hQ2⟩ =
        ⟨P.part x.2, P.part_mem.2 (mem_univ x.2)⟩ :=
      Subtype.ext (part_eq_refinementParent hQP ⟨Q.part x.2, hQ2⟩
        (Q.mem_part_self.2 (mem_univ x.2))).symm
    refine mem_biUnion.2 ⟨(Q.part x.1, Q.part x.2),
      mem_filter.2 ⟨mem_product.2 ⟨hQ1, hQ2⟩, ?_⟩,
      mem_filter.2 ⟨mem_product.2 ⟨Q.mem_part_self.2 (mem_univ x.1),
        Q.mem_part_self.2 (mem_univ x.2)⟩, hne⟩⟩
    simp only [hQ1, hQ2, ↓reduceDIte, hp1, hp2]; exact hlt
  have hE_pos_sum : (2 : ℝ) * #E_pos ≤
      ((α / 4 + 2 * Fintype.card κ * η) + η) * (Fintype.card V : ℝ) ^ 2 := by
    have hcard_le : (#E_pos : ℝ) ≤ ∑ uv ∈ FB, (#{x ∈ uv.1 ×ˢ uv.2 |
        T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) :=
      mod_cast (card_le_card hE_pos_sub).trans card_biUnion_le
    have hsplit_FB := (sum_filter_add_sum_filter_not FB
      (fun uv ↦ S.IsRegularPair η uv.1 uv.2)
      (fun uv ↦ (#{x ∈ uv.1 ×ˢ uv.2 |
        T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ))).symm
    have hirr_triv : ∑ uv ∈ FB.filter (fun uv ↦ ¬ S.IsRegularPair η uv.1 uv.2),
          (#{x ∈ uv.1 ×ˢ uv.2 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
        ∑ uv ∈ FB.filter (fun uv ↦ ¬ S.IsRegularPair η uv.1 uv.2), (#uv.1 * #uv.2 : ℝ) :=
      sum_le_sum fun _ _ ↦ mod_cast (card_filter_le _ _).trans_eq (card_product _ _)
    have hreg := sum_regular_canonicalFineBlocks_le S T_off hQP eP hα hη hgap hreg_edit
    have hirr := sum_irregular_canonicalFineBlocks_le S hQP eP hQirreg
    rw [← mul_sum] at hreg hirr
    linarith
  have hE_all_cast : (#{p : {p : V × V // p.1 ≠ p.2} | T_off.color p ≠ S.color p} : ℝ) ≤
      2 * (#E_pos : ℝ) := by
    exact_mod_cast card_edit_le_two_mul_pos S T_off eP hrev hdiag
  have hcoeff : (α / 4 + 2 * (Fintype.card κ : ℝ) * η) + η ≤ 3 / 4 * α := by linarith
  calc (#{p : {p : V × V // p.1 ≠ p.2} | T_off.color p ≠ S.color p} : ℝ)
      ≤ 2 * (#E_pos : ℝ) := hE_all_cast
    _ ≤ ((α / 4 + 2 * Fintype.card κ * η) + η) * (Fintype.card V : ℝ) ^ 2 := hE_pos_sum
    _ ≤ 3 / 4 * α * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

/-- Under the host-size threshold `pairOffDiagBound`, every cell of the fine equipartition `Q`
satisfies `q + 3 ≤ η ^ 2 * #A'`, where `η = pairOffDiagTolerance q α G #P.parts`. -/
private theorem card_add_three_le_sq_mul_card_fine_part {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (hQ : Q.IsEquipartition) {q l₀ : ℕ} {α : ℝ}
    {G : ℕ → ℝ} (hη : 0 < pairOffDiagTolerance q α G #P.parts) (hQpos : 0 < #Q.parts)
    (hPcard : #P.parts ≤ pairOffDiagPartsBound q α G l₀)
    (hQcard : #Q.parts ≤ strongPairColorStepBound (pairOffDiagTolerance q α G)
      (pairOffDiagPartsBound q α G l₀))
    (hV : pairOffDiagBound q α G l₀ ≤ Fintype.card V)
    {A' : Finset V} (hA' : A' ∈ Q.parts) :
    (q + 3 : ℝ) ≤ (pairOffDiagTolerance q α G #P.parts) ^ 2 * #A' := by
  set M_coarse := pairOffDiagPartsBound q α G l₀
  set M_fine := strongPairColorStepBound (pairOffDiagTolerance q α G) M_coarse
  set η := pairOffDiagTolerance q α G #P.parts
  set K := ⌈(q + 3 : ℝ) / η ^ 2⌉₊
  have hKsup : K ≤ (range (M_coarse + 1)).sup
      (fun t ↦ ⌈(q + 3 : ℝ) / (pairOffDiagTolerance q α G t) ^ 2⌉₊) :=
    le_sup (f := fun t ↦ ⌈(q + 3 : ℝ) / (pairOffDiagTolerance q α G t) ^ 2⌉₊)
      (mem_range.2 (Nat.lt_succ_of_le hPcard))
  have hQK : #Q.parts * K ≤ Fintype.card V :=
    calc #Q.parts * K ≤ max 1 M_fine * (K + 1) :=
          Nat.mul_le_mul (hQcard.trans (le_max_right 1 M_fine)) (Nat.le_succ K)
      _ ≤ pairOffDiagBound q α G l₀ := by
          rw [pairOffDiagBound_def]
          exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hKsup)
      _ ≤ Fintype.card V := hV
  have hKdiv : K ≤ #(univ : Finset V) / #Q.parts := by
    rw [card_univ, Nat.le_div_iff_mul_le hQpos, mul_comm]; exact hQK
  have hKA' : (K : ℝ) ≤ #A' := by exact_mod_cast hKdiv.trans (hQ.average_le_card_part hA')
  have hceil : (q + 3 : ℝ) / η ^ 2 ≤ K := Nat.le_ceil _
  rw [div_le_iff₀ (pow_pos hη 2)] at hceil
  linarith [mul_le_mul_of_nonneg_right hKA' (sq_nonneg η)]

open Classical in
/-- For each pair of fine parts `A', B'` of `Q`, choose a local recoloring `T` with
`T.rev = S.rev` which—whenever `A'` and `B'` have distinct `P`-parents—satisfies the coupled
rectangle-discrepancy and regular edit bounds toward the coarse pair-color density on
`(parent A', parent B')`. -/
private theorem exists_fine_block_recoloring {κ V : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) {η : ℝ} (hη : 0 < η)
    (hQsize : ∀ A' ∈ Q.parts, (Fintype.card κ + 3 : ℝ) ≤ η ^ 2 * #A')
    (A' B' : Q.parts) :
    ∃ T : PairColorSystem κ V, T.rev = S.rev ∧
      (refinementParent hQP A' ≠ refinementParent hQP B' →
        (∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1, ∀ d : κ,
          |(#{x ∈ s' ×ˢ t' | T.colorOfPair x.1 x.2 = some d} : ℝ) -
            (pairColorDensity S d (refinementParent hQP A').1 (refinementParent hQP B').1 : ℝ) *
              (#s' * #t')| ≤ 2 * (max (Fintype.card κ) 1 : ℕ) * η * (#A'.1 * #B'.1)) ∧
        (S.IsRegularPair η A'.1 B'.1 →
          (#{x ∈ A'.1 ×ˢ B'.1 | T.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
            (∑ c : κ, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1| *
              (#A'.1 * #B'.1)) / 2 + Fintype.card κ * η * (#A'.1 * #B'.1))) := by
  classical
  by_cases hne : refinementParent hQP A' = refinementParent hQP B'
  · exact ⟨S, rfl, fun h ↦ absurd hne h⟩
  set pA := refinementParent hQP A'
  set pB := refinementParent hQP B'
  have hpAB : pA.1 ≠ pB.1 := Subtype.coe_injective.ne hne
  have hdisjP : Disjoint pA.1 pB.1 := P.disjoint pA.2 pB.2 hpAB
  have hdisjQ : Disjoint A'.1 B'.1 :=
    hdisjP.mono (le_refinementParent hQP A') (le_refinementParent hQP B')
  have hp : ∀ c : κ, 0 ≤ (pairColorDensity S c pA.1 pB.1 : ℝ) := fun c ↦ by
    exact_mod_cast pairColorDensity_nonneg S c pA.1 pB.1
  have hp1 : ∑ c : κ, (pairColorDensity S c pA.1 pB.1 : ℝ) = 1 := by
    obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts pA.2
    obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts pB.2
    exact_mod_cast sum_pairColorDensity S pA.1 pB.1
      ⟨(u, v), mem_filter.2 ⟨mem_product.2 ⟨hu, hv⟩, hdisjP.forall_ne_finset hu hv⟩⟩
  obtain ⟨T, hrev, -, hdisc, hedit⟩ :=
    S.exists_coupled_recoloring_abs_card_filter_sub_le hdisjQ hp hp1 hη
      (hQsize A'.1 A'.2) (hQsize B'.1 B'.2)
  exact ⟨T, hrev, fun _ ↦ ⟨hdisc, hedit⟩⟩

open Classical in
/-- If `T_off` has rectangle discrepancy at most `η_rect * (#A' * #B')` toward the coarse
densities of `S` on every fine subblock `A' ×ˢ B'` with `eP (parent A') < eP (parent B')`,
and `2 * η_rect ≤ δ ^ 3` with `0 < δ ≤ 1 / 2`, then every off-diagonal pair of `P` is
`δ`-regular in `T_off`. -/
private theorem isRegularPair_offDiag_of_fine_discrepancy {κ V : Type*}
    [Fintype V] [DecidableEq V] (S T_off : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    (eP : P.parts ≃ Fin (Fintype.card P.parts)) {δ η_rect : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη_δ : 2 * η_rect ≤ δ ^ 3)
    (hdisc : ∀ A' B' : Q.parts,
      eP (refinementParent hQP A') < eP (refinementParent hQP B') →
      ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1, ∀ d : κ,
        |(#{x ∈ s' ×ˢ t' | T_off.colorOfPair x.1 x.2 = some d} : ℝ) -
          (pairColorDensity S d (refinementParent hQP A').1 (refinementParent hQP B').1 : ℝ) *
            (#s' * #t')| ≤ η_rect * (#A'.1 * #B'.1))
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
    T_off.IsRegularPair δ A B := by
  have hoff_lt {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
      (hlt : eP ⟨A, hA⟩ < eP ⟨B, hB⟩) : T_off.IsRegularPair δ A B := by
    have hAB' : A ≠ B := fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
    refine (T_off.isRegularPair_of_abs_card_filter_colorOfPair_sub_le
      (p := fun c ↦ (pairColorDensity S c A B : ℝ)) (η := η_rect)
      (P.disjoint hA hB hAB') (P.nonempty_of_mem_parts hA) (P.nonempty_of_mem_parts hB)
      hδ0 (by rw [min_eq_right (by linarith)]; linarith)
      fun c X hX Y hY ↦
        T_off.abs_card_filter_colorOfPair_sub_le_of_refines hQP hA hB c hX hY
          fun A' hA' hA'A B' hB' hB'B ↦ ?_).1
    have hpA : refinementParent hQP ⟨A', hA'⟩ = ⟨A, hA⟩ := (refinementParent_eq_iff hQP).2 hA'A
    have hpB : refinementParent hQP ⟨B', hB'⟩ = ⟨B, hB⟩ := (refinementParent_eq_iff hQP).2 hB'B
    simpa only [hpA, hpB] using hdisc ⟨A', hA'⟩ ⟨B', hB'⟩ (by rwa [hpA, hpB])
      (X ∩ A') inter_subset_right (Y ∩ B') inter_subset_right c
  have hne : eP ⟨A, hA⟩ ≠ eP ⟨B, hB⟩ := fun h ↦ hAB (Subtype.ext_iff.1 (eP.injective h))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hoff_lt hA hB hlt
  · exact (hoff_lt hB hA hgt).symm

open Classical in
/-- Core off-diagonal strong regular approximation: constructs `P ≤ P₀` and `T_off` over the
original palette `κ` preserving `S.rev` and within-cell colors, with `min (1 / 2) (G #P.parts)`-
regular off-diagonal cell pairs, cell sizes satisfying `1 < min (1 / 2) (G #P.parts) * #A`, and
at most `(3 / 4) * α |V|²` edited ordered distinct pairs. -/
private theorem exists_refining_equipartition_regular_offDiag_aux {κ V : Type*}
    [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {α : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ} (hG : ∀ n, 0 < G n)
    (hV : pairOffDiagBound (Fintype.card κ) α G #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T_off : PairColorSystem κ V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ pairOffDiagPartsBound (Fintype.card κ) α G #P₀.parts ∧
      T_off.rev = S.rev ∧
      (∀ u v, P.part u = P.part v → T_off.colorOfPair u v = S.colorOfPair u v) ∧
      (∀ A ∈ P.parts, 1 < min (1 / 2) (G #P.parts) * #A) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
        T_off.IsRegularPair (min (1 / 2) (G #P.parts)) A B) ∧
      (#{p : {p : V × V // p.1 ≠ p.2} | T_off.color p ≠ S.color p} : ℝ) ≤
        3 / 4 * α * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set q := Fintype.card κ
  set q' : ℕ := max q 1
  set M_coarse := pairOffDiagPartsBound q α G #P₀.parts
  -- Step 1: Obtain strong pair-regularity witness `Q ≤ P ≤ P₀` and fine cell-size bounds.
  have : Nonempty V := Fintype.card_pos_iff.1 ((pairOffDiagBound_pos q α G #P₀.parts).trans_le hV)
  have hP₀_pos : 0 < #P₀.parts := (P₀.parts_nonempty univ_nonempty.ne_empty).card_pos
  have hg₂ : 0 < (α / (4 * (q' : ℝ))) ^ 2 := by positivity
  obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard', hQcard', hQirreg, hgap⟩ :=
    S.exists_strong_refining_equipartitions P₀ hP₀ hg₂ (pairOffDiagTolerance_pos q hα hG)
  have hPcard : #P.parts ≤ M_coarse := by
    simpa only [M_coarse, q, q', pairOffDiagPartsBound_def] using hPcard'
  have hQcard : #Q.parts ≤ strongPairColorStepBound (pairOffDiagTolerance q α G) M_coarse :=
    hQcard'.trans (strongPairColorStepBound_mono _ hPcard)
  have hQparts_pos : 0 < #Q.parts := (hP₀_pos.trans_le (card_mono hPP₀)).trans_le (card_mono hQP)
  set η := pairOffDiagTolerance q α G #P.parts
  have hη : 0 < η := pairOffDiagTolerance_pos q hα hG #P.parts
  have hQsize (A' : Finset V) (hA' : A' ∈ Q.parts) : (q + 3 : ℝ) ≤ η ^ 2 * #A' :=
    card_add_three_le_sq_mul_card_fine_part hQ hη hQparts_pos hPcard hQcard hV hA'
  -- Step 2: Choose fine-block recolorings and glue them along `eP ∘ refinementParent`.
  let eP : P.parts ≃ Fin (Fintype.card P.parts) := Fintype.equivFin P.parts
  choose T hTrev hTspec using S.exists_fine_block_recoloring hQP hη hQsize
  obtain ⟨T_off, hT_off_rev, hT_off_lt, hT_off_eq⟩ :=
    S.exists_recoloring_colorOfPair_eq Q (fun A' ↦ eP (refinementParent hQP A')) T
      (fun A' B' _ ↦ hTrev A' B')
  have hdiag_eq (u v : V) (hpart : P.part u = P.part v) :
      T_off.colorOfPair u v = S.colorOfPair u v := by
    let A' : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩
    let B' : Q.parts := ⟨Q.part v, Q.part_mem.2 (mem_univ v)⟩
    have hparent : refinementParent hQP A' = refinementParent hQP B' := Subtype.ext <| by
      rw [← part_eq_refinementParent hQP A' (Q.mem_part_self.2 (mem_univ u)),
        ← part_eq_refinementParent hQP B' (Q.mem_part_self.2 (mem_univ v)), hpart]
    exact hT_off_eq A' B' (congrArg eP hparent) u (Q.mem_part_self.2 (mem_univ u))
      v (Q.mem_part_self.2 (mem_univ v))
  -- Step 3: Coarse cell-size lower bound, off-diagonal regularity, and off-diagonal edit bound.
  set δ := min (1 / 2) (G #P.parts)
  have hδ0 : 0 < δ := lt_min (by norm_num) (hG _)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hη_δ : 4 * (q' : ℝ) * η ≤ δ ^ 3 :=
    (le_div_iff₀' (by positivity : (0 : ℝ) < 4 * q')).1
      (by simp [η, pairOffDiagTolerance_def, δ, q'])
  have hdiag (A : Finset V) (hA : A ∈ P.parts) : 1 < δ * #A := by
    obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts hA
    have hQu : Q.part u ∈ Q.parts := Q.part_mem.2 (mem_univ u)
    have hcardA : (#(Q.part u) : ℝ) ≤ #A :=
      Nat.cast_le.2 (card_le_card (P.part_eq_of_mem hA hu ▸ part_mono hQP u))
    have h3 := hQsize (Q.part u) hQu
    have hδ3 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ]
    have hq'1 : (1 : ℝ) ≤ q' := by exact_mod_cast le_max_right q 1
    have hη_le_δ : η ≤ δ := by nlinarith
    have hη2 : η ^ 2 ≤ δ := by nlinarith
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hoff (A : Finset V) (hA : A ∈ P.parts) (B : Finset V) (hB : B ∈ P.parts)
      (hAB : A ≠ B) : T_off.IsRegularPair δ A B :=
    isRegularPair_offDiag_of_fine_discrepancy S T_off hQP eP (η_rect := 2 * (q' : ℝ) * η)
      hδ0 hδ1 (by linarith)
      (fun A' B' hlt s' hs' t' ht' d ↦ by
        have hne : refinementParent hQP A' ≠ refinementParent hQP B' :=
          fun h ↦ (ne_of_lt hlt) (congrArg eP h)
        have hf : {x ∈ s' ×ˢ t' | T_off.colorOfPair x.1 x.2 = some d} =
            {x ∈ s' ×ˢ t' | (T A' B').colorOfPair x.1 x.2 = some d} :=
          filter_congr fun x hx ↦ by
            rw [hT_off_lt A' B' hlt x.1 (hs' (mem_product.1 hx).1) x.2 (ht' (mem_product.1 hx).2)]
        rw [hf]; exact (hTspec A' B' hne).1 s' hs' t' ht' d) hA hB hAB
  have hη_α : (2 * (q : ℝ) + 1) * η ≤ α / 2 := by
    have hle : η ≤ α / (4 * ((q' : ℝ) + 1)) := by simp [η, pairOffDiagTolerance_def, q']
    have hqq' : (q : ℝ) ≤ q' := by exact_mod_cast le_max_left q 1
    rw [le_div_iff₀' (by positivity : (0 : ℝ) < 4 * ((q' : ℝ) + 1))] at hle
    nlinarith
  refine ⟨P, T_off, hPP₀, hP, hPcard, hT_off_rev, hdiag_eq, hdiag, hoff,
    card_edit_offDiag_le S T_off hQP eP hT_off_rev hdiag_eq hα hη hQirreg hgap hη_α
      fun A' B' hlt hreg ↦ ?_⟩
  have hne : refinementParent hQP A' ≠ refinementParent hQP B' :=
    fun h ↦ (ne_of_lt hlt) (congrArg eP h)
  have hf : {x ∈ A'.1 ×ˢ B'.1 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} =
      {x ∈ A'.1 ×ˢ B'.1 | (T A' B').colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} :=
    filter_congr fun x hx ↦ by
      rw [hT_off_lt A' B' hlt x.1 (mem_product.1 hx).1 x.2 (mem_product.1 hx).2]
  rw [hf]; exact (hTspec A' B' hne).2 hreg

open Classical in
/-- Replacing within-cell pairs of `T_off` via `fillDiagonal P` increases the number of edited
ordered distinct pairs relative to `S` by at most `|V|² / #P.parts`. -/
private theorem card_edit_fillDiagonal_le {κ V : Type*} [Fintype V] [DecidableEq V]
    (S T_off : PairColorSystem κ V) {P : Finpartition (univ : Finset V)}
    (hP : P.IsEquipartition) (hPpos : 0 < #P.parts) :
    (#{p : {p : V × V // p.1 ≠ p.2} | (T_off.fillDiagonal P).color p ≠ some (S.color p)} : ℝ) ≤
      (Fintype.card V : ℝ) ^ 2 / #P.parts +
        #{p : {p : V × V // p.1 ≠ p.2} | T_off.color p ≠ S.color p} := by
  classical
  set T := T_off.fillDiagonal P
  set E_all : Finset {p : V × V // p.1 ≠ p.2} := {p | T.color p ≠ some (S.color p)}
  set E_diag : Finset (V × V) :=
    {y : V × V | T.colorOfPair y.1 y.2 ≠ (T_off.colorOfPair y.1 y.2).map some}
  set E_off : Finset {p : V × V // p.1 ≠ p.2} := {p | T_off.color p ≠ S.color p}
  have hE_split : #E_all ≤ #E_diag + #E_off := by
    calc #E_all = #(E_all.map ⟨Subtype.val, Subtype.val_injective⟩) := (card_map _).symm
      _ ≤ #(E_diag ∪ E_off.map ⟨Subtype.val, Subtype.val_injective⟩) := by
          refine card_le_card fun x hx ↦ ?_
          obtain ⟨⟨y, hy⟩, hmem, rfl⟩ := mem_map.1 hx
          have hTne : T.color ⟨y, hy⟩ ≠ some (S.color ⟨y, hy⟩) := (mem_filter.1 hmem).2
          by_cases hsame : P.part y.1 = P.part y.2
          · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _,
              (T_off.fillDiagonal_colorOfPair_ne_iff P y.1 y.2).2 ⟨hy, hsame⟩⟩)
          · refine mem_union_right _ (mem_map.2 ⟨⟨y, hy⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩)
            exact fun heq ↦ hTne (by simp [T, hsame, heq])
      _ ≤ #E_diag + #(E_off.map ⟨Subtype.val, Subtype.val_injective⟩) := card_union_le _ _
      _ = #E_diag + #E_off := by rw [card_map]
  have hdiv_le : (#E_diag : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / #P.parts := by
    set n := Fintype.card V
    have hnat : #E_diag ≤ n * (n / #P.parts) :=
      T_off.card_fillDiagonal_colorOfPair_ne_le_of_isEquipartition P hP
    rw [le_div_iff₀ (Nat.cast_pos.2 hPpos)]
    calc (#E_diag : ℝ) * #P.parts
        ≤ ((n * (n / #P.parts) : ℕ) : ℝ) * #P.parts :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) (Nat.cast_nonneg _)
      _ = (n : ℝ) * (((n / #P.parts : ℕ) * #P.parts : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (n : ℝ) * n := by gcongr; exact_mod_cast Nat.div_mul_le_self n #P.parts
      _ = (n : ℝ) ^ 2 := (sq _).symm
  have hcast : (#E_all : ℝ) ≤ #E_diag + #E_off := by exact_mod_cast hE_split
  linarith

end Assembly

/-! ### Main strong regular approximation theorems -/

open Classical in
/-- **Off-diagonal strong regular approximation of a pair-color system**, seeded form. Given an
equitable partition `P₀`, an edit budget `α > 0`, and a positive schedule `G`, if `V` has at least
`pairOffDiagBound (card κ) α G #P₀.parts` vertices, there exist an equitable refinement `P ≤ P₀`
with at most `pairOffDiagPartsBound (card κ) α G #P₀.parts` cells and a pair-color system `T` over
the same palette `κ` preserving `S.rev` and all within-cell colors, such that every pair of
distinct cells of `P` is `G #P.parts`-regular and `T` differs from `S` on at most `α |V|²` ordered
distinct pairs. -/
theorem exists_refining_equipartition_regular_offDiag {κ V : Type*}
    [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {α : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ} (hG : ∀ n, 0 < G n)
    (hV : pairOffDiagBound (Fintype.card κ) α G #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem κ V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ pairOffDiagPartsBound (Fintype.card κ) α G #P₀.parts ∧
      T.rev = S.rev ∧
      (∀ u v, P.part u = P.part v → T.colorOfPair u v = S.colorOfPair u v) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → T.IsRegularPair (G #P.parts) A B) ∧
      (#{p : {p : V × V // p.1 ≠ p.2} | T.color p ≠ S.color p} : ℝ) ≤
        α * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, T, hPP₀, hP, hPcard, hrev, hdiag_eq, -, hoff, hedit⟩ :=
    S.exists_refining_equipartition_regular_offDiag_aux P₀ hP₀ hα hG hV
  exact ⟨P, T, hPP₀, hP, hPcard, hrev, hdiag_eq,
    fun A hA B hB hAB ↦ (hoff A hA B hB hAB).mono (min_le_right _ _),
    hedit.trans (by nlinarith [sq_nonneg (Fintype.card V : ℝ)])⟩

open Classical in
/-- **Off-diagonal strong regular approximation of a pair-color system**, unseeded form. For an
edit budget `α > 0`, a positive schedule `G`, and a minimum part count `l`, if `V` has at least
`pairOffDiagBound (card κ) α G (max l 1)` vertices, there exist an equipartition `P` with
`l ≤ #P.parts ≤ pairOffDiagPartsBound (card κ) α G (max l 1)` and a pair-color system `T` over the
same palette `κ` preserving `S.rev` and all within-cell colors, such that every pair of distinct
cells of `P` is `G #P.parts`-regular and `T` differs from `S` on at most `α |V|²` ordered distinct
pairs. -/
theorem exists_equipartition_regular_offDiag {κ V : Type*}
    [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V) {l : ℕ}
    {α : ℝ} (hα : 0 < α) {G : ℕ → ℝ} (hG : ∀ n, 0 < G n)
    (hV : pairOffDiagBound (Fintype.card κ) α G (max l 1) ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem κ V),
      P.IsEquipartition ∧ l ≤ #P.parts ∧
      #P.parts ≤ pairOffDiagPartsBound (Fintype.card κ) α G (max l 1) ∧
      T.rev = S.rev ∧
      (∀ u v, P.part u = P.part v → T.colorOfPair u v = S.colorOfPair u v) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → T.IsRegularPair (G #P.parts) A B) ∧
      (#{p : {p : V × V // p.1 ≠ p.2} | T.color p ≠ S.color p} : ℝ) ≤
        α * (Fintype.card V : ℝ) ^ 2 := by
  have hlV : max l 1 ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (le_pairOffDiagPartsBound (Fintype.card κ) hα hG (max l 1)).trans
      ((pairOffDiagPartsBound_le_pairOffDiagBound (Fintype.card κ) hα hG (max l 1)).trans hV)
  obtain ⟨P₀, hP₀, hcard⟩ :=
    exists_equipartition_card_eq (univ : Finset V) (by positivity : max l 1 ≠ 0) hlV
  obtain ⟨P, T, hPP₀, hP, hPcard, hrev, hdiag_eq, hoff, hedit⟩ :=
    S.exists_refining_equipartition_regular_offDiag P₀ hP₀ hα hG (by rwa [hcard])
  exact ⟨P, T, hP, (le_max_left l 1).trans (hcard ▸ card_mono hPP₀), hcard ▸ hPcard,
    hrev, hdiag_eq, hoff, hedit⟩

open Classical in
/-- **Strong regular approximation of a pair-color system.** Given an equitable partition `P₀`,
an edit budget `α > 0`, and a positive error schedule `F`, if `V` has at least
`pairApproximationBound (card κ) α F #P₀.parts` vertices, there exist an equitable refinement
`P ≤ P₀` with at most `pairApproximationPartsBound (card κ) α F #P₀.parts` cells and a
pair-color system `T` over `Option κ` with `T.rev = Option.map S.rev` such that `⟨P, T⟩` is
`F`-regular at its lower complexity and `T` differs from `some ∘ S.color` on at most `α |V|²`
ordered distinct pairs. -/
theorem exists_refining_equipartition_lowerSkeletonRegular {κ V : Type*}
    [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {α : ℝ} (hα : 0 < α)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : pairApproximationBound (Fintype.card κ) α F #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ pairApproximationPartsBound (Fintype.card κ) α F #P₀.parts ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (#{p : {p : V × V // p.1 ≠ p.2} | T.color p ≠ some (S.color p)} : ℝ) ≤
        α * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set q := Fintype.card κ
  set a₀ : ℕ := max 1 ⌈4 / α⌉₊
  have ha₀ : a₀ ≠ 0 := by positivity
  have : Nonempty V :=
    Fintype.card_pos_iff.1 ((pairApproximationBound_pos q α F #P₀.parts).trans_le hV)
  have hP₀_pos : 0 < #P₀.parts := (P₀.parts_nonempty univ_nonempty.ne_empty).card_pos
  have ha₀P₀ : a₀ * #P₀.parts ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (mul_le_pairApproximationPartsBound q hα hF #P₀.parts).trans
      ((pairApproximationPartsBound_le_pairApproximationBound q hα hF #P₀.parts).trans hV)
  obtain ⟨P₁, hP₁, hP₁card, hP₁P₀, -⟩ :=
    hP₀.exists_refining_equipartition_card_eq_mul P₀ le_rfl ha₀ ha₀P₀
  obtain ⟨P, T_off, hPP₁, hP, hPcard', hrev, -, hAsize, hoff, hedit_off⟩ :=
    S.exists_refining_equipartition_regular_offDiag_aux P₁ hP₁ hα (G := fun t ↦ F (t + q + 1))
      (fun _ ↦ hF _) (by rw [hP₁card]; exact hV)
  have hPcard : #P.parts ≤ pairApproximationPartsBound q α F #P₀.parts := by
    rw [hP₁card] at hPcard'; exact hPcard'
  set T : PairColorSystem (Option κ) V := T_off.fillDiagonal P
  have hlower : (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F := by
    rw [PairSkeleton3.lowerSkeletonRegular_iff, Fintype.card_option, ← add_assoc]
    exact (T_off.isPairColorRegular_fillDiagonal P hAsize hoff).mono (min_le_right _ _)
  have hPparts_ge : a₀ * #P₀.parts ≤ #P.parts := hP₁card ▸ card_mono hPP₁
  have hPparts_pos : 0 < #P.parts :=
    lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero ha₀) hP₀_pos) hPparts_ge
  have ha₀_le : 4 / α ≤ #P.parts :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 ((le_max_right 1 ⌈4 / α⌉₊).trans
      ((Nat.le_mul_of_pos_right a₀ hP₀_pos).trans hPparts_ge)))
  have hdiag_bound : (Fintype.card V : ℝ) ^ 2 / #P.parts ≤ α / 4 * (Fintype.card V : ℝ) ^ 2 := by
    rw [div_le_iff₀ (Nat.cast_pos.2 hPparts_pos)]
    have h1 : 1 ≤ α / 4 * #P.parts := by rw [div_le_iff₀ hα] at ha₀_le; linarith
    linarith [le_mul_of_one_le_left (sq_nonneg (Fintype.card V : ℝ)) h1]
  have hfill_edit := card_edit_fillDiagonal_le S T_off hP hPparts_pos
  refine ⟨P, T, hPP₁.trans hP₁P₀, hP, hPcard,
    funext fun c ↦ by simp only [T, fillDiagonal_rev, hrev], hlower, ?_⟩
  linarith

open Classical in
/-- **Strong regular approximation of a pair-color system**, unseeded form. For an edit budget
`α > 0`, a positive error schedule `F`, and a minimum part count `l`, if `V` has at least
`pairApproximationBound (card κ) α F (max l 1)` vertices, there exist an equipartition `P` with
`l ≤ #P.parts ≤ pairApproximationPartsBound (card κ) α F (max l 1)` and a pair-color system `T`
over `Option κ` with `T.rev = Option.map S.rev` such that `⟨P, T⟩` is `F`-regular at its lower
complexity and `T` differs from `some ∘ S.color` on at most `α |V|²` ordered distinct pairs. -/
theorem exists_equipartition_lowerSkeletonRegular {κ V : Type*}
    [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V) {l : ℕ}
    {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : pairApproximationBound (Fintype.card κ) α F (max l 1) ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P.IsEquipartition ∧ l ≤ #P.parts ∧
      #P.parts ≤ pairApproximationPartsBound (Fintype.card κ) α F (max l 1) ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (#{p : {p : V × V // p.1 ≠ p.2} | T.color p ≠ some (S.color p)} : ℝ) ≤
        α * (Fintype.card V : ℝ) ^ 2 := by
  have hlV : max l 1 ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (le_pairApproximationPartsBound (Fintype.card κ) hα hF (max l 1)).trans
      ((pairApproximationPartsBound_le_pairApproximationBound (Fintype.card κ) hα hF
        (max l 1)).trans hV)
  obtain ⟨P₀, hP₀, hcard⟩ :=
    exists_equipartition_card_eq (univ : Finset V) (by positivity : max l 1 ≠ 0) hlV
  obtain ⟨P, T, hPP₀, hP, hPcard, hrev, hlower, hedit⟩ :=
    S.exists_refining_equipartition_lowerSkeletonRegular P₀ hP₀ hα hF (by rwa [hcard])
  exact ⟨P, T, hP, (le_max_left l 1).trans (hcard ▸ card_mono hPP₀), hcard ▸ hPcard,
    hrev, hlower, hedit⟩

end PairColorSystem
end TauCeti
