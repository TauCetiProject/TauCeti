/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Cleanup
public import TauCeti.Combinatorics.Hypergraph.PairColor.StrongRegularization
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import TauCeti.Data.Finset.Basic

/-!
# Scheduled regular approximation of lower skeletons

Cleaning up irregular cell pairs and diagonal blocks on a fixed partition (`PairColor/Cleanup.lean`)
makes a lower skeleton regular at a fixed tolerance `2ε`. However, when the required tolerance is a
schedule `F (#P.parts + card κ')` evaluated at the lower complexity of the returned skeleton,
refining `P` to reduce the irregular mass shrinks `F (#P.parts + card κ')` faster than the cell
sizes allow uncoupled recoloring to stay within a prescribed edit budget `ε |V|²`.

This file resolves that circularity by combining strong equitable pair-color regularity
(`PairColor/StrongRegularization.lean`) with coupled low-discrepancy recoloring
(`PairColor/Recoloring.lean`):

1. Refine the seed equipartition `P₀` into at least `⌈4 / ε⌉₊` equitable cells so within-cell pairs
   have total mass at most `(ε / 4) |V|²`.
2. Apply strong equitable regularity with energy-gap threshold `g = (ε / (4 (card κ + 1)))²` and a
   fine schedule `η m` polynomial in `F (m + card κ + 1)` and `ε`, obtaining nested equipartitions
   `Q ≤ P ≤ P₀` with `S.energy Q - S.energy P ≤ g`.
3. Keep all pairs inside coarse cells of `P` unchanged; recolor `η`-irregular fine pairs between
   distinct coarse cells `A ≠ B` independently toward `pairColorDensity S · A B`; and recolor
   `η`-regular fine pairs toward `pairColorDensity S · A B` via coupled low-discrepancy recoloring.
   Summing the fine rectangle count bounds over the fine cells inside `A ×ˢ B` makes `(A, B)`
   `δ`-regular on the coarse partition `P`, while the `L¹` energy-gap bound
   (`PairColorSystem.sum_card_mul_abs_pairColorDensity_sub_refinementParent_le`) keeps the total
   off-diagonal edit count below `(3ε / 4) |V|²`.
4. Apply `PairColorSystem.fillDiagonal P` to clean up diagonal blocks at edit cost at most
   `(ε / 4) |V|²`, achieving `PairSkeleton3.LowerSkeletonRegular F` on `(P, T)` within total edit
   budget `ε |V|²`. When `|V|` is smaller than `lowerSkeletonApproximationBound`, the singleton
   partition `⊥` achieves `LowerSkeletonRegular F` with zero edits.

## Main definitions

* `TauCeti.lowerSkeletonApproximationBound`: upper bound on the number of vertex cells in the
  scheduled regular approximation of a lower skeleton.

## Main results

* `TauCeti.PairColorSystem.exists_recoloring_regular_offDiag_of_refines`: recoloring across a
  refinement `Q ≤ P` makes all distinct coarse cell pairs `δ`-regular with edit count controlled by
  the fine irregular mass and the energy gap `S.energy Q - S.energy P`.
* `TauCeti.PairColorSystem.exists_refining_equipartition_lowerSkeletonRegular`: scheduled regular
  approximation of a pair-color system refining any given equipartition.
* `TauCeti.PairColorSystem.exists_equipartition_lowerSkeletonRegular`: unseeded scheduled regular
  approximation with at least `l` equitable cells.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2 and Theorem 2.5 (regular approximation).
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Theorem 4.3 (regular graph approximation via strong regularity).
-/

public section

open Finset Finpartition

namespace TauCeti

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V]

section AcrossRefinement

open Classical in
/-- Sum fine rectangle count discrepancies over the fine cells refining `A` and `B` to obtain a
rectangle count bound on every subrectangle `A' ×ˢ B' ⊆ A ×ˢ B`. -/
private theorem abs_card_filter_coarse_sub_le {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    (R : PairColorSystem κ V) {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    {p : κ → ℝ} {ω : ℝ} (c : κ)
    (hfine : ∀ C D : Q.parts, refinementParent hQP C = ⟨A, hA⟩ →
      refinementParent hQP D = ⟨B, hB⟩ → ∀ C' ⊆ C.1, ∀ D' ⊆ D.1,
        |(#{q ∈ C' ×ˢ D' | R.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#C' * #D')| ≤
          ω * (#C.1 * #D.1))
    {A' B' : Finset V} (hA' : A' ⊆ A) (hB' : B' ⊆ B) :
    |(#{q ∈ A' ×ˢ B' | R.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#A' * #B')| ≤
      ω * (#A * #B) := by
  set CA : Finset Q.parts := {C | refinementParent hQP C = ⟨A, hA⟩}
  set DB : Finset Q.parts := {D | refinementParent hQP D = ⟨B, hB⟩}
  let sub (CD : Q.parts × Q.parts) : Finset (V × V) := (A' ∩ CD.1.1) ×ˢ (B' ∩ CD.2.1)
  have hA'eq : CA.biUnion (fun C ↦ A' ∩ C.1) = A' := by
    rw [← inter_biUnion, biUnion_filter_refinementParent_eq hQP ⟨A, hA⟩, inter_eq_left.2 hA']
  have hB'eq : DB.biUnion (fun D ↦ B' ∩ D.1) = B' := by
    rw [← inter_biUnion, biUnion_filter_refinementParent_eq hQP ⟨B, hB⟩, inter_eq_left.2 hB']
  have hrect : (CA ×ˢ DB).biUnion sub = A' ×ˢ B' := by
    ext ⟨u, v⟩
    have hu : u ∈ CA.biUnion (fun C ↦ A' ∩ C.1) ↔ u ∈ A' := by rw [hA'eq]
    have hv : v ∈ DB.biUnion (fun D ↦ B' ∩ D.1) ↔ v ∈ B' := by rw [hB'eq]
    simp only [mem_biUnion, mem_inter] at hu hv
    simp only [sub, mem_biUnion, mem_product, mem_inter, Prod.exists]
    exact ⟨fun ⟨C, D, ⟨hC, hD⟩, h₁, h₂⟩ ↦ ⟨hu.1 ⟨C, hC, h₁⟩, hv.1 ⟨D, hD, h₂⟩⟩,
      fun ⟨h₁, h₂⟩ ↦ let ⟨C, hC, h₁⟩ := hu.2 h₁; let ⟨D, hD, h₂⟩ := hv.2 h₂
        ⟨C, D, ⟨hC, hD⟩, h₁, h₂⟩⟩
  have hdisj : ((CA ×ˢ DB : Finset _) : Set (Q.parts × Q.parts)).PairwiseDisjoint sub := by
    intro CD₁ _ CD₂ _ hne
    refine disjoint_product.2 ?_
    by_cases h₁ : CD₁.1 = CD₂.1
    · exact Or.inr ((Q.disjoint CD₁.2.2 CD₂.2.2
        (Subtype.coe_injective.ne fun h₂ ↦ hne (Prod.ext h₁ h₂))).mono
        inter_subset_right inter_subset_right)
    · exact Or.inl ((Q.disjoint CD₁.1.2 CD₂.1.2 (Subtype.coe_injective.ne h₁)).mono
        inter_subset_right inter_subset_right)
  have hcnt : (#{q ∈ A' ×ˢ B' | R.colorOfPair q.1 q.2 = some c} : ℝ) =
      ∑ CD ∈ CA ×ˢ DB, (#{q ∈ sub CD | R.colorOfPair q.1 q.2 = some c} : ℝ) := by
    rw [← hrect, filter_biUnion, card_biUnion fun CD₁ h₁ CD₂ h₂ hne ↦
      (hdisj h₁ h₂ hne).mono (filter_subset _ _) (filter_subset _ _), Nat.cast_sum]
  have hprd : p c * (#A' * #B') =
      ∑ CD ∈ CA ×ˢ DB, p c * (#(A' ∩ CD.1.1) * #(B' ∩ CD.2.1) : ℝ) := by
    have h₁ : (∑ C ∈ CA, (#(A' ∩ C.1) : ℝ)) = #A' :=
      mod_cast (sum_card_inter_filter_refinementParent_eq hQP ⟨A, hA⟩ A').trans
        (congrArg card (inter_eq_left.2 hA'))
    have h₂ : (∑ D ∈ DB, (#(B' ∩ D.1) : ℝ)) = #B' :=
      mod_cast (sum_card_inter_filter_refinementParent_eq hQP ⟨B, hB⟩ B').trans
        (congrArg card (inter_eq_left.2 hB'))
    rw [← mul_sum, sum_product]; dsimp only; rw [← sum_mul_sum, h₁, h₂]
  have htot : ∑ CD ∈ CA ×ˢ DB, ω * (#CD.1.1 * #CD.2.1 : ℝ) = ω * (#A * #B) := by
    have h₁ : (∑ C ∈ CA, (#C.1 : ℝ)) = #A :=
      mod_cast sum_card_filter_refinementParent_eq hQP ⟨A, hA⟩
    have h₂ : (∑ D ∈ DB, (#D.1 : ℝ)) = #B :=
      mod_cast sum_card_filter_refinementParent_eq hQP ⟨B, hB⟩
    rw [← mul_sum, sum_product]; dsimp only; rw [← sum_mul_sum, h₁, h₂]
  rw [hcnt, hprd, ← sum_sub_distrib, ← htot]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun CD hCD ↦
    hfine CD.1 CD.2 (mem_filter.1 (mem_product.1 hCD).1).2 (mem_filter.1 (mem_product.1 hCD).2).2
      _ inter_subset_right _ inter_subset_right)

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- Uniform rectangle count control with `2 * ω ≤ δ ^ 3` and `0 < δ ≤ 1` makes a disjoint nonempty
cell pair `(A, B)` `δ`-regular with densities within `δ / 2` of `p`. -/
private theorem isRegularPair_of_coarse_discrepancy (R : PairColorSystem κ V) {A B : Finset V}
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hst : Disjoint A B) {p : κ → ℝ} {ω δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hω : 2 * ω ≤ δ ^ 3)
    (hcnt : ∀ c, ∀ A' ⊆ A, ∀ B' ⊆ B,
      |(#{q ∈ A' ×ˢ B' | R.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#A' * #B')| ≤
        ω * (#A * #B)) :
    R.IsRegularPair δ A B ∧ ∀ c, |(pairColorDensity R c A B : ℝ) - p c| ≤ δ / 2 := by
  have hA0 : (0 : ℝ) < #A := Nat.cast_pos.2 hAn.card_pos
  have hB0 : (0 : ℝ) < #B := Nat.cast_pos.2 hBn.card_pos
  have hsub (c : κ) {A' B' : Finset V} (hA' : A' ⊆ A) (hB' : B' ⊆ B)
      (hA's : δ * #A ≤ #A') (hB's : δ * #B ≤ #B') :
      |(pairColorDensity R c A' B' : ℝ) - p c| ≤ δ / 2 := by
    have hpos : (0 : ℝ) < #A' * #B' :=
      mul_pos ((mul_pos hδ hA0).trans_le hA's) ((mul_pos hδ hB0).trans_le hB's)
    have hd : (#{q ∈ A' ×ˢ B' | R.colorOfPair q.1 q.2 = some c} : ℝ) =
        pairColorDensity R c A' B' * (#A' * #B') :=
      mod_cast (pairColorDensity_mul_card_of_disjoint R c (hst.mono hA' hB')).symm
    have hc := hcnt c A' hA' B' hB'
    rw [hd, ← sub_mul, abs_mul, abs_of_pos hpos] at hc
    refine le_of_mul_le_mul_right ?_ hpos
    have hprod : (δ * #A) * (δ * #B) ≤ #A' * #B' :=
      mul_le_mul hA's hB's (by positivity) (by positivity)
    nlinarith [mul_pos hA0 hB0]
  have hfull (c : κ) : |(pairColorDensity R c A B : ℝ) - p c| ≤ δ / 2 :=
    hsub c subset_rfl subset_rfl (mul_le_of_le_one_left hA0.le hδ1)
      (mul_le_of_le_one_left hB0.le hδ1)
  refine ⟨isRegularPair_iff.2 fun c A' hA' B' hB' hA's hB's ↦ ?_, hfull⟩
  have h₁ := hsub c hA' hB' hA's hB's
  have h₂ := hfull c
  calc |(pairColorDensity R c A' B' : ℝ) - pairColorDensity R c A B|
      ≤ |(pairColorDensity R c A' B' : ℝ) - p c| + |p c - pairColorDensity R c A B| :=
        abs_sub_le _ _ _
    _ ≤ δ := by rw [abs_sub_comm (p c)]; linarith

open Classical in
/-- Choose a local recoloring for each fine cell pair `(C, D)` relative to `hQP : Q ≤ P`: keep `S`
inside coarse cells, recolor irregular off-diagonal fine pairs independently toward the coarse block
densities, and coupled-recolor `η`-regular off-diagonal fine pairs. -/
private theorem exists_fine_pair_recoloring [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η ξ : ℝ} (hξ : 0 < ξ)
    (hsize : ∀ C ∈ Q.parts, Fintype.card κ + 2 ≤ ξ ^ 6 * #C) (C D : Q.parts) :
    ∃ T : PairColorSystem κ V, T.rev = S.rev ∧
      (refinementParent hQP C = refinementParent hQP D → T = S) ∧
      (refinementParent hQP C ≠ refinementParent hQP D →
        (∀ c, ∀ C' ⊆ C.1, ∀ D' ⊆ D.1,
          |(#{q ∈ C' ×ˢ D' | T.colorOfPair q.1 q.2 = some c} : ℝ) -
              pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1 *
                (#C' * #D')| ≤
            Fintype.card κ * (max η 0 + ξ ^ 3) * (#C.1 * #D.1)) ∧
        (S.IsRegularPair η C.1 D.1 →
          (#{q ∈ C.1 ×ˢ D.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
            (∑ c, (#C.1 * #D.1 : ℝ) *
              |(pairColorDensity S c C.1 D.1 : ℝ) -
                pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1|) / 2 +
              Fintype.card κ * ξ ^ 3 * (#C.1 * #D.1))) := by
  set A := refinementParent hQP C
  set B := refinementParent hQP D
  by_cases hAB : A = B
  · exact ⟨S, rfl, fun _ ↦ rfl, fun h ↦ (h hAB).elim⟩
  have hABv : A.1 ≠ B.1 := Subtype.coe_injective.ne hAB
  have hdisjAB : Disjoint A.1 B.1 := P.disjoint A.2 B.2 hABv
  have hdisjCD : Disjoint C.1 D.1 :=
    hdisjAB.mono (le_refinementParent hQP C) (le_refinementParent hQP D)
  have hneAB : ((A.1 ×ˢ B.1).filter fun p ↦ p.1 ≠ p.2).Nonempty := by
    rw [filter_ne_product_of_disjoint hdisjAB]
    exact (P.nonempty_of_mem_parts A.2).product (P.nonempty_of_mem_parts B.2)
  let p (c : κ) : ℝ := pairColorDensity S c A.1 B.1
  have hp (c : κ) : 0 ≤ p c := by dsimp [p]; exact_mod_cast pairColorDensity_nonneg S c A.1 B.1
  have hp1 : ∑ c, p c = 1 := by dsimp [p]; exact_mod_cast sum_pairColorDensity S A.1 B.1 hneAB
  have hK1 : (1 : ℝ) ≤ Fintype.card κ := by
    have : Nonempty κ := by by_contra! h; simp at hp1
    exact Nat.one_le_cast.2 Fintype.card_pos
  by_cases hreg : S.IsRegularPair η C.1 D.1
  · obtain ⟨T, hrev, -, hedit, hdisc⟩ :=
      S.exists_coupled_recoloring_abs_card_filter_colorOfPair_sub_le hdisjCD
        (hreg.mono (le_max_left η 0)) hp hp1 hξ (hsize C C.2) (hsize D D.2)
    refine ⟨T, hrev, fun h ↦ (hAB h).elim, fun _ ↦ ⟨fun c C' hC' D' hD' ↦ ?_, fun _ ↦ ?_⟩⟩
    · simpa only [mul_assoc] using hdisc c C' hC' D' hD'
    · simpa only [mul_assoc] using hedit
  · obtain ⟨T, hrev, -, hdisc⟩ := S.exists_recoloring_abs_card_filter_colorOfPair_sub_le hdisjCD
      hp hp1 hξ (by linarith [hsize C C.2]) (by linarith [hsize D D.2])
    refine ⟨T, hrev, fun h ↦ (hAB h).elim, fun _ ↦ ⟨fun c C' hC' D' hD' ↦ ?_,
      fun h ↦ (hreg h).elim⟩⟩
    refine (hdisc c C' hC' D' hD').trans ?_
    have hle : ξ ^ 3 ≤ Fintype.card κ * (max η 0 + ξ ^ 3) := by
      nlinarith [le_max_right η 0, pow_pos hξ 3]
    calc ξ ^ 3 * #C.1 * #D.1
        = ξ ^ 3 * (#C.1 * #D.1) := mul_assoc _ _ _
      _ ≤ Fintype.card κ * (max η 0 + ξ ^ 3) * (#C.1 * #D.1) :=
          mul_le_mul_of_nonneg_right hle (by positivity)

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- Transfer rectangle color counts between `s ×ˢ t` and `t ×ˢ s` via reversal symmetry. -/
private theorem card_filter_colorOfPair_eq_swap (R S : PairColorSystem κ V) (hrev : R.rev = S.rev)
    (s t : Finset V) (c : κ) :
    #{q ∈ s ×ˢ t | R.colorOfPair q.1 q.2 = some c} =
      #{q ∈ t ×ˢ s | R.colorOfPair q.1 q.2 = some (S.rev c)} := by
  have hiff (q : V × V) :
      R.colorOfPair q.1 q.2 = some c ↔ R.colorOfPair q.2 q.1 = some (S.rev c) := by
    rw [R.colorOfPair_swap q.1 q.2, hrev, Option.map_eq_some_iff]
    exact ⟨fun h ↦ ⟨c, h, rfl⟩, fun ⟨a, ha, h⟩ ↦ S.rev_involutive.injective h ▸ ha⟩
  refine card_bij (fun q _ ↦ q.swap) (fun q hq ↦ ?_) (fun _ _ _ _ h ↦ Prod.swap_injective h)
    fun q hq ↦ ⟨q.swap, ?_, Prod.swap_swap q⟩
  · obtain ⟨hp, hc⟩ := mem_filter.1 hq
    exact mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 hp).2, (mem_product.1 hp).1⟩, (hiff q).1 hc⟩
  · obtain ⟨hp, hc⟩ := mem_filter.1 hq
    exact mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 hp).2, (mem_product.1 hp).1⟩,
      (hiff q.swap).2 hc⟩

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- Transfer edit counts between `s ×ˢ t` and `t ×ˢ s` via reversal symmetry. -/
private theorem card_filter_colorOfPair_ne_swap (R S : PairColorSystem κ V) (hrev : R.rev = S.rev)
    (s t : Finset V) :
    #{q ∈ s ×ˢ t | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
      #{q ∈ t ×ˢ s | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
  have hiff (q : V × V) :
      R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2 ↔
        R.colorOfPair q.2 q.1 ≠ S.colorOfPair q.2 q.1 := by
    rw [R.colorOfPair_swap q.2 q.1, S.colorOfPair_swap q.2 q.1, hrev]
    exact (Option.map_injective S.rev_involutive.injective).ne_iff
  refine card_bij (fun q _ ↦ q.swap) (fun q hq ↦ ?_) (fun _ _ _ _ h ↦ Prod.swap_injective h)
    fun q hq ↦ ⟨q.swap, ?_, Prod.swap_swap q⟩
  · obtain ⟨hp, hc⟩ := mem_filter.1 hq
    exact mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 hp).2, (mem_product.1 hp).1⟩, (hiff q).1 hc⟩
  · obtain ⟨hp, hc⟩ := mem_filter.1 hq
    exact mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 hp).2, (mem_product.1 hp).1⟩,
      (hiff q.swap).2 hc⟩

open Classical in
/-- Transfer the coupled edit bound on a regular fine cell pair `(C, D)` from the chosen orientation
of `order` to both orientations. -/
private theorem card_edits_block_le_of_isRegularPair [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (order : LinearOrder Q.parts)
    (T : Q.parts → Q.parts → PairColorSystem κ V) (R : PairColorSystem κ V)
    (hRrev : R.rev = S.rev)
    (hlocal : ∀ C D : Q.parts, order.le C D → ∀ x ∈ C.1, ∀ y ∈ D.1,
      R.colorOfPair x y = (T C D).colorOfPair x y)
    {η ξ : ℝ}
    (hedit : ∀ C D : Q.parts, refinementParent hQP C ≠ refinementParent hQP D →
      S.IsRegularPair η C.1 D.1 →
      (#{q ∈ C.1 ×ˢ D.1 | (T C D).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        (∑ c, (#C.1 * #D.1 : ℝ) *
          |(pairColorDensity S c C.1 D.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1|) / 2 +
          Fintype.card κ * ξ ^ 3 * (#C.1 * #D.1))
    (C D : Q.parts) (hCD : refinementParent hQP C ≠ refinementParent hQP D)
    (hreg : S.IsRegularPair η C.1 D.1) :
    (#{q ∈ C.1 ×ˢ D.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
      (∑ c, (#C.1 * #D.1 : ℝ) *
        |(pairColorDensity S c C.1 D.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1|) / 2 +
        Fintype.card κ * ξ ^ 3 * (#C.1 * #D.1) := by
  let : LinearOrder Q.parts := order
  rcases le_total C D with hle | hle
  · have hfeq : {q ∈ C.1 ×ˢ D.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
        {q ∈ C.1 ×ˢ D.1 | (T C D).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
      filter_congr fun q hq ↦ by
        rw [hlocal C D hle q.1 (mem_product.1 hq).1 q.2 (mem_product.1 hq).2]
    rw [hfeq]
    exact hedit C D hCD hreg
  · rw [card_filter_colorOfPair_ne_swap R S hRrev C.1 D.1]
    have hfeq : {q ∈ D.1 ×ˢ C.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
        {q ∈ D.1 ×ˢ C.1 | (T D C).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
      filter_congr fun q hq ↦ by
        rw [hlocal D C hle q.1 (mem_product.1 hq).1 q.2 (mem_product.1 hq).2]
    rw [hfeq]
    refine (hedit D C hCD.symm hreg.symm).trans_eq ?_
    have hsum : (∑ c, (#D.1 * #C.1 : ℝ) *
          |(pairColorDensity S c D.1 C.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP D).1 (refinementParent hQP C).1|) =
        ∑ c, (#C.1 * #D.1 : ℝ) *
          |(pairColorDensity S c C.1 D.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1| := by
      rw [← S.rev_involutive.bijective.sum_comp]
      refine sum_congr rfl fun c _ ↦ ?_
      rw [pairColorDensity_swap, pairColorDensity_swap, mul_comm (#D.1 : ℝ) (#C.1)]
    rw [hsum, mul_comm (#D.1 : ℝ) (#C.1)]

/-- Bound the sum of coupled-recoloring `L¹` deviations and random-coloring slack over a subset
`G ⊆ (univ : Finset Q.parts).offDiag` using the energy gap `S.energy Q - S.energy P ≤ g`. -/
private theorem sum_fine_dev_add_slack_le [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    {G : Finset (Q.parts × Q.parts)} (hG : G ⊆ (univ : Finset Q.parts).offDiag)
    {g ξ : ℝ} (hgap : S.energy Q - S.energy P ≤ g) (hξ : 0 ≤ ξ) :
    ∑ CD ∈ G, ((∑ c, (#CD.1.1 * #CD.2.1 : ℝ) *
        |(pairColorDensity S c CD.1.1 CD.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP CD.1).1 (refinementParent hQP CD.2).1|) / 2 +
        Fintype.card κ * ξ ^ 3 * (#CD.1.1 * #CD.2.1)) ≤
      (Fintype.card κ * √g / 2 + Fintype.card κ * ξ ^ 3) * (Fintype.card V : ℝ) ^ 2 := by
  have hdev : (∑ CD ∈ G, ∑ c, (#CD.1.1 * #CD.2.1 : ℝ) *
        |(pairColorDensity S c CD.1.1 CD.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP CD.1).1 (refinementParent hQP CD.2).1|) / 2 ≤
      Fintype.card κ * √g / 2 * (Fintype.card V : ℝ) ^ 2 := by
    have h₁ : ∑ CD ∈ G, ∑ c, (#CD.1.1 * #CD.2.1 : ℝ) *
          |(pairColorDensity S c CD.1.1 CD.2.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP CD.1).1 (refinementParent hQP CD.2).1| ≤
        ∑ _c : κ, √g * #(univ : Finset V).offDiag := by
      refine (sum_le_sum_of_subset_of_nonneg hG fun _ _ _ ↦
        sum_nonneg fun _ _ ↦ by positivity).trans ?_
      rw [sum_comm]
      exact sum_le_sum fun c _ ↦
        S.sum_card_mul_abs_pairColorDensity_sub_refinementParent_le hQP hgap c
    have hoff : (#(univ : Finset V).offDiag : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
      have hle : #(univ : Finset V).offDiag ≤ Fintype.card V ^ 2 := by
        rw [offDiag_card, card_univ, sq]
        exact Nat.sub_le _ _
      exact_mod_cast hle
    rw [sum_const, card_univ, nsmul_eq_mul] at h₁
    have h₂ : (Fintype.card κ : ℝ) * (√g * #(univ : Finset V).offDiag) ≤
        Fintype.card κ * (√g * (Fintype.card V : ℝ) ^ 2) := by gcongr
    linarith
  have hslack : ∑ CD ∈ G, Fintype.card κ * ξ ^ 3 * (#CD.1.1 * #CD.2.1 : ℝ) ≤
      Fintype.card κ * ξ ^ 3 * (Fintype.card V : ℝ) ^ 2 := by
    refine (sum_le_sum_of_subset_of_nonneg (subset_univ G)
      fun _ _ _ ↦ by positivity).trans_eq ?_
    rw [← mul_sum, Fintype.sum_prod_type]
    dsimp only
    rw [← sum_mul_sum, Q.sum_card_subtype, card_univ, sq]
  rw [sum_add_distrib, ← sum_div]
  linarith

open Classical in
/-- Sum the blockwise edit bounds over `Q.parts × Q.parts`, charging irregular fine pairs to
`S.irregularPairs η Q` and regular fine pairs to the `L¹` energy-gap bound. -/
private theorem card_edits_le_of_fine_recoloring [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (R : PairColorSystem κ V)
    (hkeep : ∀ x y, P.part x = P.part y → R.colorOfPair x y = S.colorOfPair x y)
    {g η ξ : ℝ} (hgap : S.energy Q - S.energy P ≤ g) (hξ : 0 ≤ ξ)
    (hblock : ∀ C D : Q.parts, refinementParent hQP C ≠ refinementParent hQP D →
      S.IsRegularPair η C.1 D.1 →
      (#{q ∈ C.1 ×ˢ D.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        (∑ c, (#C.1 * #D.1 : ℝ) *
          |(pairColorDensity S c C.1 D.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1|) / 2 +
          Fintype.card κ * ξ ^ 3 * (#C.1 * #D.1)) :
    (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
      (∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ)) +
        (Fintype.card κ * √g / 2 + Fintype.card κ * ξ ^ 3) * (Fintype.card V : ℝ) ^ 2 := by
  set G : Finset (Q.parts × Q.parts) :=
    {CD ∈ (univ : Finset Q.parts).offDiag |
      refinementParent hQP CD.1 ≠ refinementParent hQP CD.2 ∧ S.IsRegularPair η CD.1.1 CD.2.1}
  have hsub : (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ⊆
      (S.irregularPairs η Q).biUnion (fun AB ↦ AB.1 ×ˢ AB.2) ∪
        G.biUnion (fun CD ↦ {q ∈ CD.1.1 ×ˢ CD.2.1 |
          R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2}) := by
    intro p hp
    have hne := (mem_filter.1 hp).2
    let C : Q.parts := ⟨Q.part p.1, Q.part_mem.2 (mem_univ _)⟩
    let D : Q.parts := ⟨Q.part p.2, Q.part_mem.2 (mem_univ _)⟩
    have hpC : p.1 ∈ C.1 := Q.mem_part_self.2 (mem_univ _)
    have hpD : p.2 ∈ D.1 := Q.mem_part_self.2 (mem_univ _)
    have hpar : refinementParent hQP C ≠ refinementParent hQP D := fun heq ↦ hne <| hkeep p.1 p.2 <|
      by rw [part_eq_refinementParent hQP C hpC, part_eq_refinementParent hQP D hpD, heq]
    have hCD : C ≠ D := fun h ↦ hpar (congrArg _ h)
    by_cases hreg : S.IsRegularPair η C.1 D.1
    · exact mem_union_right _ (mem_biUnion.2 ⟨(C, D),
        mem_filter.2 ⟨mem_offDiag.2 ⟨mem_univ _, mem_univ _, hCD⟩, hpar, hreg⟩,
        mem_filter.2 ⟨mem_product.2 ⟨hpC, hpD⟩, hne⟩⟩)
    · exact mem_union_left _ (mem_biUnion.2 ⟨(C.1, D.1),
        S.mem_irregularPairs.2 ⟨C.2, D.2, Subtype.coe_injective.ne hCD, hreg⟩,
        mem_product.2 ⟨hpC, hpD⟩⟩)
  have hcard : #{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} ≤
      (∑ AB ∈ S.irregularPairs η Q, #AB.1 * #AB.2) +
        ∑ CD ∈ G, #{q ∈ CD.1.1 ×ˢ CD.2.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
    (card_le_card hsub).trans <| (card_union_le _ _).trans <|
      add_le_add (card_biUnion_le.trans_eq (by simp only [card_product])) card_biUnion_le
  calc (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ)
      ≤ (∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ)) +
          ∑ CD ∈ G, (#{q ∈ CD.1.1 ×ˢ CD.2.1 |
            R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) := by exact_mod_cast hcard
    _ ≤ (∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ)) +
          ∑ CD ∈ G, ((∑ c, (#CD.1.1 * #CD.2.1 : ℝ) *
            |(pairColorDensity S c CD.1.1 CD.2.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP CD.1).1 (refinementParent hQP CD.2).1|) /
                2 + Fintype.card κ * ξ ^ 3 * (#CD.1.1 * #CD.2.1)) :=
        add_le_add le_rfl (sum_le_sum fun CD hCD ↦
          hblock CD.1 CD.2 (mem_filter.1 hCD).2.1 (mem_filter.1 hCD).2.2)
    _ ≤ _ := add_le_add le_rfl (S.sum_fine_dev_add_slack_le hQP (filter_subset _ _) hgap hξ)

open Classical in
/-- Transfer the local rectangle count bound from `T C D` (chosen on `order.le C D`) to the glued
system `R` on both orientations of `(C, D)`. -/
private theorem abs_card_filter_fine_sub_le (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (order : LinearOrder Q.parts)
    (T : Q.parts → Q.parts → PairColorSystem κ V) (R : PairColorSystem κ V)
    (hRrev : R.rev = S.rev)
    (hlocal : ∀ C D : Q.parts, order.le C D → ∀ x ∈ C.1, ∀ y ∈ D.1,
      R.colorOfPair x y = (T C D).colorOfPair x y)
    {ω : ℝ}
    (hdisc : ∀ C D : Q.parts, refinementParent hQP C ≠ refinementParent hQP D →
      ∀ c, ∀ C' ⊆ C.1, ∀ D' ⊆ D.1,
        |(#{q ∈ C' ×ˢ D' | (T C D).colorOfPair q.1 q.2 = some c} : ℝ) -
            pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1 *
              (#C' * #D')| ≤ ω * (#C.1 * #D.1))
    (C D : Q.parts) (hCD : refinementParent hQP C ≠ refinementParent hQP D) (c : κ)
    {C' D' : Finset V} (hC' : C' ⊆ C.1) (hD' : D' ⊆ D.1) :
    |(#{q ∈ C' ×ˢ D' | R.colorOfPair q.1 q.2 = some c} : ℝ) -
        pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1 *
          (#C' * #D')| ≤ ω * (#C.1 * #D.1) := by
  let : LinearOrder Q.parts := order
  rcases le_total C D with hle | hle
  · have hfeq : {q ∈ C' ×ˢ D' | R.colorOfPair q.1 q.2 = some c} =
        {q ∈ C' ×ˢ D' | (T C D).colorOfPair q.1 q.2 = some c} :=
      filter_congr fun q hq ↦ by
        rw [hlocal C D hle q.1 (hC' (mem_product.1 hq).1) q.2 (hD' (mem_product.1 hq).2)]
    rw [hfeq]
    exact hdisc C D hCD c C' hC' D' hD'
  · rw [card_filter_colorOfPair_eq_swap R S hRrev C' D' c]
    have hfeq : {q ∈ D' ×ˢ C' | R.colorOfPair q.1 q.2 = some (S.rev c)} =
        {q ∈ D' ×ˢ C' | (T D C).colorOfPair q.1 q.2 = some (S.rev c)} :=
      filter_congr fun q hq ↦ by
        rw [hlocal D C hle q.1 (hD' (mem_product.1 hq).1) q.2 (hC' (mem_product.1 hq).2)]
    have hdswap : (pairColorDensity S (S.rev c) (refinementParent hQP D).1
        (refinementParent hQP C).1 : ℝ) =
          pairColorDensity S c (refinementParent hQP C).1 (refinementParent hQP D).1 := by
      rw [← pairColorDensity_swap S (S.rev c), S.rev_rev]
    rw [hfeq]
    simpa only [hdswap, mul_comm (#D' : ℝ) (#C'), mul_comm (#D.1 : ℝ) (#C.1)] using
      hdisc D C hCD.symm (S.rev c) D' hD' C' hC'

open Classical in
/-- **Off-diagonal regular recoloring across a partition refinement.** Let `Q ≤ P` with energy gap
`S.energy Q - S.energy P ≤ g`. If every fine cell `C ∈ Q.parts` satisfies
`card κ + 2 ≤ ξ ^ 6 * #C` and `2 * (card κ * (η + ξ ^ 3)) ≤ δ ^ 3` with `0 < η`, `0 < ξ`, and
`0 < δ ≤ 1`, then there is a recoloring `R` preserving `S.rev` and all pairs inside coarse cells of
`P` such that every distinct coarse cell pair `(A, B)` is `δ`-regular for `R`, its color densities
change by at most `δ / 2`, and the number of edited ordered pairs is bounded by the `η`-irregular
mass of `Q` plus `(card κ * √g / 2 + card κ * ξ ^ 3) |V|²`. -/
theorem exists_recoloring_regular_offDiag_of_refines [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {g η ξ δ : ℝ}
    (hgap : S.energy Q - S.energy P ≤ g) (hη : 0 < η) (hξ : 0 < ξ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbudget : 2 * ((Fintype.card κ : ℝ) * (η + ξ ^ 3)) ≤ δ ^ 3)
    (hsize : ∀ C ∈ Q.parts, Fintype.card κ + 2 ≤ ξ ^ 6 * #C) :
    ∃ R : PairColorSystem κ V, R.rev = S.rev ∧
      (∀ x y, P.part x = P.part y → R.colorOfPair x y = S.colorOfPair x y) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → R.IsRegularPair δ A B) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity R c A B : ℝ) - pairColorDensity S c A B| ≤ δ / 2) ∧
      (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
        (∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ)) +
          (Fintype.card κ * √g / 2 + Fintype.card κ * ξ ^ 3) * (Fintype.card V : ℝ) ^ 2 := by
  let order : LinearOrder Q.parts := LinearOrder.lift' (Fintype.equivFin Q.parts)
    (Fintype.equivFin Q.parts).injective
  let : LinearOrder Q.parts := order
  choose T hrev hsame hoff using S.exists_fine_pair_recoloring (η := η) hQP hξ hsize
  obtain ⟨R, hRrev, hlocal⟩ := S.exists_cellwise_recoloring Q order T hrev
  set ω : ℝ := Fintype.card κ * (η + ξ ^ 3)
  have hfine := S.abs_card_filter_fine_sub_le hQP order T R hRrev hlocal (ω := ω)
    fun C D hCD c C' hC' D' hD' ↦ by
      simpa only [ω, max_eq_left hη.le] using (hoff C D hCD).1 c C' hC' D' hD'
  have hcoarse (A B : Finset V) (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
      R.IsRegularPair δ A B ∧
        ∀ c, |(pairColorDensity R c A B : ℝ) - pairColorDensity S c A B| ≤ δ / 2 :=
    isRegularPair_of_coarse_discrepancy R (P.nonempty_of_mem_parts hA) (P.nonempty_of_mem_parts hB)
      (P.disjoint hA hB hAB) hδ hδ1 hbudget fun c A' hA' B' hB' ↦
        abs_card_filter_coarse_sub_le hQP R hA hB (p := fun c ↦ (pairColorDensity S c A B : ℝ))
          (ω := ω) c
          (fun C D hCA hDB C' hC' D' hD' ↦ by
            have hCD : refinementParent hQP C ≠ refinementParent hQP D := by
              rw [hCA, hDB]; exact fun h ↦ hAB (congrArg Subtype.val h)
            simpa only [hCA, hDB] using hfine C D hCD c hC' hD') hA' hB'
  have hkeep (x y : V) (hxy : P.part x = P.part y) : R.colorOfPair x y = S.colorOfPair x y := by
    let cell (u : V) : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩
    have hpar : refinementParent hQP (cell x) = refinementParent hQP (cell y) :=
      Subtype.ext (by
        rw [← part_eq_refinementParent hQP (cell x) (Q.mem_part_self.2 (mem_univ x)),
          ← part_eq_refinementParent hQP (cell y) (Q.mem_part_self.2 (mem_univ y)), hxy])
    rcases le_total (cell x) (cell y) with hle | hle
    · rw [hlocal (cell x) (cell y) hle x (Q.mem_part_self.2 (mem_univ x))
        y (Q.mem_part_self.2 (mem_univ y)), hsame _ _ hpar]
    · rw [R.colorOfPair_swap y x, S.colorOfPair_swap y x, hRrev,
        hlocal (cell y) (cell x) hle y (Q.mem_part_self.2 (mem_univ y))
          x (Q.mem_part_self.2 (mem_univ x)), hsame _ _ hpar.symm]
  refine ⟨R, hRrev, hkeep, fun A hA B hB hAB ↦ (hcoarse A B hA hB hAB).1,
    fun A hA B hB hAB ↦ (hcoarse A B hA hB hAB).2,
    S.card_edits_le_of_fine_recoloring hQP R hkeep hgap hξ.le
      (S.card_edits_block_le_of_isRegularPair hQP order T R hRrev hlocal
        fun C D hCD hreg ↦ (hoff C D hCD).2 hreg)⟩

end AcrossRefinement

end PairColorSystem

/-! ### Scheduled regular approximation of lower skeletons -/

/-- Upper bound on the number of vertex cells in the scheduled regular approximation of a
`k`-color pair system within edit fraction `ε` at schedule `F` from `l` initial cells. It dominates
both the coarse cell count of strong equitable regularity and the host-size threshold ensuring all
fine cells have size at least `⌈(k + 2) / ξ ^ 6⌉₊`, so hosts smaller than this bound are handled by
the singleton partition `⊥`. -/
noncomputable def lowerSkeletonApproximationBound (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) : ℕ :=
  let δ : ℕ → ℝ := fun m ↦ min (F (m + (k + 1))) (min (ε / 4) (1 / 2))
  let η : ℕ → ℝ := fun m ↦ δ m ^ 3 / (4 * (k + 1))
  let ξ : ℕ → ℝ := fun m ↦ δ m / (4 * (k + 1))
  let g : ℝ := (ε / (4 * (k + 1))) ^ 2
  let M : ℕ := strongPairColorRegularityBound g η (max ⌈4 / ε⌉₊ 1 * max l 1)
  max 2 (max M ((range (M + 1)).sup fun m ↦
    ⌈((k : ℝ) + 2) / ξ m ^ 6⌉₊ * equitablePairColorRegularityBound (η m) m))

/-- Unfolding lemma for `TauCeti.lowerSkeletonApproximationBound`. -/
theorem lowerSkeletonApproximationBound_def (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) :
    lowerSkeletonApproximationBound k ε F l =
      let δ : ℕ → ℝ := fun m ↦ min (F (m + (k + 1))) (min (ε / 4) (1 / 2))
      let η : ℕ → ℝ := fun m ↦ δ m ^ 3 / (4 * (k + 1))
      let ξ : ℕ → ℝ := fun m ↦ δ m / (4 * (k + 1))
      let g : ℝ := (ε / (4 * (k + 1))) ^ 2
      let M : ℕ := strongPairColorRegularityBound g η (max ⌈4 / ε⌉₊ 1 * max l 1)
      max 2 (max M ((range (M + 1)).sup fun m ↦
        ⌈((k : ℝ) + 2) / ξ m ^ 6⌉₊ * equitablePairColorRegularityBound (η m) m)) :=
  (rfl)

/-- `lowerSkeletonApproximationBound` is always at least `2`. -/
theorem two_le_lowerSkeletonApproximationBound (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) :
    2 ≤ lowerSkeletonApproximationBound k ε F l :=
  le_max_left _ _

/-- `lowerSkeletonApproximationBound` is always positive. -/
theorem lowerSkeletonApproximationBound_pos (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) :
    0 < lowerSkeletonApproximationBound k ε F l :=
  Nat.lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_lowerSkeletonApproximationBound k ε F l)

/-- `lowerSkeletonApproximationBound` is at least the initial cell count `l`. -/
theorem le_lowerSkeletonApproximationBound (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) :
    l ≤ lowerSkeletonApproximationBound k ε F l := by
  rw [lowerSkeletonApproximationBound_def]
  exact (le_max_left l 1).trans <|
    (Nat.le_mul_of_pos_left _ (by positivity : 0 < max ⌈4 / ε⌉₊ 1)).trans <|
      (le_strongPairColorRegularityBound _ _ _).trans <|
        (le_max_left _ _).trans (le_max_right _ _)

/-- `lowerSkeletonApproximationBound` is monotone in the initial cell count `l`. -/
theorem monotone_lowerSkeletonApproximationBound (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) :
    Monotone (lowerSkeletonApproximationBound k ε F) := fun l₁ l₂ h ↦ by
  simp only [lowerSkeletonApproximationBound_def]
  have hM : strongPairColorRegularityBound ((ε / (4 * (k + 1))) ^ 2)
      (fun m ↦ min (F (m + (k + 1))) (min (ε / 4) (1 / 2)) ^ 3 / (4 * (k + 1)))
      (max ⌈4 / ε⌉₊ 1 * max l₁ 1) ≤
      strongPairColorRegularityBound ((ε / (4 * (k + 1))) ^ 2)
      (fun m ↦ min (F (m + (k + 1))) (min (ε / 4) (1 / 2)) ^ 3 / (4 * (k + 1)))
      (max ⌈4 / ε⌉₊ 1 * max l₂ 1) :=
    monotone_strongPairColorRegularityBound _ _
      (Nat.mul_le_mul_left (max ⌈4 / ε⌉₊ 1) (max_le_max h (le_rfl : 1 ≤ 1)))
  exact max_le_max le_rfl (max_le_max hM (Finset.sup_mono (range_mono (Nat.succ_le_succ hM))))

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- Diagonal cleanup on an equipartition with at least `⌈4 / ε⌉₊` cells edits at most
`(ε / 4) |V|²` ordered pairs. -/
private theorem sum_card_mul_pred_le_of_isEquipartition {P : Finpartition (univ : Finset V)}
    (hP : P.IsEquipartition) {ε : ℝ} (hε : 0 < ε) (hm : ⌈4 / ε⌉₊ ≤ #P.parts) :
    ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : ℝ) ≤ (ε / 4) * (Fintype.card V : ℝ) ^ 2 := by
  have hm_pos : 0 < #P.parts := (Nat.ceil_pos.2 (div_pos (by norm_num) hε)).trans_le hm
  have hm_pos' : (0 : ℝ) < #P.parts := Nat.cast_pos.2 hm_pos
  have hnat : ∑ A ∈ P.parts, #A * (#A - 1) ≤ Fintype.card V * (Fintype.card V / #P.parts) := by
    calc ∑ A ∈ P.parts, #A * (#A - 1)
        ≤ ∑ A ∈ P.parts, #A * (Fintype.card V / #P.parts) := sum_le_sum fun A hA ↦ by
          have hle := hP.card_part_le_average_add_one hA
          rw [card_univ] at hle
          exact Nat.mul_le_mul_left _ (Nat.sub_le_of_le_add hle)
      _ = Fintype.card V * (Fintype.card V / #P.parts) := by
          rw [← sum_mul, P.sum_card_parts, card_univ]
  have hq : ((Fintype.card V / #P.parts : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / #P.parts :=
    (le_div_iff₀' hm_pos').2 (mod_cast Nat.mul_div_le (Fintype.card V) #P.parts)
  have hdiv : (Fintype.card V : ℝ) / #P.parts ≤ (ε / 4) * Fintype.card V := by
    rw [div_le_iff₀ hm_pos']
    have h4 : 4 ≤ (#P.parts : ℝ) * ε :=
      (div_le_iff₀ hε).1 ((Nat.le_ceil _).trans (Nat.cast_le.2 hm))
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
  calc ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : ℝ)
      ≤ (Fintype.card V : ℝ) * ((Fintype.card V / #P.parts : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) / #P.parts) := by gcongr
    _ ≤ (Fintype.card V : ℝ) * ((ε / 4) * Fintype.card V) := by gcongr
    _ = (ε / 4) * (Fintype.card V : ℝ) ^ 2 := by ring

/-- Arithmetic inequalities relating the fine tolerances `η`, `ξ`, the energy-gap threshold `g`,
and the coarse regularity target `δ`. -/
private theorem approx_params_bounds (k : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hδ_ε : δ ≤ ε / 4) (hδ_half : δ ≤ 1 / 2) :
    let D : ℝ := 4 * (k + 1)
    let η : ℝ := δ ^ 3 / D
    let ξ : ℝ := δ / D
    let g : ℝ := (ε / D) ^ 2
    0 < η ∧ 0 < ξ ∧ ξ ^ 6 ≤ δ ∧
      2 * ((k : ℝ) * (η + ξ ^ 3)) ≤ δ ^ 3 ∧
      η + (k : ℝ) * √g / 2 + (k : ℝ) * ξ ^ 3 ≤ 3 * ε / 4 := by
  intro D η ξ g
  have hD4 : 4 ≤ D := by dsimp [D]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hD0 : 0 < D := by linarith
  have hη : 0 < η := div_pos (pow_pos hδ 3) hD0
  have hξ : 0 < ξ := div_pos hδ hD0
  have hξ_le_δ : ξ ≤ δ := div_le_self hδ.le (by linarith)
  have hξ6 : ξ ^ 6 ≤ δ :=
    (pow_le_of_le_one hξ.le (by linarith) (by norm_num)).trans hξ_le_δ
  have hξ3_le_η : ξ ^ 3 ≤ η := by
    dsimp [ξ, η]
    rw [div_pow]
    have hD3 : D ≤ D ^ 3 := by
      calc D = D * 1 := (mul_one D).symm
        _ ≤ D * D ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hD0.le
        _ = D ^ 3 := by ring
    exact div_le_div_of_nonneg_left (pow_pos hδ 3).le hD0 hD3
  have hbud : 2 * ((k : ℝ) * (η + ξ ^ 3)) ≤ δ ^ 3 := by
    calc 2 * ((k : ℝ) * (η + ξ ^ 3))
        ≤ 2 * (((k : ℝ) + 1) * (2 * η)) := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      _ = D * (δ ^ 3 / D) := by dsimp [D, η]; ring
      _ = δ ^ 3 := mul_div_cancel₀ _ hD0.ne'
  have hδ3 : δ ^ 3 ≤ ε / 4 :=
    (pow_le_of_le_one hδ.le (by linarith) (by norm_num)).trans hδ_ε
  have h₁ : η ≤ ε / 16 := by
    dsimp [η]
    exact (div_le_div_of_nonneg_left (pow_pos hδ 3).le (by norm_num : (0 : ℝ) < 4) hD4).trans
      (by linarith)
  have h₂ : (k : ℝ) * √g / 2 ≤ ε / 8 := by
    have hsqrt : √g = ε / D := Real.sqrt_sq (by positivity)
    rw [hsqrt]
    have hle : (k : ℝ) * (ε / D) ≤ ((k : ℝ) + 1) * (ε / D) := by gcongr; linarith
    have heq : ((k : ℝ) + 1) * (ε / D) = ε / 4 := by dsimp [D]; field_simp
    linarith
  have h₃ : (k : ℝ) * ξ ^ 3 ≤ ε / 16 := by
    have hle : (k : ℝ) * ξ ^ 3 ≤ ((k : ℝ) + 1) * η :=
      mul_le_mul (by linarith) hξ3_le_η (by positivity) (by positivity)
    have heq : ((k : ℝ) + 1) * η = δ ^ 3 / 4 := by dsimp [η, D]; field_simp
    linarith
  exact ⟨hη, hξ, hξ6, hbud, by linarith⟩

open Classical in
/-- Small hosts (`|V| ≤ B`) satisfy scheduled lower-skeleton regularity via the singleton partition
`⊥` with zero edits. -/
private theorem exists_bot_lowerSkeletonRegular [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m)
    {B : ℕ} (hV : Fintype.card V ≤ B) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧ #P.parts ≤ B ∧ T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity T c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤
          min (F (#P.parts + Fintype.card (Option κ))) ε) ∧
      (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  refine ⟨⊥, S.fillDiagonal ⊥, bot_le, bot_isEquipartition _, ?_,
    funext (S.fillDiagonal_rev ⊥),
    PairSkeleton3.lowerSkeletonRegular_iff.2 (PairSkeleton3.isPairColorRegular_bot (hF _) _),
    ?_, ?_⟩
  · simpa [card_bot, card_univ] using hV
  · intro A hA B hB hAB c
    rw [S.pairColorDensity_fillDiagonal_of_ne ⊥ hA hB hAB subset_rfl subset_rfl c]
    cases c <;> simpa using le_min (hF _).le hε.le
  · rw [S.card_fillDiagonal_colorOfPair_ne ⊥]
    have hzero : ∑ A ∈ (⊥ : Finpartition (univ : Finset V)).parts, #A * (#A - 1) = 0 :=
      sum_eq_zero fun A hA ↦ by obtain ⟨v, -, rfl⟩ := mem_bot_iff.1 hA; simp
    rw [hzero, Nat.cast_zero]
    positivity

open Classical in
/-- Combine an off-diagonal `δ`-regular recoloring `R` on an equipartition `P` with
`R.fillDiagonal P` to obtain `LowerSkeletonRegular F`, off-diagonal density stability, and total
edit count at most `ε |V|²`. -/
private theorem fillDiagonal_lowerSkeletonRegular_of_offDiag [Fintype κ]
    (S R : PairColorSystem κ V) {P : Finpartition (univ : Finset V)} (hP : P.IsEquipartition)
    (hRrev : R.rev = S.rev) {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m)
    (hδF : δ ≤ F (#P.parts + Fintype.card (Option κ))) (hδε : δ ≤ ε / 4)
    (hceilP : ⌈4 / ε⌉₊ ≤ #P.parts) (hPlarge : ∀ A ∈ P.parts, 1 < δ * #A)
    (hRreg : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → R.IsRegularPair δ A B)
    (hRdens : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
      |(pairColorDensity R c A B : ℝ) - pairColorDensity S c A B| ≤ δ / 2)
    (hoff : (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
      (3 * ε / 4) * (Fintype.card V : ℝ) ^ 2) :
    (R.fillDiagonal P).rev = Option.map S.rev ∧
      (⟨P, R.fillDiagonal P⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity (R.fillDiagonal P) c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤
          min (F (#P.parts + Fintype.card (Option κ))) ε) ∧
      (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some} : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  refine ⟨funext fun c ↦ by simp only [fillDiagonal_rev, hRrev],
    PairSkeleton3.lowerSkeletonRegular_iff.2
      ((R.isPairColorRegular_fillDiagonal P hPlarge hRreg).mono hδF), ?_, ?_⟩
  · intro A hA B hB hAB c
    rw [R.pairColorDensity_fillDiagonal_of_ne P hA hB hAB subset_rfl subset_rfl]
    cases c with
    | none => simpa using le_min (hF _).le hε.le
    | some c =>
      exact (hRdens A hA B hB hAB c).trans (le_min (by linarith) (by linarith))
  · have hsub : (univ.filter fun p : V × V ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some) ⊆
        (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ∪
          (univ.filter fun p : V × V ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
            (R.colorOfPair p.1 p.2).map some) := fun p hp ↦ by
      rw [mem_union, mem_filter, mem_filter]
      have hp' := (mem_filter.1 hp).2
      by_cases h : R.colorOfPair p.1 p.2 = S.colorOfPair p.1 p.2
      · exact Or.inr ⟨mem_univ _, h ▸ hp'⟩
      · exact Or.inl ⟨mem_univ _, h⟩
    have hdiag : (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (R.colorOfPair p.1 p.2).map some} : ℝ) ≤ (ε / 4) * (Fintype.card V : ℝ) ^ 2 := by
      rw [R.card_fillDiagonal_colorOfPair_ne P]
      exact sum_card_mul_pred_le_of_isEquipartition hP hε hceilP
    have hunion : (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
        (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) +
          #{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
            (R.colorOfPair p.1 p.2).map some} :=
      mod_cast (card_le_card hsub).trans (card_union_le _ _)
    linarith

/-- Deduce fine and coarse cell-size lower bounds from `#Q.parts` equitability when `|V|` exceeds
the scheduled host-size threshold. -/
private theorem fine_and_coarse_size_bounds (k : ℕ) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (hQ : Q.IsEquipartition) (hV : 0 < Fintype.card V)
    {δ ξ : ℝ} (hδ0 : 0 < δ) (hξ0 : 0 < ξ) (hξ6 : ξ ^ 6 ≤ δ)
    (hsup : ⌈((k : ℝ) + 2) / ξ ^ 6⌉₊ * #Q.parts ≤ Fintype.card V) :
    (∀ C ∈ Q.parts, (k : ℝ) + 2 ≤ ξ ^ 6 * #C) ∧ ∀ A ∈ P.parts, 1 < δ * #A := by
  have hQpos : 0 < #Q.parts :=
    (Q.parts_nonempty (card_pos.1 (by rwa [card_univ])).ne_empty).card_pos
  have hfine (C : Finset V) (hC : C ∈ Q.parts) : (k : ℝ) + 2 ≤ ξ ^ 6 * #C := by
    have havg := hQ.average_le_card_part hC
    rw [card_univ] at havg
    have hC_ge : ⌈((k : ℝ) + 2) / ξ ^ 6⌉₊ ≤ #C :=
      ((Nat.le_div_iff_mul_le hQpos).2 hsup).trans havg
    exact (div_le_iff₀' (pow_pos hξ0 6)).1 ((Nat.le_ceil _).trans (Nat.cast_le.2 hC_ge))
  refine ⟨hfine, fun A hA ↦ ?_⟩
  obtain ⟨C, hC, hCA⟩ := exists_le_of_le hQP hA
  have h₁ := hfine C hC
  have h₂ : ξ ^ 6 * #C ≤ δ * #A :=
    mul_le_mul hξ6 (Nat.cast_le.2 (card_le_card hCA)) (by positivity) hδ0.le
  linarith [Nat.cast_nonneg (α := ℝ) k]

open Classical in
/-- **Scheduled regular approximation of a lower skeleton refining a seed.** Given an equipartition
`P₀` of `V`, an edit budget `ε > 0`, and a positive schedule `F : ℕ → ℝ`, there exist a refining
equipartition `P ≤ P₀` with `#P.parts ≤ lowerSkeletonApproximationBound (card κ) ε F #P₀.parts` and
a pair-color system `T` on `Option κ` with reversal `Option.map S.rev` such that `(P, T)` satisfies
`PairSkeleton3.LowerSkeletonRegular F`, off-diagonal block densities on `P` change by at most
`min (F (#P.parts + card (Option κ))) ε`, and `T` differs from `S` (after embedding `κ` into
`Option κ`) on at most `ε |V|²` ordered vertex pairs. -/
theorem exists_refining_equipartition_lowerSkeletonRegular [Fintype κ]
    (S : PairColorSystem κ V) (P₀ : Finpartition (univ : Finset V))
    (hP₀ : P₀.IsEquipartition) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ lowerSkeletonApproximationBound (Fintype.card κ) ε F #P₀.parts ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity T c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤
          min (F (#P.parts + Fintype.card (Option κ))) ε) ∧
      (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  set k := Fintype.card κ
  set B := lowerSkeletonApproximationBound k ε F #P₀.parts
  obtain hsmall | hlarge := lt_or_ge (Fintype.card V) B
  · exact S.exists_bot_lowerSkeletonRegular P₀ hε hF hsmall.le
  let δ (m : ℕ) : ℝ := min (F (m + (k + 1))) (min (ε / 4) (1 / 2))
  let η (m : ℕ) : ℝ := δ m ^ 3 / (4 * (k + 1))
  let ξ (m : ℕ) : ℝ := δ m / (4 * (k + 1))
  let g : ℝ := (ε / (4 * (k + 1))) ^ 2
  let a : ℕ := max ⌈4 / ε⌉₊ 1
  let M : ℕ := strongPairColorRegularityBound g η (a * max #P₀.parts 1)
  have hδ0 (m : ℕ) : 0 < δ m := lt_min (hF _) (lt_min (by positivity) (by norm_num))
  have hpar (m : ℕ) := approx_params_bounds k hε (hδ0 m)
    ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
  have hV2 : 2 ≤ Fintype.card V := (two_le_lowerSkeletonApproximationBound _ _ _ _).trans hlarge
  have hP₀_pos : 1 ≤ #P₀.parts :=
    (P₀.parts_nonempty (card_pos.1 (by rw [card_univ]; omega)).ne_empty).card_pos
  have haM : a * #P₀.parts ≤ #(univ : Finset V) := by
    rw [card_univ, ← max_eq_left hP₀_pos]
    exact (le_strongPairColorRegularityBound g η _).trans
      ((le_max_left M _).trans ((le_max_right 2 _).trans hlarge))
  obtain ⟨P₁, hP₁, hP₁_card, hP₁P₀, -⟩ :=
    hP₀.exists_refining_equipartition_card_eq_mul P₀ le_rfl (by positivity : a ≠ 0) haM
  obtain ⟨P, Q, hQP, hPP₁, hP, hQ, hPM', hQcard, hirreg, hgap⟩ :=
    S.exists_strong_refining_equipartition_sum_irregularPairs_le P₁ hP₁ (by positivity : 0 < g)
      fun m ↦ (hpar m).1
  have hPM : #P.parts ≤ M := by rwa [hP₁_card, ← max_eq_left hP₀_pos] at hPM'
  obtain ⟨hfine_size, hPlarge⟩ := fine_and_coarse_size_bounds k hQP hQ (by omega) (hδ0 #P.parts)
    (hpar #P.parts).2.1 (hpar #P.parts).2.2.1 <|
    (Nat.mul_le_mul_left _ hQcard).trans <|
      (le_sup (f := fun m ↦ ⌈((k : ℝ) + 2) / ξ m ^ 6⌉₊ *
        equitablePairColorRegularityBound (η m) m) (mem_range.2 (Nat.lt_succ_of_le hPM))).trans <|
        (le_max_right M _).trans ((le_max_right 2 _).trans hlarge)
  obtain ⟨R, hRrev, -, hRreg, hRdens, hRedit⟩ := S.exists_recoloring_regular_offDiag_of_refines hQP
    hgap (hpar #P.parts).1 (hpar #P.parts).2.1 (hδ0 #P.parts)
    (((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num))
    (hpar #P.parts).2.2.2.1 hfine_size
  refine ⟨P, R.fillDiagonal P, hPP₁.trans hP₁P₀, hP,
    hPM.trans ((le_max_left M _).trans (le_max_right 2 _)),
    fillDiagonal_lowerSkeletonRegular_of_offDiag S R hP hRrev hε (hδ0 #P.parts) hF
      (by rw [Fintype.card_option]; exact min_le_left _ _)
      ((min_le_right _ _).trans (min_le_left _ _))
      (((le_max_left ⌈4 / ε⌉₊ 1).trans (Nat.le_mul_of_pos_right a hP₀_pos)).trans
        (hP₁_card ▸ card_mono hPP₁))
      hPlarge hRreg hRdens
      (hRedit.trans (by
        have hsum := (hpar #P.parts).2.2.2.2
        nlinarith [hirreg, sq_nonneg (Fintype.card V : ℝ)]))⟩

open Classical in
/-- **Scheduled regular approximation of a lower skeleton.** Given an edit budget `ε > 0`, a
positive schedule `F : ℕ → ℝ`, and `l ≤ |V|`, there exist an equipartition `P` of `V` with
`l ≤ #P.parts ≤ lowerSkeletonApproximationBound (card κ) ε F l` and a pair-color system `T` on
`Option κ` with reversal `Option.map S.rev` such that `(P, T)` satisfies
`PairSkeleton3.LowerSkeletonRegular F`, off-diagonal block densities on `P` change by at most
`min (F (#P.parts + card (Option κ))) ε`, and `T` edits at most `ε |V|²` ordered vertex pairs. -/
theorem exists_equipartition_lowerSkeletonRegular [Fintype κ]
    (S : PairColorSystem κ V) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m)
    {l : ℕ} (hl : l ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P.IsEquipartition ∧ l ≤ #P.parts ∧
      #P.parts ≤ lowerSkeletonApproximationBound (Fintype.card κ) ε F l ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity T c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤
          min (F (#P.parts + Fintype.card (Option κ))) ε) ∧
      (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  by_cases hsize : max l 1 ≤ Fintype.card V
  · obtain ⟨P₀, hP₀, hcard⟩ := exists_equipartition_card_eq (univ : Finset V)
      (by positivity : max l 1 ≠ 0) (by rwa [card_univ])
    obtain ⟨P, T, hPP₀, hP, hPcard, hrev, hreg, hdens, hedit⟩ :=
      S.exists_refining_equipartition_lowerSkeletonRegular P₀ hP₀ hε hF
    refine ⟨P, T, hP, (le_max_left l 1).trans (hcard ▸ card_mono hPP₀), ?_, hrev, hreg, hdens,
      hedit⟩
    simpa [hcard, lowerSkeletonApproximationBound_def, max_assoc] using hPcard
  · have hn : Fintype.card V = 0 := by omega
    have hl0 : l = 0 := by omega
    obtain ⟨P, T, -, hP, hPcard, hrev, hreg, hdens, hedit⟩ :=
      S.exists_refining_equipartition_lowerSkeletonRegular ⊥ (bot_isEquipartition _) hε hF
    refine ⟨P, T, hP, by omega, ?_, hrev, hreg, hdens, hedit⟩
    simpa [card_bot, card_univ, hn, hl0] using hPcard

end PairColorSystem

end TauCeti
