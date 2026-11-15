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
edit tolerance `α > 0`, and a positive error schedule `F : ℕ → ℝ`, this file constructs an
exact equitable refinement `P ≤ P₀` of bounded size together with a recolored pair-color system
`T` over `Option κ` such that the lower skeleton `⟨P, T⟩` is `F`-regular at its own lower
complexity and `T` disagrees with `some ∘ S.color` on at most `α |V|²` ordered distinct pairs.

Unlike single-scale cleanup (`PairColorSystem.exists_recoloring_isPairColorRegular`), which takes
a constant tolerance `ε` and cannot refine `P` without shrinking `F (#P.parts + card κ + 1)`,
schedule-governed regular approximation uses two-scale strong regularity
(`PairColorSystem.exists_strong_refining_equipartitions`) to obtain nested equipartitions
`Q ≤ P ≤ P₀` with bounded energy gap `S.energy Q - S.energy P` and `Q` regular at a fine
tolerance governed by `F (#P.parts + card κ + 1)`. By
`PairColorSystem.sum_abs_pairColorDensity_sub_le`, the fine block densities of `S` are close in
`L¹` to the coarse block densities on `P`. On each canonical off-diagonal fine block `A' ×ˢ B'`,
`PairColorSystem.exists_coupled_recoloring_abs_card_filter_sub_le` adjusts regular fine blocks
toward `pairColorDensity S · A B` while editing few pairs and replaces irregular fine blocks by
quasi-random colorings. Summing rectangle discrepancies across the fine subblocks of each coarse
pair `(A, B)` makes every off-diagonal coarse pair regular, and `PairColorSystem.fillDiagonal`
cleans up within-cell pairs.

## Main definitions

* `TauCeti.pairApproximationTolerance`: fine regularity tolerance for a coarse partition size.
* `TauCeti.pairApproximationPartsBound`: part-count bound for the returned coarse equipartition.
* `TauCeti.pairApproximationBound`: host-size threshold for pair-color regular approximation.

## Main results

* `TauCeti.PairColorSystem.exists_refining_equipartition_lowerSkeletonRegular`: strong regular
  approximation of a pair-color system refining a seed equipartition.

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

/-- The fine pair-regularity tolerance requested over a coarse partition with `t` cells, for a
palette of `q` colors, edit budget `α`, and schedule `F`. The `t + q + 1` argument accounts for
the fresh diagonal color added by `PairColorSystem.fillDiagonal`. -/
noncomputable def pairApproximationTolerance (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (t : ℕ) : ℝ :=
  min (α / (4 * ((max q 1 : ℕ) + 1)))
    ((min (1 / 2) (F (t + q + 1))) ^ 3 / (4 * (max q 1 : ℕ)))

/-- Unfolding lemma for `TauCeti.pairApproximationTolerance`. -/
theorem pairApproximationTolerance_def (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (t : ℕ) :
    pairApproximationTolerance q α F t =
      min (α / (4 * ((max q 1 : ℕ) + 1)))
        ((min (1 / 2) (F (t + q + 1))) ^ 3 / (4 * (max q 1 : ℕ))) :=
  (rfl)

/-- For positive `α` and a positive schedule `F`, `pairApproximationTolerance` is positive. -/
theorem pairApproximationTolerance_pos (q : ℕ) {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (t : ℕ) :
    0 < pairApproximationTolerance q α F t := by
  rw [pairApproximationTolerance_def]
  have hδ : 0 < min (1 / 2) (F (t + q + 1)) := lt_min (by norm_num) (hF _)
  exact lt_min (by positivity) (by positivity)

/-- `pairApproximationTolerance` never exceeds `1 / 32`. -/
theorem pairApproximationTolerance_le_one_div_32 (q : ℕ) (α : ℝ) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (t : ℕ) :
    pairApproximationTolerance q α F t ≤ 1 / 32 := by
  have hq : (1 : ℝ) ≤ (max q 1 : ℕ) := by exact_mod_cast le_max_right q 1
  have hδ0 : 0 ≤ min (1 / 2) (F (t + q + 1)) := le_min (by norm_num) (hF _).le
  have hδ : min (1 / 2) (F (t + q + 1)) ≤ 1 / 2 := min_le_left _ _
  calc pairApproximationTolerance q α F t
      ≤ (min (1 / 2) (F (t + q + 1))) ^ 3 / (4 * (max q 1 : ℕ)) := min_le_right _ _
    _ ≤ (1 / 2 : ℝ) ^ 3 / (4 * 1) :=
        div_le_div₀ (by norm_num) (pow_le_pow_left₀ hδ0 hδ 3) (by norm_num) (by linarith)
    _ = 1 / 32 := by norm_num

/-- Upper bound on the number of cells of the coarse equipartition in strong pair-color
approximation, starting from an equipartition with `l₀` cells. -/
noncomputable def pairApproximationPartsBound (q : ℕ) (α : ℝ) (F : ℕ → ℝ)
    (l₀ : ℕ) : ℕ :=
  strongPairColorRegularityBound ((α / (4 * (max q 1 : ℕ))) ^ 2)
    (pairApproximationTolerance q α F) (max 1 ⌈4 / α⌉₊ * l₀)

/-- Unfolding lemma for `TauCeti.pairApproximationPartsBound`. -/
theorem pairApproximationPartsBound_def (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    pairApproximationPartsBound q α F l₀ =
      strongPairColorRegularityBound ((α / (4 * (max q 1 : ℕ))) ^ 2)
        (pairApproximationTolerance q α F) (max 1 ⌈4 / α⌉₊ * l₀) :=
  (rfl)

/-- `pairApproximationPartsBound` is monotone in the starting cell count `l₀`. -/
theorem pairApproximationPartsBound_mono (q : ℕ) (α : ℝ) (F : ℕ → ℝ) :
    Monotone (pairApproximationPartsBound q α F) := fun _ _ h ↦
  strongPairColorRegularityBound_mono _ _ (Nat.mul_le_mul_left _ h)

/-- For positive parameters, `pairApproximationPartsBound` is at least
`max 1 ⌈4 / α⌉₊ * l₀`. -/
theorem mul_le_pairApproximationPartsBound (q : ℕ) {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (l₀ : ℕ) :
    max 1 ⌈4 / α⌉₊ * l₀ ≤ pairApproximationPartsBound q α F l₀ :=
  le_strongPairColorRegularityBound _ (pairApproximationTolerance_pos q hα hF) _

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
  let M := pairApproximationPartsBound q α F l₀
  max 1 (strongPairColorStepBound (pairApproximationTolerance q α F) M) *
    ((range (M + 1)).sup
      (fun t ↦ ⌈(q + 3 : ℝ) / (pairApproximationTolerance q α F t) ^ 2⌉₊) + 1)

/-- Unfolding lemma for `TauCeti.pairApproximationBound`. -/
theorem pairApproximationBound_def (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    pairApproximationBound q α F l₀ =
      max 1 (strongPairColorStepBound (pairApproximationTolerance q α F)
          (pairApproximationPartsBound q α F l₀)) *
        ((range (pairApproximationPartsBound q α F l₀ + 1)).sup
          (fun t ↦ ⌈(q + 3 : ℝ) / (pairApproximationTolerance q α F t) ^ 2⌉₊) + 1) :=
  (rfl)

/-- `pairApproximationBound` is monotone in `l₀`. -/
theorem pairApproximationBound_mono (q : ℕ) (α : ℝ) (F : ℕ → ℝ) :
    Monotone (pairApproximationBound q α F) := fun _ _ h ↦ by
  have hM := pairApproximationPartsBound_mono q α F h
  refine Nat.mul_le_mul (max_le_max le_rfl (strongPairColorStepBound_mono _ hM))
    (Nat.succ_le_succ (sup_mono (range_mono (Nat.succ_le_succ hM))))

/-- For positive parameters, `pairApproximationBound` bounds `pairApproximationPartsBound`. -/
theorem pairApproximationPartsBound_le_pairApproximationBound (q : ℕ) {α : ℝ} (hα : 0 < α)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (l₀ : ℕ) :
    pairApproximationPartsBound q α F l₀ ≤ pairApproximationBound q α F l₀ :=
  calc pairApproximationPartsBound q α F l₀
      ≤ strongPairColorStepBound (pairApproximationTolerance q α F)
          (pairApproximationPartsBound q α F l₀) :=
        le_strongPairColorStepBound (pairApproximationTolerance_pos q hα hF) _
    _ ≤ max 1 (strongPairColorStepBound (pairApproximationTolerance q α F)
          (pairApproximationPartsBound q α F l₀)) :=
        le_max_right _ _
    _ ≤ pairApproximationBound q α F l₀ :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

namespace PairColorSystem

/-! ### Assembling coarse regularity and bounding edits -/

section Assembly

open Classical in
/-- Summing rectangle discrepancies of `T_off` over the fine subblocks `A' ×ˢ B'` of a coarse
block `A ×ˢ B` yields coarse `δ`-regularity once `2 * τ ≤ δ ^ 3`. -/
private theorem isRegularPair_of_fine_discrepancy {κ V : Type*} [Fintype V] [DecidableEq V]
    {T_off : PairColorSystem κ V} {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (p : κ → ℝ) {τ δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hτδ : 2 * τ ≤ δ ^ 3)
    (hdisc : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
      ∀ s' ⊆ A', ∀ t' ⊆ B', ∀ d : κ,
        |(#{q ∈ s' ×ˢ t' | T_off.colorOfPair q.1 q.2 = some d} : ℝ) - p d * (#s' * #t')| ≤
          τ * (#A' * #B')) :
    T_off.IsRegularPair δ A B := by
  classical
  have hdisj : Disjoint A B := P.disjoint hA hB hAB
  have hApos : (0 : ℝ) < #A := Nat.cast_pos.2 (P.nonempty_of_mem_parts hA).card_pos
  have hBpos : (0 : ℝ) < #B := Nat.cast_pos.2 (P.nonempty_of_mem_parts hB).card_pos
  set QA := {C ∈ Q.parts | C ⊆ A}
  set QB := {C ∈ Q.parts | C ⊆ B}
  have hQA_disj : (QA : Set (Finset V)).PairwiseDisjoint id :=
    Q.supIndep.pairwiseDisjoint.subset (filter_subset _ _)
  have hQB_disj : (QB : Set (Finset V)).PairwiseDisjoint id :=
    Q.supIndep.pairwiseDisjoint.subset (filter_subset _ _)
  have hQA_union : QA.biUnion id = A := biUnion_filter_subset_eq_of_le hQP hA
  have hQB_union : QB.biUnion id = B := biUnion_filter_subset_eq_of_le hQP hB
  -- Sum the fine rectangle discrepancies to obtain a rectangle discrepancy on `A ×ˢ B`.
  have hrect_disc (X Y : Finset V) (hXA : X ⊆ A) (hYB : Y ⊆ B) (d : κ) :
      |(pairColorDensity T_off d X Y : ℝ) - p d| * (#X * #Y) ≤ τ * (#A * #B) := by
    have hX_u : QA.biUnion (fun C ↦ X ∩ C) = X := by
      rw [← inter_biUnion]
      exact (congrArg (X ∩ ·) hQA_union).trans (inter_eq_left.2 hXA)
    have hY_u : QB.biUnion (fun C ↦ Y ∩ C) = Y := by
      rw [← inter_biUnion]
      exact (congrArg (Y ∩ ·) hQB_union).trans (inter_eq_left.2 hYB)
    have hXsum : ∑ A' ∈ QA, (#(X ∩ A') : ℝ) = #X := by
      exact_mod_cast (card_biUnion (fun C hC D hD hCD ↦
        (hQA_disj hC hD hCD).mono inter_subset_right inter_subset_right)).symm.trans
        (congrArg card hX_u)
    have hYsum : ∑ B' ∈ QB, (#(Y ∩ B') : ℝ) = #Y := by
      exact_mod_cast (card_biUnion (fun C hC D hD hCD ↦
        (hQB_disj hC hD hCD).mono inter_subset_right inter_subset_right)).symm.trans
        (congrArg card hY_u)
    have hAsum : ∑ A' ∈ QA, (#A' : ℝ) = #A := by
      exact_mod_cast (card_biUnion hQA_disj).symm.trans (congrArg card hQA_union)
    have hBsum : ∑ B' ∈ QB, (#B' : ℝ) = #B := by
      exact_mod_cast (card_biUnion hQB_disj).symm.trans (congrArg card hQB_union)
    have hXY_union : (QA ×ˢ QB).biUnion (fun u ↦ (X ∩ u.1) ×ˢ (Y ∩ u.2)) = X ×ˢ Y := by
      ext q
      simp only [mem_biUnion, mem_product, mem_inter]
      refine ⟨fun ⟨_, _, ⟨hqX, _⟩, hqY, _⟩ ↦ ⟨hqX, hqY⟩, fun ⟨hqX, hqY⟩ ↦ ?_⟩
      obtain ⟨A', hA', hqA'⟩ := mem_biUnion.1 (hQA_union.symm ▸ hXA hqX)
      obtain ⟨B', hB', hqB'⟩ := mem_biUnion.1 (hQB_union.symm ▸ hYB hqY)
      exact ⟨(A', B'), ⟨hA', hB'⟩, ⟨hqX, hqA'⟩, hqY, hqB'⟩
    have hXY_disj : ((QA ×ˢ QB : Finset _) : Set _).PairwiseDisjoint
        (fun u : Finset V × Finset V ↦ (X ∩ u.1) ×ˢ (Y ∩ u.2)) := by
      intro u hu v hv huv
      rw [mem_coe, mem_product] at hu hv
      refine disjoint_product.2 ?_
      by_cases h1 : u.1 = v.1
      · exact Or.inr ((hQB_disj hu.2 hv.2 fun h2 ↦ huv (Prod.ext h1 h2)).mono
          inter_subset_right inter_subset_right)
      · exact Or.inl ((hQA_disj hu.1 hv.1 h1).mono inter_subset_right inter_subset_right)
    have hcount : (#{q ∈ X ×ˢ Y | T_off.colorOfPair q.1 q.2 = some d} : ℝ) =
        ∑ u ∈ QA ×ˢ QB, (#{q ∈ (X ∩ u.1) ×ˢ (Y ∩ u.2) |
          T_off.colorOfPair q.1 q.2 = some d} : ℝ) := by
      rw [← Nat.cast_sum, ← card_biUnion (fun u hu v hv huv ↦
        (hXY_disj hu hv huv).mono (filter_subset _ _) (filter_subset _ _)),
        ← filter_biUnion, hXY_union]
    have hmul : (pairColorDensity T_off d X Y : ℝ) * (#X * #Y) =
        #{q ∈ X ×ˢ Y | T_off.colorOfPair q.1 q.2 = some d} :=
      mod_cast pairColorDensity_mul_card_of_disjoint T_off d (hdisj.mono hXA hYB)
    have hXYprod : (#X : ℝ) * #Y = ∑ u ∈ QA ×ˢ QB, (#(X ∩ u.1) : ℝ) * #(Y ∩ u.2) := by
      rw [← hXsum, ← hYsum, sum_mul_sum, ← sum_product']
    have hABprod : (#A : ℝ) * #B = ∑ u ∈ QA ×ˢ QB, (#u.1 : ℝ) * #u.2 := by
      rw [← hAsum, ← hBsum, sum_mul_sum, ← sum_product']
    have hnonneg : 0 ≤ (#X : ℝ) * #Y := by positivity
    rw [← abs_of_nonneg hnonneg, ← abs_mul, sub_mul, hmul, hcount, hXYprod, mul_sum,
      ← sum_sub_distrib, hABprod, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u hu ↦ ?_)
    obtain ⟨huA, huB⟩ := mem_product.1 hu
    obtain ⟨huA1, huA2⟩ := mem_filter.1 huA
    obtain ⟨huB1, huB2⟩ := mem_filter.1 huB
    exact hdisc u.1 huA1 huA2 u.2 huB1 huB2 (X ∩ u.1) inter_subset_right
      (Y ∩ u.2) inter_subset_right d
  -- Convert rectangle discrepancy on `A ×ˢ B` into `δ`-regularity via `(X, Y)` and `(A, B)`.
  have hdens (X Y : Finset V) (hXA : X ⊆ A) (hYB : Y ⊆ B)
      (hX : δ * #A ≤ #X) (hY : δ * #B ≤ #Y) (d : κ) :
      |(pairColorDensity T_off d X Y : ℝ) - p d| ≤ δ / 2 := by
    have hXpos : 0 < (#X : ℝ) := (mul_pos hδ0 hApos).trans_le hX
    have hYpos : 0 < (#Y : ℝ) := (mul_pos hδ0 hBpos).trans_le hY
    have hXY : δ ^ 2 * (#A * #B) ≤ #X * #Y := by
      calc δ ^ 2 * (#A * #B) = (δ * #A) * (δ * #B) := by ring
        _ ≤ #X * #Y := mul_le_mul hX hY (by positivity) hXpos.le
    refine le_of_mul_le_mul_right ?_ (mul_pos hXpos hYpos)
    calc |(pairColorDensity T_off d X Y : ℝ) - p d| * (#X * #Y)
        ≤ τ * (#A * #B) := hrect_disc X Y hXA hYB d
      _ ≤ (δ ^ 3 / 2) * (#A * #B) := by
          have : τ ≤ δ ^ 3 / 2 := by linarith
          gcongr
      _ = (δ / 2) * (δ ^ 2 * (#A * #B)) := by ring
      _ ≤ (δ / 2) * (#X * #Y) := by gcongr
  rw [isRegularPair_iff]
  intro d X hXA Y hYB hX hY
  have h1 := hdens X Y hXA hYB hX hY d
  have h2 := hdens A B Subset.rfl Subset.rfl
    (mul_le_of_le_one_left hApos.le hδ1) (mul_le_of_le_one_left hBpos.le hδ1) d
  calc |(pairColorDensity T_off d X Y : ℝ) - pairColorDensity T_off d A B|
      ≤ |(pairColorDensity T_off d X Y : ℝ) - p d| +
          |p d - pairColorDensity T_off d A B| := abs_sub_le _ _ _
    _ ≤ δ := by rw [abs_sub_comm (p d)]; linarith

/-- Assemble a coherent off-diagonal recoloring from local systems ordered by `eP`. -/
private noncomputable def assembleOffDiag {κ V : Type*} [Fintype V] [DecidableEq V]
    (S : PairColorSystem κ V) (P Q : Finpartition (univ : Finset V))
    (eP : P.parts ≃ Fin (Fintype.card P.parts))
    (blockSys : Finset V → Finset V → Finset V → Finset V → PairColorSystem κ V)
    (hrev : ∀ A B A' B', (blockSys A B A' B').rev = S.rev) :
    PairColorSystem κ V where
  color p :=
    let u := p.1.1; let v := p.1.2
    let pA : P.parts := ⟨P.part u, P.part_mem.2 (mem_univ u)⟩
    let pB : P.parts := ⟨P.part v, P.part_mem.2 (mem_univ v)⟩
    if eP pA < eP pB then
      (blockSys pA.1 pB.1 (Q.part u) (Q.part v)).color p
    else if eP pB < eP pA then
      (blockSys pB.1 pA.1 (Q.part v) (Q.part u)).color p
    else S.color p
  rev := S.rev
  rev_involutive := S.rev_involutive
  color_rev p := by
    obtain ⟨⟨u, v⟩, huv⟩ := p
    let pA : P.parts := ⟨P.part u, P.part_mem.2 (mem_univ u)⟩
    let pB : P.parts := ⟨P.part v, P.part_mem.2 (mem_univ v)⟩
    by_cases h1 : eP pA < eP pB
    · have h2 : ¬ eP pB < eP pA := lt_asymm h1
      simpa [pA, pB, h1, h2, hrev] using
        (blockSys pA.1 pB.1 (Q.part u) (Q.part v)).color_rev ⟨(u, v), huv⟩
    · by_cases h2 : eP pB < eP pA
      · simpa [pA, pB, h1, h2, hrev] using
          (blockSys pB.1 pA.1 (Q.part v) (Q.part u)).color_rev ⟨(u, v), huv⟩
      · simpa [pA, pB, h1, h2] using S.color_rev ⟨(u, v), huv⟩

/-- On a canonical fine block `A' ×ˢ B'` (`eP A < eP B`), `assembleOffDiag` agrees with
`blockSys A B A' B'`. -/
private theorem colorOfPair_assembleOffDiag {κ V : Type*} [Fintype V] [DecidableEq V]
    {S : PairColorSystem κ V} {P Q : Finpartition (univ : Finset V)}
    {eP : P.parts ≃ Fin (Fintype.card P.parts)}
    {blockSys : Finset V → Finset V → Finset V → Finset V → PairColorSystem κ V}
    {hrev : ∀ A B A' B', (blockSys A B A' B').rev = S.rev}
    {A B A' B' : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hlt : eP ⟨A, hA⟩ < eP ⟨B, hB⟩) (hA' : A' ∈ Q.parts) (hB' : B' ∈ Q.parts)
    (hA'A : A' ⊆ A) (hB'B : B' ⊆ B) {q0 : V × V} (hq0 : q0 ∈ A' ×ˢ B') :
    (assembleOffDiag S P Q eP blockSys hrev).colorOfPair q0.1 q0.2 =
      (blockSys A B A' B').colorOfPair q0.1 q0.2 := by
  obtain ⟨hu', hv'⟩ := mem_product.1 hq0
  have huA : q0.1 ∈ A := hA'A hu'
  have hvB : q0.2 ∈ B := hB'B hv'
  have hAB : A ≠ B := fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
  have huv : q0.1 ≠ q0.2 := (P.disjoint hA hB hAB).forall_ne_finset huA hvB
  rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
  simp only [assembleOffDiag, hlt, ↓reduceIte, P.part_eq_of_mem hA huA,
    P.part_eq_of_mem hB hvB, Q.part_eq_of_mem hA' hu', Q.part_eq_of_mem hB' hv']

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
/-- Twice the edits across `η`-regular canonical fine blocks is bounded by the `L¹` energy-gap
term `(α / 4) |V|²` plus the coupling slack `2 |κ| η |V|²`. -/
private theorem sum_regular_canonicalFineBlocks_le
    {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (eP : P.parts ≃ Fin (Fintype.card P.parts))
    (blockSys : Finset V → Finset V → Finset V → Finset V → PairColorSystem κ V)
    (hrev : ∀ A B A' B', (blockSys A B A' B').rev = S.rev)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (hgap : S.energy Q - S.energy P ≤ (α / (4 * (max (Fintype.card κ) 1 : ℕ))) ^ 2)
    (hreg_edit : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
      ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B → S.IsRegularPair η A' B' →
        (#{x ∈ A' ×ˢ B' |
            (blockSys A B A' B').colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
          (∑ c : κ, |(pairColorDensity S c A' B' : ℝ) - pairColorDensity S c A B| *
            (#A' * #B')) / 2 + Fintype.card κ * η * (#A' * #B')) :
    ∑ uv ∈ (canonicalFineBlocks hQP eP).filter (fun uv ↦ S.IsRegularPair η uv.1 uv.2),
      2 * (#{x ∈ uv.1 ×ˢ uv.2 |
        (assembleOffDiag S P Q eP blockSys hrev).colorOfPair x.1 x.2 ≠
          S.colorOfPair x.1 x.2} : ℝ) ≤
      (α / 4 + 2 * Fintype.card κ * η) * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set q := Fintype.card κ
  set q' : ℕ := max q 1
  set T_off := assembleOffDiag S P Q eP blockSys hrev
  set FB_reg := (canonicalFineBlocks hQP eP).filter fun uv ↦ S.IsRegularPair η uv.1 uv.2
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
    have huv_sub1 : uv.1 ⊆ pA.1 := le_refinementParent hQP ⟨uv.1, h1⟩
    have huv_sub2 : uv.2 ⊆ pB.1 := le_refinementParent hQP ⟨uv.2, h2⟩
    have hpAB : pA.1 ≠ pB.1 := fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
    have hf : {x ∈ uv.1 ×ˢ uv.2 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} =
        {x ∈ uv.1 ×ˢ uv.2 |
          (blockSys pA.1 pB.1 uv.1 uv.2).colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} :=
      filter_congr fun x hx ↦ by
        rw [colorOfPair_assembleOffDiag pA.2 pB.2 hlt h1 h2 huv_sub1 huv_sub2 hx]
    have hspec := hreg_edit pA.1 pA.2 pB.1 pB.2 hpAB uv.1 h1 huv_sub1 uv.2 h2 huv_sub2 hreg
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
            P.part_eq_of_mem pA.2 (huv_sub1 hx1), P.part_eq_of_mem pB.2 (huv_sub2 hx2)]
      rw [sum_congr rfl hpt, sum_const, card_product, nsmul_eq_mul]
      push_cast; ring
    rw [hf]; linarith
  have hFB_disj : ((FB_reg : Finset _) : Set _).PairwiseDisjoint
      (fun uv : Finset V × Finset V ↦ uv.1 ×ˢ uv.2) := by
    intro u hu v hv huv
    obtain ⟨h1u, h2u, -⟩ := mem_canonicalFineBlocks_elim (mem_filter.1 hu).1
    obtain ⟨h1v, h2v, -⟩ := mem_canonicalFineBlocks_elim (mem_filter.1 hv).1
    refine disjoint_product.2 ?_
    by_cases h1 : u.1 = v.1
    · exact Or.inr (Q.disjoint h2u h2v fun h2 ↦ huv (Prod.ext h1 h2))
    · exact Or.inl (Q.disjoint h1u h1v h1)
  have hFB_off : FB_reg.biUnion (fun uv ↦ uv.1 ×ˢ uv.2) ⊆ (univ : Finset V).offDiag := by
    intro x hx
    obtain ⟨uv, huv, hxuv⟩ := mem_biUnion.1 hx
    obtain ⟨h1, h2, hlt⟩ := mem_canonicalFineBlocks_elim (mem_filter.1 huv).1
    obtain ⟨hx1, hx2⟩ := mem_product.1 hxuv
    have hpAB : (refinementParent hQP ⟨uv.1, h1⟩).1 ≠ (refinementParent hQP ⟨uv.2, h2⟩).1 :=
      fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
    exact mem_offDiag.2 ⟨mem_univ _, mem_univ _,
      (P.disjoint (refinementParent hQP ⟨uv.1, h1⟩).2
        (refinementParent hQP ⟨uv.2, h2⟩).2 hpAB).forall_ne_finset
        (le_refinementParent hQP ⟨uv.1, h1⟩ hx1) (le_refinementParent hQP ⟨uv.2, h2⟩ hx2)⟩
  have hL1_total : ∑ uv ∈ FB_reg, ∑ x ∈ uv.1 ×ˢ uv.2, ∑ c : κ,
        |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
          pairColorDensity S c (P.part x.1) (P.part x.2)| ≤
      α / 4 * (Fintype.card V : ℝ) ^ 2 := by
    set g₂ := (α / (4 * (q' : ℝ))) ^ 2
    have hg₂_sqrt : √g₂ = α / (4 * (q' : ℝ)) := sqrt_sq (by positivity)
    have hoff_le : (#(univ : Finset V).offDiag : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
      have : #(univ : Finset V).offDiag ≤ Fintype.card V * Fintype.card V := by simp
      exact_mod_cast this.trans_eq (sq _).symm
    calc ∑ uv ∈ FB_reg, ∑ x ∈ uv.1 ×ˢ uv.2, ∑ c : κ,
            |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
              pairColorDensity S c (P.part x.1) (P.part x.2)|
        = ∑ x ∈ FB_reg.biUnion (fun uv ↦ uv.1 ×ˢ uv.2), ∑ c : κ,
            |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
              pairColorDensity S c (P.part x.1) (P.part x.2)| := (sum_biUnion hFB_disj).symm
      _ ≤ ∑ x ∈ (univ : Finset V).offDiag, ∑ c : κ,
            |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
              pairColorDensity S c (P.part x.1) (P.part x.2)| :=
          sum_le_sum_of_subset_of_nonneg hFB_off
            fun _ _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _
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
  have hmass_FB : ∑ uv ∈ FB_reg, (#uv.1 * #uv.2 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have hle : ∑ uv ∈ FB_reg, (#uv.1 * #uv.2) ≤ Fintype.card V * Fintype.card V := by
      have hc1 : #(FB_reg.biUnion fun uv ↦ uv.1 ×ˢ uv.2) = ∑ uv ∈ FB_reg, #uv.1 * #uv.2 := by
        rw [card_biUnion hFB_disj]; exact sum_congr rfl fun _ _ ↦ card_product _ _
      simpa [hc1, Fintype.card_prod] using
        card_le_univ (FB_reg.biUnion fun uv ↦ uv.1 ×ˢ uv.2)
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
        exact add_le_add hL1_total (mul_le_mul_of_nonneg_left hmass_FB (by positivity))
    _ = (α / 4 + 2 * q * η) * (Fintype.card V : ℝ) ^ 2 := by ring

open Classical in
/-- Bound the total edited ordered distinct pairs of `(assembleOffDiag ...).fillDiagonal P` by
the diagonal, `L¹` energy-gap, regular-coupling, and irregular-pair budgets. -/
private theorem card_edit_fillDiagonal_assembleOffDiag_le
    {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (hP : P.IsEquipartition) (hPparts_pos : 0 < #P.parts)
    (eP : P.parts ≃ Fin (Fintype.card P.parts))
    (blockSys : Finset V → Finset V → Finset V → Finset V → PairColorSystem κ V)
    (hrev : ∀ A B A' B', (blockSys A B A' B').rev = S.rev)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (ha₀_le : 4 / α ≤ #P.parts)
    (hQirreg : ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) ≤
      η * (Fintype.card V : ℝ) ^ 2)
    (hgap : S.energy Q - S.energy P ≤ (α / (4 * (max (Fintype.card κ) 1 : ℕ))) ^ 2)
    (hη_α : (2 * (Fintype.card κ : ℝ) + 1) * η ≤ α / 2)
    (hreg_edit : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
      ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B → S.IsRegularPair η A' B' →
        (#{x ∈ A' ×ˢ B' |
            (blockSys A B A' B').colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
          (∑ c : κ, |(pairColorDensity S c A' B' : ℝ) - pairColorDensity S c A B| *
            (#A' * #B')) / 2 + Fintype.card κ * η * (#A' * #B')) :
    (#{p : {p : V × V // p.1 ≠ p.2} |
      ((assembleOffDiag S P Q eP blockSys hrev).fillDiagonal P).color p ≠
        some (S.color p)} : ℝ) ≤
      α * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set T_off := assembleOffDiag S P Q eP blockSys hrev
  set T := T_off.fillDiagonal P
  set E_all : Finset {p : V × V // p.1 ≠ p.2} := {p | T.color p ≠ some (S.color p)}
  set E_diag : Finset (V × V) :=
    {y : V × V | T.colorOfPair y.1 y.2 ≠ (T_off.colorOfPair y.1 y.2).map some}
  set E_pos : Finset (V × V) :=
    {x ∈ (univ : Finset V).offDiag |
      eP ⟨P.part x.1, P.part_mem.2 (mem_univ x.1)⟩ <
        eP ⟨P.part x.2, P.part_mem.2 (mem_univ x.2)⟩ ∧
      T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2}
  set E_neg : Finset (V × V) :=
    {x ∈ (univ : Finset V).offDiag |
      eP ⟨P.part x.2, P.part_mem.2 (mem_univ x.2)⟩ <
        eP ⟨P.part x.1, P.part_mem.2 (mem_univ x.1)⟩ ∧
      T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2}
  have hE_split : #E_all ≤ #E_diag + #E_pos + #E_neg := by
    calc #E_all = #(E_all.map ⟨Subtype.val, Subtype.val_injective⟩) := (card_map _).symm
      _ ≤ #(E_diag ∪ E_pos ∪ E_neg) := by
          refine card_le_card fun x hx ↦ ?_
          obtain ⟨⟨y, hy⟩, hmem, rfl⟩ := mem_map.1 hx
          have hTne : T.color ⟨y, hy⟩ ≠ some (S.color ⟨y, hy⟩) := (mem_filter.1 hmem).2
          by_cases hsame : P.part y.1 = P.part y.2
          · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨mem_univ _,
              (T_off.fillDiagonal_colorOfPair_ne_iff P y.1 y.2).2 ⟨hy, hsame⟩⟩))
          · have hoff_ne : T_off.colorOfPair y.1 y.2 ≠ S.colorOfPair y.1 y.2 := by
              simp only [colorOfPair_of_ne _ hy, ne_eq, Option.some.injEq]
              exact fun heq ↦ hTne (by simp [T, hsame, heq])
            have hne_eP : eP ⟨P.part y.1, P.part_mem.2 (mem_univ y.1)⟩ ≠
                eP ⟨P.part y.2, P.part_mem.2 (mem_univ y.2)⟩ := fun h ↦
              hsame (Subtype.ext_iff.1 (eP.injective h))
            have hy_off : y ∈ (univ : Finset V).offDiag :=
              mem_offDiag.2 ⟨mem_univ _, mem_univ _, hy⟩
            rcases lt_or_gt_of_ne hne_eP with hlt | hgt
            · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hy_off, hlt, hoff_ne⟩))
            · exact mem_union_right _ (mem_filter.2 ⟨hy_off, hgt, hoff_ne⟩)
      _ ≤ #(E_diag ∪ E_pos) + #E_neg := card_union_le _ _
      _ ≤ #E_diag + #E_pos + #E_neg := Nat.add_le_add_right (card_union_le _ _) _
  have hswap_ne {x : V × V}
      (hne : T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2) :
      T_off.colorOfPair x.2 x.1 ≠ S.colorOfPair x.2 x.1 := fun heq ↦
    hne ((T_off.colorOfPair_swap x.2 x.1).trans
      ((congrArg (Option.map S.rev) heq).trans (S.colorOfPair_swap x.2 x.1).symm))
  have hE_symm : #E_neg = #E_pos := by
    refine card_bij (fun x _ ↦ x.swap) (fun x hx ↦ ?_)
      (fun _ _ _ _ h ↦ Prod.swap_injective h)
      (fun x hx ↦ ⟨x.swap, ?_, Prod.swap_swap x⟩)
    · obtain ⟨hx_off, hlt, hne⟩ := mem_filter.1 hx
      have hxy := (mem_offDiag.1 hx_off).2.2
      exact mem_filter.2
        ⟨mem_offDiag.2 ⟨mem_univ _, mem_univ _, hxy.symm⟩, hlt, hswap_ne hne⟩
    · obtain ⟨hx_off, hlt, hne⟩ := mem_filter.1 hx
      have hxy := (mem_offDiag.1 hx_off).2.2
      exact mem_filter.2
        ⟨mem_offDiag.2 ⟨mem_univ _, mem_univ _, hxy.symm⟩, hlt, hswap_ne hne⟩
  have hdiag_bound : (#E_diag : ℝ) ≤ α / 4 * (Fintype.card V : ℝ) ^ 2 := by
    set n := Fintype.card V
    have hnat : #E_diag ≤ n * (n / #P.parts) :=
      T_off.card_fillDiagonal_colorOfPair_ne_le_of_isEquipartition P hP
    have hdiv_le : (#E_diag : ℝ) ≤ (n : ℝ) ^ 2 / #P.parts := by
      rw [le_div_iff₀ (Nat.cast_pos.2 hPparts_pos)]
      calc (#E_diag : ℝ) * #P.parts
          ≤ ((n * (n / #P.parts) : ℕ) : ℝ) * #P.parts :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) (Nat.cast_nonneg _)
        _ = (n : ℝ) * (((n / #P.parts : ℕ) * #P.parts : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (n : ℝ) * n := by gcongr; exact_mod_cast Nat.div_mul_le_self n #P.parts
        _ = (n : ℝ) ^ 2 := (sq _).symm
    refine hdiv_le.trans ?_
    rw [div_le_iff₀ (Nat.cast_pos.2 hPparts_pos)]
    have h1 : 1 ≤ α / 4 * #P.parts := by rw [div_le_iff₀ hα] at ha₀_le; linarith
    linarith [le_mul_of_one_le_left (sq_nonneg (n : ℝ)) h1]
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
    have hreg :=
      sum_regular_canonicalFineBlocks_le S hQP eP blockSys hrev hα hη hgap hreg_edit
    have hirr := sum_irregular_canonicalFineBlocks_le S hQP eP hQirreg
    rw [← mul_sum] at hreg hirr
    linarith
  have hE_all_cast : (#E_all : ℝ) ≤ #E_diag + 2 * (#E_pos : ℝ) := by
    have : #E_all ≤ #E_diag + 2 * #E_pos := by omega
    exact_mod_cast this
  have hcoeff : α / 4 + ((α / 4 + 2 * (Fintype.card κ : ℝ) * η) + η) ≤ α := by linarith
  calc (#E_all : ℝ) ≤ #E_diag + 2 * (#E_pos : ℝ) := hE_all_cast
    _ ≤ α / 4 * (Fintype.card V : ℝ) ^ 2 +
          ((α / 4 + 2 * Fintype.card κ * η) + η) * (Fintype.card V : ℝ) ^ 2 :=
        add_le_add hdiag_bound hE_pos_sum
    _ = (α / 4 + ((α / 4 + 2 * (Fintype.card κ : ℝ) * η) + η)) *
          (Fintype.card V : ℝ) ^ 2 := by
        ring
    _ ≤ α * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

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
  set q' : ℕ := max q 1
  set a₀ : ℕ := max 1 ⌈4 / α⌉₊
  set M_coarse := pairApproximationPartsBound q α F #P₀.parts
  set M_fine := strongPairColorStepBound (pairApproximationTolerance q α F) M_coarse
  -- Step 1: Seed refinement `P₁ ≤ P₀` and strong pair witness `Q ≤ P ≤ P₁`.
  have ha₀ : a₀ ≠ 0 := by positivity
  have hVpos : 0 < Fintype.card V := lt_of_lt_of_le (by
    rw [pairApproximationBound_def]
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (Nat.succ_pos _)) hV
  have : Nonempty V := Fintype.card_pos_iff.1 hVpos
  have hP₀_pos : 0 < #P₀.parts := (P₀.parts_nonempty univ_nonempty.ne_empty).card_pos
  have ha₀P₀ : a₀ * #P₀.parts ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (mul_le_pairApproximationPartsBound q hα hF #P₀.parts).trans
      ((pairApproximationPartsBound_le_pairApproximationBound q hα hF #P₀.parts).trans hV)
  obtain ⟨P₁, hP₁, hP₁card, hP₁P₀, -⟩ :=
    hP₀.exists_refining_equipartition_card_eq_mul P₀ le_rfl ha₀ ha₀P₀
  have hg₂ : 0 < (α / (4 * (q' : ℝ))) ^ 2 := by positivity
  obtain ⟨P, Q, hQP, hPP₁, hP, hQ, hPcard', hQcard', hQirreg, hgap⟩ :=
    S.exists_strong_refining_equipartitions P₁ hP₁ hg₂ (pairApproximationTolerance_pos q hα hF)
  have hPcard : #P.parts ≤ M_coarse := by
    simpa only [M_coarse, q, q', a₀, pairApproximationPartsBound_def, hP₁card] using hPcard'
  have hQcard : #Q.parts ≤ M_fine := hQcard'.trans (strongPairColorStepBound_mono _ hPcard)
  have hPparts_ge : a₀ * #P₀.parts ≤ #P.parts := hP₁card ▸ card_mono hPP₁
  have hPparts_pos : 0 < #P.parts :=
    lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero ha₀) hP₀_pos) hPparts_ge
  have hQparts_pos : 0 < #Q.parts := hPparts_pos.trans_le (card_mono hQP)
  -- Step 2: Cell-size lower bounds on `Q`.
  set η := pairApproximationTolerance q α F #P.parts
  have hη : 0 < η := pairApproximationTolerance_pos q hα hF #P.parts
  have hη_small : η ≤ 1 / 32 := pairApproximationTolerance_le_one_div_32 q α hF #P.parts
  have hQsize (A' : Finset V) (hA' : A' ∈ Q.parts) : (q + 3 : ℝ) ≤ η ^ 2 * #A' := by
    set K := ⌈(q + 3 : ℝ) / η ^ 2⌉₊
    have hKsup : K ≤ (range (M_coarse + 1)).sup
        (fun t ↦ ⌈(q + 3 : ℝ) / (pairApproximationTolerance q α F t) ^ 2⌉₊) :=
      le_sup (f := fun t ↦ ⌈(q + 3 : ℝ) / (pairApproximationTolerance q α F t) ^ 2⌉₊)
        (mem_range.2 (Nat.lt_succ_of_le hPcard))
    have hQK : #Q.parts * K ≤ Fintype.card V :=
      calc #Q.parts * K ≤ max 1 M_fine * (K + 1) :=
            Nat.mul_le_mul (hQcard.trans (le_max_right 1 M_fine)) (Nat.le_succ K)
        _ ≤ pairApproximationBound q α F #P₀.parts := by
            rw [pairApproximationBound_def]
            exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hKsup)
        _ ≤ Fintype.card V := hV
    have hKdiv : K ≤ #(univ : Finset V) / #Q.parts := by
      rw [card_univ, Nat.le_div_iff_mul_le hQparts_pos, mul_comm]; exact hQK
    have hKA' : (K : ℝ) ≤ #A' := by exact_mod_cast hKdiv.trans (hQ.average_le_card_part hA')
    have hceil : (q + 3 : ℝ) / η ^ 2 ≤ K := Nat.le_ceil _
    rw [div_le_iff₀ (pow_pos hη 2)] at hceil
    linarith [mul_le_mul_of_nonneg_right hKA' (sq_nonneg η)]
  -- Step 3: Choose fine block recolorings and assemble `T_off` and `T = T_off.fillDiagonal P`.
  let eP : P.parts ≃ Fin (Fintype.card P.parts) := Fintype.equivFin P.parts
  let target (A B : Finset V) : κ → ℝ := fun c ↦ (pairColorDensity S c A B : ℝ)
  have htarget_prob {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
      (∀ c, 0 ≤ target A B c) ∧ ∑ c, target A B c = 1 := by
    refine ⟨fun c ↦ ?_, ?_⟩
    · dsimp only [target]; exact_mod_cast pairColorDensity_nonneg S c A B
    · obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts hA
      obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hB
      dsimp only [target]
      exact_mod_cast sum_pairColorDensity S A B ⟨(u, v),
        mem_filter.2 ⟨mem_product.2 ⟨hu, hv⟩,
          (P.disjoint hA hB hAB).forall_ne_finset hu hv⟩⟩
  let blockSys (A B A' B' : Finset V) : PairColorSystem κ V :=
    if h : A ∈ P.parts ∧ B ∈ P.parts ∧ A ≠ B ∧ A' ∈ Q.parts ∧ B' ∈ Q.parts ∧
        A' ⊆ A ∧ B' ⊆ B then
      (S.exists_coupled_recoloring_abs_card_filter_sub_le
        ((P.disjoint h.1 h.2.1 h.2.2.1).mono h.2.2.2.2.2.1 h.2.2.2.2.2.2)
        (htarget_prob h.1 h.2.1 h.2.2.1).1 (htarget_prob h.1 h.2.1 h.2.2.1).2
        hη (hQsize A' h.2.2.2.1) (hQsize B' h.2.2.2.2.1)).choose
    else S
  have hblock_rev (A B A' B' : Finset V) : (blockSys A B A' B').rev = S.rev := by
    dsimp only [blockSys]
    split_ifs with h
    · exact (S.exists_coupled_recoloring_abs_card_filter_sub_le
        ((P.disjoint h.1 h.2.1 h.2.2.1).mono h.2.2.2.2.2.1 h.2.2.2.2.2.2)
        (htarget_prob h.1 h.2.1 h.2.2.1).1 (htarget_prob h.1 h.2.1 h.2.2.1).2
        hη (hQsize A' h.2.2.2.1) (hQsize B' h.2.2.2.2.1)).choose_spec.1
    · rfl
  have hblock_spec {A B A' B' : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
      (hA' : A' ∈ Q.parts) (hB' : B' ∈ Q.parts) (hA'A : A' ⊆ A) (hB'B : B' ⊆ B) :
      (∀ s' ⊆ A', ∀ t' ⊆ B', ∀ d : κ,
        |(#{x ∈ s' ×ˢ t' | (blockSys A B A' B').colorOfPair x.1 x.2 = some d} : ℝ) -
          target A B d * (#s' * #t')| ≤ 2 * (q' : ℝ) * η * (#A' * #B')) ∧
      (S.IsRegularPair η A' B' →
        (#{x ∈ A' ×ˢ B' |
            (blockSys A B A' B').colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
          (∑ c : κ, |(pairColorDensity S c A' B' : ℝ) - target A B c| * (#A' * #B')) / 2 +
            q * η * (#A' * #B')) := by
    have hcond : A ∈ P.parts ∧ B ∈ P.parts ∧ A ≠ B ∧ A' ∈ Q.parts ∧ B' ∈ Q.parts ∧
        A' ⊆ A ∧ B' ⊆ B := ⟨hA, hB, hAB, hA', hB', hA'A, hB'B⟩
    have hbs : blockSys A B A' B' =
        (S.exists_coupled_recoloring_abs_card_filter_sub_le
          ((P.disjoint hA hB hAB).mono hA'A hB'B)
          (htarget_prob hA hB hAB).1 (htarget_prob hA hB hAB).2
          hη (hQsize A' hA') (hQsize B' hB')).choose := dite_eq_left hcond
    have hsp := (S.exists_coupled_recoloring_abs_card_filter_sub_le
      ((P.disjoint hA hB hAB).mono hA'A hB'B)
      (htarget_prob hA hB hAB).1 (htarget_prob hA hB hAB).2
      hη (hQsize A' hA') (hQsize B' hB')).choose_spec
    rw [hbs]
    exact ⟨hsp.2.2.1, hsp.2.2.2⟩
  set T_off := assembleOffDiag S P Q eP blockSys hblock_rev
  set T : PairColorSystem (Option κ) V := T_off.fillDiagonal P
  -- Step 4: Coarse regularity of `⟨P, T⟩` and edit bound.
  have hlower : (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F := by
    rw [PairSkeleton3.lowerSkeletonRegular_iff, Fintype.card_option]
    set δ := min (1 / 2) (F (#P.parts + (q + 1)))
    have hδ0 : 0 < δ := lt_min (by norm_num) (hF _)
    have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
    have hη_δ : 4 * (q' : ℝ) * η ≤ δ ^ 3 := by
      have hle : η ≤ δ ^ 3 / (4 * (q' : ℝ)) := by
        simp [η, pairApproximationTolerance_def, δ, q', add_assoc]
      exact (le_div_iff₀' (by positivity : (0 : ℝ) < 4 * q')).1 hle
    have hdiag (A : Finset V) (hA : A ∈ P.parts) : 1 < δ * #A := by
      obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts hA
      have hQu : Q.part u ∈ Q.parts := Q.part_mem.2 (mem_univ u)
      have hQuA : Q.part u ⊆ A := P.part_eq_of_mem hA hu ▸ part_mono hQP u
      have hcardA : (#(Q.part u) : ℝ) ≤ #A := Nat.cast_le.2 (card_le_card hQuA)
      have h3 := hQsize (Q.part u) hQu
      have hη_le_δ : η ≤ δ := by
        have hδ3 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ]
        have hq'1 : (1 : ℝ) ≤ q' := by exact_mod_cast le_max_right q 1
        nlinarith
      have hη2 : η ^ 2 ≤ δ := by nlinarith
      nlinarith [Nat.cast_nonneg (α := ℝ) q]
    have hoff_lt {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
        (hlt : eP ⟨A, hA⟩ < eP ⟨B, hB⟩) : T_off.IsRegularPair δ A B := by
      have hAB : A ≠ B := fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
      refine isRegularPair_of_fine_discrepancy (τ := 2 * (q' : ℝ) * η) hQP hA hB hAB
        (target A B) hδ0 (by linarith) (by linarith)
        fun A' hA' hA'A B' hB' hB'B s' hs' t' ht' d ↦ ?_
      have hf : {x ∈ s' ×ˢ t' | T_off.colorOfPair x.1 x.2 = some d} =
          {x ∈ s' ×ˢ t' | (blockSys A B A' B').colorOfPair x.1 x.2 = some d} :=
        filter_congr fun x hx ↦ by
          rw [colorOfPair_assembleOffDiag hA hB hlt hA' hB' hA'A hB'B
            (product_subset_product hs' ht' hx)]
      rw [hf]
      exact (hblock_spec hA hB hAB hA' hB' hA'A hB'B).1 s' hs' t' ht' d
    have hoff (A : Finset V) (hA : A ∈ P.parts) (B : Finset V) (hB : B ∈ P.parts)
        (hAB : A ≠ B) : T_off.IsRegularPair δ A B := by
      have hne : eP ⟨A, hA⟩ ≠ eP ⟨B, hB⟩ :=
        fun h ↦ hAB (Subtype.ext_iff.1 (eP.injective h))
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hoff_lt hA hB hlt
      · exact (hoff_lt hB hA hgt).symm
    exact (T_off.isPairColorRegular_fillDiagonal P hdiag hoff).mono (min_le_right _ _)
  have ha₀_le : 4 / α ≤ #P.parts :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 ((le_max_right 1 ⌈4 / α⌉₊).trans
      ((Nat.le_mul_of_pos_right a₀ hP₀_pos).trans hPparts_ge)))
  have hη_α : (2 * (q : ℝ) + 1) * η ≤ α / 2 := by
    have hle : η ≤ α / (4 * ((q' : ℝ) + 1)) := by
      simp [η, pairApproximationTolerance_def, q']
    have hqq' : (q : ℝ) ≤ q' := by exact_mod_cast le_max_left q 1
    rw [le_div_iff₀' (by positivity : (0 : ℝ) < 4 * ((q' : ℝ) + 1))] at hle
    nlinarith
  refine ⟨P, T, hPP₁.trans hP₁P₀, hP, hPcard, funext (T_off.fillDiagonal_rev P), hlower,
    card_edit_fillDiagonal_assembleOffDiag_le S hQP hP hPparts_pos eP blockSys hblock_rev
      hα hη ha₀_le hQirreg hgap hη_α fun A hA B hB hAB A' hA' hA'A B' hB' hB'B hreg ↦
        (hblock_spec hA hB hAB hA' hB' hA'A hB'B).2 hreg⟩

end Assembly

end PairColorSystem
end TauCeti
