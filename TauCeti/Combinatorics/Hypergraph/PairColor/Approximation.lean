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
import TauCeti.Order.Partition.Equipartition
import TauCeti.Order.Partition.Finpartition

/-!
# Strong regular approximation of pair-color systems

Given a pair-color system `S` with a finite palette `κ`, an equitable vertex partition `P₀`, an
edit tolerance `α > 0`, and a positive error schedule `F : ℕ → ℝ`, this file constructs an
exact equitable refinement `P ≤ P₀` of bounded size together with a recolored pair-color system
`T` over `Option κ` such that the lower skeleton `⟨P, T⟩` is `F`-regular at its own lower
complexity, off-diagonal coarse block densities are preserved within `F (#P.parts + card κ + 1) / 2`
(with zero density for the fresh diagonal color), and `T` disagrees with `some ∘ S.color` on at
most `α |V|²` ordered distinct pairs. It also provides the same-palette off-diagonal strong regular
approximation `PairColorSystem.exists_refining_equipartition_regular_offDiag` (preserving `S.rev`
and all within-cell colors) and unseeded versions starting from a minimum part count `l`.

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
pair `(A, B)` makes every off-diagonal coarse pair regular while keeping its color densities close
to those of `S`, and `PairColorSystem.fillDiagonal` cleans up within-cell pairs.

## Main definitions

* `TauCeti.pairOffDiagTolerance`, `TauCeti.pairOffDiagPartsBound`, `TauCeti.pairOffDiagBound`:
  fine regularity tolerance, coarse cell-count bound, and host-size threshold for off-diagonal
  strong regular approximation.
* `TauCeti.pairApproximationTolerance`: fine regularity tolerance for a coarse partition size.
* `TauCeti.pairApproximationPartsBound`: part-count bound for the returned coarse equipartition.
* `TauCeti.pairApproximationBound`: host-size threshold for pair-color regular approximation.

## Main results

* `PairColorSystem.exists_refining_equipartition_regular_offDiag` and
  `PairColorSystem.exists_equipartition_regular_offDiag`: off-diagonal strong regular
  approximation over the original palette `κ`, preserving `S.rev` and within-cell colors.
* `PairColorSystem.exists_refining_equipartition_lowerSkeletonRegular_abs_pairColorDensity_sub_le`:
  strong regular approximation of a pair-color system refining a seed equipartition, preserving
  off-diagonal coarse block densities.
* `PairColorSystem.exists_equipartition_lowerSkeletonRegular`: unseeded strong regular
  approximation over `Option κ` with a minimum part count `l`.
* `TauCeti.PairSkeleton3.exists_refining_lowerSkeletonRegular`: strong regular approximation of a
  lower skeleton `PairSkeleton3 κ V` with minimum cell count `t₀` and finite palette
  `Fin (Fintype.card κ + 1)`.

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

/-- Fine pair-regularity tolerance requested over a `t`-cell coarse partition for off-diagonal
strong regular approximation with `q` colors, edit budget `α`, and schedule `G`. -/
noncomputable def pairOffDiagTolerance (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (t : ℕ) : ℝ :=
  min (α / (4 * ((max q 1 : ℕ) + 1))) ((min (1 / 2) (G t)) ^ 3 / (4 * (max q 1 : ℕ)))

/-- Unfolding lemma for `TauCeti.pairOffDiagTolerance`. -/
theorem pairOffDiagTolerance_def (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (t : ℕ) :
    pairOffDiagTolerance q α G t =
      min (α / (4 * ((max q 1 : ℕ) + 1))) ((min (1 / 2) (G t)) ^ 3 / (4 * (max q 1 : ℕ))) :=
  (rfl)

/-- For positive `α` and `0 < G t`, `pairOffDiagTolerance` is positive. -/
theorem pairOffDiagTolerance_pos (q : ℕ) {α : ℝ} (hα : 0 < α) {G : ℕ → ℝ}
    {t : ℕ} (hGt : 0 < G t) :
    0 < pairOffDiagTolerance q α G t := by
  rw [pairOffDiagTolerance_def]
  have : 0 < min (1 / 2) (G t) := lt_min (by norm_num) hGt
  exact lt_min (by positivity) (by positivity)

/-- `pairOffDiagTolerance` never exceeds `1 / 32`. -/
theorem pairOffDiagTolerance_le_one_div_32 (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (t : ℕ) :
    pairOffDiagTolerance q α G t ≤ 1 / 32 := by
  have hq : (1 : ℝ) ≤ (max q 1 : ℕ) := by exact_mod_cast le_max_right q 1
  have hm3 : (min (1 / 2 : ℝ) (G t)) ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := by
    obtain hm0 | hm0 := le_total (min (1 / 2 : ℝ) (G t)) 0
    · exact (Odd.pow_nonpos (by decide) hm0).trans (by norm_num)
    · exact pow_le_pow_left₀ hm0 (min_le_left _ _) 3
  calc pairOffDiagTolerance q α G t
      ≤ (min (1 / 2) (G t)) ^ 3 / (4 * (max q 1 : ℕ)) := min_le_right _ _
    _ ≤ (1 / 2 : ℝ) ^ 3 / (4 * (max q 1 : ℕ)) :=
        div_le_div_of_nonneg_right hm3 (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ 3 / (4 * 1) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    _ = 1 / 32 := by norm_num

/-- Upper bound on the coarse cell count in off-diagonal strong regular approximation starting from
`l₀` cells. -/
noncomputable def pairOffDiagPartsBound (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  strongPairColorRegularityBound ((α / (4 * (max q 1 : ℕ))) ^ 2)
    (pairOffDiagTolerance q α G) l₀

/-- Unfolding lemma for `TauCeti.pairOffDiagPartsBound`. -/
theorem pairOffDiagPartsBound_def (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) :
    pairOffDiagPartsBound q α G l₀ =
      strongPairColorRegularityBound ((α / (4 * (max q 1 : ℕ))) ^ 2)
        (pairOffDiagTolerance q α G) l₀ :=
  (rfl)

/-- `pairOffDiagPartsBound` is monotone in `l₀`. -/
theorem pairOffDiagPartsBound_mono (q : ℕ) (α : ℝ) (G : ℕ → ℝ) :
    Monotone (pairOffDiagPartsBound q α G) :=
  strongPairColorRegularityBound_mono _ _

/-- For positive parameters, `pairOffDiagPartsBound` is at least `l₀`. -/
theorem le_pairOffDiagPartsBound (q : ℕ) {α : ℝ} (hα : 0 < α) {G : ℕ → ℝ}
    (hG : ∀ n, 0 < G n) (l₀ : ℕ) :
    l₀ ≤ pairOffDiagPartsBound q α G l₀ :=
  le_strongPairColorRegularityBound _ (fun t ↦ pairOffDiagTolerance_pos q hα (hG t)) l₀

/-- Minimum host size `|V|` for off-diagonal strong regular approximation starting from `l₀`
cells. -/
noncomputable def pairOffDiagBound (q : ℕ) (α : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  let M := pairOffDiagPartsBound q α G l₀
  max 1 (strongPairColorStepBound (pairOffDiagTolerance q α G) M) *
    ((range (M + 1)).sup (fun t ↦ ⌈(q + 3 : ℝ) / (pairOffDiagTolerance q α G t) ^ 2⌉₊) + 1)

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
    0 < pairOffDiagBound q α G l₀ := by
  rw [pairOffDiagBound_def]
  exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (Nat.succ_pos _)

/-- `pairOffDiagBound` is monotone in `l₀`. -/
theorem pairOffDiagBound_mono (q : ℕ) (α : ℝ) (G : ℕ → ℝ) :
    Monotone (pairOffDiagBound q α G) := fun _ _ h ↦ by
  have hM := pairOffDiagPartsBound_mono q α G h
  refine Nat.mul_le_mul (max_le_max le_rfl (strongPairColorStepBound_mono _ hM))
    (Nat.succ_le_succ (sup_mono (range_mono (Nat.succ_le_succ hM))))

/-- For positive parameters, `pairOffDiagPartsBound ≤ pairOffDiagBound`. -/
theorem pairOffDiagPartsBound_le_pairOffDiagBound (q : ℕ) {α : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ} (hG : ∀ n, 0 < G n) (l₀ : ℕ) :
    pairOffDiagPartsBound q α G l₀ ≤ pairOffDiagBound q α G l₀ :=
  calc pairOffDiagPartsBound q α G l₀
      ≤ strongPairColorStepBound (pairOffDiagTolerance q α G)
          (pairOffDiagPartsBound q α G l₀) :=
        le_strongPairColorStepBound (fun t ↦ pairOffDiagTolerance_pos q hα (hG t)) _
    _ ≤ max 1 (strongPairColorStepBound (pairOffDiagTolerance q α G)
          (pairOffDiagPartsBound q α G l₀)) :=
        le_max_right _ _
    _ ≤ pairOffDiagBound q α G l₀ :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

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

/-- For positive `α` and `0 < F (t + q + 1)`, `pairApproximationTolerance` is positive. -/
theorem pairApproximationTolerance_pos (q : ℕ) {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ}
    {t : ℕ} (hFt : 0 < F (t + q + 1)) :
    0 < pairApproximationTolerance q α F t :=
  pairOffDiagTolerance_pos q hα hFt

/-- `pairApproximationTolerance` never exceeds `1 / 32`. -/
theorem pairApproximationTolerance_le_one_div_32 (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (t : ℕ) :
    pairApproximationTolerance q α F t ≤ 1 / 32 :=
  pairOffDiagTolerance_le_one_div_32 q α (fun t ↦ F (t + q + 1)) t

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
  le_strongPairColorRegularityBound _
    (fun t ↦ pairApproximationTolerance_pos q hα (hF (t + q + 1))) _

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

/-- `pairApproximationBound` is always positive. -/
theorem pairApproximationBound_pos (q : ℕ) (α : ℝ) (F : ℕ → ℝ) (l₀ : ℕ) :
    0 < pairApproximationBound q α F l₀ :=
  pairOffDiagBound_pos q α (fun t ↦ F (t + q + 1)) (max 1 ⌈4 / α⌉₊ * l₀)

/-- `pairApproximationBound` is monotone in `l₀`. -/
theorem pairApproximationBound_mono (q : ℕ) (α : ℝ) (F : ℕ → ℝ) :
    Monotone (pairApproximationBound q α F) := fun _ _ h ↦
  pairOffDiagBound_mono q α (fun t ↦ F (t + q + 1)) (Nat.mul_le_mul_left _ h)

/-- For positive parameters, `pairApproximationBound` bounds `pairApproximationPartsBound`. -/
theorem pairApproximationPartsBound_le_pairApproximationBound (q : ℕ) {α : ℝ} (hα : 0 < α)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (l₀ : ℕ) :
    pairApproximationPartsBound q α F l₀ ≤ pairApproximationBound q α F l₀ :=
  pairOffDiagPartsBound_le_pairOffDiagBound q hα (fun _ ↦ hF _) (max 1 ⌈4 / α⌉₊ * l₀)

namespace PairColorSystem

/-! ### Assembling coarse regularity and bounding edits -/

section Assembly

open Classical in
/-- Summing rectangle discrepancies of `T_off` over the fine subblocks `A' ×ˢ B'` of a coarse
block `A ×ˢ B` yields coarse `δ`-regularity and preserves the target densities `p` within `δ / 2`
once `2 * τ ≤ δ ^ 3`. -/
private theorem isRegularPair_of_fine_discrepancy {κ V : Type*} [Fintype V] [DecidableEq V]
    {T_off : PairColorSystem κ V} {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (p : κ → ℝ) {τ δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hτδ : 2 * τ ≤ δ ^ 3)
    (hdisc : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
      ∀ s' ⊆ A', ∀ t' ⊆ B', ∀ d : κ,
        |(#{q ∈ s' ×ˢ t' | T_off.colorOfPair q.1 q.2 = some d} : ℝ) - p d * (#s' * #t')| ≤
          τ * (#A' * #B')) :
    T_off.IsRegularPair δ A B ∧
      ∀ d : κ, |(pairColorDensity T_off d A B : ℝ) - p d| ≤ δ / 2 := by
  have hres := T_off.isRegularPair_of_abs_card_filter_colorOfPair_sub_le
    (P.disjoint hA hB hAB) (P.nonempty_of_mem_parts hA) (P.nonempty_of_mem_parts hB)
    hδ0 (fun _ ↦ hτδ)
    fun d X hXA Y hYB ↦
      T_off.abs_card_filter_colorOfPair_sub_le_of_refines hQP hA hB d hXA hYB
        fun A' hA' hA'A B' hB' hB'B ↦
          hdisc A' hA' hA'A B' hB' hB'B (X ∩ A') inter_subset_right (Y ∩ B') inter_subset_right d
  have hτ_le : τ ≤ δ / 2 := by
    have : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ]
    linarith
  exact ⟨hres.1, fun d ↦ (hres.2 d).trans hτ_le⟩

/-- Assemble a coherent off-diagonal recoloring from local systems ordered by `eP`. -/
private noncomputable def assembleOffDiag {κ V : Type*} [Fintype V] [DecidableEq V]
    (S : PairColorSystem κ V) (P Q : Finpartition (univ : Finset V))
    (eP : P.parts ≃ Fin (Fintype.card P.parts))
    (blockSys : Finset V → Finset V → Finset V → Finset V → PairColorSystem κ V)
    (hrev : ∀ A B A' B', (blockSys A B A' B').rev = S.rev) :
    PairColorSystem κ V where
  color p :=
    let u := p.val.1; let v := p.val.2
    let pA : P.parts := ⟨P.part u, P.part_mem.2 (mem_univ u)⟩
    let pB : P.parts := ⟨P.part v, P.part_mem.2 (mem_univ v)⟩
    if eP pA < eP pB then
      (blockSys pA.val pB.val (Q.part u) (Q.part v)).color p
    else if eP pB < eP pA then
      (blockSys pB.val pA.val (Q.part v) (Q.part u)).color p
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
        (blockSys pA.val pB.val (Q.part u) (Q.part v)).color_rev ⟨(u, v), huv⟩
    · by_cases h2 : eP pB < eP pA
      · simpa [pA, pB, h1, h2, hrev] using
          (blockSys pB.val pA.val (Q.part v) (Q.part u)).color_rev ⟨(u, v), huv⟩
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
    have huv_sub1 : uv.1 ⊆ pA.val := le_refinementParent hQP ⟨uv.1, h1⟩
    have huv_sub2 : uv.2 ⊆ pB.val := le_refinementParent hQP ⟨uv.2, h2⟩
    have hpAB : pA.val ≠ pB.val := fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
    have hf : {x ∈ uv.1 ×ˢ uv.2 | T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} =
        {x ∈ uv.1 ×ˢ uv.2 |
          (blockSys pA.val pB.val uv.1 uv.2).colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} :=
      filter_congr fun x hx ↦ by
        rw [colorOfPair_assembleOffDiag pA.property pB.property hlt h1 h2 huv_sub1 huv_sub2 hx]
    have hspec := hreg_edit pA.val pA.property pB.val pB.property hpAB uv.1 h1 huv_sub1 uv.2 h2
        huv_sub2 hreg
    have hconst : ∑ c : κ, |(pairColorDensity S c uv.1 uv.2 : ℝ) -
          pairColorDensity S c pA.val pB.val| * (#uv.1 * #uv.2) =
        ∑ x ∈ uv.1 ×ˢ uv.2, ∑ c : κ,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)| := by
      rw [sum_comm]
      refine sum_congr rfl fun c _ ↦ ?_
      have hpt : ∀ x ∈ uv.1 ×ˢ uv.2,
          |(pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
            pairColorDensity S c (P.part x.1) (P.part x.2)| =
          |(pairColorDensity S c uv.1 uv.2 : ℝ) - pairColorDensity S c pA.val pB.val| :=
        fun x hx ↦ by
          obtain ⟨hx1, hx2⟩ := mem_product.1 hx
          rw [Q.part_eq_of_mem h1 hx1, Q.part_eq_of_mem h2 hx2,
            P.part_eq_of_mem pA.property (huv_sub1 hx1), P.part_eq_of_mem pB.property
                (huv_sub2 hx2)]
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
    have hpAB : (refinementParent hQP ⟨uv.1, h1⟩).val ≠ (refinementParent hQP ⟨uv.2, h2⟩).val :=
      fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
    exact mem_offDiag.2 ⟨mem_univ _, mem_univ _,
      (P.disjoint (refinementParent hQP ⟨uv.1, h1⟩).property
        (refinementParent hQP ⟨uv.2, h2⟩).property hpAB).forall_ne_finset
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
private theorem E_pos_subset_canonicalFineBlocks {κ V : Type*} [Fintype V] [DecidableEq V]
    {S T_off : PairColorSystem κ V} {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    (eP : P.parts ≃ Fin (Fintype.card P.parts)) :
    {x ∈ (univ : Finset V).offDiag |
        eP ⟨P.part x.1, P.part_mem.2 (mem_univ x.1)⟩ <
          eP ⟨P.part x.2, P.part_mem.2 (mem_univ x.2)⟩ ∧
        T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} ⊆
      (canonicalFineBlocks hQP eP).biUnion (fun uv ↦
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

open Classical in
/-- Bound the edited ordered distinct pairs of `assembleOffDiag` by `3 * α / 4 * |V|²`. -/
private theorem card_edit_assembleOffDiag_le
    {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ]
    (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (eP : P.parts ≃ Fin (Fintype.card P.parts))
    (blockSys : Finset V → Finset V → Finset V → Finset V → PairColorSystem κ V)
    (hrev : ∀ A B A' B', (blockSys A B A' B').rev = S.rev)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
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
      (assembleOffDiag S P Q eP blockSys hrev).color p ≠ S.color p} : ℝ) ≤
      3 * α / 4 * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set T_off := assembleOffDiag S P Q eP blockSys hrev
  set E_off : Finset {p : V × V // p.1 ≠ p.2} := {p | T_off.color p ≠ S.color p}
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
  have hE_split : #E_off ≤ #E_pos + #E_neg := by
    calc #E_off = #(E_off.map ⟨Subtype.val, Subtype.val_injective⟩) := (card_map _).symm
      _ ≤ #(E_pos ∪ E_neg) := by
          refine card_le_card fun x hx ↦ ?_
          obtain ⟨⟨y, hy⟩, hmem, rfl⟩ := mem_map.1 hx
          have hoff_ne : T_off.colorOfPair y.1 y.2 ≠ S.colorOfPair y.1 y.2 := by
            simpa [colorOfPair_of_ne _ hy] using (mem_filter.1 hmem).2
          have hne_eP : eP ⟨P.part y.1, P.part_mem.2 (mem_univ y.1)⟩ ≠
              eP ⟨P.part y.2, P.part_mem.2 (mem_univ y.2)⟩ := by
            intro heq
            apply hoff_ne
            simp only [colorOfPair_of_ne _ hy, T_off, assembleOffDiag, heq,
              lt_self_iff_false, ↓reduceIte]
          have hy_off : y ∈ (univ : Finset V).offDiag :=
            mem_offDiag.2 ⟨mem_univ _, mem_univ _, hy⟩
          rcases lt_or_gt_of_ne hne_eP with hlt | hgt
          · exact mem_union_left _ (mem_filter.2 ⟨hy_off, hlt, hoff_ne⟩)
          · exact mem_union_right _ (mem_filter.2 ⟨hy_off, hgt, hoff_ne⟩)
      _ ≤ #E_pos + #E_neg := card_union_le _ _
  have hswap_ne {x : V × V} (hne : T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2) :
      T_off.colorOfPair x.2 x.1 ≠ S.colorOfPair x.2 x.1 := fun heq ↦
    hne ((T_off.colorOfPair_swap x.2 x.1).trans
      ((congrArg (Option.map S.rev) heq).trans (S.colorOfPair_swap x.2 x.1).symm))
  have hE_symm : #E_neg = #E_pos := by
    refine card_bij (fun x _ ↦ x.swap) (fun x hx ↦ ?_)
      (fun _ _ _ _ h ↦ Prod.swap_injective h)
      (fun x hx ↦ ⟨x.swap, ?_, Prod.swap_swap x⟩)
    · obtain ⟨hx_off, hlt, hne⟩ := mem_filter.1 hx
      exact mem_filter.2 ⟨mem_offDiag.2 ⟨mem_univ _, mem_univ _,
        (mem_offDiag.1 hx_off).2.2.symm⟩, hlt, hswap_ne hne⟩
    · obtain ⟨hx_off, hlt, hne⟩ := mem_filter.1 hx
      exact mem_filter.2 ⟨mem_offDiag.2 ⟨mem_univ _, mem_univ _,
        (mem_offDiag.1 hx_off).2.2.symm⟩, hlt, hswap_ne hne⟩
  have hE_pos_sum : (2 : ℝ) * #E_pos ≤
      ((α / 4 + 2 * Fintype.card κ * η) + η) * (Fintype.card V : ℝ) ^ 2 := by
    set FB := canonicalFineBlocks hQP eP
    have hcard_le : (#E_pos : ℝ) ≤ ∑ uv ∈ FB, (#{x ∈ uv.1 ×ˢ uv.2 |
        T_off.colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) :=
      mod_cast (card_le_card (E_pos_subset_canonicalFineBlocks hQP eP)).trans card_biUnion_le
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
  have hE_off_cast : (#E_off : ℝ) ≤ 2 * (#E_pos : ℝ) := by
    have : #E_off ≤ 2 * #E_pos := by omega
    exact_mod_cast this
  have hcoeff : (α / 4 + 2 * (Fintype.card κ : ℝ) * η) + η ≤ 3 * α / 4 := by linarith
  exact hE_off_cast.trans (hE_pos_sum.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)))

open Classical in
/-- Replacing within-cell pairs of `T_off` via `fillDiagonal P` adds at most `|V|² / #P.parts`
edited ordered distinct pairs. -/
private theorem card_edit_fillDiagonal_le {κ V : Type*} [Fintype V] [DecidableEq V]
    (S T_off : PairColorSystem κ V) {P : Finpartition (univ : Finset V)}
    (hP : P.IsEquipartition) :
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
    simpa only [E_diag, T, T_off.card_fillDiagonal_colorOfPair_ne P, card_univ] using
      hP.cast_sum_card_mul_sub_one_le (K := ℝ)
  have hcast : (#E_all : ℝ) ≤ #E_diag + #E_off := by exact_mod_cast hE_split
  linarith

open Classical in
/-- Choose coupled/quasi-random local recolorings on every off-diagonal fine block `A' ×ˢ B'`. -/
private theorem exists_fine_block_recolorings {κ V : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)} {η : ℝ}
    (hη : 0 < η) (hQsize : ∀ A' ∈ Q.parts, (Fintype.card κ + 3 : ℝ) ≤ η ^ 2 * #A') :
    ∃ blockSys : Finset V → Finset V → Finset V → Finset V → PairColorSystem κ V,
      (∀ A B A' B', (blockSys A B A' B').rev = S.rev) ∧
      ∀ {A B A' B'}, A ∈ P.parts → B ∈ P.parts → A ≠ B → A' ∈ Q.parts → B' ∈ Q.parts →
        A' ⊆ A → B' ⊆ B →
        (∀ s' ⊆ A', ∀ t' ⊆ B', ∀ d : κ,
          |(#{x ∈ s' ×ˢ t' | (blockSys A B A' B').colorOfPair x.1 x.2 = some d} : ℝ) -
            pairColorDensity S d A B * (#s' * #t')| ≤
              2 * (max (Fintype.card κ) 1 : ℕ) * η * (#A' * #B')) ∧
        (S.IsRegularPair η A' B' →
          (#{x ∈ A' ×ˢ B' |
              (blockSys A B A' B').colorOfPair x.1 x.2 ≠ S.colorOfPair x.1 x.2} : ℝ) ≤
            (∑ c : κ, |(pairColorDensity S c A' B' : ℝ) - pairColorDensity S c A B| *
              (#A' * #B')) / 2 + Fintype.card κ * η * (#A' * #B')) := by
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
  refine ⟨blockSys, fun A B A' B' ↦ ?_, fun {A B A' B'} hA hB hAB hA' hB' hA'A hB'B ↦ ?_⟩
  · dsimp only [blockSys]; split_ifs with h
    · exact (S.exists_coupled_recoloring_abs_card_filter_sub_le
        ((P.disjoint h.1 h.2.1 h.2.2.1).mono h.2.2.2.2.2.1 h.2.2.2.2.2.2)
        (htarget_prob h.1 h.2.1 h.2.2.1).1 (htarget_prob h.1 h.2.1 h.2.2.1).2
        hη (hQsize A' h.2.2.2.1) (hQsize B' h.2.2.2.2.1)).choose_spec.1
    · rfl
  · have hcond : A ∈ P.parts ∧ B ∈ P.parts ∧ A ≠ B ∧ A' ∈ Q.parts ∧ B' ∈ Q.parts ∧
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
    rw [hbs]; exact ⟨hsp.2.2.1, hsp.2.2.2⟩

open Classical in
/-- Auxiliary off-diagonal strong regular approximation returning both `min (1 / 2) (G #P.parts)`
regularity, off-diagonal density preservation, `1 < min (1 / 2) (G #P.parts) * #A` on all cells,
and the `3 * α / 4 * |V|²` edit bound needed for downstream diagonal filling. -/
private theorem exists_refining_equipartition_regular_offDiag_aux
    {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {α : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ} (hG : ∀ n, 0 < G n)
    (hV : pairOffDiagBound (Fintype.card κ) α G #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem κ V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ pairOffDiagPartsBound (Fintype.card κ) α G #P₀.parts ∧
      T.rev = S.rev ∧
      (∀ u v, P.part u = P.part v → T.colorOfPair u v = S.colorOfPair u v) ∧
      (∀ A ∈ P.parts, 1 < min (1 / 2) (G #P.parts) * #A) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
        T.IsRegularPair (min (1 / 2) (G #P.parts)) A B ∧
        ∀ c : κ, |(pairColorDensity T c A B : ℝ) - pairColorDensity S c A B| ≤
          min (1 / 2) (G #P.parts) / 2) ∧
      (#{p : {p : V × V // p.1 ≠ p.2} | T.color p ≠ S.color p} : ℝ) ≤
        3 * α / 4 * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set q := Fintype.card κ
  set q' : ℕ := max q 1
  set M_coarse := pairOffDiagPartsBound q α G #P₀.parts
  set M_fine := strongPairColorStepBound (pairOffDiagTolerance q α G) M_coarse
  have : Nonempty V :=
    Fintype.card_pos_iff.1 ((pairOffDiagBound_pos q α G #P₀.parts).trans_le hV)
  obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard', hQirreg, hgap⟩ :=
    S.exists_strong_refining_equipartitions P₀ hP₀ (by positivity : 0 < (α / (4 * (q' : ℝ))) ^ 2)
      (fun t ↦ pairOffDiagTolerance_pos q hα (hG t))
  have hQcard : #Q.parts ≤ M_fine := hQcard'.trans (strongPairColorStepBound_mono _ hPcard)
  set η := pairOffDiagTolerance q α G #P.parts
  have hη : 0 < η := pairOffDiagTolerance_pos q hα (hG #P.parts)
  have hQsize (A' : Finset V) (hA' : A' ∈ Q.parts) : (q + 3 : ℝ) ≤ η ^ 2 * #A' := by
    have hKsup : ⌈(q + 3 : ℝ) / η ^ 2⌉₊ ≤ (range (M_coarse + 1)).sup
        (fun t ↦ ⌈(q + 3 : ℝ) / (pairOffDiagTolerance q α G t) ^ 2⌉₊) :=
      le_sup (f := fun t ↦ ⌈(q + 3 : ℝ) / (pairOffDiagTolerance q α G t) ^ 2⌉₊)
        (mem_range.2 (Nat.lt_succ_of_le hPcard))
    have hMK : max 1 M_fine * ⌈(q + 3 : ℝ) / η ^ 2⌉₊ ≤ #(univ : Finset V) := by
      rw [card_univ]; exact (Nat.mul_le_mul_left _ (hKsup.trans (Nat.le_succ _))).trans hV
    exact (div_le_iff₀' (pow_pos hη 2)).1 ((Nat.le_ceil _).trans (by
      exact_mod_cast hQ.le_card_part_of_mul_le (hQcard.trans (le_max_right 1 M_fine)) hMK hA'))
  obtain ⟨blockSys, hblock_rev, hblock_spec⟩ := S.exists_fine_block_recolorings hη hQsize
  let eP : P.parts ≃ Fin (Fintype.card P.parts) := Fintype.equivFin P.parts
  set T_off := assembleOffDiag S P Q eP blockSys hblock_rev
  set δ := min (1 / 2) (G #P.parts)
  have hδ0 : 0 < δ := lt_min (by norm_num) (hG _)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hη_δ : 4 * (q' : ℝ) * η ≤ δ ^ 3 := by
    have hle : η ≤ δ ^ 3 / (4 * (q' : ℝ)) := by simp [η, pairOffDiagTolerance_def, δ, q']
    exact (le_div_iff₀' (by positivity : (0 : ℝ) < 4 * q')).1 hle
  have hdiag (A : Finset V) (hA : A ∈ P.parts) : 1 < δ * #A := by
    obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts hA
    have hQu : Q.part u ∈ Q.parts := Q.part_mem.2 (mem_univ u)
    have hcardA : (#(Q.part u) : ℝ) ≤ #A :=
      Nat.cast_le.2 (card_le_card (P.part_eq_of_mem hA hu ▸ part_mono hQP u))
    have h3 := hQsize (Q.part u) hQu
    have hq'1 : (1 : ℝ) ≤ q' := by exact_mod_cast le_max_right q 1
    have hδ3 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ]
    have hη2 : η ^ 2 ≤ δ := by nlinarith
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hoff_lt {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
      (hlt : eP ⟨A, hA⟩ < eP ⟨B, hB⟩) :
      T_off.IsRegularPair δ A B ∧
        ∀ d : κ, |(pairColorDensity T_off d A B : ℝ) - pairColorDensity S d A B| ≤ δ / 2 := by
    have hAB : A ≠ B := fun h ↦ (ne_of_lt hlt) (congrArg eP (Subtype.ext h))
    refine isRegularPair_of_fine_discrepancy (τ := 2 * (q' : ℝ) * η) hQP hA hB hAB
      (fun d ↦ (pairColorDensity S d A B : ℝ)) hδ0 (by linarith) (by linarith)
      fun A' hA' hA'A B' hB' hB'B s' hs' t' ht' d ↦ ?_
    have hf : {x ∈ s' ×ˢ t' | T_off.colorOfPair x.1 x.2 = some d} =
        {x ∈ s' ×ˢ t' | (blockSys A B A' B').colorOfPair x.1 x.2 = some d} :=
      filter_congr fun x hx ↦ by
        rw [colorOfPair_assembleOffDiag hA hB hlt hA' hB' hA'A hB'B
          (product_subset_product hs' ht' hx)]
    rw [hf]; exact (hblock_spec hA hB hAB hA' hB' hA'A hB'B).1 s' hs' t' ht' d
  have hoff (A : Finset V) (hA : A ∈ P.parts) (B : Finset V) (hB : B ∈ P.parts) (hAB : A ≠ B) :
      T_off.IsRegularPair δ A B ∧
        ∀ d : κ, |(pairColorDensity T_off d A B : ℝ) - pairColorDensity S d A B| ≤ δ / 2 := by
    rcases lt_or_gt_of_ne (a := eP ⟨A, hA⟩) (b := eP ⟨B, hB⟩)
      (fun h ↦ hAB (Subtype.ext_iff.1 (eP.injective h))) with hlt | hgt
    · exact hoff_lt hA hB hlt
    · refine ⟨(hoff_lt hB hA hgt).1.symm, fun d ↦ ?_⟩
      have h := (hoff_lt hB hA hgt).2 (S.rev d)
      have hT : pairColorDensity T_off (S.rev d) B A = pairColorDensity T_off d A B :=
        pairColorDensity_swap T_off d A B
      rwa [hT, pairColorDensity_swap] at h
  have hdiag_eq (u v : V) (huv : P.part u = P.part v) :
      T_off.colorOfPair u v = S.colorOfPair u v := by
    by_cases h : u = v
    · simp [h]
    · simp [colorOfPair_of_ne _ h, T_off, assembleOffDiag, huv]
  have hη_α : (2 * (q : ℝ) + 1) * η ≤ α / 2 := by
    have hle : η ≤ α / (4 * ((q' : ℝ) + 1)) := by simp [η, pairOffDiagTolerance_def, q']
    have hqq' : (q : ℝ) ≤ q' := by exact_mod_cast le_max_left q 1
    rw [le_div_iff₀' (by positivity : (0 : ℝ) < 4 * ((q' : ℝ) + 1))] at hle
    nlinarith
  exact ⟨P, T_off, hPP₀, hP, hPcard, rfl, hdiag_eq, hdiag, hoff,
    card_edit_assembleOffDiag_le S hQP eP blockSys hblock_rev hα hη hQirreg hgap hη_α
      fun A hA B hB hAB A' hA' hA'A B' hB' hB'B hreg ↦
        (hblock_spec hA hB hAB hA' hB' hA'A hB'B).2 hreg⟩

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
    fun A hA B hB hAB ↦ (hoff A hA B hB hAB).1.mono (min_le_right _ _),
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
/-- **Strong regular approximation of a pair-color system with off-diagonal density preservation.**
Given an equitable partition `P₀`, an edit budget `α > 0`, and a positive error schedule `F`, if
`V` has at least `pairApproximationBound (card κ) α F #P₀.parts` vertices, there exist an
equitable refinement `P ≤ P₀` with at most `pairApproximationPartsBound (card κ) α F #P₀.parts`
cells and a pair-color system `T` over `Option κ` with `T.rev = Option.map S.rev` such that
`⟨P, T⟩` is `F`-regular at its lower complexity, every off-diagonal coarse block `(A, B)` preserves
each original color's density within `F (#P.parts + card κ + 1) / 2` while assigning density zero
to the fresh diagonal color `none`, and `T` differs from `some ∘ S.color` on at most `α |V|²`
ordered distinct pairs. -/
theorem exists_refining_equipartition_lowerSkeletonRegular_abs_pairColorDensity_sub_le
    {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {α : ℝ} (hα : 0 < α)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : pairApproximationBound (Fintype.card κ) α F #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ pairApproximationPartsBound (Fintype.card κ) α F #P₀.parts ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
        ∀ c : κ, |(pairColorDensity T (some c) A B : ℝ) - pairColorDensity S c A B| ≤
          F (#P.parts + Fintype.card κ + 1) / 2) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → pairColorDensity T none A B = 0) ∧
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
  obtain ⟨P, T_off, hPP₁, hP, hPcard', hrev_off, -, hdiag, hoff, hedit_off⟩ :=
    S.exists_refining_equipartition_regular_offDiag_aux P₁ hP₁ hα (G := fun t ↦ F (t + q + 1))
      (fun _ ↦ hF _) (by rw [hP₁card]; exact hV)
  have hPcard : #P.parts ≤ pairApproximationPartsBound q α F #P₀.parts := by
    rw [hP₁card] at hPcard'; exact hPcard'
  set T : PairColorSystem (Option κ) V := T_off.fillDiagonal P
  have hlower : (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F := by
    rw [PairSkeleton3.lowerSkeletonRegular_iff, Fintype.card_option, ← add_assoc]
    exact (T_off.isPairColorRegular_fillDiagonal P hdiag fun A hA B hB hAB ↦
      (hoff A hA B hB hAB).1).mono (min_le_right _ _)
  have hdens (A : Finset V) (hA : A ∈ P.parts) (B : Finset V) (hB : B ∈ P.parts)
      (hAB : A ≠ B) (c : κ) :
      |(pairColorDensity T (some c) A B : ℝ) - pairColorDensity S c A B| ≤
        F (#P.parts + q + 1) / 2 := by
    dsimp only [T]
    rw [T_off.pairColorDensity_fillDiagonal_of_ne P hA hB hAB Subset.rfl Subset.rfl (some c),
      Option.elim_some]
    exact ((hoff A hA B hB hAB).2 c).trans
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hnone (A : Finset V) (hA : A ∈ P.parts) (B : Finset V) (hB : B ∈ P.parts) (hAB : A ≠ B) :
      pairColorDensity T none A B = 0 := by
    simpa [T] using T_off.pairColorDensity_fillDiagonal_of_ne P hA hB hAB Subset.rfl Subset.rfl none
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
  have hfill_edit := card_edit_fillDiagonal_le S T_off hP
  refine ⟨P, T, hPP₁.trans hP₁P₀, hP, hPcard,
    funext (fun c ↦ (T_off.fillDiagonal_rev P c).trans (by rw [hrev_off])),
    hlower, hdens, hnone, by linarith⟩

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
  obtain ⟨P, T, hPP₀, hP, hPcard, hrev, hlower, -, -, hedit⟩ :=
    S.exists_refining_equipartition_lowerSkeletonRegular_abs_pairColorDensity_sub_le P₀ hP₀ hα hF
      (by rwa [hcard])
  exact ⟨P, T, hP, (le_max_left l 1).trans (hcard ▸ card_mono hPP₀), hcard ▸ hPcard,
    hrev, hlower, hedit⟩

end PairColorSystem

namespace PairSkeleton3

/-- **Strong regular approximation of a lower skeleton at a scheduled tolerance.**
Given `S : PairSkeleton3 κ V` whose vertex partition is an equipartition, a minimum cell count
`t₀`, a pair-edit budget `α > 0`, and a positive schedule `F : ℕ → ℝ`, once
`pairApproximationBound (card κ) α F (max 1 t₀ * #S.vertexPart.parts) ≤ |V|` there exist a lower
skeleton `T : PairSkeleton3 (Fin (card κ + 1)) V` and a palette embedding
`g : κ ↪ Fin (card κ + 1)` such that:

* `T.vertexPart ≤ S.vertexPart`, `T.vertexPart.IsEquipartition`, and
  `t₀ ≤ #T.vertexPart.parts ≤`
  `pairApproximationPartsBound (card κ) α F (max 1 t₀ * #S.vertexPart.parts)`;
* `T.LowerSkeletonRegular F`;
* `g` intertwines palette reversals (`T.pairColors.rev (g c) = g (S.pairColors.rev c)`);
* on every off-diagonal cell pair `(A, B)`, each embedded color `g c` keeps its density within
  `F (#T.vertexPart.parts + card κ + 1) / 2` of `pairColorDensity S.pairColors c A B`, while the
  fresh color outside `Set.range g` has density zero; and
* `T.pairColors.color p ≠ g (S.pairColors.color p)` on at most `α |V|²` ordered distinct
  pairs `p`. -/
theorem exists_refining_lowerSkeletonRegular {κ V : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] (S : PairSkeleton3 κ V) (hS : S.vertexPart.IsEquipartition) (t₀ : ℕ)
    {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : pairApproximationBound (Fintype.card κ) α F (max 1 t₀ * #S.vertexPart.parts) ≤
      Fintype.card V) :
    ∃ (T : PairSkeleton3 (Fin (Fintype.card κ + 1)) V) (g : κ ↪ Fin (Fintype.card κ + 1)),
      T.vertexPart ≤ S.vertexPart ∧ T.vertexPart.IsEquipartition ∧
      t₀ ≤ #T.vertexPart.parts ∧
      #T.vertexPart.parts ≤
        pairApproximationPartsBound (Fintype.card κ) α F (max 1 t₀ * #S.vertexPart.parts) ∧
      T.LowerSkeletonRegular F ∧
      (∀ c, T.pairColors.rev (g c) = g (S.pairColors.rev c)) ∧
      (∀ A ∈ T.vertexPart.parts, ∀ B ∈ T.vertexPart.parts, A ≠ B →
        ∀ c : κ, |(pairColorDensity T.pairColors (g c) A B : ℝ) -
          pairColorDensity S.pairColors c A B| ≤
            F (#T.vertexPart.parts + Fintype.card κ + 1) / 2) ∧
      (∀ A ∈ T.vertexPart.parts, ∀ B ∈ T.vertexPart.parts, A ≠ B →
        ∀ c' ∉ Set.range g, pairColorDensity T.pairColors c' A B = 0) ∧
      (#{p : {p : V × V // p.1 ≠ p.2} |
          T.pairColors.color p ≠ g (S.pairColors.color p)} : ℝ) ≤
        α * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set m : ℕ := max 1 t₀
  have hm : m ≠ 0 := by positivity
  have hVpos : 0 < Fintype.card V := lt_of_lt_of_le (by
    rw [pairApproximationBound_def]
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (Nat.succ_pos _)) hV
  have : Nonempty V := Fintype.card_pos_iff.1 hVpos
  have hSparts_pos : 0 < #S.vertexPart.parts :=
    (S.vertexPart.parts_nonempty univ_nonempty.ne_empty).card_pos
  have hmS : m * #S.vertexPart.parts ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (le_pairApproximationPartsBound (Fintype.card κ) hα hF _).trans
      ((pairApproximationPartsBound_le_pairApproximationBound (Fintype.card κ) hα hF _).trans hV)
  obtain ⟨P₀, hP₀, hP₀card, hP₀S, -⟩ :=
    hS.exists_refining_equipartition_card_eq_mul S.vertexPart le_rfl hm hmS
  obtain ⟨P, T₀, hPP₀, hP, hPcard, hrev, hlower, hdens, hnone, hedit⟩ :=
    S.pairColors.exists_refining_equipartition_lowerSkeletonRegular_abs_pairColorDensity_sub_le
      P₀ hP₀ hα hF (hP₀card.symm ▸ hV)
  let e : Option κ ≃ Fin (Fintype.card κ + 1) :=
    (Fintype.equivFin (Option κ)).trans (finCongr Fintype.card_option)
  let T : PairSkeleton3 (Fin (Fintype.card κ + 1)) V :=
    (⟨P, T₀⟩ : PairSkeleton3 (Option κ) V).relabel e
  let g : κ ↪ Fin (Fintype.card κ + 1) :=
    ⟨fun c ↦ e (some c), fun _ _ h ↦ Option.some.inj (e.injective h)⟩
  have hg (c : κ) : g c = e (some c) := rfl
  have hT_part : T.vertexPart = P := relabel_vertexPart e
  have ht₀ : t₀ ≤ #P.parts :=
    (le_max_right 1 t₀).trans
      ((Nat.le_mul_of_pos_right m hSparts_pos).trans (hP₀card ▸ card_mono hPP₀))
  refine ⟨T, g, hT_part.symm ▸ hPP₀.trans hP₀S, hT_part.symm ▸ hP, hT_part.symm ▸ ht₀,
    hT_part.symm ▸ hP₀card ▸ hPcard,
    (lowerSkeletonRegular_relabel_iff e).2 hlower, fun c ↦ by simp [T, hg, hrev],
    fun A hA B hB hAB c ↦ by
      rw [hT_part] at hA hB ⊢
      simpa [T, hg] using hdens A hA B hB hAB c,
    fun A hA B hB hAB c' hc' ↦ ?_, ?_⟩
  · rw [hT_part] at hA hB
    rw [relabel_pairColors, pairColorDensity_relabel]
    cases h : e.symm c' with
    | none => exact hnone A hA B hB hAB
    | some c => exact absurd ⟨c, by simp [hg, ← h]⟩ hc'
  · have hcard : #{p : {p : V × V // p.1 ≠ p.2} |
          T.pairColors.color p ≠ g (S.pairColors.color p)} =
        #{p : {p : V × V // p.1 ≠ p.2} |
          T₀.color p ≠ some (S.pairColors.color p)} :=
      congrArg card <| Finset.ext fun p ↦ by
        simp only [mem_filter, mem_univ, true_and, T, hg, relabel_pairColors,
          PairColorSystem.relabel_color, ne_eq, e.injective.eq_iff]
    rwa [hcard]

end PairSkeleton3

end TauCeti
