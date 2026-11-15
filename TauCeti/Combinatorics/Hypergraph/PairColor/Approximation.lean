/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Diagonal
public import TauCeti.Combinatorics.Hypergraph.PairColor.StrongRegularization
import TauCeti.Combinatorics.Enumerative.CoupledColoring
import TauCeti.Combinatorics.Hypergraph.PairColor.Recoloring
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Regular approximation of pair-color systems and lower skeletons

Cleaning up irregular cell pairs of a single regular partition
(`PairColorSystem.exists_recoloring_isPairColorRegular`) achieves regularity at a fixed tolerance
`2 * ε` while editing at most an `O(ε)`-proportion of the pairs. A lower-skeleton regular
approximation for an arbitrary positive schedule `F : ℕ → ℝ` demands much more: every pair of cells
of the returned equipartition `P` must be regular at the scale `F #P.parts` (or
`F (#P.parts + card (Option κ))` for `PairSkeleton3.LowerSkeletonRegular F`), while the proportion
of edited pairs remains bounded by an independent `ε > 0`.

This file proves the lower-skeleton edited regular approximation lemma by combining three
ingredients:

1. **Coupled regular recoloring** (`PairColorSystem.exists_coupled_recoloring_isRegularPair`):
   if `(s, t)` is already `η`-regular for `S` with `card κ * η ≤ δ ^ 3 / 2`, pushing `S` on
   `s ×ˢ t` through the optimal transition coupling
   (`TauCeti.exists_coupled_coloring_abs_card_filter_sub_mul_card_le`) yields a `(2 * δ)`-regular
   pair with color densities within `δ` of `p` while editing at most
   `((∑ c, |d_c(s, t) - p c|) / 2 + δ / 2) * (#s * #t)` pairs of `s ×ˢ t`.
2. **Refinement-guided recoloring** (`PairColorSystem.exists_recoloring_of_refinement`): given a
   refinement `Q ≤ P`, regular fine blocks `(A', B')` between distinct coarse cells `(A, B)` are
   coupled-recolored toward the coarse densities `d_c(A, B)`, while irregular fine blocks receive
   independent quasi-random recolorings (`PairColorSystem.exists_recoloring_isRegularPair`). The
   total edit count is controlled by the `L¹` energy-gap drift plus the fine irregular mass.
3. **Strong regularity + amalgamation + diagonal cleanup**
   (`PairColorSystem.exists_regular_approximation` and
   `PairSkeleton3.exists_lowerSkeletonRegular_approximation`): applying strong equitable regularity
   (`PairColorSystem.exists_strong_equipartition`), amalgamating fine `(2 * δ)`-regular blocks onto
   `P` (`PairColorSystem.isRegularPair_of_refinement`), and filling diagonal coarse cells with a
   fresh reversal-fixed color (`PairColorSystem.fillDiagonal`) produces an everywhere regular lower
   skeleton within `ε |V|²` pair edits.

## Main definitions

* `TauCeti.pairColorApproxScale`: internal fine-block discrepancy target
  `(min 1 (min ε (F m)))³ / 8`.
* `TauCeti.pairColorApproxFineSchedule`: internal fine-partition regularity schedule.
* `TauCeti.pairColorApproximationBound`: host-independent upper bound on the coarse cell count.
* `TauCeti.pairColorApproximationFloor`: host-size threshold ensuring fine cells pass the
  exponential discrepancy union bound.

## Main results

* `TauCeti.PairColorSystem.exists_coupled_recoloring_isRegularPair`: coupled quasi-random
  recoloring of an already regular disjoint pair.
* `TauCeti.PairColorSystem.exists_recoloring_of_refinement`: refinement-guided off-diagonal
  recoloring controlled by the energy gap and fine irregular mass.
* `TauCeti.PairColorSystem.exists_regular_approximation`: edited regular approximation of a
  pair-color system at scheduled regularity `F #P.parts`.
* `TauCeti.PairSkeleton3.exists_lowerSkeletonRegular_approximation`: edited regular approximation
  satisfying `PairSkeleton3.LowerSkeletonRegular F`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), 451–476.
-/

public section

open Finset Finpartition Real

namespace TauCeti

section Bounds

/-- Internal fine-block target discrepancy scale `(min 1 (min ε (F m)))³ / 8` at `m` coarse cells.
-/
noncomputable def pairColorApproxScale (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) : ℝ :=
  (min 1 (min ε (F m))) ^ 3 / 8

/-- Unfolding lemma for `TauCeti.pairColorApproxScale`. -/
theorem pairColorApproxScale_def (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    pairColorApproxScale ε F m = (min 1 (min ε (F m))) ^ 3 / 8 :=
  (rfl)

private theorem pairColorApproxScale_pos {ε : ℝ} {F : ℕ → ℝ} {m : ℕ} (hε : 0 < ε) (hF : 0 < F m) :
    0 < pairColorApproxScale ε F m := by
  have : 0 < min 1 (min ε (F m)) := lt_min zero_lt_one (lt_min hε hF)
  rw [pairColorApproxScale_def]
  positivity

private theorem pairColorApproxScale_le_one_div_eight {ε : ℝ} {F : ℕ → ℝ} {m : ℕ} (hε : 0 < ε)
    (hF : 0 < F m) : pairColorApproxScale ε F m ≤ 1 / 8 := by
  have hm0 : 0 ≤ min 1 (min ε (F m)) := le_min zero_le_one (le_min hε.le hF.le)
  have hm1 : min 1 (min ε (F m)) ≤ 1 := min_le_left _ _
  have hpow : (min 1 (min ε (F m))) ^ 3 ≤ 1 := pow_le_one₀ hm0 hm1
  rw [pairColorApproxScale_def]
  linarith

/-- Internal fine-partition regularity schedule `(pairColorApproxScale ε F m)³ / (2 (k + 1))` for a
palette of size `k`. -/
noncomputable def pairColorApproxFineSchedule (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) : ℝ :=
  (pairColorApproxScale ε F m) ^ 3 / (2 * (k + 1 : ℝ))

/-- Unfolding lemma for `TauCeti.pairColorApproxFineSchedule`. -/
theorem pairColorApproxFineSchedule_def (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    pairColorApproxFineSchedule k ε F m =
      (pairColorApproxScale ε F m) ^ 3 / (2 * (k + 1 : ℝ)) :=
  (rfl)

private theorem pairColorApproxFineSchedule_pos (k : ℕ) {ε : ℝ} {F : ℕ → ℝ} {m : ℕ} (hε : 0 < ε)
    (hF : 0 < F m) : 0 < pairColorApproxFineSchedule k ε F m := by
  have hδ := pairColorApproxScale_pos hε hF
  rw [pairColorApproxFineSchedule_def]
  positivity

/-- Upper bound on the number of cells of the approximating equipartition in
`PairColorSystem.exists_regular_approximation`, for a palette of size `k`, edit tolerance `ε`,
regularity schedule `F`, requested minimum cell count `l`, and seed cell count `m₀`. -/
noncomputable def pairColorApproximationBound (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) : ℕ :=
  strongPairColorRegularityBound (ε ^ 2 / (4 * (k + 1 : ℝ)))
    (pairColorApproxFineSchedule k ε F) (max l ⌈4 / ε⌉₊ * m₀)

/-- Unfolding lemma for `TauCeti.pairColorApproximationBound`. -/
theorem pairColorApproximationBound_def (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) :
    pairColorApproximationBound k ε F l m₀ =
      strongPairColorRegularityBound (ε ^ 2 / (4 * (k + 1 : ℝ)))
        (pairColorApproxFineSchedule k ε F) (max l ⌈4 / ε⌉₊ * m₀) :=
  (rfl)

/-- `pairColorApproximationBound` is monotone in the seed cell count `m₀`. -/
theorem pairColorApproximationBound_mono (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) :
    Monotone (pairColorApproximationBound k ε F l) := fun _ _ h ↦
  strongPairColorRegularityBound_mono _ _ (Nat.mul_le_mul_left _ h)

/-- Host-size threshold for `PairColorSystem.exists_regular_approximation`: ensures both the initial
equitable split and the discrepancy union bound on every fine cell at all reachable coarse cell
counts up to `pairColorApproximationBound k ε F l m₀`. -/
noncomputable def pairColorApproximationFloor (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) : ℕ :=
  let M := pairColorApproximationBound k ε F l m₀
  max (max l ⌈4 / ε⌉₊ * m₀)
    (max 1 ((range (M + 1)).sup fun j ↦ ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F j) ^ 6⌉₊) *
      max 1 (strongPairColorRegularityStep (pairColorApproxFineSchedule k ε F) M))

/-- Unfolding lemma for `TauCeti.pairColorApproximationFloor`. -/
theorem pairColorApproximationFloor_def (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) :
    pairColorApproximationFloor k ε F l m₀ =
      max (max l ⌈4 / ε⌉₊ * m₀)
        (max 1 ((range (pairColorApproximationBound k ε F l m₀ + 1)).sup fun j ↦
            ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F j) ^ 6⌉₊) *
          max 1 (strongPairColorRegularityStep (pairColorApproxFineSchedule k ε F)
            (pairColorApproximationBound k ε F l m₀))) :=
  (rfl)

/-- `pairColorApproximationFloor` is always at least `1`. -/
theorem one_le_pairColorApproximationFloor (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) :
    1 ≤ pairColorApproximationFloor k ε F l m₀ :=
  (Nat.mul_le_mul (le_max_left 1 _) (le_max_left 1 _)).trans (le_max_right _ _)

/-- `pairColorApproximationFloor` is monotone in the seed cell count `m₀`. -/
theorem pairColorApproximationFloor_mono (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) :
    Monotone (pairColorApproximationFloor k ε F l) := by
  intro m₁ m₂ hm
  have hM := pairColorApproximationBound_mono k ε F l hm
  refine max_le_max (Nat.mul_le_mul_left _ hm) (Nat.mul_le_mul ?_ ?_)
  · exact max_le_max le_rfl (Finset.sup_mono (range_mono (Nat.succ_le_succ hM)))
  · exact max_le_max le_rfl (strongPairColorRegularityStep_mono _ hM)

end Bounds

namespace PairColorSystem

section CoupledRecoloring

variable {κ V : Type*}

open Classical in
/-- Recolor pairs in `s ×ˢ t` by `x`, pairs in `t ×ˢ s` by `S.rev ∘ x ∘ Prod.swap`, and leave all
other pairs unchanged. -/
private noncomputable def recolorPair (S : PairColorSystem κ V) {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) : PairColorSystem κ V where
  color q :=
    if q.1 ∈ s ×ˢ t then x q.1 else if q.1.swap ∈ s ×ˢ t then S.rev (x q.1.swap) else S.color q
  rev := S.rev
  rev_involutive := S.rev_involutive
  color_rev q := by
    obtain ⟨⟨u, v⟩, huv⟩ := q
    have hboth : ¬((u, v) ∈ s ×ˢ t ∧ (v, u) ∈ s ×ˢ t) := fun ⟨h₁, h₂⟩ ↦
      disjoint_left.1 hst (mem_product.1 h₂).1 (mem_product.1 h₁).2
    by_cases h₁ : (u, v) ∈ s ×ˢ t <;> by_cases h₂ : (v, u) ∈ s ×ˢ t
    · exact absurd ⟨h₁, h₂⟩ hboth
    · simp [h₁, h₂]
    · simp [h₁, h₂]
    · simpa [h₁, h₂] using S.color_rev ⟨(u, v), huv⟩

private theorem colorOfPair_recolorPair_of_mem {S : PairColorSystem κ V} {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) {u v : V} (h : (u, v) ∈ s ×ˢ t) :
    (S.recolorPair hst x).colorOfPair u v = some (x (u, v)) := by
  have huv : u ≠ v := hst.forall_ne_finset (mem_product.1 h).1 (mem_product.1 h).2
  rw [colorOfPair_of_ne _ huv]
  simp [recolorPair, h]

private theorem colorOfPair_recolorPair_of_not_mem {S : PairColorSystem κ V} {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) {u v : V} (hs : u ∈ s → v ∉ t) (ht : u ∈ t → v ∉ s) :
    (S.recolorPair hst x).colorOfPair u v = S.colorOfPair u v := by
  by_cases huv : u = v
  · simp [huv]
  have h₁ : (u, v) ∉ s ×ˢ t := fun h ↦ hs (mem_product.1 h).1 (mem_product.1 h).2
  have h₂ : (v, u) ∉ s ×ˢ t := fun h ↦ ht (mem_product.1 h).2 (mem_product.1 h).1
  rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
  simp [recolorPair, h₁, h₂]

/-- Exponential union bound for coupled recoloring on all subrectangles of `s ×ˢ t` when
`8 (card κ + 1)³ ≤ δ⁶ #s` and `8 (card κ + 1)³ ≤ δ⁶ #t`. -/
private theorem coupled_union_bound_lt_one [Fintype κ] [Nonempty κ] {δ : ℝ} {s t : Finset V}
    (hs : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #s)
    (ht : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #t) :
    2 * (2 ^ #s * 2 ^ #t + 1 : ℕ) * Fintype.card κ *
      exp (-2 * ((δ ^ 3 / 2 * #s * #t) / Fintype.card κ) ^ 2 / (#s * #t : ℕ)) < 1 := by
  let K : ℝ := Fintype.card κ
  have hK : 1 ≤ K := Nat.one_le_cast.2 Fintype.card_pos
  have h8pos : (0 : ℝ) < 8 * (K + 1) ^ 3 := by positivity
  have hspos : (0 : ℝ) < #s :=
    pos_of_mul_pos_right (h8pos.trans_le hs) (by positivity)
  have htpos : (0 : ℝ) < #t :=
    pos_of_mul_pos_right (h8pos.trans_le ht) (by positivity)
  have hs1 : (1 : ℝ) ≤ #s := Nat.one_le_cast.2 (Nat.cast_pos.1 hspos)
  have ht1 : (1 : ℝ) ≤ #t := Nat.one_le_cast.2 (Nat.cast_pos.1 htpos)
  have h2e : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hpow (n : ℕ) : (2 : ℝ) ^ n ≤ exp n :=
    (pow_le_pow_left₀ (by norm_num) h2e n).trans_eq (by rw [← exp_nat_mul, mul_one])
  have hpre : 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) * K ≤ exp (#s + #t + 2 + K) := by
    have h2st : (1 : ℝ) ≤ (2 : ℝ) ^ #s * (2 : ℝ) ^ #t :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    have h4 : 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ 2 * ((2 : ℝ) ^ #s * (2 : ℝ) ^ #t) := by push_cast; linarith
    have hKexp : K ≤ exp K := by linarith [add_one_le_exp K]
    calc 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) * K
        ≤ ((2 : ℝ) ^ 2 * ((2 : ℝ) ^ #s * (2 : ℝ) ^ #t)) * K := by gcongr
      _ ≤ (exp (2 : ℕ) * (exp #s * exp #t)) * exp K := by
          gcongr; exacts [hpow 2, hpow #s, hpow #t]
      _ = exp (#s + #t + 2 + K) := by simp only [← exp_add, Nat.cast_ofNat]; ring_nf
  have hexp : -2 * ((δ ^ 3 / 2 * #s * #t) / K) ^ 2 / (#s * #t : ℕ) =
      -(δ ^ 6 * #s * #t) / (2 * K ^ 2) := by push_cast; field_simp
  calc 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) * K *
          exp (-2 * ((δ ^ 3 / 2 * #s * #t) / K) ^ 2 / (#s * #t : ℕ))
      ≤ exp (#s + #t + 2 + K) * exp (-(δ ^ 6 * #s * #t) / (2 * K ^ 2)) := by
        rw [hexp]; gcongr
    _ = exp ((#s + #t + 2 + K) - (δ ^ 6 * #s * #t) / (2 * K ^ 2)) := by
        rw [← exp_add, neg_div, ← sub_eq_add_neg]
    _ < 1 := by
        rw [exp_lt_one_iff, sub_lt_zero, lt_div_iff₀ (by positivity)]
        have hKpoly : 4 * K ^ 2 * (2 * K + 2) ≤ 8 * (K + 1) ^ 3 := by nlinarith
        have h1 := mul_le_mul_of_nonneg_right (hKpoly.trans hs) htpos.le
        have h2 := mul_le_mul_of_nonneg_right (hKpoly.trans ht) hspos.le
        nlinarith [mul_le_mul_of_nonneg_left hs1 (sq_nonneg K),
          mul_le_mul_of_nonneg_left ht1 (sq_nonneg K)]

private theorem card_filter_getD_eq_pairColorDensity_mul [DecidableEq κ]
    (S : PairColorSystem κ V) {u v : Finset V} (huv : Disjoint u v) (c_def c : κ) :
    (#{q ∈ u ×ˢ v | (S.colorOfPair q.1 q.2).getD c_def = c} : ℝ) =
      pairColorDensity S c u v * (#u * #v) := by
  classical
  have hf : {q ∈ u ×ˢ v | (S.colorOfPair q.1 q.2).getD c_def = c} =
      {q ∈ u ×ˢ v | S.colorOfPair q.1 q.2 = some c} := filter_congr fun q hq ↦ by
    simp [colorOfPair_of_ne S (huv.forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2)]
  rw [hf]
  exact mod_cast (pairColorDensity_mul_card_of_disjoint S c huv).symm

/-- Translate `S.IsRegularPair η s t` into the count-discrepancy hypothesis expected by
`exists_coupled_coloring_abs_card_filter_sub_mul_card_le`. -/
private theorem abs_card_filter_getD_sub_le [DecidableEq κ] {S : PairColorSystem κ V}
    {s t s' t' : Finset V} (hst : Disjoint s t) (hs0 : (0 : ℝ) < #s) (ht0 : (0 : ℝ) < #t)
    {η : ℝ} (hreg : S.IsRegularPair η s t) (hs' : s' ⊆ s) (ht' : t' ⊆ t) (c_def c₀ : κ) :
    |(#{q ∈ s' ×ˢ t' | (S.colorOfPair q.1 q.2).getD c_def = c₀} : ℝ) -
      ((#{q ∈ s ×ˢ t | (S.colorOfPair q.1 q.2).getD c_def = c₀} : ℝ) / #(s ×ˢ t)) *
        #(s' ×ˢ t')| ≤ η * #s * #t := by
  classical
  have hiff : {q ∈ s' ×ˢ t' | (S.colorOfPair q.1 q.2).getD c_def = c₀} =
      {q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c₀} := filter_congr fun q hq ↦ by
    simp [colorOfPair_of_ne S ((hst.mono hs' ht').forall_ne_finset (mem_product.1 hq).1
      (mem_product.1 hq).2)]
  have h1 := hreg.abs_card_filter_colorOfPair_sub_le (c := c₀) hst hs' ht'
  rw [← hiff] at h1
  have h2 : ((#{q ∈ s ×ˢ t | (S.colorOfPair q.1 q.2).getD c_def = c₀} : ℝ) / #(s ×ˢ t)) *
      #(s' ×ˢ t') = pairColorDensity S c₀ s t * #s' * #t' := by
    rw [card_filter_getD_eq_pairColorDensity_mul S hst, card_product, card_product, Nat.cast_mul,
      Nat.cast_mul, mul_div_cancel_right₀ _ (mul_pos hs0 ht0).ne', mul_assoc]
  rwa [h2]

open Classical in
/-- Core `< 1` case of coupled pair recoloring: achieves density accuracy `δ` on every `δ`-large
subrectangle while bounding edits on `s ×ˢ t`. -/
private theorem exists_coupled_recoloring_abs_pairColorDensity_sub_le [Fintype κ]
    (S : PairColorSystem κ V) {s t : Finset V} (hst : Disjoint s t) {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {η δ : ℝ} (hreg : S.IsRegularPair η s t)
    (hδ : 0 < δ) (hηδ : Fintype.card κ * η ≤ δ ^ 3 / 2)
    (hs : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #s)
    (ht : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c s t : ℝ) - p c|) / 2 + δ ^ 3 / 2) * (#s * #t) ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t, δ * #s ≤ #s' → δ * #t ≤ #t' →
        |(pairColorDensity S' c s' t' : ℝ) - p c| ≤ δ := by
  classical
  have hκ : Nonempty κ := by by_contra! h; simp at hp1
  have h8pos : (0 : ℝ) < 8 * (Fintype.card κ + 1 : ℝ) ^ 3 := by positivity
  have hs0 : (0 : ℝ) < #s := pos_of_mul_pos_right (h8pos.trans_le hs) (by positivity)
  have ht0 : (0 : ℝ) < #t := pos_of_mul_pos_right (h8pos.trans_le ht) (by positivity)
  let c_def := Classical.arbitrary κ
  let x₀ (q : V × V) : κ := (S.colorOfPair q.1 q.2).getD c_def
  obtain ⟨x, -, hedit, htest⟩ := exists_coupled_coloring_abs_card_filter_sub_mul_card_le hp hp1
    (s ×ˢ t) x₀ (I := ↥(s.powerset ×ˢ t.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2)
    (fun i ↦ product_subset_product (mem_powerset.1 (mem_product.1 i.2).1)
      (mem_powerset.1 (mem_product.1 i.2).2))
    (a := δ ^ 3 / 2 * #s * #t) (by positivity)
    (by simpa [card_product] using coupled_union_bound_lt_one hs ht)
  refine ⟨S.recolorPair hst x, rfl, fun u v ↦ colorOfPair_recolorPair_of_not_mem hst x, ?_, ?_⟩
  · have hne_eq : {q ∈ s ×ˢ t | (S.recolorPair hst x).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
        {q ∈ s ×ˢ t | x q ≠ x₀ q} := filter_congr fun q hq ↦ by
      simp [x₀, colorOfPair_recolorPair_of_mem hst x hq,
        colorOfPair_of_ne S (hst.forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2)]
    have hsum_eq : ∑ c : κ, |(#{q ∈ s ×ˢ t | x₀ q = c} : ℝ) - p c * #(s ×ˢ t)| =
        (∑ c : κ, |(pairColorDensity S c s t : ℝ) - p c|) * (#s * #t) := by
      rw [sum_mul]
      refine sum_congr rfl fun c _ ↦ ?_
      rw [card_filter_getD_eq_pairColorDensity_mul S hst c_def c, card_product, Nat.cast_mul,
        ← sub_mul, abs_mul, abs_of_pos (mul_pos hs0 ht0)]
    rw [hne_eq]
    linarith [hedit]
  · intro c s' hs' t' ht' hs's ht't
    have hpos : (0 : ℝ) < #s' * #t' :=
      mul_pos ((mul_pos hδ hs0).trans_le hs's) ((mul_pos hδ ht0).trans_le ht't)
    have hdev := htest ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩
      (fun c₀ ↦ abs_card_filter_getD_sub_le hst hs0 ht0 hreg hs' ht' c_def c₀) c
    have hx_card : (#{q ∈ s' ×ˢ t' | x q = c} : ℝ) =
        pairColorDensity (S.recolorPair hst x) c s' t' * (#s' * #t') := by
      have hf : {q ∈ s' ×ˢ t' | (S.recolorPair hst x).colorOfPair q.1 q.2 = some c} =
          {q ∈ s' ×ˢ t' | x q = c} := filter_congr fun q hq ↦ by
        rw [colorOfPair_recolorPair_of_mem hst x (product_subset_product hs' ht' hq),
          Option.some_inj]
      rw [← hf]
      exact mod_cast (pairColorDensity_mul_card_of_disjoint _ c (hst.mono hs' ht')).symm
    rw [hx_card, card_product, Nat.cast_mul, ← sub_mul, abs_mul, abs_of_pos hpos] at hdev
    refine le_of_mul_le_mul_right ?_ hpos
    have hrect : δ ^ 3 * (#s * #t) ≤ δ * (#s' * #t') :=
      (by ring : δ ^ 3 * (#s * #t) = δ * ((δ * #s) * (δ * #t))).trans_le
        (mul_le_mul_of_nonneg_left (mul_le_mul hs's ht't (by positivity) (by positivity)) hδ.le)
    nlinarith [mul_le_mul_of_nonneg_right hηδ (mul_pos hs0 ht0).le]

open Classical in
/-- **Coupled regular recoloring of a disjoint pair.** If `(s, t)` is disjoint and `η`-regular for
`S` with `card κ * η ≤ δ ^ 3 / 2`, `8 (card κ + 1)³ ≤ δ⁶ #s`, and `8 (card κ + 1)³ ≤ δ⁶ #t`, then
for any target probability distribution `p` on `κ` there is a pair-color system `S'` with the same
palette reversal and the same colors outside `(s ×ˢ t) ∪ (t ×ˢ s)` such that `(s, t)` is
`(2 * δ)`-regular for `S'`, its color densities lie within `δ` of `p`, and at most
`((∑ c, |d_c(s, t) - p c|) / 2 + δ / 2) * (#s * #t)` pairs of `s ×ˢ t` are edited. -/
theorem exists_coupled_recoloring_isRegularPair [Fintype κ] (S : PairColorSystem κ V)
    {s t : Finset V} (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    {η δ : ℝ} (hreg : S.IsRegularPair η s t) (hδ : 0 < δ)
    (hηδ : Fintype.card κ * η ≤ δ ^ 3 / 2)
    (hs : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #s)
    (ht : 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      S'.IsRegularPair (2 * δ) s t ∧
      (∀ c, |(pairColorDensity S' c s t : ℝ) - p c| ≤ δ) ∧
      (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c s t : ℝ) - p c|) / 2 + δ / 2) * (#s * #t) := by
  classical
  obtain hδ1 | hδ1 := le_or_gt 1 δ
  · refine ⟨S, rfl, fun _ _ _ _ ↦ rfl, isRegularPair_of_one_le (by linarith), fun c ↦ ?_, ?_⟩
    · have h₀ : (0 : ℝ) ≤ pairColorDensity S c s t := mod_cast pairColorDensity_nonneg S c s t
      have h₁ : (pairColorDensity S c s t : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S c s t
      have hpc : p c ≤ 1 := hp1 ▸ single_le_sum (fun c _ ↦ hp c) (mem_univ c)
      exact (abs_sub_le_iff.2 ⟨by linarith [hp c], by linarith [hp c]⟩).trans hδ1
    · have : 0 ≤ ∑ c, |(pairColorDensity S c s t : ℝ) - p c| :=
        sum_nonneg fun _ _ ↦ abs_nonneg _
      simp only [ne_eq, not_true_eq_false, filter_false, card_empty, Nat.cast_zero]
      positivity
  · obtain ⟨S', hrev, hagree, hedit, hdens⟩ :=
      S.exists_coupled_recoloring_abs_pairColorDensity_sub_le hst hp hp1 hreg hδ hηδ hs ht
    have hthr (u : Finset V) : δ * #u ≤ #u := mul_le_of_le_one_left (Nat.cast_nonneg _) hδ1.le
    have hfull (c : κ) : |(pairColorDensity S' c s t : ℝ) - p c| ≤ δ :=
      hdens c s subset_rfl t subset_rfl (hthr s) (hthr t)
    refine ⟨S', hrev, hagree, ?_, hfull, hedit.trans ?_⟩
    · obtain h2δ | _ := le_or_gt 1 (2 * δ)
      · exact isRegularPair_of_one_le h2δ
      rw [isRegularPair_iff]
      intro c s' hs' t' ht' hs's ht't
      have h1 := hdens c s' hs' t' ht'
        ((by nlinarith [Nat.cast_nonneg (α := ℝ) #s] : δ * #s ≤ 2 * δ * #s).trans hs's)
        ((by nlinarith [Nat.cast_nonneg (α := ℝ) #t] : δ * #t ≤ 2 * δ * #t).trans ht't)
      exact (abs_sub_le _ (p c) _).trans (by rw [abs_sub_comm (p c)]; linarith [hfull c])
    · have hpow : δ ^ 3 ≤ δ := pow_le_of_le_one hδ.le hδ1.le (by norm_num)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end CoupledRecoloring

section RefinementRecoloring

/-- Reindexing by `S.rev` shows the `ℓ¹` palette distance between a fine block and its coarse parent
is invariant under swapping both blocks. -/
private theorem sum_abs_pairColorDensity_swap {κ V : Type*} [Fintype κ] (S : PairColorSystem κ V)
    (A' B' A B : Finset V) :
    ∑ c : κ, |(pairColorDensity S c B' A' : ℝ) - pairColorDensity S c B A| =
      ∑ c : κ, |(pairColorDensity S c A' B' : ℝ) - pairColorDensity S c A B| :=
  (Fintype.sum_bijective S.rev S.rev_involutive.bijective _ _ fun c ↦ by
    rw [pairColorDensity_swap, pairColorDensity_swap]).symm

private theorem card_colorOfPair_ne_swap_eq {κ V : Type*} {S R T₀ : PairColorSystem κ V}
    {s t : Finset V}
    [DecidablePred fun q : V × V ↦ R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2]
    [DecidablePred fun q : V × V ↦ T₀.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2]
    (hRrev : R.rev = S.rev)
    (hlocal : ∀ y ∈ t, ∀ x ∈ s, R.colorOfPair y x = T₀.colorOfPair y x) :
    #{q ∈ s ×ˢ t | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
      #{q ∈ t ×ˢ s | T₀.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
  refine card_bij (fun q _ ↦ q.swap) (fun ⟨x, y⟩ hq ↦ ?_)
    (fun _ _ _ _ h ↦ Prod.swap_injective h) (fun ⟨y, x⟩ hq ↦ ⟨(x, y), ?_, rfl⟩)
  · obtain ⟨hxy, hne'⟩ := mem_filter.1 hq
    obtain ⟨hx, hy⟩ := mem_product.1 hxy
    refine mem_filter.2 ⟨mem_product.2 ⟨hy, hx⟩, fun heq ↦ hne' ?_⟩
    dsimp only [Prod.fst_swap, Prod.snd_swap] at heq ⊢
    rw [R.colorOfPair_swap y x, S.colorOfPair_swap y x, hRrev, hlocal y hy x hx, heq]
  · obtain ⟨hyx, hne'⟩ := mem_filter.1 hq
    obtain ⟨hy, hx⟩ := mem_product.1 hyx
    refine mem_filter.2 ⟨mem_product.2 ⟨hx, hy⟩, fun heq ↦ hne' ?_⟩
    dsimp only at heq ⊢
    have h1 := congrArg (Option.map S.rev) heq
    have hmap (o : Option κ) : (o.map S.rev).map S.rev = o := by cases o <;> simp [S.rev_rev]
    rwa [R.colorOfPair_swap y x, hRrev, hmap, ← S.colorOfPair_swap x y, hlocal y hy x hx] at h1

variable {κ V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- Local recoloring of a single pair `(A', B')` of fine parts: leaves within-coarse-cell pairs
untouched, applies coupled recoloring when `(A', B')` is `η`-regular, and falls back to independent
quasi-random recoloring when `(A', B')` is `η`-irregular. -/
private theorem exists_local_refinement_recoloring [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η δ : ℝ} (hδ : 0 < δ)
    (hηδ : Fintype.card κ * η ≤ δ ^ 3 / 2)
    (hsize : ∀ A' ∈ Q.parts, 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #A')
    (A' B' : Q.parts) :
    ∃ T : PairColorSystem κ V, T.rev = S.rev ∧
      (refinementParent hQP A' = refinementParent hQP B' → T = S) ∧
      (refinementParent hQP A' ≠ refinementParent hQP B' →
        T.IsRegularPair (2 * δ) A'.1 B'.1 ∧
        (∀ c, |(pairColorDensity T c A'.1 B'.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1| ≤ δ) ∧
        (#{q ∈ A'.1 ×ˢ B'.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
          ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
            δ / 2) * (#A'.1 * #B'.1) +
            if (A'.1, B'.1) ∈ S.irregularPairs η Q then (#A'.1 * #B'.1 : ℝ) else 0) := by
  classical
  by_cases hpar : refinementParent hQP A' = refinementParent hQP B'
  · exact ⟨S, rfl, fun _ ↦ rfl, fun hne ↦ (hne hpar).elim⟩
  have hAB : (refinementParent hQP A').1 ≠ (refinementParent hQP B').1 :=
    fun h ↦ hpar (Subtype.ext h)
  have hdisjP : Disjoint (refinementParent hQP A').1 (refinementParent hQP B').1 :=
    P.disjoint (refinementParent hQP A').2 (refinementParent hQP B').2 hAB
  have hdisj : Disjoint A'.1 B'.1 :=
    hdisjP.mono (le_refinementParent hQP A') (le_refinementParent hQP B')
  obtain ⟨u₀, hu₀⟩ := P.nonempty_of_mem_parts (refinementParent hQP A').2
  obtain ⟨v₀, hv₀⟩ := P.nonempty_of_mem_parts (refinementParent hQP B').2
  have hne_supp : (((refinementParent hQP A').1 ×ˢ (refinementParent hQP B').1).filter
      fun q ↦ q.1 ≠ q.2).Nonempty :=
    ⟨(u₀, v₀), mem_filter.2 ⟨mem_product.2 ⟨hu₀, hv₀⟩, hdisjP.forall_ne_finset hu₀ hv₀⟩⟩
  have hp (c : κ) : 0 ≤ (pairColorDensity S c (refinementParent hQP A').1
      (refinementParent hQP B').1 : ℝ) := mod_cast pairColorDensity_nonneg S c _ _
  have hp1 : ∑ c, (pairColorDensity S c (refinementParent hQP A').1
      (refinementParent hQP B').1 : ℝ) = 1 := mod_cast sum_pairColorDensity S _ _ hne_supp
  by_cases hreg : S.IsRegularPair η A'.1 B'.1
  · obtain ⟨T, hrev, -, hTreg, hTdens, hTedit⟩ := S.exists_coupled_recoloring_isRegularPair
      hdisj hp hp1 hreg hδ hηδ (hsize A'.1 A'.2) (hsize B'.1 B'.2)
    refine ⟨T, hrev, fun hh ↦ (hpar hh).elim, fun _ ↦ ⟨hTreg, hTdens, ?_⟩⟩
    exact hTedit.trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
  · have hsmall (u : Finset V) (hu : u ∈ Q.parts) : Fintype.card κ + 1 ≤ δ ^ 6 * #u := by
      have : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
      have hsq : 1 ≤ (Fintype.card κ + 1 : ℝ) ^ 2 := by nlinarith
      nlinarith [hsize u hu]
    obtain ⟨T, hrev, -, hTreg, hTdens⟩ := S.exists_recoloring_isRegularPair hdisj hp hp1 hδ
      (hsmall A'.1 A'.2) (hsmall B'.1 B'.2)
    have hirr : (A'.1, B'.1) ∈ S.irregularPairs η Q :=
      S.mem_irregularPairs.2 ⟨A'.2, B'.2, fun h ↦ hpar (congrArg (refinementParent hQP)
        (Subtype.ext h)), hreg⟩
    refine ⟨T, hrev, fun hh ↦ (hpar hh).elim, fun _ ↦ ⟨hTreg, hTdens, ?_⟩⟩
    rw [ite_eq_left_iff.2 fun h ↦ (h hirr).elim]
    have htriv : (#{q ∈ A'.1 ×ˢ B'.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        #A'.1 * #B'.1 := mod_cast (card_filter_le _ _).trans_eq (card_product _ _)
    have hnonneg : 0 ≤ ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
        δ / 2) * (#A'.1 * #B'.1) :=
      mul_nonneg (add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num))
        (by positivity)) (by positivity)
    linarith

/-- Symmetrically glue local fine-block systems `T A' B'` along a linear order on `Q.parts`. -/
private theorem exists_cellwise_refinement_recoloring (S : PairColorSystem κ V)
    (Q : Finpartition (univ : Finset V)) (order : LinearOrder Q.parts)
    (T : Q.parts → Q.parts → PairColorSystem κ V) (hrev : ∀ A' B', (T A' B').rev = S.rev) :
    ∃ R : PairColorSystem κ V, R.rev = S.rev ∧
      ∀ A' B' : Q.parts, order.le A' B' → ∀ x ∈ A'.1, ∀ y ∈ B'.1,
        R.colorOfPair x y = (T A' B').colorOfPair x y := by
  classical
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  let cell (x : V) : Q.parts := ⟨Q.part x, Q.part_mem.2 (mem_univ x)⟩
  let R : PairColorSystem κ V :=
    { color := fun p ↦ (T (min (cell p.1.1) (cell p.1.2))
        (max (cell p.1.1) (cell p.1.2))).color p
      rev := S.rev
      rev_involutive := S.rev_involutive
      color_rev := fun p ↦ by
        dsimp only [Prod.fst_swap, Prod.snd_swap]
        rw [min_comm (cell p.1.2), max_comm (cell p.1.2), (T _ _).color_rev, hrev] }
  refine ⟨R, rfl, fun A' B' hle x hx y hy ↦ ?_⟩
  by_cases hxy : x = y
  · simp [hxy]
  · have hcA : cell x = A' := Subtype.ext (Q.part_eq_of_mem A'.2 hx)
    have hcB : cell y = B' := Subtype.ext (Q.part_eq_of_mem B'.2 hy)
    simp [colorOfPair_of_ne _ hxy, R, hcA, hcB, min_eq_left hle, max_eq_right hle]

/-- Transfer `(2 * δ)`-regularity and coarse density accuracy from the ordered local systems `T` to
both orientations of `R`. -/
private theorem isRegularPair_of_cellwise_refinement (S R : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {δ : ℝ} (order : LinearOrder Q.parts)
    (T : Q.parts → Q.parts → PairColorSystem κ V) (hRrev : R.rev = S.rev)
    (hlocal : ∀ A' B' : Q.parts, order.le A' B' → ∀ x ∈ A'.1, ∀ y ∈ B'.1,
      R.colorOfPair x y = (T A' B').colorOfPair x y)
    (hreg : ∀ A' B', refinementParent hQP A' ≠ refinementParent hQP B' →
      (T A' B').IsRegularPair (2 * δ) A'.1 B'.1 ∧
      ∀ c, |(pairColorDensity (T A' B') c A'.1 B'.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1| ≤ δ)
    {A' B' : Q.parts} (hne : refinementParent hQP A' ≠ refinementParent hQP B') :
    R.IsRegularPair (2 * δ) A'.1 B'.1 ∧
      ∀ c, |(pairColorDensity R c A'.1 B'.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1| ≤ δ := by
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  have hdens_eq {U W : Q.parts} (hle : U ≤ W) {s t : Finset V} (hs : s ⊆ U.1) (ht : t ⊆ W.1)
      (c : κ) : pairColorDensity R c s t = pairColorDensity (T U W) c s t :=
    pairColorDensity_congr (fun x hx y hy ↦ hlocal U W hle x (hs hx) y (ht hy)) c
  have hfwd {U W : Q.parts} (hle : U ≤ W)
      (hneUW : refinementParent hQP U ≠ refinementParent hQP W) :
      R.IsRegularPair (2 * δ) U.1 W.1 ∧
        ∀ c, |(pairColorDensity R c U.1 W.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP U).1 (refinementParent hQP W).1| ≤ δ := by
    refine ⟨isRegularPair_iff.2 fun c s hs t ht hs' ht' ↦ ?_, fun c ↦ ?_⟩
    · rw [hdens_eq hle hs ht, hdens_eq hle subset_rfl subset_rfl]
      exact isRegularPair_iff.1 (hreg U W hneUW).1 c s hs t ht hs' ht'
    · rw [hdens_eq hle subset_rfl subset_rfl]
      exact (hreg U W hneUW).2 c
  rcases le_total A' B' with hle | hle
  · exact hfwd hle hne
  · refine ⟨(hfwd hle hne.symm).1.symm, fun c ↦ ?_⟩
    have he := (hfwd hle hne.symm).2 (S.rev c)
    have he' : |(pairColorDensity R (R.rev c) B'.1 A'.1 : ℝ) -
        pairColorDensity S (S.rev c) (refinementParent hQP B').1 (refinementParent hQP A').1| ≤ δ :=
      by simpa only [hRrev] using he
    simpa only [pairColorDensity_swap] using he'

open Classical in
/-- Bound the edits of the glued system `R` on every fine block `A'.1 ×ˢ B'.1` in both orientations.
-/
private theorem card_edits_of_cellwise_refinement_le [Fintype κ] (S R : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η δ : ℝ} (order : LinearOrder Q.parts)
    (T : Q.parts → Q.parts → PairColorSystem κ V) (hRrev : R.rev = S.rev)
    (hlocal : ∀ A' B' : Q.parts, order.le A' B' → ∀ x ∈ A'.1, ∀ y ∈ B'.1,
      R.colorOfPair x y = (T A' B').colorOfPair x y)
    (hkeep : ∀ A' B', refinementParent hQP A' = refinementParent hQP B' → T A' B' = S)
    (hedit : ∀ A' B', refinementParent hQP A' ≠ refinementParent hQP B' →
      (#{q ∈ A'.1 ×ˢ B'.1 | (T A' B').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
          δ / 2) * (#A'.1 * #B'.1) +
          if (A'.1, B'.1) ∈ S.irregularPairs η Q then (#A'.1 * #B'.1 : ℝ) else 0)
    (A' B' : Q.parts) :
    (#{q ∈ A'.1 ×ˢ B'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
      if refinementParent hQP A' = refinementParent hQP B' then 0
      else ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
        δ / 2) * (#A'.1 * #B'.1) +
        if (A'.1, B'.1) ∈ S.irregularPairs η Q then (#A'.1 * #B'.1 : ℝ) else 0 := by
  classical
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  by_cases hpar : refinementParent hQP A' = refinementParent hQP B'
  · rw [ite_eq_left_iff.2 fun h ↦ (h hpar).elim]
    have hzero : {q ∈ A'.1 ×ˢ B'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} = ∅ := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_product, notMem_empty, iff_false, not_and, Classical.not_not]
      rintro ⟨hx, hy⟩
      rcases le_total A' B' with hle | hle
      · rw [hlocal A' B' hle x hx y hy, hkeep A' B' hpar]
      · rw [R.colorOfPair_swap y x, S.colorOfPair_swap y x, hRrev, hlocal B' A' hle y hy x hx,
          hkeep B' A' hpar.symm]
    simp [hzero]
  · rw [ite_eq_right_iff.2 fun h ↦ (hpar h).elim]
    rcases le_total A' B' with hle | hle
    · have heq : {q ∈ A'.1 ×ˢ B'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ A'.1 ×ˢ B'.1 | (T A' B').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
        filter_congr fun ⟨x, y⟩ hxy ↦ by
          rw [hlocal A' B' hle x (mem_product.1 hxy).1 y (mem_product.1 hxy).2]
      rw [heq]
      exact hedit A' B' hpar
    · have hirr_iff : (B'.1, A'.1) ∈ S.irregularPairs η Q ↔
          (A'.1, B'.1) ∈ S.irregularPairs η Q := by
        simp only [mem_irregularPairs, B'.2, A'.2, true_and, ne_comm, isRegularPair_comm]
      rw [card_colorOfPair_ne_swap_eq hRrev (hlocal B' A' hle)]
      refine (hedit B' A' (Ne.symm hpar)).trans_eq ?_
      rw [sum_abs_pairColorDensity_swap S A'.1 B'.1, mul_comm (#B'.1 : ℝ) #A'.1]
      by_cases hi : (A'.1, B'.1) ∈ S.irregularPairs η Q <;> simp [hirr_iff, hi, mul_comm]

open Classical in
/-- Sum the cellwise edit bounds over off-diagonal fine block pairs into the energy-gap drift term
plus the fine irregular mass. -/
private theorem sum_refinement_edit_bound_le [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η δ : ℝ} (hδ : 0 < δ) :
    ∑ AB ∈ univ.filter (fun AB : Q.parts × Q.parts ↦
        refinementParent hQP AB.1 ≠ refinementParent hQP AB.2),
      (((∑ c, |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) / 2 +
        δ / 2) * (#AB.1.1 * #AB.2.1) +
        if (AB.1.1, AB.2.1) ∈ S.irregularPairs η Q then (#AB.1.1 * #AB.2.1 : ℝ) else 0) ≤
      (√(Fintype.card κ * (S.energy Q - S.energy P)) / 2 + δ / 2) * (Fintype.card V : ℝ) ^ 2 +
        ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) := by
  classical
  let F := univ.filter fun AB : Q.parts × Q.parts ↦
    refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  have hdrift := S.sum_refinementParent_ne_abs_pairColorDensity_sub_le hQP le_rfl
  have hmass : ∑ AB ∈ F, (#AB.1.1 * #AB.2.1 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    refine (sum_le_univ_sum_of_nonneg fun _ ↦ by positivity).trans_eq ?_
    rw [Fintype.sum_prod_type]
    dsimp only
    rw [← sum_mul_sum, Q.sum_card_subtype, card_univ, sq]
  have hirr_le : (∑ AB ∈ F, if (AB.1.1, AB.2.1) ∈ S.irregularPairs η Q then
        (#AB.1.1 * #AB.2.1 : ℝ) else 0) ≤ ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) := by
    rw [← sum_filter, ← sum_image (f := fun ab : Finset V × Finset V ↦ (#ab.1 * #ab.2 : ℝ))
      fun _ _ _ _ h ↦ Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Subtype.ext (Prod.mk.inj h).2)]
    refine sum_le_sum_of_subset_of_nonneg (fun ab hab ↦ ?_) fun _ _ _ ↦ by positivity
    obtain ⟨AB, hAB, rfl⟩ := mem_image.1 hab
    exact (mem_filter.1 hAB).2
  have hsplit : ∑ AB ∈ F, (((∑ c, |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) / 2 +
        δ / 2) * (#AB.1.1 * #AB.2.1)) =
      (1 / 2) * (∑ AB ∈ F, (#AB.1.1 * #AB.2.1 : ℝ) * ∑ c,
          |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) +
        (δ / 2) * ∑ AB ∈ F, (#AB.1.1 * #AB.2.1 : ℝ) := by
    rw [sum_congr rfl fun _ _ ↦ add_mul _ _ _, sum_add_distrib, mul_sum, mul_sum]
    congr 1; refine sum_congr rfl fun _ _ ↦ by ring
  rw [sum_add_distrib, hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ δ / 2)]

open Classical in
/-- **Refinement-guided off-diagonal recoloring.** Let `Q ≤ P` be vertex partitions and suppose
every fine cell `A' ∈ Q.parts` satisfies `8 (card κ + 1)³ ≤ δ⁶ #A'` with `card κ * η ≤ δ ^ 3 / 2`.
Then there exists `R : PairColorSystem κ V` with `R.rev = S.rev` such that every fine block
`(A', B')` inside an off-diagonal coarse block `(A, B)` is `(2 * δ)`-regular for `R` with color
densities within `δ` of `d_c(A, B)` in `S`, and the total ordered-pair edits are at most
`(√(card κ * (S.energy Q - S.energy P)) / 2 + δ / 2) * |V|²` plus the `η`-irregular mass of `Q`. -/
theorem exists_recoloring_of_refinement [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η δ : ℝ} (hδ : 0 < δ)
    (hηδ : Fintype.card κ * η ≤ δ ^ 3 / 2)
    (hsize : ∀ A' ∈ Q.parts, 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #A') :
    ∃ R : PairColorSystem κ V, R.rev = S.rev ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
        ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
          R.IsRegularPair (2 * δ) A' B' ∧
          ∀ c, |(pairColorDensity R c A' B' : ℝ) - pairColorDensity S c A B| ≤ δ) ∧
      (#{q : V × V | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        (√(Fintype.card κ * (S.energy Q - S.energy P)) / 2 + δ / 2) * (Fintype.card V : ℝ) ^ 2 +
          ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) := by
  classical
  let order : LinearOrder Q.parts := LinearOrder.lift' (Fintype.equivFin Q.parts)
    (Fintype.equivFin Q.parts).injective
  choose T hrev hkeep hprop using S.exists_local_refinement_recoloring hQP hδ hηδ hsize
  obtain ⟨R, hRrev, hlocal⟩ := S.exists_cellwise_refinement_recoloring Q order T hrev
  refine ⟨R, hRrev, fun A hA B hB hAB A' hA' hA'A B' hB' hB'B ↦ ?_, ?_⟩
  · have hpA : refinementParent hQP ⟨A', hA'⟩ = ⟨A, hA⟩ := (refinementParent_eq_iff hQP).2 hA'A
    have hpB : refinementParent hQP ⟨B', hB'⟩ = ⟨B, hB⟩ := (refinementParent_eq_iff hQP).2 hB'B
    have hne : refinementParent hQP ⟨A', hA'⟩ ≠ refinementParent hQP ⟨B', hB'⟩ := by
      rw [hpA, hpB]; exact fun h ↦ hAB (congrArg Subtype.val h)
    obtain ⟨hr, hd⟩ := S.isRegularPair_of_cellwise_refinement R hQP order T hRrev hlocal
      (fun U W h ↦ ⟨(hprop U W h).1, (hprop U W h).2.1⟩) hne
    exact ⟨hr, fun c ↦ by simpa only [hpA, hpB] using hd c⟩
  · have hcover : (univ.filter fun q : V × V ↦ R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2) ⊆
        (univ : Finset (Q.parts × Q.parts)).biUnion fun AB ↦
          {q ∈ AB.1.1 ×ˢ AB.2.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := fun q hq ↦
      mem_biUnion.2 ⟨(⟨Q.part q.1, Q.part_mem.2 (mem_univ _)⟩,
        ⟨Q.part q.2, Q.part_mem.2 (mem_univ _)⟩), mem_univ _,
        mem_filter.2 ⟨mem_product.2 ⟨Q.mem_part_self.2 (mem_univ _),
          Q.mem_part_self.2 (mem_univ _)⟩, (mem_filter.1 hq).2⟩⟩
    have hbi : (#{q : V × V | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ∑ AB : Q.parts × Q.parts,
          (#{q ∈ AB.1.1 ×ˢ AB.2.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) :=
      mod_cast (card_le_card hcover).trans card_biUnion_le
    refine (hbi.trans ((sum_le_sum fun AB _ ↦ S.card_edits_of_cellwise_refinement_le R hQP order T
      hRrev hlocal hkeep (fun U W h ↦ (hprop U W h).2.2) AB.1 AB.2).trans_eq ?_)).trans
      (S.sum_refinement_edit_bound_le hQP hδ)
    rw [sum_filter]
    refine sum_congr rfl fun AB _ ↦ ?_
    by_cases h : refinementParent hQP AB.1 = refinementParent hQP AB.2 <;> simp [h]

end RefinementRecoloring

section Main

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- Counting edited distinct pairs in `{p : V × V // p.1 ≠ p.2}` agrees with counting edited pairs
in `V × V` via `PairColorSystem.colorOfPair`. -/
theorem card_color_ne_eq_card_colorOfPair_ne {κ' : Type*} (S : PairColorSystem κ V)
    (T : PairColorSystem κ' V) (g : κ → κ')
    [DecidablePred fun q : {p : V × V // p.1 ≠ p.2} ↦ T.color q ≠ g (S.color q)]
    [DecidablePred fun p : V × V ↦ T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map g] :
    #{q : {p : V × V // p.1 ≠ p.2} | T.color q ≠ g (S.color q)} =
      #{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map g} := by
  refine card_bij (fun q _ ↦ q.1) (fun q hq ↦ ?_) (fun _ _ _ _ h ↦ Subtype.ext h)
    (fun p hp ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and] at hq ⊢
    rwa [T.colorOfPair_of_ne q.2, S.colorOfPair_of_ne q.2, Option.map_some, ne_eq, Option.some_inj]
  · simp only [mem_filter, mem_univ, true_and] at hp
    have hpne : p.1 ≠ p.2 := fun h ↦ hp (by simp [h])
    refine ⟨⟨p, hpne⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    rwa [T.colorOfPair_of_ne hpne, S.colorOfPair_of_ne hpne, Option.map_some, ne_eq,
      Option.some_inj] at hp

open Classical in
/-- On an equipartition `P`, `PairColorSystem.fillDiagonal` edits at most `|V|² / #P.parts` ordered
vertex pairs. -/
theorem card_fillDiagonal_colorOfPair_ne_le_of_isEquipartition (S : PairColorSystem κ V)
    {P : Finpartition (univ : Finset V)} (hP : P.IsEquipartition) :
    (#{p : V × V | (S.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some} : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / #P.parts := by
  classical
  have hnat : ∑ A ∈ P.parts, #A * (#A - 1) ≤ Fintype.card V * (Fintype.card V / #P.parts) := by
    calc ∑ A ∈ P.parts, #A * (#A - 1)
        ≤ ∑ A ∈ P.parts, #A * (Fintype.card V / #P.parts) := sum_le_sum fun A hA ↦ by
          have hA1 := hP.card_part_le_average_add_one hA
          rw [card_univ] at hA1
          exact Nat.mul_le_mul_left _ (Nat.sub_le_iff_le_add.2 hA1)
      _ = (∑ A ∈ P.parts, #A) * (Fintype.card V / #P.parts) := (sum_mul _ _ _).symm
      _ = Fintype.card V * (Fintype.card V / #P.parts) := by rw [P.sum_card_parts, card_univ]
  rw [S.card_fillDiagonal_colorOfPair_ne P]
  calc ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : ℝ)
      ≤ ((Fintype.card V * (Fintype.card V / #P.parts) : ℕ) : ℝ) := mod_cast hnat
    _ = (Fintype.card V : ℝ) * ((Fintype.card V / #P.parts : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) / #P.parts) :=
        mul_le_mul_of_nonneg_left (Nat.cast_div_le) (Nat.cast_nonneg _)
    _ = (Fintype.card V : ℝ) ^ 2 / #P.parts := by ring

/-- Extract the fine-cell size threshold from `pairColorApproximationFloor`. -/
private theorem fine_part_size_of_floor {k l m₀ m : ℕ} {ε : ℝ} {F : ℕ → ℝ}
    {Q : Finpartition (univ : Finset V)} (hε : 0 < ε) (hF : 0 < F m)
    (hcard : pairColorApproximationFloor k ε F l m₀ ≤ Fintype.card V)
    (hQ : Q.IsEquipartition) (hmM : m ≤ pairColorApproximationBound k ε F l m₀)
    (hQstep : #Q.parts ≤ strongPairColorRegularityStep (pairColorApproxFineSchedule k ε F) m)
    {A' : Finset V} (hA' : A' ∈ Q.parts) :
    8 * (k + 1 : ℝ) ^ 3 ≤ (pairColorApproxScale ε F m) ^ 6 * #A' := by
  let M := pairColorApproximationBound k ε F l m₀
  let c := ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F m) ^ 6⌉₊
  have hc_le : c ≤ max 1 ((range (M + 1)).sup fun j ↦
      ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F j) ^ 6⌉₊) :=
    (le_sup (f := fun j ↦ ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F j) ^ 6⌉₊)
      (mem_range.2 (Nat.lt_succ_of_le hmM))).trans (le_max_right 1 _)
  have hQ_le : #Q.parts ≤ max 1 (strongPairColorRegularityStep
      (pairColorApproxFineSchedule k ε F) M) :=
    (hQstep.trans (strongPairColorRegularityStep_mono _ hmM)).trans (le_max_right 1 _)
  have hmul : c * #Q.parts ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (Nat.mul_le_mul hc_le hQ_le).trans ((le_max_right _ _).trans hcard)
  have hc_card : c ≤ #A' :=
    ((Nat.le_div_iff_mul_le (card_pos.2 ⟨A', hA'⟩)).2 hmul).trans (hQ.average_le_card_part hA')
  have hδ : 0 < pairColorApproxScale ε F m := pairColorApproxScale_pos hε hF
  have hceil : 8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F m) ^ 6 ≤ #A' :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 hc_card)
  linarith [(div_le_iff₀ (pow_pos hδ 6)).1 hceil]

/-- Combine the four `ε / 4` error contributions (energy drift, coupled discrepancy, fine irregular
mass, and diagonal cleanup) into `ε * |V|²`. -/
private theorem approx_edit_budget_le {k m : ℕ} {ε g₀ : ℝ} {F : ℕ → ℝ} (n : ℝ) (hε : 0 < ε)
    (hF : 0 < F m) (hg₀ : 0 ≤ g₀) (hgap : g₀ ≤ ε ^ 2 / (4 * (k + 1 : ℝ)))
    (hm_ceil : ⌈4 / ε⌉₊ ≤ m) :
    (√((k : ℝ) * g₀) / 2 + pairColorApproxScale ε F m / 2) * n ^ 2 +
        pairColorApproxFineSchedule k ε F m * n ^ 2 + n ^ 2 / m ≤ ε * n ^ 2 := by
  have hsqrt : √((k : ℝ) * g₀) ≤ ε / 2 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc (k : ℝ) * g₀ ≤ (k + 1 : ℝ) * (ε ^ 2 / (4 * (k + 1 : ℝ))) :=
          mul_le_mul (by linarith) hgap hg₀ (by positivity)
      _ = (ε / 2) ^ 2 := by field_simp; ring
  have hs0 : 0 ≤ min 1 (min ε (F m)) := le_min zero_le_one (le_min hε.le hF.le)
  have hs1 : min 1 (min ε (F m)) ≤ 1 := min_le_left _ _
  have hsε : min 1 (min ε (F m)) ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_pos := pairColorApproxScale_pos hε hF
  have hδ_one : pairColorApproxScale ε F m ≤ 1 :=
    (pairColorApproxScale_le_one_div_eight hε hF).trans (by norm_num)
  have hδ_ε : pairColorApproxScale ε F m ≤ ε / 8 := by
    have hp : (min 1 (min ε (F m))) ^ 3 ≤ ε := (pow_le_of_le_one hs0 hs1 (by norm_num)).trans hsε
    rw [pairColorApproxScale_def]; linarith
  have hη_ε : pairColorApproxFineSchedule k ε F m ≤ ε / 4 := by
    have hp : (pairColorApproxScale ε F m) ^ 3 ≤ pairColorApproxScale ε F m :=
      pow_le_of_le_one hδ_pos.le hδ_one (by norm_num)
    have hden : (2 : ℝ) ≤ 2 * (k + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hdiv := div_le_div_of_nonneg_left (pow_nonneg hδ_pos.le 3) (by positivity) hden
    rw [pairColorApproxFineSchedule_def]; linarith
  have hm_real : 4 / ε ≤ m := (Nat.le_ceil _).trans (Nat.cast_le.2 hm_ceil)
  have hm_pos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm_real
  have hdiag : n ^ 2 / m ≤ (ε / 4) * n ^ 2 := by
    rw [div_le_iff₀ hm_pos]
    have h1 : 1 ≤ (ε / 4) * m := by
      calc (1 : ℝ) = (ε / 4) * (4 / ε) := by field_simp
        _ ≤ (ε / 4) * m := mul_le_mul_of_nonneg_left hm_real (by positivity)
    nlinarith [sq_nonneg n]
  nlinarith [sq_nonneg n]

/-- Amalgamate fine `(2 * δ)`-regular blocks onto `P` and fill diagonal cells to obtain scheduled
regularity and coarse density preservation. -/
private theorem isPairColorRegular_fillDiagonal_of_refinement {k : ℕ} {ε : ℝ} {F : ℕ → ℝ}
    {P Q : Finpartition (univ : Finset V)} (S R : PairColorSystem κ V) (hQP : Q ≤ P) (hε : 0 < ε)
    (hF : 0 < F #P.parts)
    (hsize : ∀ A' ∈ Q.parts,
      8 * (k + 1 : ℝ) ^ 3 ≤ (pairColorApproxScale ε F #P.parts) ^ 6 * #A')
    (hRfine : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
      ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
        R.IsRegularPair (2 * pairColorApproxScale ε F #P.parts) A' B' ∧
        ∀ c, |(pairColorDensity R c A' B' : ℝ) - pairColorDensity S c A B| ≤
          pairColorApproxScale ε F #P.parts) :
    (⟨P, R.fillDiagonal P⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (F #P.parts) ∧
      ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity (R.fillDiagonal P) c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤ min ε (F #P.parts) := by
  let δ := pairColorApproxScale ε F #P.parts
  have hδ : 0 < δ := pairColorApproxScale_pos hε hF
  have hτ : 0 < min ε (F #P.parts) := lt_min hε hF
  have h4δ : 4 * δ ≤ min ε (F #P.parts) := by
    have hp := (pow_le_of_le_one (le_min zero_le_one hτ.le) (min_le_left _ _) (n := 3)
      (by norm_num)).trans (min_le_right 1 _)
    rw [show δ = _ from pairColorApproxScale_def ε F #P.parts]; linarith
  have hlarge (A : Finset V) (hA : A ∈ P.parts) : 1 < F #P.parts * #A := by
    obtain ⟨A', hA', hA'A⟩ := exists_le_of_le hQP hA
    have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) ^ 3 :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hδF : δ ^ 6 ≤ F #P.parts := (pow_le_of_le_one hδ.le
      ((pairColorApproxScale_le_one_div_eight hε hF).trans (by norm_num)) (by norm_num)).trans
      (by linarith [min_le_right ε (F #P.parts)])
    have hcard_le : (#A' : ℝ) ≤ #A := mod_cast card_le_card hA'A
    nlinarith [hsize A' hA', mul_le_mul hδF hcard_le (by positivity) hF.le]
  have hRreg (A : Finset V) (hA : A ∈ P.parts) (B : Finset V) (hB : B ∈ P.parts) (hAB : A ≠ B) :
      R.IsRegularPair (F #P.parts) A B := by
    refine (R.isRegularPair_of_refinement hQP hA hB hAB hτ ?_
      (fun A' hA' hA'A B' hB' hB'B ↦ (hRfine A hA B hB hAB A' hA' hA'A B' hB' hB'B).1)
      (fun A' hA' hA'A B' hB' hB'B c ↦
        ((hRfine A hA B hB hAB A' hA' hA'A B' hB' hB'B).2 c).trans (by linarith))).mono
      (min_le_right _ _)
    have hp := pow_le_pow_left₀ (by positivity) (min_le_right 1 (min ε (F #P.parts))) 3
    rw [pairColorApproxScale_def]; linarith
  refine ⟨R.isPairColorRegular_fillDiagonal P hlarge hRreg, fun A hA B hB hAB c ↦ ?_⟩
  rw [R.pairColorDensity_fillDiagonal_of_ne P hA hB hAB subset_rfl subset_rfl]
  cases c with
  | none => simp [hτ.le]
  | some c =>
    have hc := R.abs_pairColorDensity_sub_le_of_refinement hQP hA hB hAB
      (fun A' hA' hA'A B' hB' hB'B ↦ (hRfine A hA B hB hAB A' hA' hA'A B' hB' hB'B).1)
      (fun A' hA' hA'A B' hB' hB'B c₀ ↦
        ((hRfine A hA B hB hAB A' hA' hA'A B' hB' hB'B).2 c₀).trans (by linarith)) c
    simp only [Option.elim_some]
    linarith [hc, h4δ]

open Classical in
/-- **Edited regular approximation of a pair-color system.** Given an equipartition `P₀`, an edit
tolerance `ε > 0`, a positive regularity schedule `F : ℕ → ℝ`, and a minimum cell count `l`, once
`pairColorApproximationFloor (card κ) ε F l #P₀.parts ≤ card V` there exist an equipartition
`P ≤ P₀` with `l ≤ #P.parts ≤ pairColorApproximationBound (card κ) ε F l #P₀.parts` and a
pair-color system `T` on `Option κ` with `T.rev = Option.map S.rev` such that `(P, T)` is
`(F #P.parts)`-regular everywhere, off-diagonal coarse color densities stay within
`min ε (F #P.parts)` of those of `S`, and at most `ε |V|²` ordered pairs are edited. -/
theorem exists_regular_approximation [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) {l : ℕ}
    (hcard : pairColorApproximationFloor (Fintype.card κ) ε F l #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧ l ≤ #P.parts ∧
      #P.parts ≤ pairColorApproximationBound (Fintype.card κ) ε F l #P₀.parts ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (F #P.parts) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity T c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤ min ε (F #P.parts)) ∧
      (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  let k := Fintype.card κ
  let t₀ := max l ⌈4 / ε⌉₊
  have hVpos : 0 < Fintype.card V :=
    (one_le_pairColorApproximationFloor k ε F l #P₀.parts).trans hcard
  have hne_univ : (univ : Finset V).Nonempty := card_pos.1 (by rwa [card_univ])
  have hP₀_pos : 1 ≤ #P₀.parts := card_pos.2 (P₀.parts_nonempty hne_univ.ne_empty)
  have ht₀_pos : 1 ≤ t₀ := (Nat.one_le_ceil_iff.2 (by positivity)).trans (le_max_right l _)
  obtain ⟨P₁, hP₁, hP₁card, hP₁P₀, -⟩ := hP₀.exists_refining_equipartition_card_eq_mul P₀ le_rfl
    (by omega : t₀ ≠ 0) (by rw [card_univ]; exact (le_max_left _ _).trans hcard)
  obtain ⟨P, Q, hQP, hPP₁, hP, hQ, hPcard, hQcard, hgap, hirr⟩ := S.exists_strong_equipartition P₁
    hP₁ (g := ε ^ 2 / (4 * (k + 1 : ℝ))) (by positivity)
    (fun m ↦ pairColorApproxFineSchedule_pos k hε (hF m))
  have hmM : #P.parts ≤ pairColorApproximationBound k ε F l #P₀.parts := by
    rwa [hP₁card] at hPcard
  have ht₀_P : t₀ ≤ #P.parts :=
    (Nat.le_mul_of_pos_right t₀ hP₀_pos).trans (hP₁card.symm.trans_le (card_mono hPP₁))
  let δ := pairColorApproxScale ε F #P.parts
  have hδ : 0 < δ := pairColorApproxScale_pos hε (hF #P.parts)
  have hsize : ∀ A' ∈ Q.parts, 8 * (k + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #A' := fun _ hA' ↦
    fine_part_size_of_floor hε (hF #P.parts) hcard hQ hmM hQcard hA'
  have hηδ : (k : ℝ) * pairColorApproxFineSchedule k ε F #P.parts ≤ δ ^ 3 / 2 := by
    rw [pairColorApproxFineSchedule_def, mul_div_assoc',
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [show 0 ≤ δ ^ 3 by positivity]
  obtain ⟨R, hRrev, hRfine, hRedit⟩ := S.exists_recoloring_of_refinement hQP hδ hηδ hsize
  obtain ⟨hTreg, hTdens⟩ :=
    isPairColorRegular_fillDiagonal_of_refinement S R hQP hε (hF #P.parts) hsize hRfine
  refine ⟨P, R.fillDiagonal P, hPP₁.trans hP₁P₀, hP, (le_max_left l _).trans ht₀_P, hmM,
    funext fun c ↦ by simp [hRrev], hTreg, hTdens, ?_⟩
  have hsub : (univ.filter fun p : V × V ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some) ⊆
      (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ∪
        (univ.filter fun p : V × V ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
          (R.colorOfPair p.1 p.2).map some) := fun p hp ↦ by
    simp only [mem_union, mem_filter, mem_univ, true_and] at hp ⊢
    by_cases h : R.colorOfPair p.1 p.2 = S.colorOfPair p.1 p.2
    · exact Or.inr (by simpa only [h] using hp)
    · exact Or.inl h
  have htri : (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
      (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) +
        (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
          (R.colorOfPair p.1 p.2).map some} : ℝ) :=
    mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have hdiag := R.card_fillDiagonal_colorOfPair_ne_le_of_isEquipartition hP
  have hbud := approx_edit_budget_le (Fintype.card V : ℝ) hε (hF #P.parts)
    (sub_nonneg.2 (S.energy_mono_of_refines hQP)) hgap ((le_max_right l _).trans ht₀_P)
  linarith

end Main

end PairColorSystem

namespace PairSkeleton3

variable {κ V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- **Lower-skeleton regular approximation.** Given a lower skeleton `S` whose vertex partition is
equitable, an edit tolerance `ε > 0`, a positive schedule `F : ℕ → ℝ`, and a minimum cell count `l`,
once `V` exceeds `pairColorApproximationFloor` at the shifted schedule `m ↦ F (m + (card κ + 1))`
there exists an approximating lower skeleton `S'` on palette `Option κ` whose vertex equipartition
refines `S.vertexPart` into between `l` and `pairColorApproximationBound` cells, satisfies
`S'.LowerSkeletonRegular F`, preserves off-diagonal coarse color densities within
`min ε (F (#S'.vertexPart.parts + (card κ + 1)))`, and edits at most `ε |V|²` ordered distinct
vertex pairs. -/
theorem exists_lowerSkeletonRegular_approximation [Fintype κ] (S : PairSkeleton3 κ V)
    (hS : S.vertexPart.IsEquipartition) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    {l : ℕ}
    (hcard : pairColorApproximationFloor (Fintype.card κ) ε
      (fun m ↦ F (m + (Fintype.card κ + 1))) l #S.vertexPart.parts ≤ Fintype.card V) :
    ∃ S' : PairSkeleton3 (Option κ) V,
      S'.vertexPart ≤ S.vertexPart ∧ S'.vertexPart.IsEquipartition ∧
      l ≤ #S'.vertexPart.parts ∧
      #S'.vertexPart.parts ≤ pairColorApproximationBound (Fintype.card κ) ε
        (fun m ↦ F (m + (Fintype.card κ + 1))) l #S.vertexPart.parts ∧
      S'.pairColors.rev = Option.map S.pairColors.rev ∧
      S'.LowerSkeletonRegular F ∧
      (∀ A ∈ S'.vertexPart.parts, ∀ B ∈ S'.vertexPart.parts, A ≠ B → ∀ c,
        |(pairColorDensity S'.pairColors c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S.pairColors c A B : ℝ))| ≤
            min ε (F (#S'.vertexPart.parts + (Fintype.card κ + 1)))) ∧
      (#{q : {p : V × V // p.1 ≠ p.2} |
          S'.pairColors.color q ≠ some (S.pairColors.color q)} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨P, T, hPP₀, hP, hlP, hPM, hrev, hreg, hdens, hedit⟩ :=
    S.pairColors.exists_regular_approximation S.vertexPart hS hε
      (F := fun m ↦ F (m + (Fintype.card κ + 1))) (fun m ↦ hF _) hcard
  refine ⟨⟨P, T⟩, hPP₀, hP, hlP, hPM, hrev, ?_, hdens, ?_⟩
  · rw [lowerSkeletonRegular_iff, Fintype.card_option]
    exact hreg
  · rwa [S.pairColors.card_color_ne_eq_card_colorOfPair_ne T some]

end PairSkeleton3

end TauCeti
