/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Diagonal
public import TauCeti.Combinatorics.Hypergraph.PairColor.StrongRegularization
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.CoupledColoring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import TauCeti.Data.Finset.Basic

/-!
# Strong regular approximation of pair-color systems and lower skeletons

Given a pair-color system `S` on a finite palette `κ`, an equitable vertex partition `P₀`, a
minimum cell count `t₀`, a pair-edit budget `δ > 0`, and an arbitrary positive regularity schedule
`F : ℕ → ℝ`, we construct an equitable refinement `P ≤ P₀` of host-independent bounded complexity
and a modified pair-color system `T` on `Option κ` (one fresh reversal-fixed diagonal color `none`
plus the original palette `some c`) such that:

* `(⟨P, T⟩ : PairSkeleton3 (Option κ) V)` is `F #P.parts`-regular on *every* ordered pair of cells
  of `P` (diagonal pairs included);
* off-diagonal cell densities of `T` match those of `S` within `F #P.parts`; and
* `T` differs from `S` on at most `δ |V|²` ordered vertex pairs, provided `|V|` is at least a
  host-independent threshold.

Specializing the schedule to `fun t ↦ F (t + (card κ + 1))` and relabelling `Option κ` to
`Fin (card κ + 1)` yields `PairSkeleton3.exists_refining_lowerSkeletonRegular`: every equitable
lower skeleton `S : PairSkeleton3 κ V` admits a vertex-refining, pair-edited lower skeleton
`T : PairSkeleton3 (Fin (card κ + 1)) V` that satisfies `T.LowerSkeletonRegular F` while editing at
most `δ |V|²` ordered distinct pairs.

## Proof outline

1. Refine `P₀` cell-by-cell (`IsEquipartition.exists_refining_equipartition_card_eq_mul`) to an
   equipartition `P₁ ≤ P₀` with `#P₁.parts ≥ max t₀ ⌈4 / δ⌉₊`, ensuring `t₀ ≤ #P.parts` and
   charging within-cell diagonal cleanup at most `(δ / 4) |V|²` ordered pairs.
2. Apply strong seeded pair-color regularization
   (`PairColorSystem.exists_strong_refining_equipartition`) below `P₁` with energy-gap tolerance
   `γ = (δ / (4 * (card κ + 1))) ^ 2` and fine tolerance
   `η t = min (δ / (8 * (card κ + 1))) ((min (F t) 1) ^ 3 / (4 * (card κ + 1)))`, obtaining nested
   equipartitions `Q ≤ P ≤ P₁` with `S.energy Q - S.energy P ≤ γ`.
3. On each fine block `A' ×ˢ B'` whose coarse parents `A ≠ B` in `P` are distinct:
   * if `(A', B')` is `η #P.parts`-regular for `S`, couple `S` to the coarse distribution
     `pairColorDensity S · A B` via `TauCeti.exists_coupled_coloring_abs_card_filter_sub_lt_of_le`;
   * if `(A', B')` is irregular, sample an independent quasi-random coloring from
     `pairColorDensity S · A B` via `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`.
   Keep `S` unchanged on fine blocks inside a single coarse cell, then apply `fillDiagonal P`.
4. Summing fine-block discrepancies over `A' ⊆ A` and `B' ⊆ B` yields `F #P.parts`-regularity of
   `(P, T)`, while the edit count splits into four `(δ / 4) |V|²` contributions: diagonal cleanup,
   irregular fine blocks, total variation from the energy gap, and concentration slack.

## Main definitions

* `TauCeti.pairColorApproximationStepTol`: per-step fine-regularity and concentration tolerance.
* `TauCeti.pairColorApproximationBound`: host-independent upper bound on `#P.parts`.
* `TauCeti.pairColorApproximationThreshold`: host-independent lower threshold on `|V|`.
* `TauCeti.lowerSkeletonApproximationBound` and `TauCeti.lowerSkeletonApproximationThreshold`:
  corresponding bounds for scheduled `LowerSkeletonRegular`.

## Main results

* `TauCeti.PairColorSystem.exists_refining_equipartition_isPairColorRegular`: strong regular
  approximation of a `PairColorSystem` below an equitable seed.
* `TauCeti.PairSkeleton3.exists_refining_lowerSkeletonRegular`: strong regular approximation of a
  `PairSkeleton3` achieving `LowerSkeletonRegular F` over palette `Fin (card κ + 1)`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.5 and Lemma 4.2.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
-/

public section

open Finset Finpartition Real

namespace TauCeti

section Bounds

/-- Per-step fine-regularity and concentration tolerance used in strong regular approximation of a
pair-color system with an `m`-color palette, edit budget `δ`, and target schedule `F`. -/
noncomputable def pairColorApproximationStepTol (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t : ℕ) : ℝ :=
  min (δ / (8 * (m + 1))) ((min (F t) 1) ^ 3 / (4 * (m + 1)))

/-- Unfolding lemma for `TauCeti.pairColorApproximationStepTol`. -/
theorem pairColorApproximationStepTol_def (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t : ℕ) :
    pairColorApproximationStepTol m δ F t =
      min (δ / (8 * (m + 1))) ((min (F t) 1) ^ 3 / (4 * (m + 1))) :=
  (rfl)

/-- `TauCeti.pairColorApproximationStepTol` is positive when `δ > 0` and `F` is positive. -/
theorem pairColorApproximationStepTol_pos {m : ℕ} {δ : ℝ} {F : ℕ → ℝ} (hδ : 0 < δ)
    (hF : ∀ n, 0 < F n) (t : ℕ) : 0 < pairColorApproximationStepTol m δ F t := by
  rw [pairColorApproximationStepTol_def]
  exact lt_min (by positivity) (div_pos (pow_pos (lt_min (hF t) one_pos) 3) (by positivity))

/-- Host-independent upper bound on the number of vertex cells produced by
`PairColorSystem.exists_refining_equipartition_isPairColorRegular` for an `m`-color palette, edit
budget `δ`, target schedule `F`, minimum cell count `t₀`, and seed complexity `l₀`. -/
noncomputable def pairColorApproximationBound (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) : ℕ :=
  strongPairColorRegularityBound ((δ / (4 * (m + 1))) ^ 2)
    (pairColorApproximationStepTol m δ F) (max (max t₀ ⌈4 / δ⌉₊) 1 * max l₀ 1)

/-- Unfolding lemma for `TauCeti.pairColorApproximationBound`. -/
theorem pairColorApproximationBound_def (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) :
    pairColorApproximationBound m δ F t₀ l₀ =
      strongPairColorRegularityBound ((δ / (4 * (m + 1))) ^ 2)
        (pairColorApproximationStepTol m δ F) (max (max t₀ ⌈4 / δ⌉₊) 1 * max l₀ 1) :=
  (rfl)

/-- When `δ > 0` and `F` is positive, `TauCeti.pairColorApproximationBound` is at least `t₀`. -/
theorem le_pairColorApproximationBound_left {m : ℕ} {δ : ℝ} {F : ℕ → ℝ} (hδ : 0 < δ)
    (hF : ∀ n, 0 < F n) (t₀ l₀ : ℕ) : t₀ ≤ pairColorApproximationBound m δ F t₀ l₀ := by
  rw [pairColorApproximationBound_def]
  calc t₀ ≤ max (max t₀ ⌈4 / δ⌉₊) 1 := (le_max_left _ _).trans (le_max_left _ _)
    _ ≤ max (max t₀ ⌈4 / δ⌉₊) 1 * max l₀ 1 := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ _ := le_strongPairColorRegularityBound _ (pairColorApproximationStepTol_pos hδ hF) _

/-- When `δ > 0` and `F` is positive, `TauCeti.pairColorApproximationBound` is at least `l₀`. -/
theorem le_pairColorApproximationBound_right {m : ℕ} {δ : ℝ} {F : ℕ → ℝ} (hδ : 0 < δ)
    (hF : ∀ n, 0 < F n) (t₀ l₀ : ℕ) : l₀ ≤ pairColorApproximationBound m δ F t₀ l₀ := by
  rw [pairColorApproximationBound_def]
  calc l₀ ≤ max l₀ 1 := le_max_left _ _
    _ ≤ max (max t₀ ⌈4 / δ⌉₊) 1 * max l₀ 1 := Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ _ := le_strongPairColorRegularityBound _ (pairColorApproximationStepTol_pos hδ hF) _

/-- Host-independent vertex-count threshold above which
`PairColorSystem.exists_refining_equipartition_isPairColorRegular` applies. -/
noncomputable def pairColorApproximationThreshold (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) : ℕ :=
  let K := pairColorApproximationBound m δ F t₀ l₀
  max 2 (K * max ((range (K + 1)).sup fun t ↦
    ⌈(m + 3 : ℝ) / (pairColorApproximationStepTol m δ F t) ^ 2⌉₊) 1)

/-- Unfolding lemma for `TauCeti.pairColorApproximationThreshold`. -/
theorem pairColorApproximationThreshold_def (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) :
    pairColorApproximationThreshold m δ F t₀ l₀ =
      let K := pairColorApproximationBound m δ F t₀ l₀
      max 2 (K * max ((range (K + 1)).sup fun t ↦
        ⌈(m + 3 : ℝ) / (pairColorApproximationStepTol m δ F t) ^ 2⌉₊) 1) :=
  (rfl)

/-- Host-independent upper bound on `#T.vertexPart.parts` in
`PairSkeleton3.exists_refining_lowerSkeletonRegular`. -/
noncomputable def lowerSkeletonApproximationBound (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) : ℕ :=
  pairColorApproximationBound m δ (fun t ↦ F (t + (m + 1))) t₀ l₀

/-- Unfolding lemma for `TauCeti.lowerSkeletonApproximationBound`. -/
theorem lowerSkeletonApproximationBound_def (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) :
    lowerSkeletonApproximationBound m δ F t₀ l₀ =
      pairColorApproximationBound m δ (fun t ↦ F (t + (m + 1))) t₀ l₀ :=
  (rfl)

/-- Host-independent vertex-count threshold for
`PairSkeleton3.exists_refining_lowerSkeletonRegular`. -/
noncomputable def lowerSkeletonApproximationThreshold (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) :
    ℕ :=
  pairColorApproximationThreshold m δ (fun t ↦ F (t + (m + 1))) t₀ l₀

/-- Unfolding lemma for `TauCeti.lowerSkeletonApproximationThreshold`. -/
theorem lowerSkeletonApproximationThreshold_def (m : ℕ) (δ : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) :
    lowerSkeletonApproximationThreshold m δ F t₀ l₀ =
      pairColorApproximationThreshold m δ (fun t ↦ F (t + (m + 1))) t₀ l₀ :=
  (rfl)

end Bounds

namespace PairColorSystem

variable {κ V : Type*}

/-- Concentration union bound for coupled and independent block recolorings: when
`card κ + 3 ≤ η ^ 2 * #s` and `card κ + 3 ≤ η ^ 2 * #t`, the union bound over `2 ^ (#s + #t) + 1`
test sets and all `card κ` colors succeeds at deviation `η * (#s * #t)`. -/
private theorem two_mul_two_pow_add_one_mul_exp_lt [Fintype κ] [Nonempty κ] {η : ℝ}
    {s t : Finset V} (hs : (Fintype.card κ + 3 : ℝ) ≤ η ^ 2 * #s)
    (ht : (Fintype.card κ + 3 : ℝ) ≤ η ^ 2 * #t) :
    2 * (2 ^ #s * 2 ^ #t + 1 : ℕ) * Fintype.card κ *
      exp (-2 * (η * (#s * #t : ℕ)) ^ 2 / (#s * #t : ℕ)) < 1 := by
  have hs_pos : (0 : ℝ) < #s := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg η) h]
  have ht_pos : (0 : ℝ) < #t := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg η) h]
  have hs1 : 1 ≤ #s := Nat.cast_pos.1 hs_pos
  have ht1 : 1 ≤ #t := Nat.cast_pos.1 ht_pos
  have hpow_ge : 1 ≤ 2 ^ #s * 2 ^ #t := Nat.mul_pos (by positivity) (by positivity)
  have hpref : (2 * (2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) ≤ exp 2 * (exp #s * exp #t) := by
    have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    have h4 : (4 : ℝ) ≤ exp 2 := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
        _ = exp 2 := by rw [← exp_nat_mul]; norm_num
    have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ exp k :=
      (pow_le_pow_left₀ (by norm_num) h2 k).trans_eq (by rw [← exp_nat_mul, mul_one])
    have hle : (2 * (2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) ≤ 4 * ((2 : ℝ) ^ #s * (2 : ℝ) ^ #t) := by
      have : 2 * (2 ^ #s * 2 ^ #t + 1) ≤ 4 * (2 ^ #s * 2 ^ #t) := by omega
      exact_mod_cast this
    exact hle.trans (mul_le_mul h4 (mul_le_mul (hpow #s) (hpow #t) (by positivity) (by positivity))
      (by positivity) (by positivity))
  have hKexp : (Fintype.card κ : ℝ) ≤ exp (Fintype.card κ - 1) := by
    linarith [add_one_le_exp ((Fintype.card κ : ℝ) - 1)]
  have hexp : -2 * (η * (#s * #t : ℕ)) ^ 2 / ((#s * #t : ℕ) : ℝ) = -2 * (η ^ 2 * #s) * #t := by
    push_cast
    field_simp
  calc 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) * Fintype.card κ *
        exp (-2 * (η * (#s * #t : ℕ)) ^ 2 / (#s * #t : ℕ))
      ≤ (exp 2 * (exp #s * exp #t)) * exp (Fintype.card κ - 1) *
          exp (-2 * (η ^ 2 * #s) * #t) := by
        rw [hexp]
        gcongr
    _ = exp (#s + #t + Fintype.card κ + 1 - 2 * (η ^ 2 * #s) * #t) := by
        simp only [← exp_add]
        ring_nf
    _ < 1 := by
        rw [exp_lt_one_iff, sub_neg]
        nlinarith [Nat.one_le_cast (α := ℝ) |>.2 hs1, Nat.one_le_cast (α := ℝ) |>.2 ht1,
          mul_le_mul_of_nonneg_right hs ht_pos.le,
          mul_le_mul_of_nonneg_right ht hs_pos.le]

variable [Fintype V] [DecidableEq V]

section FineBlockGlue

variable {P Q : Finpartition (univ : Finset V)} (S : PairColorSystem κ V) (hQP : Q ≤ P)
  (idx : Q.parts ↪ ℕ) (x : Q.parts → Q.parts → V × V → κ)

/-- Assemble local block colorings `x A' B'` on fine cells `A', B' : Q.parts` with distinct coarse
parents in `P`, orienting unordered pairs via `idx : Q.parts ↪ ℕ` and preserving `S` whenever `A'`
and `B'` share the same coarse parent in `P`. -/
private noncomputable def recolorFineBlocks : PairColorSystem κ V where
  color p :=
    let A' : Q.parts := ⟨Q.part p.1.1, Q.part_mem.2 (mem_univ _)⟩
    let B' : Q.parts := ⟨Q.part p.1.2, Q.part_mem.2 (mem_univ _)⟩
    if refinementParent hQP A' = refinementParent hQP B' then S.color p
    else if idx A' < idx B' then x A' B' p.1
    else S.rev (x B' A' p.1.swap)
  rev := S.rev
  rev_involutive := S.rev_involutive
  color_rev p := by
    let A' : Q.parts := ⟨Q.part p.1.1, Q.part_mem.2 (mem_univ _)⟩
    let B' : Q.parts := ⟨Q.part p.1.2, Q.part_mem.2 (mem_univ _)⟩
    change (if refinementParent hQP B' = refinementParent hQP A' then
        S.color ⟨p.1.swap, p.2.symm⟩
      else if idx B' < idx A' then x B' A' p.1.swap
      else S.rev (x A' B' p.1)) =
      S.rev (if refinementParent hQP A' = refinementParent hQP B' then S.color p
        else if idx A' < idx B' then x A' B' p.1
        else S.rev (x B' A' p.1.swap))
    by_cases hpar : refinementParent hQP A' = refinementParent hQP B'
    · simp only [hpar, ↓reduceIte, S.color_rev]
    · have hpar' : refinementParent hQP B' ≠ refinementParent hQP A' := Ne.symm hpar
      have hne : idx A' ≠ idx B' := idx.injective.ne fun h ↦ hpar (h ▸ rfl)
      simp only [hpar, hpar', ↓reduceIte]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp only [hlt, lt_asymm hlt, ↓reduceIte]
      · simp only [hgt, lt_asymm hgt, ↓reduceIte, S.rev_rev]

@[simp]
private theorem recolorFineBlocks_rev : (S.recolorFineBlocks hQP idx x).rev = S.rev :=
  (rfl)

/-- On pairs whose fine cells have the same coarse parent, `recolorFineBlocks` agrees with `S`. -/
private theorem recolorFineBlocks_colorOfPair_of_parent_eq {u v : V}
    (h : refinementParent hQP ⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩ =
      refinementParent hQP ⟨Q.part v, Q.part_mem.2 (mem_univ v)⟩) :
    (S.recolorFineBlocks hQP idx x).colorOfPair u v = S.colorOfPair u v := by
  by_cases huv : u = v
  · simp [huv]
  · rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
    dsimp only [recolorFineBlocks]
    simp only [h, ↓reduceIte]

/-- On `A' ×ˢ B'` with `refinementParent hQP A' ≠ refinementParent hQP B'` and `idx A' < idx B'`,
`recolorFineBlocks` applies `x A' B'`. -/
private theorem recolorFineBlocks_colorOfPair_of_lt {A' B' : Q.parts}
    (hpar : refinementParent hQP A' ≠ refinementParent hQP B') (hlt : idx A' < idx B')
    {u v : V} (hu : u ∈ A'.1) (hv : v ∈ B'.1) :
    (S.recolorFineBlocks hQP idx x).colorOfPair u v = some (x A' B' (u, v)) := by
  have hdisj : Disjoint A'.1 B'.1 :=
    (P.disjoint (refinementParent hQP A').2 (refinementParent hQP B').2
      (Subtype.coe_injective.ne hpar)).mono
      (le_refinementParent hQP A') (le_refinementParent hQP B')
  have huv : u ≠ v := hdisj.forall_ne_finset hu hv
  have hA' : (⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩ : Q.parts) = A' :=
    Subtype.ext (Q.part_eq_of_mem A'.2 hu)
  have hB' : (⟨Q.part v, Q.part_mem.2 (mem_univ v)⟩ : Q.parts) = B' :=
    Subtype.ext (Q.part_eq_of_mem B'.2 hv)
  rw [colorOfPair_of_ne _ huv]
  dsimp only [recolorFineBlocks]
  rw [hA', hB']
  simp only [hpar, hlt, ↓reduceIte]

end FineBlockGlue

section LocalBlockChoice

variable {P Q : Finpartition (univ : Finset V)} (S : PairColorSystem κ V) (hQP : Q ≤ P)

open Classical in
/-- Coupled local coloring on an `η`-regular fine block `A' ×ˢ B'` with distinct coarse parents. -/
private theorem exists_local_block_coloring_of_isRegularPair [Fintype κ] [Nonempty κ] {η : ℝ}
    (hη : 0 < η) {A' B' : Q.parts} (hpar : refinementParent hQP A' ≠ refinementParent hQP B')
    (hs : (Fintype.card κ + 3 : ℝ) ≤ η ^ 2 * #A'.1)
    (ht : (Fintype.card κ + 3 : ℝ) ≤ η ^ 2 * #B'.1)
    (hreg : S.IsRegularPair η A'.1 B'.1) :
    ∃ x : V × V → κ,
      (∀ c, ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1,
        |(#{p ∈ s' ×ˢ t' | x p = c} : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1 *
              (#s' * #t')| ≤
          2 * Fintype.card κ * η * (#A'.1 * #B'.1)) ∧
      (#{p ∈ A'.1 ×ˢ B'.1 | some (x p) ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
        (1 / 2) * (∑ c, (#A'.1 * #B'.1 : ℝ) *
          |(pairColorDensity S c A'.1 B'.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) +
          Fintype.card κ * η * (#A'.1 * #B'.1) := by
  set A := refinementParent hQP A'
  set B := refinementParent hQP B'
  have hdisjP : Disjoint A.1 B.1 := P.disjoint A.2 B.2 (Subtype.coe_injective.ne hpar)
  have hdisj : Disjoint A'.1 B'.1 :=
    hdisjP.mono (le_refinementParent hQP A') (le_refinementParent hQP B')
  have hsuppP : ((A.1 ×ˢ B.1).filter fun p ↦ p.1 ≠ p.2).Nonempty := by
    rw [filter_ne_product_of_disjoint hdisjP]
    exact (P.nonempty_of_mem_parts A.2).product (P.nonempty_of_mem_parts B.2)
  let q : κ → ℝ := fun c ↦ (pairColorDensity S c A.1 B.1 : ℝ)
  have hq0 (c : κ) : 0 ≤ q c := by
    dsimp only [q]; exact_mod_cast pairColorDensity_nonneg S c A.1 B.1
  have hq1 : ∑ c, q c = 1 := by
    dsimp only [q]; exact_mod_cast sum_pairColorDensity S A.1 B.1 hsuppP
  set Z := A'.1 ×ˢ B'.1
  have hZpos : (0 : ℝ) < #Z := by
    rw [card_product, Nat.cast_mul]
    exact mul_pos (Nat.cast_pos.2 (Q.nonempty_of_mem_parts A'.2).card_pos)
      (Nat.cast_pos.2 (Q.nonempty_of_mem_parts B'.2).card_pos)
  let T : ↥(A'.1.powerset ×ˢ B'.1.powerset) → Finset (V × V) := fun i ↦ i.1.1 ×ˢ i.1.2
  have hT_le (i) : #(T i) ≤ #Z := by
    obtain ⟨hs', ht'⟩ := mem_product.1 i.2
    rw [card_product, card_product]
    exact Nat.mul_le_mul (card_le_card (mem_powerset.1 hs')) (card_le_card (mem_powerset.1 ht'))
  let y : V × V → κ := fun p ↦ if hp : p.1 ≠ p.2 then S.color ⟨p, hp⟩ else Classical.arbitrary κ
  have hy_eq {s' t' : Finset V} (hs' : s' ⊆ A'.1) (ht' : t' ⊆ B'.1) (b : κ) :
      {p ∈ s' ×ˢ t' | y p = b} = {p ∈ s' ×ˢ t' | S.colorOfPair p.1 p.2 = some b} :=
    filter_congr fun p hp ↦ by
      have hne := hdisj.forall_ne_finset (hs' (mem_product.1 hp).1) (ht' (mem_product.1 hp).2)
      simp [y, hne]
  have hyZ (b : κ) : (#{p ∈ Z | y p = b} : ℝ) = pairColorDensity S b A'.1 B'.1 * #Z := by
    rw [hy_eq Subset.rfl Subset.rfl, card_product, Nat.cast_mul]
    exact mod_cast (pairColorDensity_mul_card_of_disjoint S b hdisj).symm
  have hd (i) (b : κ) :
      |(#{p ∈ T i | y p = b} : ℝ) - (#{p ∈ Z | y p = b} : ℝ) / #Z * #(T i)| ≤
        η * (#A'.1 * #B'.1) := by
    obtain ⟨hs', ht'⟩ := mem_product.1 i.2
    rw [hy_eq (mem_powerset.1 hs') (mem_powerset.1 ht'), hyZ b, mul_div_cancel_right₀ _ hZpos.ne']
    simpa [T, card_product, mul_assoc] using
      hreg.abs_card_filter_colorOfPair_sub_le hdisj (mem_powerset.1 hs') (mem_powerset.1 ht')
  have hconc : 2 * (Fintype.card ↥(A'.1.powerset ×ˢ B'.1.powerset) + 1 : ℕ) * Fintype.card κ *
      exp (-2 * (η * #Z) ^ 2 / #Z) < 1 := by
    rw [Fintype.card_coe, card_product, card_powerset, card_powerset]
    simpa only [Z, card_product] using two_mul_two_pow_add_one_mul_exp_lt (κ := κ) hs ht
  obtain ⟨x, hedit, hdisc⟩ := exists_coupled_coloring_abs_card_filter_sub_lt_of_le Z y hq0 hq1 T
    hT_le (mul_pos hη hZpos) hd hconc
  refine ⟨x, fun c s' hs' t' ht' ↦ ?_, ?_⟩
  · have hi := hdisc ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
    dsimp only [T, Z, q] at hi
    rw [card_product, Nat.cast_mul, card_product, Nat.cast_mul] at hi
    linarith
  · have hedit_eq : {p ∈ Z | some (x p) ≠ S.colorOfPair p.1 p.2} = {p ∈ Z | x p ≠ y p} :=
      filter_congr fun p hp ↦ by
        have hne := hdisj.forall_ne_finset (mem_product.1 hp).1 (mem_product.1 hp).2
        simp [y, hne]
    have htv : ∑ c, |(#{p ∈ Z | y p = c} : ℝ) - q c * #Z| =
        ∑ c, (#A'.1 * #B'.1 : ℝ) * |(pairColorDensity S c A'.1 B'.1 : ℝ) - q c| :=
      sum_congr rfl fun c _ ↦ by
        rw [hyZ c, ← sub_mul, abs_mul, abs_of_pos hZpos, mul_comm, card_product, Nat.cast_mul]
    rw [hedit_eq]
    refine hedit.le.trans ?_
    dsimp only [Z, q] at htv ⊢
    rw [htv, card_product, Nat.cast_mul]
    linarith

open Classical in
/-- On a single fine block `A' ×ˢ B'` with distinct coarse parents `A ≠ B`, choose a coupled
coloring (when `(A', B')` is `η`-regular) or an independent random coloring (when `(A', B')` is
irregular) targeting `pairColorDensity S · A B`. -/
private theorem exists_local_block_coloring [Fintype κ] [Nonempty κ] {η : ℝ} (hη : 0 < η)
    (hsize : ∀ C ∈ Q.parts, (Fintype.card κ + 3 : ℝ) ≤ η ^ 2 * #C) (A' B' : Q.parts) :
    ∃ x : V × V → κ,
      (refinementParent hQP A' ≠ refinementParent hQP B' →
        ∀ c, ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1,
          |(#{p ∈ s' ×ˢ t' | x p = c} : ℝ) -
              pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1 *
                (#s' * #t')| ≤
            2 * Fintype.card κ * η * (#A'.1 * #B'.1)) ∧
      (refinementParent hQP A' ≠ refinementParent hQP B' → S.IsRegularPair η A'.1 B'.1 →
        (#{p ∈ A'.1 ×ˢ B'.1 | some (x p) ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
          (1 / 2) * (∑ c, (#A'.1 * #B'.1 : ℝ) *
            |(pairColorDensity S c A'.1 B'.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) +
            Fintype.card κ * η * (#A'.1 * #B'.1)) := by
  by_cases hpar : refinementParent hQP A' = refinementParent hQP B'
  · exact ⟨fun _ ↦ Classical.arbitrary κ, fun h ↦ (h hpar).elim, fun h ↦ (h hpar).elim⟩
  by_cases hreg : S.IsRegularPair η A'.1 B'.1
  · obtain ⟨x, hdisc, hedit⟩ := S.exists_local_block_coloring_of_isRegularPair hQP hη hpar
      (hsize A'.1 A'.2) (hsize B'.1 B'.2) hreg
    exact ⟨x, fun _ ↦ hdisc, fun _ _ ↦ hedit⟩
  · set A := refinementParent hQP A'
    set B := refinementParent hQP B'
    have hdisjP : Disjoint A.1 B.1 := P.disjoint A.2 B.2 (Subtype.coe_injective.ne hpar)
    have hsuppP : ((A.1 ×ˢ B.1).filter fun p ↦ p.1 ≠ p.2).Nonempty := by
      rw [filter_ne_product_of_disjoint hdisjP]
      exact (P.nonempty_of_mem_parts A.2).product (P.nonempty_of_mem_parts B.2)
    let q : κ → ℝ := fun c ↦ (pairColorDensity S c A.1 B.1 : ℝ)
    have hq0 (c : κ) : 0 ≤ q c := by
      dsimp only [q]; exact_mod_cast pairColorDensity_nonneg S c A.1 B.1
    have hq1 : ∑ c, q c = 1 := by
      dsimp only [q]; exact_mod_cast sum_pairColorDensity S A.1 B.1 hsuppP
    set Z := A'.1 ×ˢ B'.1
    have hZpos : (0 : ℝ) < #Z := by
      rw [card_product, Nat.cast_mul]
      exact mul_pos (Nat.cast_pos.2 (Q.nonempty_of_mem_parts A'.2).card_pos)
        (Nat.cast_pos.2 (Q.nonempty_of_mem_parts B'.2).card_pos)
    let T : ↥(A'.1.powerset ×ˢ B'.1.powerset) → Finset (V × V) := fun i ↦ i.1.1 ×ˢ i.1.2
    have hT_le (i) : #(T i) ≤ #Z := by
      obtain ⟨hs', ht'⟩ := mem_product.1 i.2
      rw [card_product, card_product]
      exact Nat.mul_le_mul (card_le_card (mem_powerset.1 hs')) (card_le_card (mem_powerset.1 ht'))
    have hconc_ind :
        2 * (Fintype.card ↥(A'.1.powerset ×ˢ B'.1.powerset) : ℝ) * Fintype.card κ *
          exp (-2 * (η * #Z) ^ 2 / #Z) < 1 := by
      have hle : (Fintype.card ↥(A'.1.powerset ×ˢ B'.1.powerset) : ℝ) ≤
          (2 ^ #A'.1 * 2 ^ #B'.1 + 1 : ℕ) := by
        rw [Fintype.card_coe, card_product, card_powerset, card_powerset]
        exact_mod_cast Nat.le_succ _
      have hle2 : 2 * (Fintype.card ↥(A'.1.powerset ×ˢ B'.1.powerset) : ℝ) ≤
          2 * (2 ^ #A'.1 * 2 ^ #B'.1 + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle2 (Nat.cast_nonneg _))
        (exp_pos _).le).trans_lt ?_
      simpa only [Z, card_product] using
        two_mul_two_pow_add_one_mul_exp_lt (κ := κ) (hsize A'.1 A'.2) (hsize B'.1 B'.2)
    obtain ⟨x, hdisc⟩ := exists_forall_abs_card_filter_sub_mul_card_lt hq0 hq1 T hT_le
      (mul_pos hη hZpos) hconc_ind
    refine ⟨x, fun _ c s' hs' t' ht' ↦ ?_, fun _ h ↦ (hreg h).elim⟩
    have hi := hdisc ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
    have hK1 : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
    have hηZ : 0 < η * (#A'.1 * #B'.1) := by
      rwa [card_product, Nat.cast_mul] at hZpos |> mul_pos hη
    dsimp only [T, Z, q] at hi
    rw [card_product, Nat.cast_mul, card_product, Nat.cast_mul] at hi
    nlinarith

open Classical in
/-- Discrepancy of `recolorFineBlocks` on any subrectangle `s' ×ˢ t'` of a fine block `A' ×ˢ B'`
with distinct coarse parents, in either orientation of `idx`. -/
private theorem abs_card_recolorFineBlocks_sub_le (idx : Q.parts ↪ ℕ)
    (x : Q.parts → Q.parts → V × V → κ) {τ : ℝ}
    (hdisc : ∀ A' B' : Q.parts, refinementParent hQP A' ≠ refinementParent hQP B' →
      ∀ c, ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1,
        |(#{p ∈ s' ×ˢ t' | x A' B' p = c} : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1 *
              (#s' * #t')| ≤ τ * (#A'.1 * #B'.1))
    {A' B' : Q.parts} (hpar : refinementParent hQP A' ≠ refinementParent hQP B')
    (c : κ) {s' t' : Finset V} (hs' : s' ⊆ A'.1) (ht' : t' ⊆ B'.1) :
    |(#{p ∈ s' ×ˢ t' | (S.recolorFineBlocks hQP idx x).colorOfPair p.1 p.2 = some c} : ℝ) -
        pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1 *
          (#s' * #t')| ≤
      τ * (#A'.1 * #B'.1) := by
  have hne : idx A' ≠ idx B' := idx.injective.ne fun h ↦ hpar (h ▸ rfl)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hf : {p ∈ s' ×ˢ t' | (S.recolorFineBlocks hQP idx x).colorOfPair p.1 p.2 = some c} =
        {p ∈ s' ×ˢ t' | x A' B' p = c} :=
      filter_congr fun p hp ↦ by
        rw [recolorFineBlocks_colorOfPair_of_lt S hQP idx x hpar hlt
          (hs' (mem_product.1 hp).1) (ht' (mem_product.1 hp).2), Option.some_inj]
    rw [hf]
    exact hdisc A' B' hpar c s' hs' t' ht'
  · have hswap : #{p ∈ s' ×ˢ t' | (S.recolorFineBlocks hQP idx x).colorOfPair p.1 p.2 = some c} =
        #{q ∈ t' ×ˢ s' | x B' A' q = S.rev c} := by
      refine card_equiv (Equiv.prodComm V V) fun p ↦ ?_
      simp only [mem_filter, mem_product, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      refine ⟨fun ⟨⟨hp₁, hp₂⟩, hc⟩ ↦ ⟨⟨hp₂, hp₁⟩, ?_⟩,
        fun ⟨⟨hp₂, hp₁⟩, hc⟩ ↦ ⟨⟨hp₁, hp₂⟩, ?_⟩⟩
      · rwa [← (S.recolorFineBlocks hQP idx x).colorOfPair_swap_eq_some_iff,
          recolorFineBlocks_rev,
          recolorFineBlocks_colorOfPair_of_lt S hQP idx x hpar.symm hgt (ht' hp₂) (hs' hp₁),
          Option.some_inj] at hc
      · rwa [← (S.recolorFineBlocks hQP idx x).colorOfPair_swap_eq_some_iff,
          recolorFineBlocks_rev,
          recolorFineBlocks_colorOfPair_of_lt S hQP idx x hpar.symm hgt (ht' hp₂) (hs' hp₁),
          Option.some_inj]
    rw [hswap, ← pairColorDensity_swap S c, mul_comm (#s' : ℝ), mul_comm (#A'.1 : ℝ)]
    exact hdisc B' A' hpar.symm (S.rev c) t' ht' s' hs'

open Classical in
/-- Summing fine-block discrepancies over `A' ⊆ A` and `B' ⊆ B` transfers fine rectangle
discrepancy `τ * (#A' * #B')` to coarse rectangle discrepancy `τ * (#A * #B)`. -/
private theorem abs_pairColorDensity_recolorFineBlocks_sub_mul_le (idx : Q.parts ↪ ℕ)
    (x : Q.parts → Q.parts → V × V → κ) {τ : ℝ}
    (hdisc : ∀ A' B' : Q.parts, refinementParent hQP A' ≠ refinementParent hQP B' →
      ∀ c, ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1,
        |(#{p ∈ s' ×ˢ t' | x A' B' p = c} : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1 *
              (#s' * #t')| ≤ τ * (#A'.1 * #B'.1))
    {A B : P.parts} (hAB : A ≠ B) (c : κ) {X Y : Finset V} (hXA : X ⊆ A.1) (hYB : Y ⊆ B.1) :
    |(pairColorDensity (S.recolorFineBlocks hQP idx x) c X Y : ℝ) -
        pairColorDensity S c A.1 B.1| * (#X * #Y) ≤ τ * (#A.1 * #B.1) := by
  set R := S.recolorFineBlocks hQP idx x
  have hdisjP : Disjoint A.1 B.1 := P.disjoint A.2 B.2 (Subtype.coe_injective.ne hAB)
  set FA : Finset Q.parts := {A' | refinementParent hQP A' = A}
  set FB : Finset Q.parts := {B' | refinementParent hQP B' = B}
  have hXeq : X = FA.biUnion fun A' ↦ X ∩ A'.1 := by
    conv_lhs => rw [← inter_eq_left.2 hXA, ← biUnion_filter_refinementParent_eq hQP A,
      inter_biUnion]
  have hYeq : Y = FB.biUnion fun B' ↦ Y ∩ B'.1 := by
    conv_lhs => rw [← inter_eq_left.2 hYB, ← biUnion_filter_refinementParent_eq hQP B,
      inter_biUnion]
  have hdisjFA : (FA : Set Q.parts).PairwiseDisjoint fun A' ↦ X ∩ A'.1 := fun A₁ _ A₂ _ hne ↦
    (Q.pairwiseDisjoint_subtype_val _ (Set.mem_univ _) (Set.mem_univ _) hne).mono
      inter_subset_right inter_subset_right
  have hdisjFB : (FB : Set Q.parts).PairwiseDisjoint fun B' ↦ Y ∩ B'.1 := fun B₁ _ B₂ _ hne ↦
    (Q.pairwiseDisjoint_subtype_val _ (Set.mem_univ _) (Set.mem_univ _) hne).mono
      inter_subset_right inter_subset_right
  have hcount_split : (#{p ∈ X ×ˢ Y | R.colorOfPair p.1 p.2 = some c} : ℝ) =
      ∑ A' ∈ FA, ∑ B' ∈ FB,
        (#{p ∈ (X ∩ A'.1) ×ˢ (Y ∩ B'.1) | R.colorOfPair p.1 p.2 = some c} : ℝ) := by
    have hprod : X ×ˢ Y = (FA ×ˢ FB).biUnion fun AB ↦ (X ∩ AB.1.1) ×ˢ (Y ∩ AB.2.1) := by
      ext ⟨u, v⟩
      have hu : u ∈ X ↔ ∃ A' ∈ FA, u ∈ X ∩ A'.1 := by conv_lhs => rw [hXeq]; rw [mem_biUnion]
      have hv : v ∈ Y ↔ ∃ B' ∈ FB, v ∈ Y ∩ B'.1 := by conv_lhs => rw [hYeq]; rw [mem_biUnion]
      simp only [mem_product, mem_biUnion, Prod.exists, hu, hv]
      exact ⟨fun ⟨⟨A', hA', huA'⟩, ⟨B', hB', hvB'⟩⟩ ↦ ⟨A', B', ⟨hA', hB'⟩, huA', hvB'⟩,
        fun ⟨A', B', ⟨hA', hB'⟩, huA', hvB'⟩ ↦ ⟨⟨A', hA', huA'⟩, ⟨B', hB', hvB'⟩⟩⟩
    have hdisj_prod : ((FA ×ˢ FB : Finset _) : Set _).PairwiseDisjoint
        fun AB : Q.parts × Q.parts ↦ (X ∩ AB.1.1) ×ˢ (Y ∩ AB.2.1) := by
      intro u hu v hv huv
      refine disjoint_product.2 ?_
      by_cases h₁ : u.1 = v.1
      · exact Or.inr (hdisjFB (mem_product.1 hu).2 (mem_product.1 hv).2 fun h₂ ↦
          huv (Prod.ext h₁ h₂))
      · exact Or.inl (hdisjFA (mem_product.1 hu).1 (mem_product.1 hv).1 h₁)
    rw [hprod, filter_biUnion, card_biUnion fun u hu v hv huv ↦
      disjoint_filter_filter (hdisj_prod hu hv huv), sum_product, Nat.cast_sum]
    exact sum_congr rfl fun A' _ ↦ Nat.cast_sum _ _
  have hXsum : (#X : ℝ) = ∑ A' ∈ FA, (#(X ∩ A'.1) : ℝ) := by
    have : #X = ∑ A' ∈ FA, #(X ∩ A'.1) := by
      conv_lhs => rw [← inter_eq_left.2 hXA, ← sum_card_inter_filter_refinementParent_eq hQP A X]
    exact_mod_cast this
  have hYsum : (#Y : ℝ) = ∑ B' ∈ FB, (#(Y ∩ B'.1) : ℝ) := by
    have : #Y = ∑ B' ∈ FB, #(Y ∩ B'.1) := by
      conv_lhs => rw [← inter_eq_left.2 hYB, ← sum_card_inter_filter_refinementParent_eq hQP B Y]
    exact_mod_cast this
  have hRcount : (#{p ∈ X ×ˢ Y | R.colorOfPair p.1 p.2 = some c} : ℝ) =
      pairColorDensity R c X Y * (#X * #Y) :=
    mod_cast (pairColorDensity_mul_card_of_disjoint R c (hdisjP.mono hXA hYB)).symm
  have hAsum : (∑ A' ∈ FA, (#A'.1 : ℝ)) = #A.1 := by
    exact_mod_cast sum_card_filter_refinementParent_eq hQP A
  have hBsum : (∑ B' ∈ FB, (#B'.1 : ℝ)) = #B.1 := by
    exact_mod_cast sum_card_filter_refinementParent_eq hQP B
  have hlhs : |(pairColorDensity R c X Y : ℝ) - pairColorDensity S c A.1 B.1| * (#X * #Y) =
      |(#{p ∈ X ×ˢ Y | R.colorOfPair p.1 p.2 = some c} : ℝ) -
        pairColorDensity S c A.1 B.1 * (#X * #Y)| := by
    rw [hRcount, ← sub_mul, abs_mul,
      abs_of_nonneg (a := (#X : ℝ) * #Y) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have hrhs : (pairColorDensity S c A.1 B.1 : ℝ) * (#X * #Y) =
      ∑ A' ∈ FA, ∑ B' ∈ FB,
        (pairColorDensity S c A.1 B.1 : ℝ) * (#(X ∩ A'.1) * #(Y ∩ B'.1)) := by
    rw [hXsum, hYsum, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun _ _ ↦ mul_sum _ _ _
  have hτ_sum : ∑ A' ∈ FA, ∑ B' ∈ FB, τ * ((#A'.1 : ℝ) * #B'.1) = τ * (#A.1 * #B.1) := by
    have : ∑ A' ∈ FA, ∑ B' ∈ FB, τ * ((#A'.1 : ℝ) * #B'.1) =
        τ * ((∑ A' ∈ FA, (#A'.1 : ℝ)) * (∑ B' ∈ FB, (#B'.1 : ℝ))) := by
      rw [sum_mul_sum, mul_sum]
      exact sum_congr rfl fun _ _ ↦ (mul_sum _ _ _).symm
    rw [this, hAsum, hBsum]
  rw [hlhs, hcount_split, hrhs]
  simp only [← sum_sub_distrib]
  refine ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ ↦ abs_sum_le_sum_abs _ _)).trans ?_
  refine (sum_le_sum fun A' hA' ↦ sum_le_sum fun B' hB' ↦ ?_).trans_eq hτ_sum
  have hA'p := (mem_filter.1 hA').2
  have hB'p := (mem_filter.1 hB').2
  have hpar' : refinementParent hQP A' ≠ refinementParent hQP B' := by rwa [hA'p, hB'p]
  simpa only [hA'p, hB'p] using abs_card_recolorFineBlocks_sub_le S hQP idx x hdisc
    hpar' c inter_subset_right inter_subset_right

open Classical in
/-- Coarse rectangle discrepancy `τ * (#A * #B)` yields `ε`-regularity and density preservation on
`(A, B)` whenever `2 * τ ≤ ε ^ 3` and `0 < ε ≤ 1`. -/
private theorem isRegularPair_recolorFineBlocks_of_le [Nonempty κ] (idx : Q.parts ↪ ℕ)
    (x : Q.parts → Q.parts → V × V → κ) {τ ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : 2 * τ ≤ ε ^ 3)
    (hdisc : ∀ A' B' : Q.parts, refinementParent hQP A' ≠ refinementParent hQP B' →
      ∀ c, ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1,
        |(#{p ∈ s' ×ˢ t' | x A' B' p = c} : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1 *
              (#s' * #t')| ≤ τ * (#A'.1 * #B'.1))
    {A B : P.parts} (hAB : A ≠ B) :
    (S.recolorFineBlocks hQP idx x).IsRegularPair ε A.1 B.1 ∧
      ∀ c, |(pairColorDensity (S.recolorFineBlocks hQP idx x) c A.1 B.1 : ℝ) -
        pairColorDensity S c A.1 B.1| ≤ ε := by
  set R := S.recolorFineBlocks hQP idx x
  have hrect := fun c {X Y} (hXA : X ⊆ A.1) (hYB : Y ⊆ B.1) ↦
    abs_pairColorDensity_recolorFineBlocks_sub_mul_le S hQP idx x hdisc hAB c hXA hYB
  have hAB_pos : (0 : ℝ) < #A.1 * #B.1 :=
    mul_pos (Nat.cast_pos.2 (P.nonempty_of_mem_parts A.2).card_pos)
      (Nat.cast_pos.2 (P.nonempty_of_mem_parts B.2).card_pos)
  have hτ0 : 0 ≤ τ := by
    obtain ⟨A', hA', hA'A⟩ := exists_le_of_le hQP A.2
    obtain ⟨B', hB', hB'B⟩ := exists_le_of_le hQP B.2
    have hpar' : refinementParent hQP ⟨A', hA'⟩ ≠ refinementParent hQP ⟨B', hB'⟩ := by
      rwa [(refinementParent_eq_iff hQP).2 hA'A, (refinementParent_eq_iff hQP).2 hB'B]
    have hpos' : (0 : ℝ) < #A' * #B' :=
      mul_pos (Nat.cast_pos.2 (Q.nonempty_of_mem_parts hA').card_pos)
        (Nat.cast_pos.2 (Q.nonempty_of_mem_parts hB').card_pos)
    have h0 := (abs_nonneg _).trans
      (hdisc ⟨A', hA'⟩ ⟨B', hB'⟩ hpar' (Classical.arbitrary κ)
        ∅ (empty_subset _) ∅ (empty_subset _))
    exact nonneg_of_mul_nonneg_left h0 hpos'
  have hfull (c : κ) : |(pairColorDensity R c A.1 B.1 : ℝ) - pairColorDensity S c A.1 B.1| ≤
      τ := le_of_mul_le_mul_right (hrect c Subset.rfl Subset.rfl) hAB_pos
  have hτ_le_ε : τ ≤ ε := by
    have : ε ^ 3 ≤ ε := pow_le_of_le_one hε0.le hε1 (by norm_num)
    linarith
  refine ⟨isRegularPair_iff.2 fun c X hXA Y hYB hX hY ↦ ?_, fun c ↦ (hfull c).trans hτ_le_ε⟩
  have hXY_ge : ε ^ 2 * (#A.1 * #B.1) ≤ #X * #Y := by
    calc ε ^ 2 * (#A.1 * #B.1) = (ε * #A.1) * (ε * #B.1) := by ring
      _ ≤ #X * #Y := mul_le_mul hX hY (by positivity) (by positivity)
  have hsub1 : |(pairColorDensity R c X Y : ℝ) - pairColorDensity S c A.1 B.1| ≤ τ / ε ^ 2 := by
    rw [le_div_iff₀ (pow_pos hε0 2)]
    calc |(pairColorDensity R c X Y : ℝ) - pairColorDensity S c A.1 B.1| * ε ^ 2
        ≤ |(pairColorDensity R c X Y : ℝ) - pairColorDensity S c A.1 B.1| *
            ((#X * #Y) / (#A.1 * #B.1)) :=
          mul_le_mul_of_nonneg_left ((le_div_iff₀ hAB_pos).2 hXY_ge) (abs_nonneg _)
      _ ≤ τ := by
          rw [← mul_div_assoc, div_le_iff₀ hAB_pos]
          exact hrect c hXA hYB
  have hτ_div : τ ≤ τ / ε ^ 2 := by
    rw [le_div_iff₀ (pow_pos hε0 2)]
    exact mul_le_of_le_one_right hτ0 (pow_le_one₀ hε0.le hε1)
  have hsum_le : τ / ε ^ 2 + τ ≤ ε := by
    have h2 : 2 * τ / ε ^ 2 ≤ ε := (div_le_iff₀ (pow_pos hε0 2)).2 (hτ.trans_eq (by ring))
    have hsplit2 : 2 * τ / ε ^ 2 = τ / ε ^ 2 + τ / ε ^ 2 := by ring
    linarith
  calc |(pairColorDensity R c X Y : ℝ) - pairColorDensity R c A.1 B.1|
      ≤ |(pairColorDensity R c X Y : ℝ) - (pairColorDensity S c A.1 B.1 : ℝ)| +
          |(pairColorDensity S c A.1 B.1 : ℝ) - (pairColorDensity R c A.1 B.1 : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ τ / ε ^ 2 + τ := by
        rw [abs_sub_comm (pairColorDensity S c A.1 B.1 : ℝ)]
        exact add_le_add hsub1 (hfull c)
    _ ≤ ε := hsum_le

/-- Summing total-variation density deviations over a subset `J` of distinct-parent fine-cell pairs
gives at most `card κ * √γ * |V|²` whenever `S.energy Q - S.energy P ≤ γ`. -/
private theorem sum_tv_of_subset_filter_refinementParent_ne_le [Fintype κ]
    {J : Finset (Q.parts × Q.parts)}
    (hJ : ∀ AB ∈ J, refinementParent hQP AB.1 ≠ refinementParent hQP AB.2)
    {γ : ℝ} (hγ : S.energy Q - S.energy P ≤ γ) :
    ∑ AB ∈ J, ∑ c, (#AB.1.1 * #AB.2.1 : ℝ) *
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| ≤
      Fintype.card κ * √γ * (Fintype.card V : ℝ) ^ 2 := by
  set I : Finset (Q.parts × Q.parts) :=
    (univ : Finset (Q.parts × Q.parts)).filter fun AB ↦
      refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  have hJI : J ⊆ I := fun AB hAB ↦ mem_filter.2 ⟨mem_univ _, hJ AB hAB⟩
  have h1 : ∑ AB ∈ J, ∑ c, (#AB.1.1 * #AB.2.1 : ℝ) *
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| ≤
      ∑ AB ∈ I, ∑ c, (#AB.1.1 * #AB.2.1 : ℝ) *
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| :=
    sum_le_sum_of_subset_of_nonneg hJI fun _ _ _ ↦ sum_nonneg fun _ _ ↦ by positivity
  have h2 : ∑ AB ∈ I, ∑ c, (#AB.1.1 * #AB.2.1 : ℝ) *
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| =
      ∑ c, ∑ AB ∈ I, (#AB.1.1 * #AB.2.1 : ℝ) *
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| :=
    Finset.sum_comm
  have h3 : ∑ c, ∑ AB ∈ I, (#AB.1.1 * #AB.2.1 : ℝ) *
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| ≤
      Fintype.card κ * √γ * #(univ : Finset V).offDiag := by
    refine (sum_le_sum fun c _ ↦ S.sum_card_mul_abs_pairColorDensity_sub_le hQP hγ c).trans_eq ?_
    rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc]
  have hoff : (#(univ : Finset V).offDiag : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have : #(univ : Finset V).offDiag ≤ Fintype.card V * Fintype.card V := by
      rw [offDiag_card, card_univ]
      exact Nat.sub_le _ _
    simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).2 this
  exact (h1.trans_eq h2).trans (h3.trans (mul_le_mul_of_nonneg_left hoff (by positivity)))

open Classical in
/-- Total ordered-pair edit bound for `recolorFineBlocks`: edits occur only on fine blocks with
distinct coarse parents, splitting into irregular fine blocks plus twice the `idx`-oriented regular
fine blocks. -/
private theorem card_recolorFineBlocks_colorOfPair_ne_le [Fintype κ] (idx : Q.parts ↪ ℕ)
    (x : Q.parts → Q.parts → V × V → κ) {η γ : ℝ} (hη : 0 ≤ η)
    (hirr : ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2)
    (hγ : S.energy Q - S.energy P ≤ γ)
    (hedit : ∀ A' B' : Q.parts, refinementParent hQP A' ≠ refinementParent hQP B' →
      S.IsRegularPair η A'.1 B'.1 →
        (#{p ∈ A'.1 ×ˢ B'.1 | some (x A' B' p) ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
          (1 / 2) * (∑ c, (#A'.1 * #B'.1 : ℝ) *
            |(pairColorDensity S c A'.1 B'.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) +
            Fintype.card κ * η * (#A'.1 * #B'.1)) :
    (#{p : V × V | (S.recolorFineBlocks hQP idx x).colorOfPair p.1 p.2 ≠
        S.colorOfPair p.1 p.2} : ℝ) ≤
      (η + Fintype.card κ * √γ + 2 * Fintype.card κ * η) * (Fintype.card V : ℝ) ^ 2 := by
  set R := S.recolorFineBlocks hQP idx x
  let E (s t : Finset V) : Finset (V × V) :=
    (s ×ˢ t).filter fun p ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2
  set J : Finset (Q.parts × Q.parts) :=
    univ.filter fun AB ↦ idx AB.1 < idx AB.2 ∧
      refinementParent hQP AB.1 ≠ refinementParent hQP AB.2 ∧ S.IsRegularPair η AB.1.1 AB.2.1
  have hcover : (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ⊆
      ((S.irregularPairs η Q).biUnion fun AB ↦ AB.1 ×ˢ AB.2) ∪
        J.biUnion fun AB ↦ E AB.1.1 AB.2.1 ∪ E AB.2.1 AB.1.1 := by
    intro p hp
    have hne := (mem_filter.1 hp).2
    let A' : Q.parts := ⟨Q.part p.1, Q.part_mem.2 (mem_univ _)⟩
    let B' : Q.parts := ⟨Q.part p.2, Q.part_mem.2 (mem_univ _)⟩
    have hpA' : p.1 ∈ A'.1 := Q.mem_part_self.2 (mem_univ _)
    have hpB' : p.2 ∈ B'.1 := Q.mem_part_self.2 (mem_univ _)
    have hpar : refinementParent hQP A' ≠ refinementParent hQP B' := fun heq ↦
      hne (recolorFineBlocks_colorOfPair_of_parent_eq S hQP idx x heq)
    have hAB_ne : A'.1 ≠ B'.1 := Subtype.coe_injective.ne fun h ↦ hpar (h ▸ rfl)
    by_cases hreg : S.IsRegularPair η A'.1 B'.1
    · refine mem_union.2 (Or.inr <| mem_biUnion.2 ?_)
      rcases lt_or_gt_of_ne (idx.injective.ne (Subtype.coe_injective.ne_iff.1 hAB_ne)) with
        hlt | hgt
      · exact ⟨(A', B'), mem_filter.2 ⟨mem_univ _, hlt, hpar, hreg⟩,
          mem_union_left _ (mem_filter.2 ⟨mem_product.2 ⟨hpA', hpB'⟩, hne⟩)⟩
      · exact ⟨(B', A'), mem_filter.2 ⟨mem_univ _, hgt, hpar.symm, hreg.symm⟩,
          mem_union_right _ (mem_filter.2 ⟨mem_product.2 ⟨hpA', hpB'⟩, hne⟩)⟩
    · exact mem_union.2 (Or.inl <| mem_biUnion.2
        ⟨(A'.1, B'.1), S.mem_irregularPairs.2 ⟨A'.2, B'.2, hAB_ne, hreg⟩,
          mem_product.2 ⟨hpA', hpB'⟩⟩)
  have hswap_card (A' B' : Q.parts) : #(E B'.1 A'.1) = #(E A'.1 B'.1) := by
    refine card_equiv (Equiv.prodComm V V) fun p ↦ ?_
    simp only [E, mem_filter, mem_product, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    have hiff : R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2 ↔
        R.colorOfPair p.2 p.1 ≠ S.colorOfPair p.2 p.1 := by
      rw [R.colorOfPair_swap p.1 p.2, S.colorOfPair_swap p.1 p.2, recolorFineBlocks_rev]
      exact (Option.map_injective S.rev_involutive.injective).ne_iff.symm
    exact ⟨fun ⟨⟨hp₁, hp₂⟩, hc⟩ ↦ ⟨⟨hp₂, hp₁⟩, hiff.1 hc⟩,
      fun ⟨⟨hp₂, hp₁⟩, hc⟩ ↦ ⟨⟨hp₁, hp₂⟩, hiff.2 hc⟩⟩
  have hJ_local (AB : Q.parts × Q.parts) (hAB : AB ∈ J) :
      (#(E AB.1.1 AB.2.1 ∪ E AB.2.1 AB.1.1) : ℝ) ≤
        (∑ c, (#AB.1.1 * #AB.2.1 : ℝ) *
          |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) +
          2 * Fintype.card κ * η * (#AB.1.1 * #AB.2.1) := by
    obtain ⟨-, hlt, hpar, hreg⟩ := mem_filter.1 hAB
    have heqE : E AB.1.1 AB.2.1 =
        {p ∈ AB.1.1 ×ˢ AB.2.1 | some (x AB.1 AB.2 p) ≠ S.colorOfPair p.1 p.2} :=
      filter_congr fun p hp ↦ by
        rw [recolorFineBlocks_colorOfPair_of_lt S hQP idx x hpar hlt
          (mem_product.1 hp).1 (mem_product.1 hp).2]
    have hunion : (#(E AB.1.1 AB.2.1 ∪ E AB.2.1 AB.1.1) : ℝ) ≤ 2 * #(E AB.1.1 AB.2.1) := by
      have := (card_union_le (E AB.1.1 AB.2.1) (E AB.2.1 AB.1.1)).trans_eq
        (by rw [hswap_card AB.1 AB.2, ← two_mul])
      exact_mod_cast this
    have hb := hedit AB.1 AB.2 hpar hreg
    rw [← heqE] at hb
    linarith
  have htv_sum := S.sum_tv_of_subset_filter_refinementParent_ne_le hQP
    (J := J) (fun AB hAB ↦ (mem_filter.1 hAB).2.2.1) hγ
  have hconc_sum : ∑ AB ∈ J, 2 * (Fintype.card κ : ℝ) * η * (#AB.1.1 * #AB.2.1) ≤
      2 * Fintype.card κ * η * (Fintype.card V : ℝ) ^ 2 := by
    calc ∑ AB ∈ J, 2 * (Fintype.card κ : ℝ) * η * (#AB.1.1 * #AB.2.1)
        ≤ ∑ AB : Q.parts × Q.parts, 2 * (Fintype.card κ : ℝ) * η * (#AB.1.1 * #AB.2.1) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ by positivity
      _ = 2 * Fintype.card κ * η * (∑ A' : Q.parts, (#A'.1 : ℝ)) *
            (∑ B' : Q.parts, (#B'.1 : ℝ)) := by
          rw [← mul_sum, Fintype.sum_prod_type]
          dsimp only
          rw [← sum_mul_sum]; ring
      _ = 2 * Fintype.card κ * η * (Fintype.card V : ℝ) ^ 2 := by
          rw [Q.sum_card_subtype, card_univ, sq]; ring
  have hirr_card : (#((S.irregularPairs η Q).biUnion fun AB ↦ AB.1 ×ˢ AB.2) : ℝ) ≤
      η * (Fintype.card V : ℝ) ^ 2 := by
    refine le_trans ?_ hirr
    exact_mod_cast card_biUnion_le.trans_eq (by simp [card_product])
  have hJ_card : (#(J.biUnion fun AB ↦ E AB.1.1 AB.2.1 ∪ E AB.2.1 AB.1.1) : ℝ) ≤
      (Fintype.card κ * √γ + 2 * Fintype.card κ * η) * (Fintype.card V : ℝ) ^ 2 := by
    calc (#(J.biUnion fun AB ↦ E AB.1.1 AB.2.1 ∪ E AB.2.1 AB.1.1) : ℝ)
        ≤ ∑ AB ∈ J, (#(E AB.1.1 AB.2.1 ∪ E AB.2.1 AB.1.1) : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ AB ∈ J, ((∑ c, (#AB.1.1 * #AB.2.1 : ℝ) *
            |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) +
            2 * Fintype.card κ * η * (#AB.1.1 * #AB.2.1)) := sum_le_sum hJ_local
      _ ≤ Fintype.card κ * √γ * (Fintype.card V : ℝ) ^ 2 +
            2 * Fintype.card κ * η * (Fintype.card V : ℝ) ^ 2 := by
          rw [sum_add_distrib]; exact add_le_add htv_sum hconc_sum
      _ = _ := by ring
  have htotal : (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
      (#((S.irregularPairs η Q).biUnion fun AB ↦ AB.1 ×ˢ AB.2) : ℝ) +
        #(J.biUnion fun AB ↦ E AB.1.1 AB.2.1 ∪ E AB.2.1 AB.1.1) := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  linarith

end LocalBlockChoice

/-- Within-cell distinct-pair count of an equipartition `P` is at most `|V|² / #P.parts`. -/
private theorem sum_card_mul_sub_one_le_of_isEquipartition {P : Finpartition (univ : Finset V)}
    (hP : P.IsEquipartition) :
    ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : ℝ) ≤
      (Fintype.card V : ℝ) ^ 2 / #P.parts := by
  have hnat : ∑ A ∈ P.parts, #A * (#A - 1) ≤ Fintype.card V * (Fintype.card V / #P.parts) := by
    calc ∑ A ∈ P.parts, #A * (#A - 1)
        ≤ ∑ A ∈ P.parts, #A * (Fintype.card V / #P.parts) :=
          sum_le_sum fun A hA ↦ Nat.mul_le_mul_left _ <| Nat.sub_le_of_le_add <| by
            simpa [card_univ] using hP.card_part_le_average_add_one hA
      _ = (∑ A ∈ P.parts, #A) * (Fintype.card V / #P.parts) := (sum_mul _ _ _).symm
      _ = Fintype.card V * (Fintype.card V / #P.parts) := by rw [P.sum_card_parts, card_univ]
  calc ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : ℝ)
      ≤ (Fintype.card V : ℝ) * (Fintype.card V / #P.parts : ℕ) := by exact_mod_cast hnat
    _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) / #P.parts) :=
        mul_le_mul_of_nonneg_left (Nat.cast_div_le ..) (Nat.cast_nonneg _)
    _ = (Fintype.card V : ℝ) ^ 2 / #P.parts := by ring

/-- When `|V|` exceeds `K` times the supremum of `⌈(m + 3) / (η t)²⌉₊` over `t ≤ K`, every cell of
an equipartition `Q` with `1 ≤ #Q.parts ≤ K` satisfies `m + 3 ≤ (η t)² * #C` for any `t ≤ K` with
`0 < η t`. -/
private theorem card_part_ge_of_sup_mul_le {Q : Finpartition (univ : Finset V)}
    (hQ : Q.IsEquipartition) {m K t : ℕ} {η : ℕ → ℝ} (hQ_pos : 0 < #Q.parts)
    (hQ_le_K : #Q.parts ≤ K) (ht_le_K : t ≤ K) (hη : 0 < η t)
    (hKM : K * max ((range (K + 1)).sup fun j ↦ ⌈(m + 3 : ℝ) / (η j) ^ 2⌉₊) 1 ≤ Fintype.card V)
    {C : Finset V} (hC : C ∈ Q.parts) :
    (m + 3 : ℝ) ≤ (η t) ^ 2 * #C := by
  have hK_pos : 0 < K := hQ_pos.trans_le hQ_le_K
  have hsup : ⌈(m + 3 : ℝ) / (η t) ^ 2⌉₊ ≤
      max ((range (K + 1)).sup fun j ↦ ⌈(m + 3 : ℝ) / (η j) ^ 2⌉₊) 1 :=
    (le_sup (f := fun j ↦ ⌈(m + 3 : ℝ) / (η j) ^ 2⌉₊)
      (mem_range.2 (Nat.lt_succ_of_le ht_le_K))).trans (le_max_left _ _)
  have hdivK : max ((range (K + 1)).sup fun j ↦ ⌈(m + 3 : ℝ) / (η j) ^ 2⌉₊) 1 ≤
      Fintype.card V / K := (Nat.le_div_iff_mul_le hK_pos).2 (by rwa [mul_comm])
  have hdivQ : Fintype.card V / K ≤ #C :=
    (Nat.div_le_div_left hQ_le_K hQ_pos).trans
      (by simpa [card_univ] using hQ.average_le_card_part hC)
  have hdiv_le : (m + 3 : ℝ) / (η t) ^ 2 ≤ #C :=
    (Nat.le_ceil _).trans (by exact_mod_cast hsup.trans (hdivK.trans hdivQ))
  exact (div_le_iff₀' (pow_pos hη 2)).1 hdiv_le

open Classical in
/-- Combine the off-diagonal edit bound between `R` and `S` with the diagonal cleanup edit bound of
`R.fillDiagonal P` into a single `δ |V|²` pair-edit bound. -/
private theorem card_fillDiagonal_colorOfPair_ne_le_of_le (S R : PairColorSystem κ V)
    {P : Finpartition (univ : Finset V)} (hP : P.IsEquipartition) {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) (h4δ : ⌈4 / δ⌉₊ ≤ #P.parts)
    (heditR : (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
      (pairColorApproximationStepTol m δ F #P.parts +
        m * √((δ / (4 * (m + 1))) ^ 2) +
        2 * m * pairColorApproximationStepTol m δ F #P.parts) * (Fintype.card V : ℝ) ^ 2) :
    (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some} : ℝ) ≤ δ * (Fintype.card V : ℝ) ^ 2 := by
  set η := pairColorApproximationStepTol m δ F #P.parts
  have hη_pos : 0 < η := pairColorApproximationStepTol_pos hδ hF #P.parts
  have hsub : (univ.filter fun p : V × V ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some) ⊆
      (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ∪
        (univ.filter fun p : V × V ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
          (R.colorOfPair p.1 p.2).map some) := by
    intro p hp
    simp only [mem_union, mem_filter, mem_univ, true_and] at hp ⊢
    by_cases h : R.colorOfPair p.1 p.2 = S.colorOfPair p.1 p.2
    · exact Or.inr (h ▸ hp)
    · exact Or.inl h
  have hPpos : (0 : ℝ) < #P.parts :=
    Nat.cast_pos.2 ((Nat.ceil_pos.2 (div_pos (by positivity) hδ)).trans_le h4δ)
  have hdiag_edit : (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (R.colorOfPair p.1 p.2).map some} : ℝ) ≤ (δ / 4) * (Fintype.card V : ℝ) ^ 2 := by
    rw [R.card_fillDiagonal_colorOfPair_ne P]
    refine (sum_card_mul_sub_one_le_of_isEquipartition hP).trans ?_
    have h4δ' : 4 / δ ≤ (#P.parts : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h4δ)
    rw [div_le_iff₀ hPpos]
    have : (1 : ℝ) ≤ δ / 4 * #P.parts := by rw [div_le_iff₀ hδ] at h4δ'; linarith
    nlinarith [sq_nonneg (Fintype.card V : ℝ)]
  have hη_δ : η ≤ δ / (8 * (m + 1)) := min_le_left _ _
  have h1 : η ≤ δ / 4 := hη_δ.trans <| by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have h2 : (m : ℝ) * √((δ / (4 * (m + 1))) ^ 2) ≤ δ / 4 := by
    rw [Real.sqrt_sq (by positivity : 0 ≤ δ / (4 * (m + 1)))]
    calc (m : ℝ) * (δ / (4 * (m + 1))) ≤ (m + 1 : ℝ) * (δ / (4 * (m + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = δ / 4 := by field_simp
  have h3 : 2 * (m : ℝ) * η ≤ δ / 4 := by
    calc 2 * (m : ℝ) * η ≤ 2 * (m + 1) * (δ / (8 * (m + 1))) :=
          mul_le_mul (by linarith) hη_δ hη_pos.le (by positivity)
      _ = δ / 4 := by field_simp; ring
  have hunion : (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
      (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) +
        #{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
          (R.colorOfPair p.1 p.2).map some} := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  nlinarith [sq_nonneg (Fintype.card V : ℝ)]

open Classical in
/-- **Strong regular approximation of a pair-color system below an equitable seed.**
Given an equipartition `P₀` of `V`, a minimum cell count `t₀`, a pair-edit budget `δ > 0`, and a
positive schedule `F : ℕ → ℝ`, once
`pairColorApproximationThreshold (card κ) δ F t₀ #P₀.parts ≤ |V|` there exist an equipartition
`P ≤ P₀` and a pair-color system `T` on `Option κ` such that:

* `t₀ ≤ #P.parts` and `#P.parts ≤ pairColorApproximationBound (card κ) δ F t₀ #P₀.parts`;
* `T.rev = Option.map S.rev`;
* `(⟨P, T⟩ : PairSkeleton3 (Option κ) V)` is `F #P.parts`-regular everywhere;
* off-diagonal cell densities of `T` agree with those of `S` within `F #P.parts`; and
* `T` edits at most `δ |V|²` ordered pairs relative to `S`. -/
theorem exists_refining_equipartition_isPairColorRegular [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) (t₀ : ℕ) {δ : ℝ}
    (hδ : 0 < δ) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : pairColorApproximationThreshold (Fintype.card κ) δ F t₀ #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧ t₀ ≤ #P.parts ∧
      #P.parts ≤ pairColorApproximationBound (Fintype.card κ) δ F t₀ #P₀.parts ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (F #P.parts) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity T c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤ F #P.parts) ∧
      (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
        δ * (Fintype.card V : ℝ) ^ 2 := by
  set m := Fintype.card κ
  set K := pairColorApproximationBound m δ F t₀ #P₀.parts
  set η := pairColorApproximationStepTol m δ F
  set γ := (δ / (4 * (m + 1))) ^ 2
  rw [pairColorApproximationThreshold_def] at hV
  have hV2 : 2 ≤ Fintype.card V := (le_max_left _ _).trans hV
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨u₀, v₀, huv₀⟩ := exists_pair_ne V
  have : Nonempty κ := ⟨S.color ⟨(u₀, v₀), huv₀⟩⟩
  have hP₀_pos : 1 ≤ #P₀.parts := (P₀.parts_nonempty univ_nonempty.ne_empty).card_pos
  -- Step 1: Equitably refine `P₀` to `P₁` with `#P₁.parts ≥ max t₀ ⌈4 / δ⌉₊`.
  let a := max (max t₀ ⌈4 / δ⌉₊) 1
  have ha0 : a ≠ 0 := by positivity
  have haP₀_le_K : a * #P₀.parts ≤ K := by
    dsimp only [K]
    rw [pairColorApproximationBound_def, max_eq_left hP₀_pos]
    exact le_strongPairColorRegularityBound _ (pairColorApproximationStepTol_pos hδ hF) _
  have hKM_le_V : K * max ((range (K + 1)).sup fun t ↦ ⌈(m + 3 : ℝ) / (η t) ^ 2⌉₊) 1 ≤
      Fintype.card V := (le_max_right _ _).trans hV
  have hK_le_V : K ≤ Fintype.card V :=
    (Nat.le_mul_of_pos_right K (by positivity)).trans hKM_le_V
  obtain ⟨P₁, hP₁, hP₁card, hP₁P₀, -⟩ := hP₀.exists_refining_equipartition_card_eq_mul ⊥ bot_le
    ha0 (by rw [card_univ]; exact haP₀_le_K.trans hK_le_V)
  -- Step 2: Strong seeded regularization below `P₁`.
  have hη_pos : ∀ n, 0 < η n := pairColorApproximationStepTol_pos hδ hF
  obtain ⟨P, Q, hPP₁, hQP, hP, hQ, -, hQ_le_K', hirr, hEgap⟩ :=
    S.exists_strong_refining_equipartition P₁ hP₁ (by positivity : 0 < γ) hη_pos
  have hQ_le_K : #Q.parts ≤ K := by
    refine hQ_le_K'.trans ?_
    dsimp only [K]
    rw [hP₁card, pairColorApproximationBound_def, max_eq_left hP₀_pos]
  have hP_le_K : #P.parts ≤ K := (card_mono hQP).trans hQ_le_K
  have ha_le_P : a ≤ #P.parts :=
    (Nat.le_mul_of_pos_right a hP₀_pos).trans (hP₁card.symm.trans_le (card_mono hPP₁))
  -- Step 3: Fine-cell size lower bound on `Q` for concentration.
  have hQ_pos : 0 < #Q.parts := (Nat.pos_of_ne_zero ha0).trans_le (ha_le_P.trans (card_mono hQP))
  have hsizeQ : ∀ C ∈ Q.parts, (m + 3 : ℝ) ≤ (η #P.parts) ^ 2 * #C := fun C hC ↦
    card_part_ge_of_sup_mul_le hQ hQ_pos hQ_le_K hP_le_K (hη_pos #P.parts) hKM_le_V hC
  -- Step 4: Coupled/independent fine-block recoloring + diagonal cleanup on `P`.
  let idx : Q.parts ↪ ℕ :=
    (Fintype.equivFin Q.parts).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩
  choose x hx_disc hx_edit using S.exists_local_block_coloring hQP (hη_pos #P.parts) hsizeQ
  set R := S.recolorFineBlocks hQP idx x
  set ε := min (F #P.parts) 1
  have hε0 : 0 < ε := lt_min (hF #P.parts) one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hτ_budget : 2 * (2 * (m : ℝ) * η #P.parts) ≤ ε ^ 3 := by
    calc 2 * (2 * (m : ℝ) * η #P.parts) = 4 * m * η #P.parts := by ring
      _ ≤ 4 * (m + 1) * (ε ^ 3 / (4 * (m + 1))) :=
          mul_le_mul (by linarith) (min_le_right _ _) (hη_pos _).le (by positivity)
      _ = ε ^ 3 := mul_div_cancel₀ _ (by positivity)
  have hR_off (A B : P.parts) (hAB : A ≠ B) :=
    S.isRegularPair_recolorFineBlocks_of_le hQP idx x hε0 hε1 hτ_budget hx_disc hAB
  have hdiag_size : ∀ A ∈ P.parts, 1 < ε * #A := by
    intro A hA
    obtain ⟨A', hA', hA'A⟩ := exists_le_of_le hQP hA
    have h1 : (3 : ℝ) ≤ (η #P.parts) ^ 2 * #A' :=
      (by linarith [Nat.cast_nonneg (α := ℝ) m] : (3 : ℝ) ≤ m + 3).trans (hsizeQ A' hA')
    have hη_le_ε : η #P.parts ≤ ε := by
      have hε3 : ε ^ 3 ≤ ε := pow_le_of_le_one hε0.le hε1 (by norm_num)
      have hden : (1 : ℝ) ≤ 4 * (m + 1) := by linarith [Nat.cast_nonneg (α := ℝ) m]
      exact (min_le_right _ _).trans ((div_le_self (pow_nonneg hε0.le 3) hden).trans hε3)
    have hη_sq_le_ε : (η #P.parts) ^ 2 ≤ ε :=
      (pow_le_of_le_one (hη_pos _).le (hη_le_ε.trans hε1) (by norm_num)).trans hη_le_ε
    have hA'_le_A : (#A' : ℝ) ≤ #A := by exact_mod_cast card_le_card hA'A
    nlinarith [mul_le_mul hη_sq_le_ε hA'_le_A (Nat.cast_nonneg _) hε0.le]
  -- Step 5: Assemble regularity, density preservation, and pair-edit budget.
  refine ⟨P, R.fillDiagonal P, hPP₁.trans hP₁P₀, hP,
    ((le_max_left _ _).trans (le_max_left _ _)).trans ha_le_P, hP_le_K, by ext c; simp [R],
    (R.isPairColorRegular_fillDiagonal P hdiag_size fun A hA B hB hAB ↦
      (hR_off ⟨A, hA⟩ ⟨B, hB⟩ (Subtype.coe_injective.ne_iff.1 hAB)).1).mono (min_le_left _ _),
    fun A hA B hB hAB c ↦ ?_,
    card_fillDiagonal_colorOfPair_ne_le_of_le S R hP hδ hF
      (((le_max_right _ _).trans (le_max_left _ _)).trans ha_le_P)
      (S.card_recolorFineBlocks_colorOfPair_ne_le hQP idx x (hη_pos _).le hirr hEgap hx_edit)⟩
  rw [R.pairColorDensity_fillDiagonal_of_ne P hA hB hAB Subset.rfl Subset.rfl]
  cases c with
  | none => simp [(hF #P.parts).le]
  | some c =>
    simpa only [Option.elim_some] using
      ((hR_off ⟨A, hA⟩ ⟨B, hB⟩ (Subtype.coe_injective.ne_iff.1 hAB)).2 c).trans (min_le_left _ _)

end PairColorSystem

namespace PairSkeleton3

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- **Strong regular approximation of a lower skeleton at a scheduled tolerance.**
Given `S : PairSkeleton3 κ V` whose vertex partition is an equipartition, a minimum cell count
`t₀`, a pair-edit budget `δ > 0`, and a positive schedule `F : ℕ → ℝ`, once
`lowerSkeletonApproximationThreshold (card κ) δ F t₀ #S.vertexPart.parts ≤ |V|` there exist a lower
skeleton `T : PairSkeleton3 (Fin (card κ + 1)) V` and a palette embedding
`g : κ ↪ Fin (card κ + 1)` such that:

* `T.vertexPart ≤ S.vertexPart`, `T.vertexPart.IsEquipartition`, and
  `t₀ ≤ #T.vertexPart.parts ≤ lowerSkeletonApproximationBound (card κ) δ F t₀ #S.vertexPart.parts`;
* `T.LowerSkeletonRegular F`;
* `g` intertwines palette reversals (`T.pairColors.rev (g c) = g (S.pairColors.rev c)`); and
* `T.pairColors.color p ≠ g (S.pairColors.color p)` on at most `δ |V|²` ordered distinct
  pairs `p`. -/
theorem exists_refining_lowerSkeletonRegular [Fintype κ] (S : PairSkeleton3 κ V)
    (hS : S.vertexPart.IsEquipartition) (t₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) {F : ℕ → ℝ}
    (hF : ∀ n, 0 < F n)
    (hV : lowerSkeletonApproximationThreshold (Fintype.card κ) δ F t₀ #S.vertexPart.parts ≤
      Fintype.card V) :
    ∃ (T : PairSkeleton3 (Fin (Fintype.card κ + 1)) V) (g : κ ↪ Fin (Fintype.card κ + 1)),
      T.vertexPart ≤ S.vertexPart ∧ T.vertexPart.IsEquipartition ∧
      t₀ ≤ #T.vertexPart.parts ∧
      #T.vertexPart.parts ≤
        lowerSkeletonApproximationBound (Fintype.card κ) δ F t₀ #S.vertexPart.parts ∧
      T.LowerSkeletonRegular F ∧
      (∀ c, T.pairColors.rev (g c) = g (S.pairColors.rev c)) ∧
      (#{p : {p : V × V // p.1 ≠ p.2} |
          T.pairColors.color p ≠ g (S.pairColors.color p)} : ℝ) ≤
        δ * (Fintype.card V : ℝ) ^ 2 := by
  classical
  rw [lowerSkeletonApproximationThreshold_def] at hV
  obtain ⟨P, T₀, hPS, hP, ht₀, hPbound, hrev, hreg, -, hedit⟩ :=
    S.pairColors.exists_refining_equipartition_isPairColorRegular S.vertexPart hS t₀ hδ
      (fun t ↦ hF (t + (Fintype.card κ + 1))) hV
  let e : Option κ ≃ Fin (Fintype.card κ + 1) :=
    (Fintype.equivFin (Option κ)).trans (finCongr Fintype.card_option)
  let T : PairSkeleton3 (Fin (Fintype.card κ + 1)) V :=
    (⟨P, T₀⟩ : PairSkeleton3 (Option κ) V).relabel e
  let g : κ ↪ Fin (Fintype.card κ + 1) :=
    ⟨fun c ↦ e (some c), fun _ _ h ↦ Option.some.inj (e.injective h)⟩
  have hg (c : κ) : g c = e (some c) := rfl
  have hT_part : T.vertexPart = P := relabel_vertexPart e
  have hreg_low : T.LowerSkeletonRegular F := by
    rw [lowerSkeletonRegular_relabel_iff, lowerSkeletonRegular_iff, Fintype.card_option]
    exact hreg
  have hbound' : #T.vertexPart.parts ≤
      lowerSkeletonApproximationBound (Fintype.card κ) δ F t₀ #S.vertexPart.parts := by
    rw [hT_part, lowerSkeletonApproximationBound_def]
    exact hPbound
  refine ⟨T, g, hT_part.symm ▸ hPS, hT_part.symm ▸ hP, hT_part.symm ▸ ht₀, hbound', hreg_low,
    fun c ↦ ?_, ?_⟩
  · simp [T, hg, hrev]
  · have hcard : #{p : {p : V × V // p.1 ≠ p.2} |
          T.pairColors.color p ≠ g (S.pairColors.color p)} =
        #{p : V × V |
          T₀.colorOfPair p.1 p.2 ≠ (S.pairColors.colorOfPair p.1 p.2).map some} :=
      (congrArg card <| Finset.ext fun p ↦ by
          simp only [mem_filter, mem_univ, true_and, T, hg, relabel_pairColors,
            PairColorSystem.relabel_color, ne_eq, e.injective.eq_iff]).trans
        ((S.pairColors.card_color_ne_eq_card_colorOfPair_ne T₀ some).trans
          (congrArg card <| Finset.ext fun _ ↦ by simp only [mem_filter]))
    rwa [hcard]

end PairSkeleton3

end TauCeti
