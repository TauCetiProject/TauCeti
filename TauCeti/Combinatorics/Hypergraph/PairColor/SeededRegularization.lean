/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regularization
public import Mathlib.Order.Partition.Equipartition
import Mathlib.Order.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import TauCeti.Order.Partition.Finpartition

/-!
# Equitable pair-color regularity preserving a seed

A pair-color system can be regularized by refining any prescribed equitable vertex partition
exactly. The irregular ordered pairs of distinct cells then have total vertex mass at most
`ε |V|²`, with a bound on the number of cells depending only on `ε` and the initial number of
cells. This allows repeated regularization of a lower skeleton without forgetting its earlier
vertex cells.

The energy increment cuts cells along irregularity witnesses, then equitabilises within each
old cell rather than across the host. The resulting partition remains an exact refinement.
The moved-point bound for this cellwise rebalancing controls the loss of pair-color energy.

## Main definitions

* `TauCeti.equitablePairColorRegularityBound`: the bound on the number of parts, shared by the
  seeded and unseeded equitable regularity lemmas.

## Main results

* `PairColorSystem.exists_refining_equipartition_energy_add_lt`: an equitable energy increment
  preserving the old cells.
* `PairColorSystem.exists_refining_equipartition_sum_irregularPairs_le`: equitable regularity
  refining a given equipartition.

## References

* E. Szemerédi, *Regular partitions of graphs* (1978).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).

The induction adapts the original unseeded equitable pair-color energy argument from
`TauCeti.Combinatorics.Hypergraph.PairColor.EquitableRegularization`, with cellwise rebalancing.
That argument follows Y. Dillies and B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*,
ITP 2022, and Mathlib's `szemeredi_regularity`.
-/

public section

open Finset Finpartition

namespace TauCeti

/-- The bound on the number of parts in the equitable regularity lemma for pair-color systems,
asking for at least `l` parts. Each round of the energy increment replaces a number `k` of parts
by `⌈8 / ε⁵⌉ * (k * 4 ^ k ^ 2)`, and `⌊2 / ε⁵⌋ + 1` rounds suffice, starting from `max l 1`
parts. -/
noncomputable def equitablePairColorRegularityBound (ε : ℝ) (l : ℕ) : ℕ :=
  (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[⌊2 / ε ^ 5⌋₊ + 1] (max l 1)

/-- Unfolding lemma for `TauCeti.equitablePairColorRegularityBound`. -/
theorem equitablePairColorRegularityBound_def (ε : ℝ) (l : ℕ) :
    equitablePairColorRegularityBound ε l =
      (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[⌊2 / ε ^ 5⌋₊ + 1] (max l 1) :=
  (rfl)

/-- One round of the equitable energy increment grows the number of parts monotonically. -/
theorem monotone_ceil_mul_mul_four_pow_sq (ε : ℝ) :
    Monotone fun k : ℕ ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2) := fun _ _ hab ↦
  Nat.mul_le_mul_left _ (Nat.mul_le_mul hab (Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_left hab 2)))

/-- One round of the equitable energy increment does not decrease the number of parts. -/
theorem le_ceil_mul_mul_four_pow_sq {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    k ≤ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2) :=
  calc k ≤ k * 4 ^ k ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2) :=
      Nat.le_mul_of_pos_left _ (Nat.ceil_pos.2 (by positivity))

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V] (S : PairColorSystem κ V)

/-- **Equitable energy increment preserving the seed.** If the irregular pairs of an
equipartition `P` cover more than `ε |V|²` ordered pairs, splitting each cell into `a` cells
raises the energy by more than `ε⁵ / 2`, provided the host is large enough and
`8 (#P.parts * 4 ^ #P.parts²) ≤ ε⁵ (a * #P.parts)`. -/
theorem exists_refining_equipartition_energy_add_lt [Fintype κ]
    (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition) {ε : ℝ} (hε : 0 < ε)
    (hbad : ε * (Fintype.card V : ℝ) ^ 2 <
      ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ))
    {a : ℕ} (ha : a ≠ 0)
    (hT : 8 * (#P.parts * 4 ^ #P.parts ^ 2 : ℕ) ≤ ε ^ 5 * (a * #P.parts : ℕ))
    (hTV : a * #P.parts ≤ Fintype.card V) :
    ∃ Q : Finpartition (univ : Finset V), Q ≤ P ∧ Q.IsEquipartition ∧
      #Q.parts = a * #P.parts ∧ S.energy P + ε ^ 5 / 2 < S.energy Q := by
  set n := Fintype.card V
  set T := a * #P.parts
  set K := #P.parts * 4 ^ #P.parts ^ 2
  -- Resolve irregularity, then rebalance inside the old cells to retain exact nesting.
  obtain ⟨R, hRP, hRcard, hRenergy⟩ := S.exists_refinement_energy_add_lt P hε hbad
  obtain ⟨Q, hQ, hQcard, hQP, hmove⟩ :=
    hP.exists_refining_equipartition_card_eq_mul R hRP ha (by rwa [card_univ])
  rw [card_univ, Nat.div_div_eq_div_mul, mul_comm #P.parts a] at hmove
  set M := {x ∈ (univ : Finset V) | ¬Q.part x ⊆ R.part x}
  have hpart : ∀ x ∉ M, Q.part x = (Q ⊓ R).part x := fun x hx ↦ by
    rw [part_inf, inter_eq_left.2]
    simpa [M] using hx
  have hloss := (abs_le.1 (S.abs_energy_sub_energy_le M hpart)).1
  have hmono := S.energy_mono_of_refines (inf_le_right : Q ⊓ R ≤ R)
  -- A bad pair has two distinct nonempty cells, so the ordered-pair denominator is positive.
  obtain ⟨AB, hAB⟩ : (S.irregularPairs ε P).Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro he
    rw [he, sum_empty] at hbad
    nlinarith [sq_nonneg (n : ℝ)]
  obtain ⟨hA, hB, hAB', -⟩ := S.mem_irregularPairs.1 hAB
  have hP₂ : 2 ≤ #P.parts := one_lt_card.2 ⟨_, hA, _, hB, hAB'⟩
  have hn : (2 : ℝ) ≤ n := by
    exact_mod_cast hP₂.trans (P.card_parts_le_card.trans_eq card_univ)
  have hTpos : (0 : ℝ) < T := by
    exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero ha) (by omega : 0 < #P.parts)
  set D := (#(univ : Finset V).offDiag : ℝ)
  have hD : D = n * (n - 1) := by
    simp only [D, offDiag_card, card_univ]
    rw [Nat.cast_sub (Nat.le_mul_self n), Nat.cast_mul]
    ring
  have hDpos : 0 < D := by rw [hD]; nlinarith
  have hMT : (#M : ℝ) * T ≤ K * n := by
    exact_mod_cast calc #M * T ≤ (#R.parts * (n / T)) * T := Nat.mul_le_mul_right T hmove
      _ ≤ K * n := by
        rw [mul_assoc]
        exact Nat.mul_le_mul hRcard (Nat.div_mul_le_self n T)
  -- The moved-point estimate makes rebalancing cost at most half the strict energy gain.
  have hcost : 2 * (#M : ℝ) * n / D ≤ ε ^ 5 / 2 := by
    rw [div_le_iff₀ hDpos]
    have hMn : 8 * (#M : ℝ) ≤ ε ^ 5 * n := by
      apply le_of_mul_le_mul_right (a := (T : ℝ)) _ hTpos
      nlinarith [mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (α := ℝ) n)]
    have hden : (n : ℝ) ^ 2 ≤ 2 * D := by rw [hD]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hMn (Nat.cast_nonneg (α := ℝ) n),
      mul_le_mul_of_nonneg_left hden (pow_nonneg hε.le 5)]
  exact ⟨Q, hQP, hQ, hQcard, by linarith⟩

/-- Run equitable energy increments below `P₀`. Unless the irregular mass is small, the
energy after `j` rounds is at least `j ε⁵ / 2`. -/
private theorem exists_refining_equipartition_iterate [Fintype κ]
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition)
    {ε : ℝ} (hε : 0 < ε) (j : ℕ)
    (hsize : (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[j] #P₀.parts ≤ Fintype.card V) :
    ∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[j] #P₀.parts ∧
      (∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 ∨
        j * (ε ^ 5 / 2) ≤ S.energy P) := by
  let g : ℕ → ℕ := fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2)
  have hg : Monotone g := monotone_ceil_mul_mul_four_pow_sq ε
  have hid : id ≤ g := le_ceil_mul_mul_four_pow_sq hε
  induction j with
  | zero => exact ⟨P₀, le_rfl, hP₀, le_rfl, Or.inr (by simpa using S.energy_nonneg P₀)⟩
  | succ j ih =>
    have hstep : g^[j] #P₀.parts ≤ g^[j + 1] #P₀.parts :=
      Function.monotone_iterate_of_id_le hid j.le_succ _
    obtain ⟨P, hPP₀, hP, hcard, hgood⟩ := ih (hstep.trans hsize)
    by_cases hreg : ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2
    · exact ⟨P, hPP₀, hP, hcard.trans hstep, Or.inl hreg⟩
    have hgP : g #P.parts ≤ g^[j + 1] #P₀.parts := by
      rw [Function.iterate_succ_apply']
      exact hg hcard
    let a := ⌈8 / ε ^ 5⌉₊ * 4 ^ #P.parts ^ 2
    have ha : a ≠ 0 := by dsimp [a]; positivity
    have haP : a * #P.parts = g #P.parts := by dsimp [a, g]; ring
    have hT : 8 * (#P.parts * 4 ^ #P.parts ^ 2 : ℕ) ≤ ε ^ 5 * (a * #P.parts : ℕ) := by
      have hc : 8 ≤ ε ^ 5 * ⌈8 / ε ^ 5⌉₊ :=
        (div_le_iff₀' (by positivity)).1 (Nat.le_ceil _)
      rw [haP]
      dsimp [g]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hc
        (by positivity : (0 : ℝ) ≤ #P.parts * 4 ^ #P.parts ^ 2)]
    obtain ⟨Q, hQP, hQ, hQcard, hE⟩ := S.exists_refining_equipartition_energy_add_lt P hP hε
      (not_le.1 hreg) ha hT (haP ▸ hgP.trans hsize)
    refine ⟨Q, hQP.trans hPP₀, hQ, (hQcard.trans haP).le.trans hgP, Or.inr ?_⟩
    have := hgood.resolve_left hreg
    push_cast
    linarith

/-- **Equitable pair-color regularity refining a seed.** Every equipartition `P₀` has an exact
equitable refinement with at most `equitablePairColorRegularityBound ε #P₀.parts` cells whose
irregular distinct-cell pairs cover at most `ε |V|²` ordered vertex pairs. -/
theorem exists_refining_equipartition_sum_irregularPairs_le [Finite κ]
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ equitablePairColorRegularityBound ε #P₀.parts ∧
      ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  have := Fintype.ofFinite κ
  have hbound : (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[⌊2 / ε ^ 5⌋₊ + 1] #P₀.parts ≤
      equitablePairColorRegularityBound ε #P₀.parts := by
    rw [equitablePairColorRegularityBound_def]
    exact (monotone_ceil_mul_mul_four_pow_sq ε).iterate _ (le_max_left _ _)
  by_cases hsize : equitablePairColorRegularityBound ε #P₀.parts ≤ Fintype.card V
  · obtain ⟨P, hPP₀, hP, hcard, hgood⟩ := S.exists_refining_equipartition_iterate P₀ hP₀ hε
      (⌊2 / ε ^ 5⌋₊ + 1) (hbound.trans hsize)
    refine ⟨P, hPP₀, hP, hcard.trans hbound, hgood.resolve_right fun h ↦ ?_⟩
    have hN : 2 / ε ^ 5 < (⌊2 / ε ^ 5⌋₊ + 1 : ℕ) := by
      push_cast
      exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ (by positivity)] at hN
    linarith [S.energy_le_one P]
  · refine ⟨⊥, bot_le, bot_isEquipartition _, ?_, ?_⟩
    · rw [card_bot, card_univ]
      exact (not_le.1 hsize).le
    · refine (sum_eq_zero fun AB hAB ↦ ?_).trans_le (by positivity)
      obtain ⟨hA, hB, -, hreg⟩ := S.mem_irregularPairs.1 hAB
      obtain ⟨u, -, hu⟩ := mem_bot_iff.1 hA
      obtain ⟨v, -, hv⟩ := mem_bot_iff.1 hB
      exact (hreg (hu ▸ hv ▸ S.isRegularPair_singleton hε u v)).elim

end PairColorSystem

end TauCeti
