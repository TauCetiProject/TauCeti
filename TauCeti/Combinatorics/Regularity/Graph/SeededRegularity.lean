/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
public import TauCeti.Combinatorics.Regularity.Partition.AlmostRefines
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import TauCeti.Order.Partition.Finpartition

/-!
# Szemerédi regularity relative to a seed partition

Mathlib's `szemeredi_regularity` produces a uniform equipartition, but relates it to no prescribed
partition. Refining its output afterwards does not help, since uniformity is not inherited by
refinements, and a common refinement with a seed partition is not an equipartition in general.
This file instead runs the energy-increment induction behind `szemeredi_regularity` from a given
starting equipartition. Mathlib's `SzemerediRegularity.increment` is a `Finpartition.bind`, so it
refines its input exactly, and each partition built by the induction refines the start.

Starting from an equipartition that almost refines a seed `P₀` (provided by
`Finpartition.IsEquipartition.exists_equipartition_card_eq_almostRefines`), this yields a uniform
equipartition that still almost refines `P₀`, with a number of parts bounded in terms of `ε` and
the number of parts of `P₀` only. Starting instead from an exact refinement of an equipartition
`P` into equally many pieces per part, it yields a uniform equipartition refining `P` exactly.
Regularity statements that iterate the regularity lemma, such as strong regularity, need this
control on the relation between successive partitions.

## Main declarations

* `SimpleGraph.szemeredi_regularity_le`: a uniform equipartition refining a given equipartition with
  enough parts, of size bounded in terms of `ε` and the starting size.
* `TauCeti.refiningRegularityBound`: the complexity bound for almost-refining regularity.
* `SimpleGraph.exists_regular_equipartition_almost_refining`: a uniform equipartition almost
  refining a given equipartition `P₀` up to `ε`, with at most
  `refiningRegularityBound ε #P₀.parts` parts.
* `TauCeti.nestedRefinementBound`: the complexity bound for exactly refining regularity.
* `SimpleGraph.exists_regular_exact_refining_equipartition`: a uniform equipartition refining a
  given equipartition `P` exactly, with at most `nestedRefinementBound δ #P.parts` parts.
* `SimpleGraph.exists_regular_almostRefines_le_card`: a uniform equipartition almost refining a
  given equipartition `P₀` up to `ε`, with at least a requested number of parts.

## References

The induction follows the proof of `szemeredi_regularity` in Mathlib, by Yaël Dillies and Bhavik
Mehta.

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

public section

open Finset Fintype Finpartition Function SzemerediRegularity

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
  {ε : ℝ}

/-- **Szemerédi's regularity lemma below a starting equipartition.** If `P₁` is an equipartition
with at least `7` parts and `100 ≤ 4 ^ #P₁.parts * ε ^ 5`, and the graph is large enough, then
some `ε`-uniform equipartition refines `P₁` and has at most
`stepBound^[⌊4 / ε ^ 5⌋₊ + 1] #P₁.parts` parts. -/
theorem szemeredi_regularity_le {P₁ : Finpartition (univ : Finset α)} (hP₁ : P₁.IsEquipartition)
    (hP₇ : 7 ≤ #P₁.parts) (hPε : 100 ≤ 4 ^ #P₁.parts * ε ^ 5)
    (hα : stepBound^[⌊4 / ε ^ 5⌋₊] #P₁.parts * 16 ^ stepBound^[⌊4 / ε ^ 5⌋₊] #P₁.parts ≤
      card α) :
    ∃ P : Finpartition (univ : Finset α), P ≤ P₁ ∧ P.IsEquipartition ∧ P.IsUniform G ε ∧
      #P.parts ≤ stepBound^[⌊4 / ε ^ 5⌋₊ + 1] #P₁.parts := by
  have hε : 0 < ε := eps_pos hPε
  -- If `ε ≥ 1`, then `P₁` itself is `ε`-uniform.
  obtain hε₁ | hε₁ := le_total 1 ε
  · exact ⟨P₁, le_rfl, hP₁, (P₁.isUniform_one G).mono hε₁,
      id_le_iterate_of_id_le le_stepBound _ _⟩
  -- Otherwise, induct on the energy: for each `i` there is an equipartition refining `P₁`, of
  -- size at most `stepBound^[i] #P₁.parts`, which is `ε`-uniform or has energy `≥ ε ^ 5 / 4 * i`.
  suffices h : ∀ i, ∃ P : Finpartition (univ : Finset α), P ≤ P₁ ∧ P.IsEquipartition ∧
      #P.parts ≤ stepBound^[i] #P₁.parts ∧ (P.IsUniform G ε ∨ ε ^ 5 / 4 * i ≤ P.energy G) by
    -- Since energies are at most `1`, step `⌊4 / ε ^ 5⌋₊ + 1` must be uniform.
    obtain ⟨P, hPP₁, hP, hPcard, hPG⟩ := h (⌊4 / ε ^ 5⌋₊ + 1)
    refine ⟨P, hPP₁, hP, hPG.resolve_right fun hPenergy ↦ lt_irrefl (1 : ℝ) ?_, hPcard⟩
    calc
      (1 : ℝ) = ε ^ 5 / 4 * (4 / ε ^ 5) := by field_simp
      _ < ε ^ 5 / 4 * (⌊4 / ε ^ 5⌋₊ + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ ≤ (P.energy G : ℝ) := by rwa [← Nat.cast_add_one]
      _ ≤ 1 := mod_cast P.energy_le_one G
  intro i
  induction i with
  | zero =>
    refine ⟨P₁, le_rfl, hP₁, le_rfl, Or.inr ?_⟩
    rw [Nat.cast_zero, mul_zero]
    exact mod_cast P₁.energy_nonneg G
  | succ i ih =>
    obtain ⟨P, hPP₁, hP, hPcard, hPG⟩ := ih
    -- A uniform partition is kept as it is.
    by_cases huniform : P.IsUniform G ε
    · refine ⟨P, hPP₁, hP, ?_, Or.inl huniform⟩
      rw [iterate_succ_apply']
      exact hPcard.trans (le_stepBound _)
    -- Otherwise we pass to the increment of `P`, which refines `P` and gains `ε ^ 5 / 4` energy.
    replace hPG := hPG.resolve_left huniform
    have : Nonempty α := by
      obtain ⟨A, hA⟩ := nonempty_of_not_uniform huniform
      obtain ⟨a, -⟩ := P.nonempty_of_mem_parts hA
      exact ⟨a⟩
    have hP₁P : #P₁.parts ≤ #P.parts := card_mono hPP₁
    have hPε' : 100 ≤ 4 ^ #P.parts * ε ^ 5 := by grw [hPε, hP₁P]; simp
    have hi : (i : ℝ) ≤ 4 / ε ^ 5 := by
      rw [le_div_iff₀' (by positivity)]
      have hP1 : (P.energy G : ℝ) ≤ 1 := mod_cast P.energy_le_one G
      linarith
    have hsize : #P.parts ≤ stepBound^[⌊4 / ε ^ 5⌋₊] #P₁.parts :=
      hPcard.trans (monotone_iterate_of_id_le le_stepBound (Nat.le_floor hi) _)
    have hPα : #P.parts * 16 ^ #P.parts ≤ card α :=
      (Nat.mul_le_mul hsize (Nat.pow_le_pow_right (by simp) hsize)).trans hα
    have hinc : increment hP G ε ≤ P := by
      rw [increment]
      exact bind_le _ _
    refine ⟨increment hP G ε, hinc.trans hPP₁, increment_isEquipartition hP G ε, ?_,
      Or.inr <| le_trans ?_ <|
        energy_increment hP (hP₇.trans hP₁P) hPε' hPα huniform hε.le hε₁⟩
    · rw [card_increment hPα huniform, iterate_succ_apply']
      exact stepBound_mono hPcard
    · rw [Nat.cast_succ, mul_add, mul_one]
      gcongr

end SimpleGraph

namespace TauCeti

/-- The complexity bound for `exists_regular_exact_refining_equipartition`: the bound of
Szemerédi's regularity lemma started from `initialBound δ 0 * l` parts. It depends only on `δ` and
the number `l` of parts of the partition being refined. -/
noncomputable def nestedRefinementBound (δ : ℝ) (l : ℕ) : ℕ :=
  bound δ (initialBound δ 0 * l)

/-- The complexity bound is Szemerédi's bound started from `initialBound δ 0 * l` parts. -/
theorem nestedRefinementBound_def (δ : ℝ) (l : ℕ) :
    nestedRefinementBound δ l = bound δ (initialBound δ 0 * l) := (rfl)

/-- The complexity bound for exactly refining regularity is at least the number of parts being
refined. -/
theorem le_nestedRefinementBound (δ : ℝ) (l : ℕ) : l ≤ nestedRefinementBound δ l :=
  (Nat.le_mul_of_pos_left l (initialBound_pos δ 0)).trans (le_bound δ _)

/-- The complexity bound for `exists_regular_equipartition_almost_refining`: the bound of
Szemerédi's regularity lemma with at least `⌈2 * l / ε⌉₊` initial parts. It depends only on `ε`
and the number `l` of parts of the seed partition. -/
noncomputable def refiningRegularityBound (ε : ℝ) (l : ℕ) : ℕ :=
  bound ε ⌈2 * l / ε⌉₊

/-- The complexity bound is Szemerédi's bound with at least `⌈2 * l / ε⌉₊` initial parts. -/
theorem refiningRegularityBound_def (ε : ℝ) (l : ℕ) :
    refiningRegularityBound ε l = bound ε ⌈2 * l / ε⌉₊ := (rfl)

end TauCeti

namespace SimpleGraph

open TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
  {ε : ℝ}

/-- **Szemerédi's regularity lemma relative to a seed.** Every equipartition `P₀` of a finite
graph is almost refined, up to `ε`, by an `ε`-uniform equipartition with at most
`refiningRegularityBound ε #P₀.parts` parts. -/
theorem exists_regular_equipartition_almost_refining (P₀ : Finpartition (univ : Finset α))
    (hP₀ : P₀.IsEquipartition) (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset α), P.IsEquipartition ∧ P.IsUniform G ε ∧
      P.AlmostRefines P₀ ε ∧ #P.parts ≤ refiningRegularityBound ε #P₀.parts := by
  -- On a small host, the partition into singletons works.
  obtain hα | hα := le_total (card α) (refiningRegularityBound ε #P₀.parts)
  · refine ⟨⊥, bot_isEquipartition _, bot_isUniform G hε, almostRefines_of_le bot_le hε.le, ?_⟩
    rwa [card_bot, card_univ]
  -- Otherwise, start from an equipartition with `initialBound ε ⌈2 * #P₀.parts / ε⌉₊` parts
  -- almost refining `P₀`, and run the energy induction from it.
  rw [refiningRegularityBound, bound] at hα
  set t := initialBound ε ⌈2 * #P₀.parts / ε⌉₊
  have ht : t ≤ #(univ : Finset α) := by
    rw [card_univ]
    exact (id_le_iterate_of_id_le le_stepBound _ _).trans
      ((Nat.le_mul_of_pos_right _ (by positivity)).trans hα)
  have hδ : (2 * #P₀.parts : ℝ) ≤ ε * t := by
    rw [← div_le_iff₀' hε]
    exact (Nat.le_ceil _).trans (Nat.cast_le.2 (le_initialBound _ _))
  obtain ⟨P₁, hP₁, hP₁card, hP₁P₀⟩ :=
    hP₀.exists_equipartition_card_eq_almostRefines (initialBound_pos _ _).ne' ht hδ
  obtain ⟨P, hPP₁, hP, hPG, hPcard⟩ := szemeredi_regularity_le G hP₁
    (hP₁card ▸ seven_le_initialBound _ _) (hP₁card ▸ (hundred_lt_pow_initialBound_mul hε _).le)
    (hP₁card ▸ hα)
  refine ⟨P, hP, hPG, hP₁P₀.mono_left hPP₁, hPcard.trans ?_⟩
  rw [hP₁card, iterate_succ_apply', refiningRegularityBound, bound, stepBound]
  gcongr
  simp

/-- **Szemerédi's regularity lemma refining an equipartition exactly.** Every equipartition `P` of a
finite graph is refined exactly by a `δ`-uniform equipartition with at most
`nestedRefinementBound δ #P.parts` parts. -/
theorem exists_regular_exact_refining_equipartition (P : Finpartition (univ : Finset α))
    (hP : P.IsEquipartition) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : Finpartition (univ : Finset α), Q ≤ P ∧ Q.IsEquipartition ∧ Q.IsUniform G δ ∧
      #Q.parts ≤ nestedRefinementBound δ #P.parts := by
  -- On a small host, the partition into singletons works.
  obtain hα | hα := le_total (card α) (nestedRefinementBound δ #P.parts)
  · exact ⟨⊥, bot_le, bot_isEquipartition _, bot_isUniform G hδ, by rwa [card_bot, card_univ]⟩
  -- Otherwise, split every part of `P` into `a = initialBound δ 0` parts, which gives enough
  -- parts to run the energy induction.
  rw [nestedRefinementBound_def] at hα
  set a := initialBound δ 0
  set k := #P.parts
  have hk : 0 < k := card_pos.2 <| P.parts_nonempty <|
    (card_pos.1 ((bound_pos δ _).trans_le hα)).ne_empty
  obtain ⟨P₁, hP₁, hP₁card, hP₁P⟩ := hP.exists_refining_equipartition_card_eq_mul
    (initialBound_pos δ 0).ne' (by rw [card_univ]; exact (le_bound δ _).trans hα)
  -- The energy induction runs below `P₁`, whose `a * k` parts are as many as Szemerédi's
  -- regularity lemma starts from.
  set N := ⌊4 / δ ^ 5⌋₊
  have hmono : stepBound^[N] (a * k) ≤ stepBound^[N] (initialBound δ (a * k)) :=
    Monotone.iterate stepBound_mono N (le_initialBound δ _)
  have hak : a ≤ a * k := Nat.le_mul_of_pos_right a hk
  have hbound : stepBound^[N] (a * k) * 16 ^ stepBound^[N] (a * k) ≤
      nestedRefinementBound δ k := by
    rw [nestedRefinementBound_def, bound]
    gcongr
  obtain ⟨Q, hQP₁, hQ, hQG, hQcard⟩ := szemeredi_regularity_le G hP₁
    (hP₁card ▸ (seven_le_initialBound δ 0).trans hak)
    (hP₁card ▸ (hundred_lt_pow_initialBound_mul hδ 0).le.trans (by gcongr; norm_num))
    (hP₁card ▸ hbound.trans (by rwa [nestedRefinementBound_def]))
  refine ⟨Q, hQP₁.trans hP₁P, hQ, hQG, hQcard.trans ?_⟩
  rw [hP₁card, iterate_succ_apply', stepBound]
  exact hbound.trans' (by gcongr; norm_num)

/-- **Szemerédi's regularity lemma relative to a seed, with a minimum number of parts.** Every
equipartition `P₀` of a finite graph is almost refined, up to `ε`, by an `ε`-uniform equipartition
with at least `l` parts, for any requested `l ≤ card α`. It is obtained by refining exactly an
equipartition into `max l₀ ⌈2 * l₀ / ε⌉₊` parts almost refining `P₀`, where
`l₀ = max l #P₀.parts`, so it has at most `nestedRefinementBound ε (max l₀ ⌈2 * l₀ / ε⌉₊)`
parts. -/
theorem exists_regular_almostRefines_le_card (P₀ : Finpartition (univ : Finset α))
    (hP₀ : P₀.IsEquipartition) {l : ℕ} (hl : l ≤ card α) (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset α), P.IsEquipartition ∧ P.IsUniform G ε ∧
      P.AlmostRefines P₀ ε ∧ l ≤ #P.parts ∧ #P.parts ≤
        nestedRefinementBound ε (max (max l #P₀.parts) ⌈2 * (max l #P₀.parts : ℕ) / ε⌉₊) := by
  set l₀ := max l #P₀.parts
  set n := max l₀ ⌈2 * l₀ / ε⌉₊
  -- On an empty host, or one with fewer than `n` vertices, the partition into singletons works.
  by_cases hsmall : card α = 0 ∨ card α < n
  · refine ⟨⊥, bot_isEquipartition _, bot_isUniform G hε, almostRefines_of_le bot_le hε.le, ?_, ?_⟩
    · rwa [card_bot, card_univ]
    · rw [card_bot, card_univ]
      rcases hsmall with h | h
      · exact h ▸ Nat.zero_le _
      · exact h.le.trans (le_nestedRefinementBound _ _)
  push Not at hsmall
  obtain ⟨hα, hn⟩ := hsmall
  have : Nonempty α := card_pos_iff.1 (Nat.pos_of_ne_zero hα)
  have hk : 0 < #P₀.parts := card_pos.2 <| P₀.parts_nonempty univ_nonempty.ne_empty
  have hn₀ : n ≠ 0 := (hk.trans_le ((le_max_right _ _).trans (le_max_left _ _))).ne'
  have hδ : 2 * (#P₀.parts : ℝ) ≤ ε * n := by
    rw [← div_le_iff₀' hε]
    calc 2 * (#P₀.parts : ℝ) / ε ≤ 2 * (l₀ : ℝ) / ε := by gcongr; exact_mod_cast le_max_right _ _
      _ ≤ ⌈2 * (l₀ : ℝ) / ε⌉₊ := Nat.le_ceil _
      _ ≤ n := Nat.cast_le.2 (le_max_right _ _)
  obtain ⟨P₁, hP₁, hP₁card, hP₁P₀⟩ :=
    hP₀.exists_equipartition_card_eq_almostRefines hn₀ (by rwa [card_univ]) hδ
  obtain ⟨P, hPP₁, hP, hPG, hPcard⟩ := G.exists_regular_exact_refining_equipartition P₁ hP₁ hε
  refine ⟨P, hP, hPG, hP₁P₀.mono_left hPP₁, ?_, hP₁card ▸ hPcard⟩
  exact ((le_max_left _ _).trans (le_max_left _ _)).trans (hP₁card ▸ card_mono hPP₁)

end SimpleGraph
