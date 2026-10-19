/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
public import TauCeti.Combinatorics.Regularity.Partition.AlmostRefines
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
the number of parts of `P₀` only. Regularity statements that iterate the regularity lemma, such as
strong regularity, need this control on the relation between successive partitions.

## Main declarations

* `SimpleGraph.szemeredi_regularity_le`: a uniform equipartition refining a given equipartition with
  enough parts, of size bounded in terms of `ε` and the starting size.
* `TauCeti.refiningRegularityBound`: the complexity bound for almost-refining regularity.
* `SimpleGraph.exists_regular_equipartition_almost_refining`: a uniform equipartition almost
  refining a given equipartition `P₀` up to `ε`, with at most
  `refiningRegularityBound ε #P₀.parts` parts.

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

end SimpleGraph
