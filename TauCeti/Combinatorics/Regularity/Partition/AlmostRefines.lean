/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Order.Partition.Finpartition

/-!
# Almost-refinement of finite partitions

A finite partition `P` of `s` *almost refines* a partition `P₀` of `s` up to `δ` when every part
`A` of `P₀` is covered, except for at most `δ * #A` of its elements, by parts of `P` contained in
`A`. Divisibility usually prevents an equipartition with a prescribed number of parts from refining
a given partition exactly, but `Finpartition.equitabilise` always produces one that almost refines
it. Almost-refinement is preserved by passing to an exact refinement, so iterated refinement
procedures, such as the energy increment in Szemerédi's regularity lemma, keep it.

## Main declarations

* `Finpartition.AlmostRefines P P₀ δ`: `P` almost refines `P₀` up to `δ`.
* `Finpartition.almostRefines_iff`: the canonical cover is by all parts of `P` contained in `A`.
* `Finpartition.almostRefines_of_le`: an exact refinement almost refines up to any `δ ≥ 0`.
* `Finpartition.AlmostRefines.mono_left`: almost-refinement passes to exact refinements.
* `Finpartition.IsEquipartition.exists_equipartition_card_eq_almostRefines`: an equipartition
  with `k` parts is almost refined, up to `δ`, by an equipartition with any number `n ≥ 2k / δ`
  of parts, provided `n` is at most the size of the ground set.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α} {P P₀ Q : Finpartition s} {δ δ' : ℝ}

/-- `P` almost refines `P₀` up to `δ`: each part `A` of `P₀` contains a family of parts of `P`
whose union misses at most `δ * #A` elements of `A`. -/
def AlmostRefines (P P₀ : Finpartition s) (δ : ℝ) : Prop :=
  ∀ A ∈ P₀.parts, ∃ T ⊆ P.parts, (∀ B ∈ T, B ⊆ A) ∧ (#(A \ T.biUnion id) : ℝ) ≤ δ * #A

/-- Almost-refinement only has to be checked on the largest admissible cover: the parts of `P`
contained in a given part of `P₀`. -/
theorem almostRefines_iff : P.AlmostRefines P₀ δ ↔
    ∀ A ∈ P₀.parts, (#(A \ {B ∈ P.parts | B ⊆ A}.biUnion id) : ℝ) ≤ δ * #A := by
  refine ⟨fun h A hA ↦ ?_, fun h A hA ↦
    ⟨_, filter_subset _ _, fun B hB ↦ (mem_filter.1 hB).2, h A hA⟩⟩
  obtain ⟨T, hTP, hTA, hT⟩ := h A hA
  refine le_trans ?_ hT
  gcongr
  exact fun B hB ↦ mem_filter.2 ⟨hTP hB, hTA B hB⟩

/-- Almost-refinement is monotone in the tolerance. -/
theorem AlmostRefines.mono (h : P.AlmostRefines P₀ δ) (hδ : δ ≤ δ') : P.AlmostRefines P₀ δ' := by
  intro A hA
  obtain ⟨T, hTP, hTA, hT⟩ := h A hA
  exact ⟨T, hTP, hTA, hT.trans (by gcongr)⟩

/-- An exact refinement almost refines up to any nonnegative tolerance. -/
theorem almostRefines_of_le (h : P ≤ P₀) (hδ : 0 ≤ δ) : P.AlmostRefines P₀ δ := by
  refine almostRefines_iff.2 fun A hA ↦ ?_
  rw [biUnion_filter_subset_eq_of_le h hA, Finset.sdiff_self, card_empty, Nat.cast_zero]
  positivity

/-- An exact refinement of a partition almost refining `P₀` almost refines `P₀` with the same
tolerance. -/
theorem AlmostRefines.mono_left (hQP : Q ≤ P) (h : P.AlmostRefines P₀ δ) :
    Q.AlmostRefines P₀ δ := by
  rw [almostRefines_iff] at h ⊢
  refine fun A hA ↦ le_trans ?_ (h A hA)
  have hcover : {B ∈ P.parts | B ⊆ A}.biUnion id ⊆ {C ∈ Q.parts | C ⊆ A}.biUnion id := by
    refine biUnion_subset.2 fun B hB ↦ ?_
    rw [mem_filter] at hB
    rw [id, ← biUnion_filter_subset_eq_of_le hQP hB.1]
    refine biUnion_subset_biUnion_of_subset_left _ fun C hC ↦ ?_
    rw [mem_filter] at hC ⊢
    exact ⟨hC.1, hC.2.trans hB.2⟩
  gcongr

/-- If `P` is an equipartition of `s` into `k` parts and `0 < n ≤ #s` with `2k ≤ δn`, then some
equipartition of `s` into exactly `n` parts almost refines `P` up to `δ`. It is obtained from
`Finpartition.equitabilise`, which leaves at most `#s / n` elements of each part of `P`
uncovered. -/
theorem IsEquipartition.exists_equipartition_card_eq_almostRefines (hP : P.IsEquipartition)
    {n : ℕ} (hn : n ≠ 0) (hns : n ≤ #s) (hδ : 2 * #P.parts ≤ δ * n) :
    ∃ Q : Finpartition s, Q.IsEquipartition ∧ #Q.parts = n ∧ Q.AlmostRefines P δ := by
  have hsum : (n - #s % n) * (#s / n) + #s % n * (#s / n + 1) = #s := by
    rw [tsub_mul, mul_add, ← add_assoc,
      tsub_add_cancel_of_le (Nat.mul_le_mul_right _ (Nat.mod_lt _ hn.bot_lt).le), mul_one,
      add_comm, Nat.mod_add_div]
  refine ⟨P.equitabilise hsum, equitabilise_isEquipartition, ?_, almostRefines_iff.2 ?_⟩
  · rw [card_parts_equitabilise _ _ (Nat.div_pos hns hn.bot_lt).ne',
      tsub_add_cancel_of_le (Nat.mod_lt _ hn.bot_lt).le]
  intro A hA
  have hk : 0 < #P.parts := card_pos.2 ⟨A, hA⟩
  -- An equipartition part is large: `#s ≤ 2 * #P.parts * #A`.
  have hA₁ : 1 ≤ #A := card_pos.2 (P.nonempty_of_mem_parts hA)
  have hAavg : #s / #P.parts ≤ #A := hP.average_le_card_part hA
  have hslt : #s < #P.parts * (#s / #P.parts + 1) := Nat.lt_mul_div_succ _ hk
  have hsA : (#s : ℝ) ≤ 2 * #P.parts * #A := by
    norm_cast
    nlinarith [Nat.mul_le_mul_left #P.parts hAavg, Nat.mul_le_mul_left #P.parts hA₁]
  have hn' : (0 : ℝ) < n := by positivity
  calc (#(A \ {B ∈ (P.equitabilise hsum).parts | B ⊆ A}.biUnion id) : ℝ)
      ≤ (#s / n : ℕ) := mod_cast card_parts_equitabilise_subset_le _ _ hA
    _ ≤ #s / n := Nat.cast_div_le
    _ ≤ 2 * #P.parts * #A / n := by gcongr
    _ ≤ δ * n * #A / n := by gcongr
    _ = δ * #A := by field_simp

end Finpartition
