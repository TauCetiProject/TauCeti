/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Counting
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Data.Set.PowersetCard

/-!
# Edit discrepancy of colored three-uniform hypergraphs

The edit discrepancy `H.editDiscrepancy3 H'` of two colorings of the triples of `V` is six times
the number of unordered triples on which they disagree, divided by `|V|³`. Equivalently, it is
the fraction of all `|V|³` ordered triples of vertices whose entries are distinct and form a
triple on which the colorings disagree.
`H.Approximates3 H' ε` says that the edit discrepancy is at most `ε`.

The discrepancy is a pseudometric: it is nonnegative, symmetric, zero on the diagonal, and
satisfies the triangle inequality, so approximations compose with their errors added. The
vertex count is `Nat.card V`, so no finiteness hypothesis is needed: on an infinite vertex type
the denominator vanishes and every discrepancy is `0`.

Labelled induced copy counts are stable under small edits. An injection of a pattern on `k`
vertices is an induced copy in exactly one of `H` and `H'` only if it carries one of the
`k.choose 3` pattern triples onto a triple on which they disagree. For each pattern triple and
each disagreeing triple there are at most `3! * |V| ^ (k - 3)` such injections, so the two counts
differ by at most `k.choose 3 * H.editDiscrepancy3 H' * |V| ^ k`. This lets a count computed in
an approximating coloring be transferred back to the original one.

## Main definitions

* `TauCeti.Colored3Graph.editDiscrepancy3`: the normalized number of disagreeing triples.
* `TauCeti.Colored3Graph.Approximates3`: approximation within a given edit discrepancy.

## Main results

* `TauCeti.Colored3Graph.editDiscrepancy3_triangle`: the triangle inequality.
* `TauCeti.Colored3Graph.Approximates3.trans`: approximations compose, adding their errors.
* `TauCeti.Colored3Graph.abs_inducedCopyCount_sub_le`: induced copy counts of a pattern on `k`
  vertices in `H` and `H'` differ by at most `k.choose 3 * H.editDiscrepancy3 H' * |V| ^ k`.
* `TauCeti.Colored3Graph.Approximates3.abs_inducedCopyCount_sub_le`: the same bound for an
  approximation within `ε`, with `ε` in place of the edit discrepancy.
-/

public section

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*}

/-- Six times the number of unordered triples on which `H` and `H'` disagree, normalized by
`|V|³`. -/
noncomputable def editDiscrepancy3 (H H' : Colored3Graph κ V) : ℚ :=
  6 * {s | H.color s ≠ H'.color s}.ncard / (Nat.card V : ℚ) ^ 3

/-- The edit discrepancy counts disagreeing triples, normalized by `|V|³`. -/
theorem editDiscrepancy3_def (H H' : Colored3Graph κ V) :
    H.editDiscrepancy3 H' = 6 * {s | H.color s ≠ H'.color s}.ncard / (Nat.card V : ℚ) ^ 3 :=
  (rfl)

/-- The edit discrepancy is nonnegative. -/
theorem editDiscrepancy3_nonneg (H H' : Colored3Graph κ V) : 0 ≤ H.editDiscrepancy3 H' := by
  rw [editDiscrepancy3_def]
  positivity

/-- The edit discrepancy is symmetric. -/
theorem editDiscrepancy3_comm (H H' : Colored3Graph κ V) :
    H.editDiscrepancy3 H' = H'.editDiscrepancy3 H := by
  simp only [editDiscrepancy3_def, ne_comm]

/-- A coloring has edit discrepancy `0` from itself. -/
@[simp]
theorem editDiscrepancy3_self (H : Colored3Graph κ V) : H.editDiscrepancy3 H = 0 := by
  simp [editDiscrepancy3_def]

/-- The **triangle inequality** for the edit discrepancy. -/
theorem editDiscrepancy3_triangle (H₁ H₂ H₃ : Colored3Graph κ V) :
    H₁.editDiscrepancy3 H₃ ≤ H₁.editDiscrepancy3 H₂ + H₂.editDiscrepancy3 H₃ := by
  -- On an infinite vertex type every discrepancy has denominator `0`.
  cases finite_or_infinite V
  · simp only [editDiscrepancy3_def, ← add_div, ← mul_add]
    gcongr
    -- A triple on which `H₁` and `H₃` disagree is one on which `H₂` disagrees with one of them.
    have hsub : {s | H₁.color s ≠ H₃.color s} ⊆
        {s | H₁.color s ≠ H₂.color s} ∪ {s | H₂.color s ≠ H₃.color s} := by
      intro s hs
      by_contra h
      simp_all
    exact_mod_cast (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  · simp [editDiscrepancy3_def]

/-- `H` approximates `H'` within `ε` when their edit discrepancy is at most `ε`. -/
def Approximates3 (H H' : Colored3Graph κ V) (ε : ℝ) : Prop :=
  (H.editDiscrepancy3 H' : ℝ) ≤ ε

/-- Approximation within `ε` means that the edit discrepancy is at most `ε`. -/
theorem approximates3_iff (H H' : Colored3Graph κ V) (ε : ℝ) :
    H.Approximates3 H' ε ↔ (H.editDiscrepancy3 H' : ℝ) ≤ ε :=
  Iff.rfl

/-- A coloring approximates itself within any nonnegative error. -/
theorem approximates3_self (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 ≤ ε) :
    H.Approximates3 H ε := by
  simpa [approximates3_iff] using hε

namespace Approximates3

variable {H₁ H₂ H₃ : Colored3Graph κ V} {ε δ : ℝ}

/-- Approximation is symmetric. -/
theorem symm (h : H₁.Approximates3 H₂ ε) : H₂.Approximates3 H₁ ε := by
  rwa [approximates3_iff, editDiscrepancy3_comm]

/-- Approximation within `ε` implies approximation within any larger error. -/
theorem mono (h : H₁.Approximates3 H₂ ε) (hεδ : ε ≤ δ) : H₁.Approximates3 H₂ δ :=
  h.trans hεδ

/-- Approximations compose, with their errors added. -/
theorem trans (h₁₂ : H₁.Approximates3 H₂ ε) (h₂₃ : H₂.Approximates3 H₃ δ) :
    H₁.Approximates3 H₃ (ε + δ) := by
  rw [approximates3_iff] at *
  calc (H₁.editDiscrepancy3 H₃ : ℝ)
      ≤ (H₁.editDiscrepancy3 H₂ : ℝ) + H₂.editDiscrepancy3 H₃ := by
        exact_mod_cast editDiscrepancy3_triangle H₁ H₂ H₃
    _ ≤ ε + δ := add_le_add h₁₂ h₂₃

end Approximates3

section InducedCopyCount

open Finset Nat

variable [Fintype V]

/-- At most `k.choose 3 * D * 3! * |V| ^ (k - 3)` injections `Fin k ↪ V` carry some triple of
`Fin k` onto a triple on which `H` and `H'` disagree, where `D` is the number of such triples. -/
private theorem card_filter_exists_color_ne_le [DecidableEq κ]
    (H H' : Colored3Graph κ V) (k : ℕ) :
    #{f : Fin k ↪ V | ∃ s, H.color (Set.powersetCard.map 3 f s) ≠
        H'.color (Set.powersetCard.map 3 f s)} ≤
      k.choose 3 * ({t | H.color t ≠ H'.color t}.ncard * (3 ! * Fintype.card V ^ (k - 3))) := by
  classical
  set D : Finset (Set.powersetCard V 3) := {t | H.color t ≠ H'.color t}
  have hD : {t | H.color t ≠ H'.color t}.ncard = #D := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [hD]
  calc #{f : Fin k ↪ V | ∃ s, H.color (Set.powersetCard.map 3 f s) ≠
        H'.color (Set.powersetCard.map 3 f s)}
      ≤ ∑ s : Set.powersetCard (Fin k) 3, #{f : Fin k ↪ V |
          H.color (Set.powersetCard.map 3 f s) ≠ H'.color (Set.powersetCard.map 3 f s)} := by
        refine le_of_eq_of_le (congrArg card ?_) card_biUnion_le
        ext f
        simp
    _ ≤ ∑ _s : Set.powersetCard (Fin k) 3, #D * (3 ! * Fintype.card V ^ (k - 3)) := by
        -- Split the injections according to the disagreeing triple that `s` is carried onto.
        refine sum_le_sum fun s _ ↦ ?_
        rw [card_eq_sum_card_fiberwise (f := fun f ↦ Set.powersetCard.map 3 f s) (t := D)
          fun f hf ↦ by simpa [D] using hf]
        refine sum_le_card_nsmul _ _ _ fun t _ ↦ ?_
        have := Set.powersetCard.card_embedding_map_eq_le s t
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_subtype] at this
        exact (card_le_card fun f hf ↦ by simp_all).trans this
    _ = k.choose 3 * (#D * (3 ! * Fintype.card V ^ (k - 3))) := by
        rw [sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
          Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- An induced copy in `H` that is not an induced copy in `H'` carries some pattern triple onto a
triple on which `H` and `H'` disagree. -/
private theorem inducedCopyCount_le_add_card_filter [DecidableEq κ]
    (H H' : Colored3Graph κ V) (F : FiniteColored3Pattern κ) :
    H.inducedCopyCount F ≤ H'.inducedCopyCount F +
      #{f : Fin F.k ↪ V | ∃ s, H.color (Set.powersetCard.map 3 f s) ≠
        H'.color (Set.powersetCard.map 3 f s)} := by
  classical
  rw [inducedCopyCount_def, inducedCopyCount_def, add_comm]
  refine card_le_card_sdiff_add_card.trans (Nat.add_le_add_right (card_le_card fun f hf ↦ ?_) _)
  simp only [mem_sdiff, mem_inducedCopies, isInducedCopy_iff, not_forall] at hf
  obtain ⟨hH, s, hs⟩ := hf
  exact mem_filter.2 ⟨mem_univ _, s, (hH s).trans_ne (Ne.symm hs)⟩

/-- **Edit transfer for induced counts.** The numbers of labelled induced copies of a pattern on
`k` vertices in two colorings `H` and `H'` of the triples of `V` differ by at most
`k.choose 3 * H.editDiscrepancy3 H' * |V| ^ k`. -/
theorem abs_inducedCopyCount_sub_le (H H' : Colored3Graph κ V) (F : FiniteColored3Pattern κ) :
    |(H.inducedCopyCount F : ℝ) - H'.inducedCopyCount F| ≤
      F.k.choose 3 * H.editDiscrepancy3 H' * Fintype.card V ^ F.k := by
  classical
  -- Patterns on fewer than three vertices and hosts with no vertices are handled directly.
  rcases lt_or_ge F.k 3 with hk | hk
  · simp [Nat.choose_eq_zero_of_lt hk, H.inducedCopyCount_of_lt_three F hk,
      H'.inducedCopyCount_of_lt_three F hk]
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · have hlt : Fintype.card V < F.k := by omega
    simp only [H.inducedCopyCount_eq_zero_of_card_lt F hlt,
      H'.inducedCopyCount_eq_zero_of_card_lt F hlt, sub_self, abs_zero]
    have := H.editDiscrepancy3_nonneg H'
    positivity
  have h₁ := H.inducedCopyCount_le_add_card_filter H' F
  have h₂ := H'.inducedCopyCount_le_add_card_filter H F
  simp_rw [ne_comm (a := H'.color _)] at h₂
  -- The bound on the injections meeting a disagreeing triple is the edit discrepancy, rescaled.
  have hscale : ((F.k.choose 3 * ({t | H.color t ≠ H'.color t}.ncard *
      (3 ! * Fintype.card V ^ (F.k - 3))) : ℕ) : ℝ) =
      F.k.choose 3 * H.editDiscrepancy3 H' * Fintype.card V ^ F.k := by
    rw [editDiscrepancy3_def, Nat.card_eq_fintype_card, ← Nat.sub_add_cancel hk, pow_add]
    have : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
    push_cast [Nat.factorial]
    field_simp
  have hbad := hscale ▸ (Nat.cast_le (α := ℝ)).2 (card_filter_exists_color_ne_le H H' F.k)
  have h₁' := (Nat.cast_le (α := ℝ)).2 h₁
  have h₂' := (Nat.cast_le (α := ℝ)).2 h₂
  push_cast at h₁' h₂'
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- If `H` approximates `H'` within `ε`, then the numbers of labelled induced copies of a pattern
on `k` vertices in `H` and `H'` differ by at most `k.choose 3 * ε * |V| ^ k`. -/
theorem Approximates3.abs_inducedCopyCount_sub_le {H H' : Colored3Graph κ V} {ε : ℝ}
    (h : H.Approximates3 H' ε) (F : FiniteColored3Pattern κ) :
    |(H.inducedCopyCount F : ℝ) - H'.inducedCopyCount F| ≤
      F.k.choose 3 * ε * Fintype.card V ^ F.k := by
  refine (Colored3Graph.abs_inducedCopyCount_sub_le H H' F).trans ?_
  gcongr
  exact h

end InducedCopyCount

end Colored3Graph

end TauCeti
