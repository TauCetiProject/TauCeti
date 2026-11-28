/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Triadic.SingleColor

/-!
# Regression examples for strong regular approximations over a single pair color

These downstream examples check the calibration of `IsStrongRegularApproximation3` through the
public API of the complexes `TriadicComplex3.ofFinpartition`.

* With one vertex cell and one pair color there is a single polyad, its support is all
  `n (n - 1) (n - 2)` injective triples, the complexity is `3`, and for `f > 0` the lower
  skeleton is regular at `f` exactly when `n = 1` or `n > 1 / f`.
* Over any partition, distinct cells of the constant pair coloring form regular pairs at every
  positive parameter: a test of the pairs of distinct cells alone accepts every partition, so the
  diagonal tests carry the regularity condition.
* A bound `B` with the property of `Colored3Graph.exists_strong_regular_approximation3`, asking for
  `t₀` equitable cells, satisfies `t₀ ≤ B` as soon as the palette is nonempty, and the empty host
  carries no complex with a positive number of controlled cells. So no version of the theorem
  without a large-host hypothesis holds.
* For a schedule at least one, `B = t₀³ + t₀ + 1` is such a bound.
-/

open Finset

namespace TauCeti

open TriadicComplex3 Colored3Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

section OneCell

variable [Nonempty V]

-- One vertex cell and one pair color: the complexity is `3`.
example : (ofFinpartition (.indiscrete (univ_nonempty (α := V)).ne_empty)).complexity = 3 := by
  simp [complexity_ofFinpartition]

-- One vertex cell and one pair color: the single polyad carries all `n (n - 1) (n - 2)`
-- injective triples.
example (Q : Polyad3 (ofFinpartition (.indiscrete (univ_nonempty (α := V)).ne_empty)).skeleton) :
    #Q.support = (Fintype.card V).descFactorial 3 := by
  have := (isPolyadDecomposition_ofFinpartition
    (.indiscrete (univ_nonempty (α := V)).ne_empty)).sum_card_support
  rwa [ofFinpartition_polyads, univ_eq_singleton_of_card_one Q
    (by simp [card_polyad3_ofFinpartition]), sum_singleton] at this

-- One vertex cell and one pair color: for `f > 0`, the lower skeleton is regular at `f`
-- exactly when the host has one vertex or more than `1 / f` vertices.
example {F : ℕ → ℝ} (hF₀ : 0 < F 2) :
    (ofFinpartition (.indiscrete (univ_nonempty (α := V)).ne_empty)).skeleton.LowerSkeletonRegular
        F ↔
      Fintype.card V = 1 ∨ 1 / F 2 < Fintype.card V := by
  rw [lowerSkeletonRegular_ofFinpartition_iff _ (by simpa using hF₀)]
  have : 0 < Fintype.card V := Fintype.card_pos
  simp only [Finpartition.indiscrete_parts, mem_singleton, forall_eq, card_univ, card_singleton,
    Nat.reduceAdd, div_lt_iff₀ hF₀, mul_comm (F 2)]
  exact or_congr_left (by omega)

end OneCell

-- Distinct cells of the constant pair coloring are regular at every positive parameter, so a
-- lower-skeleton predicate testing only pairs of distinct cells would accept every partition.
example (P : Finpartition (univ : Finset V)) {A B : Finset V} (hA : A ∈ P.parts)
    (hB : B ∈ P.parts) (hAB : A ≠ B) {ε : ℝ} (hε : 0 < ε) :
    (ofFinpartition P).skeleton.pairColors.IsRegularPair ε A B :=
  isRegularPair_ofFinpartition_of_ne P hε hA hB hAB

-- An admissible bound for the strong regular approximation theorem with `t₀` equitable cells is
-- at least `t₀` when the palette is nonempty.
example {κ : Type} [DecidableEq κ] [Nonempty κ] {ε : ℝ} {F : ℕ → ℝ} {R : ℕ → ℕ} {t₀ B : ℕ}
    (hB : ∀ (W : Type) [Fintype W] [DecidableEq W], B ≤ Fintype.card W →
      ∀ H : Colored3Graph κ W, ∃ (H' : Colored3Graph κ W) (C : TriadicComplex3 W),
        C.VertexCellsControlled t₀ ∧ H.IsStrongRegularApproximation3 H' C ε F R B) :
    t₀ ≤ B := by
  obtain ⟨-, C, hC, -⟩ := hB (Fin B) (by simp) (const (Classical.arbitrary κ))
  simpa using hC.le_card

-- The empty host carries no complex with a positive number of controlled cells.
example {t₀ : ℕ} (ht₀ : 0 < t₀) (C : TriadicComplex3 Empty) : ¬C.VertexCellsControlled t₀ :=
  fun hC ↦ by simpa using ht₀.trans_le hC.le_card

-- For a schedule at least one, `t₀³ + t₀ + 1` is an admissible bound: every coloring of the
-- triples of a host of at least that size has a strong regular approximation with `t₀`
-- equitable cells and complexity at most `t₀³ + t₀ + 1`.
example {κ : Type*} [DecidableEq κ] (H : Colored3Graph κ V) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ}
    (hF : ∀ n, 1 ≤ F n) (R : ℕ → ℕ) {t₀ : ℕ} (ht₀ : 1 ≤ t₀)
    (hV : t₀ ^ 3 + t₀ + 1 ≤ Fintype.card V) :
    ∃ (H' : Colored3Graph κ V) (C : TriadicComplex3 V), C.VertexCellsControlled t₀ ∧
      H.IsStrongRegularApproximation3 H' C ε F R (t₀ ^ 3 + t₀ + 1) := by
  obtain ⟨C, hC, h⟩ := H.exists_strong_regular_approximation3_of_one_le hε.le (hF _) (hF _) R
    ht₀ (by omega)
  exact ⟨H, C, hC, h⟩

end TauCeti
