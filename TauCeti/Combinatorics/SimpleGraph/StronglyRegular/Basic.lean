/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import TauCeti.Combinatorics.SimpleGraph.AdjMatrix

import Mathlib.Tactic.Ring

/-!
# The strongly regular equation

A finite simple graph `G` with adjacency matrix `A` is strongly regular with parameters
`(n, k, ℓ, μ)` (Mathlib's `SimpleGraph.IsSRGWith`) exactly when it has `n` vertices and
`A² = (ℓ - μ) A + (k - μ) I + μ J`, where `J` is the all-ones matrix. Since the `(v, w)` entry of
`A²` counts the common neighbours of `v` and `w`, an identity `A² = a A + b I + c J` says that
every degree is `b + c`, that adjacent vertices have `a + c` common neighbours and that distinct
nonadjacent vertices have `c`. This file proves this dictionary and the parameter inequalities
that hold away from the complete and the edgeless graphs.

Mathlib's `SimpleGraph.IsSRGWith` admits the complete graph (with every `μ`) and the edgeless
graph (with every `ℓ`); the matrix equation and its converse hold in these cases as well, while
the parameter bounds exclude them by hypothesis.

## Main results

* `SimpleGraph.adjMatrix_sq_eq_iff`: `A² = a A + b I + c J` in terms of degrees and numbers of
  common neighbours.
* `SimpleGraph.isSRGWith_iff_adjMatrix_sq_eq`: over a ring of characteristic zero, `G` is
  strongly regular with parameters `(n, k, ℓ, μ)` exactly when it has `n` vertices and
  `A² = (ℓ - μ) A + (k - μ) I + μ J`.
* `SimpleGraph.exists_isSRGWith_iff_exists_adjMatrix_sq_eq`: `G` is strongly regular for some
  parameters exactly when `A²` is a linear combination of `A`, `I` and `J` over a ring of
  characteristic zero.
* `SimpleGraph.IsSRGWith.le_of_ne_top`, `SimpleGraph.IsSRGWith.lt_of_ne_bot`: `μ ≤ k` when `G` is
  not complete, and `ℓ < k` when `G` has an edge.
* `SimpleGraph.IsSRGWith.param_eq_cast`: the parameter relation `k (k - ℓ - 1) = (n - k - 1) μ`
  with subtraction in a commutative ring.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012,
  Theorem 9.1.2 and Theorem 9.1.3 (i), pp. 117–118.
* N. Biggs, *Algebraic Graph Theory*, 2nd ed., Cambridge University Press, 1993, Additional
  result 3c, p. 20.
-/

public section

open Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {n k ℓ μ : ℕ}

/-! ### The square of the adjacency matrix -/

section Square

variable [DecidableEq V] {R : Type*}

/-- `A² = a A + b I + c J` holds exactly when every vertex has degree `b + c`, every two adjacent
vertices have `a + c` common neighbours and every two distinct nonadjacent vertices have `c`
common neighbours. -/
theorem adjMatrix_sq_eq_iff [Semiring R] {a b c : R} :
    G.adjMatrix R ^ 2 = a • G.adjMatrix R + b • (1 : Matrix V V R) +
        c • Matrix.of (fun _ _ ↦ (1 : R)) ↔
      (∀ v, (G.degree v : R) = b + c) ∧
        (∀ v w, G.Adj v w → (Fintype.card (G.commonNeighbors v w) : R) = a + c) ∧
          Pairwise fun v w ↦ ¬G.Adj v w → (Fintype.card (G.commonNeighbors v w) : R) = c := by
  have hdiag (v : V) : (G.adjMatrix R ^ 2) v v = G.degree v := by
    rw [sq, adjMatrix_mul_self_apply_self]
  rw [← Matrix.ext_iff]
  refine ⟨fun h ↦ ⟨fun v ↦ ?_, fun v w hvw ↦ ?_, fun v w hne hvw ↦ ?_⟩,
    fun ⟨hdeg, hadj, hnadj⟩ v w ↦ ?_⟩
  · simpa [hdiag] using h v v
  · simpa [adjMatrix_sq_apply, hvw, hvw.ne] using h v w
  · simpa [adjMatrix_sq_apply, hvw, hne] using h v w
  · obtain rfl | hne := eq_or_ne v w
    · simpa [hdiag] using hdeg v
    · by_cases hvw : G.Adj v w
      · simpa [adjMatrix_sq_apply, hvw, hne] using hadj v w hvw
      · simpa [adjMatrix_sq_apply, hvw, hne] using hnadj hne hvw

/-! ### The strongly regular equation -/

/-- **The strongly regular equation.** Over a ring of characteristic zero, `G` is strongly
regular with parameters `(n, k, ℓ, μ)` exactly when it has `n` vertices and
`A² = (ℓ - μ) A + (k - μ) I + μ J`. -/
theorem isSRGWith_iff_adjMatrix_sq_eq [Ring R] [CharZero R] :
    G.IsSRGWith n k ℓ μ ↔ Fintype.card V = n ∧
      G.adjMatrix R ^ 2 = ((ℓ : R) - μ) • G.adjMatrix R + ((k : R) - μ) • (1 : Matrix V V R) +
        (μ : R) • Matrix.of (fun _ _ ↦ (1 : R)) := by
  simp only [adjMatrix_sq_eq_iff, sub_add_cancel, Nat.cast_inj]
  exact ⟨fun ⟨hn, hk, hℓ, hμ⟩ ↦ ⟨hn, hk, hℓ, hμ⟩, fun ⟨hn, hk, hℓ, hμ⟩ ↦ ⟨hn, hk, hℓ, hμ⟩⟩

/-- **The strongly regular equation with arbitrary coefficients.** Over a ring of characteristic
zero, `G` is strongly regular for some parameters exactly when `A²` is a linear combination of
`A`, the identity `I` and the all-ones matrix `J`. -/
theorem exists_isSRGWith_iff_exists_adjMatrix_sq_eq [Ring R] [CharZero R] :
    (∃ k ℓ μ : ℕ, G.IsSRGWith (Fintype.card V) k ℓ μ) ↔
      ∃ a b c : R, G.adjMatrix R ^ 2 =
        a • G.adjMatrix R + b • (1 : Matrix V V R) + c • Matrix.of (fun _ _ ↦ (1 : R)) := by
  refine ⟨fun ⟨k, ℓ, μ, h⟩ ↦ ⟨_, _, _, (isSRGWith_iff_adjMatrix_sq_eq.1 h).2⟩, ?_⟩
  rintro ⟨a, b, c, h⟩
  obtain ⟨hdeg, hadj, hnadj⟩ := adjMatrix_sq_eq_iff.1 h
  -- A natural-number count with a constant value in `R` on a set of pairs is constant.
  have key (P : V → V → Prop) (f : V → V → ℕ) (x : R) (hf : ∀ v w, P v w → (f v w : R) = x) :
      ∃ m : ℕ, ∀ v w, P v w → f v w = m := by
    by_cases hP : ∃ v w, P v w
    · obtain ⟨v₀, w₀, h₀⟩ := hP
      exact ⟨f v₀ w₀, fun v w hvw ↦ by exact_mod_cast (hf v w hvw).trans (hf v₀ w₀ h₀).symm⟩
    · exact ⟨0, fun v w hvw ↦ (hP ⟨v, w, hvw⟩).elim⟩
  obtain ⟨k, hk⟩ := key (fun v w ↦ v = w) (fun v _ ↦ G.degree v) (b + c) (by grind)
  obtain ⟨ℓ, hℓ⟩ := key G.Adj (fun v w ↦ Fintype.card (G.commonNeighbors v w)) (a + c) hadj
  obtain ⟨μ, hμ⟩ := key (fun v w ↦ v ≠ w ∧ ¬G.Adj v w)
    (fun v w ↦ Fintype.card (G.commonNeighbors v w)) c fun v w h ↦ hnadj h.1 h.2
  exact ⟨k, ℓ, μ, rfl, fun v ↦ hk v v rfl, hℓ, fun v w hne hvw ↦ hμ v w ⟨hne, hvw⟩⟩

end Square

/-! ### Parameter bounds -/

/-- In a strongly regular graph that is not complete, `μ ≤ k`: two distinct nonadjacent
vertices have their `μ` common neighbours among the `k` neighbours of one of them. -/
theorem IsSRGWith.le_of_ne_top (h : G.IsSRGWith n k ℓ μ) (htop : G ≠ ⊤) : μ ≤ k := by
  obtain ⟨v, w, hne, hvw⟩ := ne_top_iff_exists_not_adj.1 htop
  rw [← h.of_not_adj hne hvw, ← h.regular v]
  exact G.card_commonNeighbors_le_degree_left v w

/-- In a strongly regular graph with an edge, `ℓ < k`: two adjacent vertices `v`, `w` have their
`ℓ` common neighbours among the neighbours of `v` other than `w`. -/
theorem IsSRGWith.lt_of_ne_bot (h : G.IsSRGWith n k ℓ μ) (hbot : G ≠ ⊥) : ℓ < k := by
  obtain ⟨v, w, hvw⟩ := ne_bot_iff_exists_adj.1 hbot
  rw [← h.of_adj v w hvw, ← h.regular v]
  exact hvw.card_commonNeighbors_lt_degree

/-- **The parameter relation in a commutative ring.** For a strongly regular graph with at least
one vertex, `k (k - ℓ - 1) = (n - k - 1) μ` with subtraction in any commutative ring, in
particular in `ℤ` and `ℝ`. Mathlib's `SimpleGraph.IsSRGWith.param_eq` is the same relation with
truncated subtraction in `ℕ`. -/
theorem IsSRGWith.param_eq_cast {R : Type*} [CommRing R] (h : G.IsSRGWith n k ℓ μ)
    (hn : 0 < n) : (k : R) * ((k : R) - ℓ - 1) = ((n : R) - k - 1) * μ := by
  obtain ⟨v⟩ : Nonempty V := by rw [← Fintype.card_pos_iff, h.card]; exact hn
  have hkn : k + 1 ≤ n := h.card ▸ h.regular v ▸ G.degree_lt_card_verts v
  have hR : ((n : R) - k - 1) * μ = (((n - k - 1) * μ : ℕ) : R) := by
    push_cast [Nat.sub_sub, Nat.cast_sub hkn]
    ring
  have hL : (k : R) * ((k : R) - ℓ - 1) = ((k * (k - ℓ - 1) : ℕ) : R) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).1 (h.regular v ▸ hk)
    have hℓk : ℓ + 1 ≤ k := h.lt_of_ne_bot (ne_bot_iff_exists_adj.2 ⟨v, w, hvw⟩)
    push_cast [Nat.sub_sub, Nat.cast_sub hℓk]
    ring
  rw [hL, hR, h.param_eq G hn]

end SimpleGraph
