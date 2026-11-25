/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
public import TauCeti.Combinatorics.SimpleGraph.OddTriangles
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Kozlov's staircase graphs

For natural numbers `c` and `t`, `SimpleGraph.staircase c t` is the bipartite graph on
`Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c` that joins `Sum.inl i` to `Sum.inr (Sum.inl j)` whenever
`(i : ℕ) < c * (t - (j : ℕ) / c)` and has no other edges, leaving the `c` vertices of `Fin c`
isolated. When `c, t ≥ 1` and `n = c * (2 * t + 1)`, this realizes the `c`-fold blow-up of the
staircase Ferrers graph `G_n(t, t - 1, …, 1)` of D. N. Kozlov, *The first Cheeger constant of a
simplex*, arXiv:1610.07136v2, Definition 3.2, which serves as the extremal binary witness on
`n` vertices whenever `n ≥ 3` is not a power of two.

## Main definitions and results

* `SimpleGraph.staircase`: Kozlov's staircase graph on `Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c`.
* `SimpleGraph.card_edgeFinset_staircase`: `#(staircase c t).edgeFinset = c ^ 2 * t * (t + 1) / 2`.
* `SimpleGraph.isCutMinimal_staircase`: `(staircase c t).IsCutMinimal`
  (Kozlov, Lemma 3.8 and Corollary 3.13).
* `SimpleGraph.card_oddTriangleFinset_staircase`: the odd-triangle count over `ℝ` is
  `((c * (2 * t + 1) : ℝ) / 3) * #(staircase c t).edgeFinset`
  (Kozlov, equation (2.5) and Lemma 3.10).
-/

public section

open Finset

namespace SimpleGraph

/-! ### Definition, decidability, and adjacency -/

private def staircaseRel (c t : ℕ) :
    Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c → Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c → Prop
  | .inl i, .inr (.inl j) => (i : ℕ) < c * (t - (j : ℕ) / c)
  | _, _ => False

/-- **Kozlov's staircase graph** on `Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c` joins `Sum.inl i` to
`Sum.inr (Sum.inl j)` iff `(i : ℕ) < c * (t - (j : ℕ) / c)` and has no other edges, leaving the
`Fin c` summand isolated (Kozlov, arXiv:1610.07136v2, Definition 3.2). -/
def staircase (c t : ℕ) : SimpleGraph (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c) :=
  SimpleGraph.fromRel (staircaseRel c t)

/-- Adjacency from the left part `Fin (c * t)` to the middle part `Fin (c * t)` in
`staircase c t`. -/
@[simp]
theorem staircase_adj_inl_inr_inl {c t : ℕ} (i j : Fin (c * t)) :
    (staircase c t).Adj (.inl i) (.inr (.inl j)) ↔ (i : ℕ) < c * (t - (j : ℕ) / c) := by
  simp [staircase, staircaseRel]

/-- Adjacency from the middle part `Fin (c * t)` to the left part `Fin (c * t)` in
`staircase c t`. -/
@[simp]
theorem staircase_adj_inr_inl_inl {c t : ℕ} (j i : Fin (c * t)) :
    (staircase c t).Adj (.inr (.inl j)) (.inl i) ↔ (i : ℕ) < c * (t - (j : ℕ) / c) := by
  simp [staircase, staircaseRel]

/-- No two vertices in the left part of `staircase c t` are adjacent. -/
@[simp]
theorem not_staircase_adj_inl_inl {c t : ℕ} (i j : Fin (c * t)) :
    ¬ (staircase c t).Adj (.inl i) (.inl j) := by
  simp [staircase, staircaseRel]

/-- No two vertices in the right sum `Fin (c * t) ⊕ Fin c` of `staircase c t` are adjacent. -/
@[simp]
theorem not_staircase_adj_inr_inr {c t : ℕ} (u v : Fin (c * t) ⊕ Fin c) :
    ¬ (staircase c t).Adj (.inr u) (.inr v) := by
  simp [staircase, staircaseRel]

/-- Vertices in the `Fin c` summand of `staircase c t` have no neighbours on the left. -/
@[simp]
theorem not_staircase_adj_inl_inr_inr {c t : ℕ} (i : Fin (c * t)) (k : Fin c) :
    ¬ (staircase c t).Adj (.inl i) (.inr (.inr k)) := by
  simp [staircase, staircaseRel]

/-- Vertices in the `Fin c` summand of `staircase c t` have no neighbours on the left (symmetric
orientation). -/
@[simp]
theorem not_staircase_adj_inr_inr_inl {c t : ℕ} (k : Fin c) (i : Fin (c * t)) :
    ¬ (staircase c t).Adj (.inr (.inr k)) (.inl i) := by
  simp [staircase, staircaseRel]

/-- Adjacency in `staircase c t` is decidable. -/
instance instDecidableRelStaircaseAdj (c t : ℕ) : DecidableRel (staircase c t).Adj
  | .inl i, .inr (.inl j) => decidable_of_iff' _ (staircase_adj_inl_inr_inl i j)
  | .inr (.inl j), .inl i => decidable_of_iff' _ (staircase_adj_inr_inl_inl j i)
  | .inl i, .inl j => isFalse (not_staircase_adj_inl_inl i j)
  | .inr u, .inr v => isFalse (not_staircase_adj_inr_inr u v)
  | .inl i, .inr (.inr k) => isFalse (not_staircase_adj_inl_inr_inr i k)
  | .inr (.inr k), .inl i => isFalse (not_staircase_adj_inr_inr_inl k i)

/-- Block-index characterization of adjacency in `staircase c t`: `Sum.inl i` and
`Sum.inr (Sum.inl j)` are adjacent iff their `c`-block indices have sum strictly below `t`. -/
theorem staircase_adj_inl_inr_inl_iff_add_lt {c t : ℕ} (i j : Fin (c * t)) :
    (staircase c t).Adj (.inl i) (.inr (.inl j)) ↔ (i : ℕ) / c + (j : ℕ) / c < t := by
  have hc : 0 < c := Nat.pos_of_ne_zero fun h ↦ by
    subst h
    exact Fin.elim0 (Fin.cast (Nat.zero_mul t) i)
  have hj : (j : ℕ) / c < t := (Nat.div_lt_iff_lt_mul hc).mpr (by simp [mul_comm])
  rw [staircase_adj_inl_inr_inl, mul_comm c (t - (j : ℕ) / c), ← Nat.div_lt_iff_lt_mul hc]
  omega

/-- At blow-up parameter `0`, `staircase 0 t` is the empty graph. -/
@[simp]
theorem staircase_zero_left (t : ℕ) : staircase 0 t = ⊥ := by
  ext u v
  rcases u with i | (j | k)
  · exact Fin.elim0 (Fin.cast (Nat.zero_mul t) i)
  · rcases v with i | _
    · exact Fin.elim0 (Fin.cast (Nat.zero_mul t) i)
    · simp
  · exact Fin.elim0 k

/-- At step parameter `0`, `staircase c 0` is the empty graph. -/
@[simp]
theorem staircase_zero_right (c : ℕ) : staircase c 0 = ⊥ := by
  ext u v
  rcases u with i | (j | k)
  · exact Fin.elim0 i
  · exact Fin.elim0 j
  · rcases v with i | w
    · exact Fin.elim0 i
    · simp [not_staircase_adj_inr_inr (.inr k) w]

/-- `staircase c t` is bipartite, with `Fin (c * t)` on one side and `Fin (c * t) ⊕ Fin c` on the
other. -/
theorem isBipartite_staircase (c t : ℕ) : (staircase c t).IsBipartite := by
  refine ⟨Coloring.mk (Sum.elim (fun _ ↦ (0 : Fin 2)) (fun _ ↦ 1)) ?_⟩
  intro u v huv
  rcases u with i | u <;> rcases v with j | v <;> simp_all

/-- `staircase c t` is bipartite with the rows `Sum.inl i` on one side and the columns
`Sum.inr (Sum.inl j)` on the other; the vertices of the `Fin c` summand lie on neither side. -/
theorem isBipartiteWith_staircase (c t : ℕ) :
    (staircase c t).IsBipartiteWith (Set.range Sum.inl) (Set.range fun j ↦ .inr (.inl j)) where
  disjoint := Set.disjoint_left.mpr <| by rintro _ ⟨i, rfl⟩ ⟨j, hj⟩; cases hj
  mem_of_adj u v h := by
    rcases u with i | (j | k) <;> rcases v with i' | (j' | k') <;> simp_all

/-- `staircase c t` contains no `3`-cliques. -/
theorem cliqueFree_staircase (c t : ℕ) : (staircase c t).CliqueFree 3 :=
  (isBipartite_staircase c t).cliqueFree (by decide)

/-! ### Block reindexing, vertex degrees, and edge count -/

private def blockEquiv (c t : ℕ) : Fin t × Fin c ≃ Fin (c * t) :=
  finProdFinEquiv.trans (finCongr (mul_comm t c))

private theorem val_blockEquiv (c t : ℕ) (p : Fin t × Fin c) :
    (blockEquiv c t p : ℕ) = p.2 + c * p.1 := by
  simp [blockEquiv]

private theorem blockEquiv_div (c t : ℕ) (p : Fin t × Fin c) :
    (blockEquiv c t p : ℕ) / c = p.1 := by
  have hc : 0 < c := Nat.pos_of_ne_zero fun h ↦ by subst h; exact Fin.elim0 p.2
  rw [val_blockEquiv, Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt p.2.isLt, zero_add]

private theorem blockEquiv_symm_fst (c t : ℕ) (i : Fin (c * t)) :
    (((blockEquiv c t).symm i).1 : ℕ) = (i : ℕ) / c := by
  simpa using (blockEquiv_div c t ((blockEquiv c t).symm i)).symm

/-- Degree of a left-part vertex `Sum.inl i` in `staircase c t`. -/
@[simp]
theorem degree_staircase_inl {c t : ℕ} (i : Fin (c * t)) :
    (staircase c t).degree (.inl i) = c * (t - (i : ℕ) / c) := by
  rw [← card_neighborFinset_eq_degree]
  have hle : c * (t - (i : ℕ) / c) ≤ c * t := Nat.mul_le_mul_left c (Nat.sub_le t _)
  let emb : Fin (c * t) ↪ Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c :=
    (Function.Embedding.inl).trans (Function.Embedding.inr)
  have hnbhd :
      (staircase c t).neighborFinset (.inl i) =
        ((range (c * (t - (i : ℕ) / c))).attachFin
          (fun m hm ↦ (mem_range.mp hm).trans_le hle)).map emb := by
    ext v
    rcases v with j | (j | k)
    · simp [emb]
    · simp only [emb, mem_neighborFinset, staircase_adj_inl_inr_inl_iff_add_lt, mem_map,
        mem_attachFin, mem_range, Function.Embedding.trans_apply, Function.Embedding.inl_apply,
        Function.Embedding.inr_apply, Sum.inr.injEq, Sum.inl.injEq, exists_eq_right]
      rw [add_comm, ← staircase_adj_inl_inr_inl_iff_add_lt, staircase_adj_inl_inr_inl]
    · simp [emb]
  rw [hnbhd, card_map, card_attachFin, card_range]

/-- Degree of a middle-part vertex `Sum.inr (Sum.inl j)` in `staircase c t`. -/
@[simp]
theorem degree_staircase_inr_inl {c t : ℕ} (j : Fin (c * t)) :
    (staircase c t).degree (.inr (.inl j)) = c * (t - (j : ℕ) / c) := by
  rw [← card_neighborFinset_eq_degree]
  have hle : c * (t - (j : ℕ) / c) ≤ c * t := Nat.mul_le_mul_left c (Nat.sub_le t _)
  have hnbhd :
      (staircase c t).neighborFinset (.inr (.inl j)) =
        ((range (c * (t - (j : ℕ) / c))).attachFin
          (fun m hm ↦ (mem_range.mp hm).trans_le hle)).map Function.Embedding.inl := by
    ext v
    rcases v with i | _ <;> simp
  rw [hnbhd, card_map, card_attachFin, card_range]

/-- Every vertex in the `Fin c` summand of `staircase c t` is isolated. -/
@[simp]
theorem degree_staircase_inr_inr {c t : ℕ} (k : Fin c) :
    (staircase c t).degree (.inr (.inr k)) = 0 := by
  rw [← card_neighborFinset_eq_degree, card_eq_zero]
  ext v
  rcases v with _ | _ <;> simp

/-- Twice the edge count of `staircase c t` is `c ^ 2 * t * (t + 1)`. -/
theorem two_mul_card_edgeFinset_staircase (c t : ℕ) :
    2 * #(staircase c t).edgeFinset = c ^ 2 * t * (t + 1) := by
  rw [← sum_degrees_eq_twice_card_edges, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [degree_staircase_inl, degree_staircase_inr_inl, degree_staircase_inr_inr,
    sum_const_zero, add_zero, ← two_mul]
  rw [Fin.sum_univ_eq_sum_range (fun l ↦ c * (t - l / c)) (c * t), sum_range_mul_eq_sum_sum]
  have hblocks :
      ∑ a ∈ range t, ∑ r ∈ range c, c * (t - (c * a + r) / c) =
        c ^ 2 * ∑ a ∈ range t, (t - a) := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    have hinner : ∑ r ∈ range c, c * (t - (c * a + r) / c) = ∑ _r ∈ range c, c * (t - a) :=
      sum_congr rfl fun r hr ↦ by
        have hr' : r < c := mem_range.mp hr
        rw [Nat.mul_add_div (Nat.zero_lt_of_lt hr'), Nat.div_eq_of_lt hr', add_zero]
    rw [hinner, sum_const, card_range, smul_eq_mul]
    ring
  have hsum : 2 * ∑ a ∈ range t, (t - a) = t * (t + 1) := by
    rw [← sum_range_reflect (fun a ↦ t - a) t, mul_sum, ← sum_range_two_mul_succ]
    exact sum_congr rfl fun k hk ↦ congrArg (2 * ·) (by have := mem_range.mp hk; omega)
  calc
    2 * ∑ a ∈ range t, ∑ r ∈ range c, c * (t - (c * a + r) / c)
      = c ^ 2 * (2 * ∑ a ∈ range t, (t - a)) := by rw [hblocks]; ring
    _ = c ^ 2 * t * (t + 1) := by rw [hsum]; ring

/-- `staircase c t` has `c ^ 2 * t * (t + 1) / 2` edges. -/
theorem card_edgeFinset_staircase (c t : ℕ) :
    #(staircase c t).edgeFinset = c ^ 2 * t * (t + 1) / 2 := by
  rw [← two_mul_card_edgeFinset_staircase, Nat.mul_div_right _ (by decide)]

/-! ### Cut-minimality -/

private theorem staircase_endpoint_bound {U V Q c : ℤ} {t : ℕ} (hc : 0 ≤ c)
    (hU₁ : -(t : ℤ) * c ≤ U) (hU₂ : U ≤ (t : ℤ) * c)
    (hV₁ : -(t : ℤ) * c ≤ V) (hV₂ : V ≤ (t : ℤ) * c)
    (hpos : (U + V + c) ^ 2 - 4 * Q ≤ (2 * (t : ℤ) ^ 2 + 2 * (t : ℤ) + 1) * c ^ 2)
    (hneg : (U + V - c) ^ 2 - 4 * Q ≤ (2 * (t : ℤ) ^ 2 + 2 * (t : ℤ) + 1) * c ^ 2)
    (su sv sw : Bool) :
    (U + (if su then c else -c) + V + (if sv then c else -c) + (if sw then c else -c)) ^ 2 -
      4 * (Q + U * (if sv then c else -c) +
        (if su then c else -c) * (if sv then c else -c)) ≤
      (2 * ((t : ℤ) + 1) ^ 2 + 2 * ((t : ℤ) + 1) + 1) * c ^ 2 := by
  cases su <;> cases sv <;> cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith

private theorem staircase_step_bound {U V Q c ut v0 w : ℤ} {t : ℕ} (hc : 0 ≤ c)
    (hU₁ : -(t : ℤ) * c ≤ U) (hU₂ : U ≤ (t : ℤ) * c)
    (hV₁ : -(t : ℤ) * c ≤ V) (hV₂ : V ≤ (t : ℤ) * c)
    (hpos : (U + V + c) ^ 2 - 4 * Q ≤ (2 * (t : ℤ) ^ 2 + 2 * (t : ℤ) + 1) * c ^ 2)
    (hneg : (U + V - c) ^ 2 - 4 * Q ≤ (2 * (t : ℤ) ^ 2 + 2 * (t : ℤ) + 1) * c ^ 2)
    (hut : -c ≤ ut ∧ ut ≤ c) (hv0 : -c ≤ v0 ∧ v0 ≤ c) (hw : -c ≤ w ∧ w ≤ c) :
    (U + ut + V + v0 + w) ^ 2 - 4 * (Q + U * v0 + ut * v0) ≤
      (2 * ((t : ℤ) + 1) ^ 2 + 2 * ((t : ℤ) + 1) + 1) * c ^ 2 := by
  -- A monic quadratic `x ^ 2 + b * x + d` on `[-c, c]` is bounded by its values at `±c`.
  have hquad {b d x M : ℤ} (hx₁ : -c ≤ x) (hx₂ : x ≤ c)
      (h₁ : c ^ 2 - b * c + d ≤ M) (h₂ : c ^ 2 + b * c + d ≤ M) :
      x ^ 2 + b * x + d ≤ M := by
    rcases le_or_gt 0 b with hb | hb <;> nlinarith
  have h1 (su sv : Bool) :
      (U + (if su then c else -c) + V + (if sv then c else -c) + w) ^ 2 -
        4 * (Q + U * (if sv then c else -c) +
          (if su then c else -c) * (if sv then c else -c)) ≤
        (2 * ((t : ℤ) + 1) ^ 2 + 2 * ((t : ℤ) + 1) + 1) * c ^ 2 := by
    set ut' : ℤ := if su then c else -c
    set v0' : ℤ := if sv then c else -c
    -- Collect terms as a monic quadratic in `w` to reduce to the endpoints `w = ±c`.
    have hquad_w :
        (U + ut' + V + v0' + w) ^ 2 - 4 * (Q + U * v0' + ut' * v0') =
          w ^ 2 + 2 * (U + ut' + V + v0') * w +
            ((U + ut' + V + v0') ^ 2 - 4 * (Q + U * v0' + ut' * v0')) := by ring
    rw [hquad_w]
    refine hquad hw.1 hw.2 ?_ ?_
    · convert staircase_endpoint_bound hc hU₁ hU₂ hV₁ hV₂ hpos hneg su sv false using 1
      simp only [ut', v0', Bool.false_eq_true, ↓reduceIte]; ring
    · convert staircase_endpoint_bound hc hU₁ hU₂ hV₁ hV₂ hpos hneg su sv true using 1
      simp only [ut', v0', ↓reduceIte]; ring
  have h2 (su : Bool) :
      (U + (if su then c else -c) + V + v0 + w) ^ 2 -
        4 * (Q + U * v0 + (if su then c else -c) * v0) ≤
        (2 * ((t : ℤ) + 1) ^ 2 + 2 * ((t : ℤ) + 1) + 1) * c ^ 2 := by
    set ut' : ℤ := if su then c else -c
    -- Collect terms as a monic quadratic in `v0` to reduce to the endpoints `v0 = ±c`.
    have hquad_v0 :
        (U + ut' + V + v0 + w) ^ 2 - 4 * (Q + U * v0 + ut' * v0) =
          v0 ^ 2 + (2 * (U + ut' + V + w) - 4 * (U + ut')) * v0 +
            ((U + ut' + V + w) ^ 2 - 4 * Q) := by ring
    rw [hquad_v0]
    refine hquad hv0.1 hv0.2 ?_ ?_
    · convert h1 su false using 1; simp only [ut', Bool.false_eq_true, ↓reduceIte]; ring
    · convert h1 su true using 1; simp only [ut', ↓reduceIte]; ring
  -- Collect terms as a monic quadratic in `ut` to reduce to the endpoints `ut = ±c`.
  have hquad_ut :
      (U + ut + V + v0 + w) ^ 2 - 4 * (Q + U * v0 + ut * v0) =
        ut ^ 2 + (2 * (U + V + v0 + w) - 4 * v0) * ut +
          ((U + V + v0 + w) ^ 2 - 4 * (Q + U * v0)) := by ring
  rw [hquad_ut]
  refine hquad hut.1 hut.2 ?_ ?_
  · convert h2 false using 1; simp only [Bool.false_eq_true, ↓reduceIte]; ring
  · convert h2 true using 1; simp only [↓reduceIte]; ring

private theorem staircase_poly_le {c : ℤ} (hc : 0 ≤ c) (t : ℕ) :
    ∀ (u v : ℕ → ℤ) (w : ℤ),
      (∀ a < t, -c ≤ u a ∧ u a ≤ c) →
      (∀ b < t, -c ≤ v b ∧ v b ≤ c) →
      (-c ≤ w ∧ w ≤ c) →
      (∑ a ∈ range t, u a + ∑ b ∈ range t, v b + w) ^ 2 -
        4 * ∑ a ∈ range t, ∑ b ∈ range (t - a), u a * v b ≤
        (2 * (t : ℤ) ^ 2 + 2 * (t : ℤ) + 1) * c ^ 2 := by
  induction t with
  | zero =>
    intro _ _ w _ _ hw
    simp only [range_zero, sum_empty, zero_add, mul_zero, sub_zero, Nat.cast_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_mul]
    nlinarith
  | succ t ih =>
    intro u v w hu hv hw
    let U := ∑ a ∈ range t, u a
    let V := ∑ b ∈ range t, v (b + 1)
    let Q := ∑ a ∈ range t, ∑ b ∈ range (t - a), u a * v (b + 1)
    have hU₁ : -(t : ℤ) * c ≤ U := by
      simpa [U, neg_mul] using sum_le_sum fun a ha ↦ (hu a (Nat.lt_succ_of_lt (mem_range.mp ha))).1
    have hU₂ : U ≤ (t : ℤ) * c := by
      simpa [U] using sum_le_sum fun a ha ↦ (hu a (Nat.lt_succ_of_lt (mem_range.mp ha))).2
    have hV₁ : -(t : ℤ) * c ≤ V := by
      simpa [V, neg_mul] using
        sum_le_sum fun b hb ↦ (hv (b + 1) (Nat.succ_lt_succ (mem_range.mp hb))).1
    have hV₂ : V ≤ (t : ℤ) * c := by
      simpa [V] using sum_le_sum fun b hb ↦ (hv (b + 1) (Nat.succ_lt_succ (mem_range.mp hb))).2
    have hpos := ih u (fun b ↦ v (b + 1)) c
      (fun a ha ↦ hu a (Nat.lt_succ_of_lt ha)) (fun b hb ↦ hv (b + 1) (Nat.succ_lt_succ hb))
      ⟨by linarith, le_rfl⟩
    have hneg := ih u (fun b ↦ v (b + 1)) (-c)
      (fun a ha ↦ hu a (Nat.lt_succ_of_lt ha)) (fun b hb ↦ hv (b + 1) (Nat.succ_lt_succ hb))
      ⟨le_rfl, by linarith⟩
    have hQ : ∑ a ∈ range (t + 1), ∑ b ∈ range (t + 1 - a), u a * v b =
        Q + U * v 0 + u t * v 0 := by
      rw [sum_range_succ, Nat.add_sub_self_left, range_one, sum_singleton]
      have hinner : ∑ a ∈ range t, ∑ b ∈ range (t + 1 - a), u a * v b =
          Q + ∑ a ∈ range t, u a * v 0 := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun a ha ↦ ?_
        have hat : t + 1 - a = (t - a) + 1 := by have := mem_range.mp ha; omega
        rw [hat, sum_range_succ']
      rw [hinner, ← sum_mul]
    rw [sum_range_succ u t, sum_range_succ' v t, hQ, ← add_assoc (U + u t) V (v 0)]
    have hgoal := staircase_step_bound hc hU₁ hU₂ hV₁ hV₂ hpos hneg
      (hu t (Nat.lt_succ_self t)) (hv 0 (Nat.zero_lt_succ t)) hw
    simpa only [Nat.cast_add, Nat.cast_one] using hgoal

private theorem card_between_staircase_bij {c t : ℕ}
    (S : Set (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) [DecidablePred (· ∈ S)] :
    #((staircase c t).between S Sᶜ).edgeFinset =
      #{p : (Fin t × Fin c) × (Fin t × Fin c) |
        (p.1.1 : ℕ) + (p.2.1 : ℕ) < t ∧
          ((.inl (blockEquiv c t p.1) ∈ S ∧ .inr (.inl (blockEquiv c t p.2)) ∉ S) ∨
            (.inl (blockEquiv c t p.1) ∉ S ∧ .inr (.inl (blockEquiv c t p.2)) ∈ S))} := by
  symm
  refine card_bij (fun p _ ↦ s(.inl (blockEquiv c t p.1), .inr (.inl (blockEquiv c t p.2))))
    ?_ ?_ ?_
  · rintro ⟨p₁, p₂⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    rw [mem_edgeFinset, mem_edgeSet, between_adj, staircase_adj_inl_inr_inl_iff_add_lt,
      blockEquiv_div, blockEquiv_div]
    exact ⟨hp.1, hp.2⟩
  · rintro ⟨p₁, p₂⟩ _ ⟨q₁, q₂⟩ _ h
    rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
    · exact Prod.ext ((blockEquiv c t).injective (Sum.inl.inj h₁))
        ((blockEquiv c t).injective (Sum.inl.inj (Sum.inr.inj h₂)))
    · exact False.elim (Sum.inl_ne_inr h₁)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeFinset, mem_edgeSet, between_adj] at he
      rcases u with i | (j | k) <;> rcases v with i' | (j' | k')
      · exact False.elim (not_staircase_adj_inl_inl _ _ he.1)
      · refine ⟨((blockEquiv c t).symm i, (blockEquiv c t).symm j'), ?_, by simp⟩
        simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply, blockEquiv_symm_fst]
        rw [staircase_adj_inl_inr_inl_iff_add_lt] at he
        simpa [Set.mem_compl_iff] using he
      · exact False.elim (not_staircase_adj_inl_inr_inr _ _ he.1)
      · refine ⟨((blockEquiv c t).symm i', (blockEquiv c t).symm j), ?_, by simp [Sym2.eq_swap]⟩
        simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply, blockEquiv_symm_fst]
        rw [adj_comm, staircase_adj_inl_inr_inl_iff_add_lt] at he
        refine ⟨he.1, ?_⟩
        rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ⟨Set.mem_compl_iff _ _ |>.mp h2, h1⟩
        · exact Or.inl ⟨h2, Set.mem_compl_iff _ _ |>.mp h1⟩
      · exact False.elim (not_staircase_adj_inr_inr _ _ he.1)
      · exact False.elim (not_staircase_adj_inr_inr _ _ he.1)
      · exact False.elim (not_staircase_adj_inr_inr_inl _ _ he.1)
      · exact False.elim (not_staircase_adj_inr_inr _ _ he.1)
      · exact False.elim (not_staircase_adj_inr_inr _ _ he.1)

private theorem card_between_staircase_eq {c t : ℕ}
    (S : Set (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) [DecidablePred (· ∈ S)] :
    #((staircase c t).between S Sᶜ).edgeFinset =
      ∑ a : Fin t, ∑ b ∈ {b : Fin t | (a : ℕ) + (b : ℕ) < t},
        (#{r : Fin c | .inl (blockEquiv c t (a, r)) ∈ S} *
            (c - #{r : Fin c | .inr (.inl (blockEquiv c t (b, r))) ∈ S}) +
          (c - #{r : Fin c | .inl (blockEquiv c t (a, r)) ∈ S}) *
            #{r : Fin c | .inr (.inl (blockEquiv c t (b, r))) ∈ S}) := by
  rw [card_between_staircase_bij S]
  let P (a b : Fin t) : Finset (Fin c × Fin c) :=
    {r : Fin c × Fin c |
      (.inl (blockEquiv c t (a, r.1)) ∈ S ∧ .inr (.inl (blockEquiv c t (b, r.2))) ∉ S) ∨
        (.inl (blockEquiv c t (a, r.1)) ∉ S ∧ .inr (.inl (blockEquiv c t (b, r.2))) ∈ S)}
  rw [card_eq_sum_card_fiberwise
    (f := fun p : (Fin t × Fin c) × (Fin t × Fin c) ↦ (p.1.1, p.2.1))
    (t := {ab : Fin t × Fin t | (ab.1 : ℕ) + (ab.2 : ℕ) < t})
    (fun p hp ↦ by simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢; exact hp.1)]
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [← sum_filter]
  refine sum_congr rfl fun b hb ↦ ?_
  have hab : (a : ℕ) + (b : ℕ) < t := (mem_filter.mp hb).2
  have hfib :
      #{p : (Fin t × Fin c) × (Fin t × Fin c) |
        ((p.1.1 : ℕ) + (p.2.1 : ℕ) < t ∧
          ((.inl (blockEquiv c t p.1) ∈ S ∧ .inr (.inl (blockEquiv c t p.2)) ∉ S) ∨
            (.inl (blockEquiv c t p.1) ∉ S ∧ .inr (.inl (blockEquiv c t p.2)) ∈ S))) ∧
          (p.1.1, p.2.1) = (a, b)} = #(P a b) := by
    refine card_nbij' (fun p ↦ (p.1.2, p.2.2)) (fun r ↦ ((a, r.1), (b, r.2))) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [P, mem_coe, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hp ⊢
      rcases hp with ⟨⟨_, hpred⟩, rfl, rfl⟩
      exact hpred
    · intro r hr
      simp only [P, mem_coe, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hr ⊢
      exact ⟨⟨hab, hr⟩, trivial⟩
    · rintro ⟨⟨a', r₁⟩, ⟨b', r₂⟩⟩ hp
      simp only [mem_coe, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hp
      rcases hp.2 with ⟨rfl, rfl⟩
      rfl
    · intro _ _; rfl
  rw [filter_filter, hfib]
  let A := ({r : Fin c | .inl (blockEquiv c t (a, r)) ∈ S} : Finset (Fin c))
  let B := ({r : Fin c | .inr (.inl (blockEquiv c t (b, r))) ∈ S} : Finset (Fin c))
  have hP : P a b = A ×ˢ Bᶜ ∪ Aᶜ ×ˢ B := by ext ⟨r₁, r₂⟩; simp [P, A, B]
  have hdisj : Disjoint (A ×ˢ Bᶜ) (Aᶜ ×ˢ B) := by
    rw [Finset.disjoint_left]
    rintro ⟨r₁, r₂⟩ h₁ h₂
    exact (mem_compl.mp (mem_product.mp h₂).1) (mem_product.mp h₁).1
  rw [hP, card_union_of_disjoint hdisj, card_product, card_product, card_compl, card_compl,
    Fintype.card_fin]

private theorem card_toFinset_staircase {c t : ℕ}
    (S : Set (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) [DecidablePred (· ∈ S)] :
    #S.toFinset =
      (∑ a : Fin t, #{r : Fin c | .inl (blockEquiv c t (a, r)) ∈ S}) +
        (∑ b : Fin t, #{r : Fin c | .inr (.inl (blockEquiv c t (b, r))) ∈ S}) +
        #{r : Fin c | .inr (.inr r) ∈ S} := by
  have hsum :
      #S.toFinset =
        #{i : Fin (c * t) | .inl i ∈ S} +
          (#{j : Fin (c * t) | .inr (.inl j) ∈ S} + #{k : Fin c | .inr (.inr k) ∈ S}) := by
    have h1 : S.toFinset = ({v | v ∈ S} : Finset _) := by ext; simp
    rw [h1, ← Fintype.card_subtype]
    let eqv :
        {v : Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c // v ∈ S} ≃
          {i : Fin (c * t) // .inl i ∈ S} ⊕
            ({j : Fin (c * t) // .inr (.inl j) ∈ S} ⊕ {k : Fin c // .inr (.inr k) ∈ S}) :=
      Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.refl _) Equiv.subtypeSum)
    rw [Fintype.card_congr eqv, Fintype.card_sum, Fintype.card_sum, Fintype.card_subtype,
      Fintype.card_subtype, Fintype.card_subtype]
  have hblock (P : Fin (c * t) → Prop) [DecidablePred P] :
      #{i : Fin (c * t) | P i} = ∑ a : Fin t, #{r : Fin c | P (blockEquiv c t (a, r))} := by
    have hbij : #{i : Fin (c * t) | P i} = #{p : Fin t × Fin c | P (blockEquiv c t p)} :=
      card_nbij' (blockEquiv c t).symm (blockEquiv c t)
        (fun i hi ↦ by simp only [mem_coe, mem_filter, mem_univ, true_and] at hi ⊢; simpa using hi)
        (fun p hp ↦ by simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢; exact hp)
        (fun _ _ ↦ (blockEquiv c t).apply_symm_apply _)
        (fun _ _ ↦ (blockEquiv c t).symm_apply_apply _)
    rw [hbij, card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun a _ ↦ card_nbij' Prod.snd (fun r ↦ (a, r)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
      exact hp.2 ▸ hp.1
    · intro r hr
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hr ⊢
      exact ⟨hr, trivial⟩
    · intro p hp
      simp only [mem_coe, mem_filter] at hp
      exact Prod.ext hp.2.symm rfl
    · intro _ _; rfl
  rw [hsum, hblock (fun i ↦ .inl i ∈ S), hblock (fun j ↦ .inr (.inl j) ∈ S), add_assoc]

private theorem eight_mul_sum_blocks_eq {c t : ℕ} {x y : ℕ → ℕ}
    (hx : ∀ a, x a ≤ c) (hy : ∀ b, y b ≤ c) :
    8 * ((∑ a ∈ range t, ∑ b ∈ range (t - a), (x a * (c - y b) + (c - x a) * y b) : ℕ) : ℤ) =
      2 * (t : ℤ) * ((t : ℤ) + 1) * (c : ℤ) ^ 2 -
        4 * ∑ a ∈ range t, ∑ b ∈ range (t - a),
          (2 * (x a : ℤ) - c) * (2 * (y b : ℤ) - c) := by
  push_cast
  rw [mul_sum]
  have hterm :
      (∑ a ∈ range t, 8 * ∑ b ∈ range (t - a),
          ((x a : ℤ) * ↑(c - y b) + ↑(c - x a) * (y b : ℤ))) =
        ∑ a ∈ range t, ∑ b ∈ range (t - a),
          (4 * (c : ℤ) ^ 2 - 4 * ((2 * (x a : ℤ) - c) * (2 * (y b : ℤ) - c))) := by
    refine sum_congr rfl fun a _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ ↦ ?_
    rw [Nat.cast_sub (hy b), Nat.cast_sub (hx a)]
    ring
  have h2sum_nat : 2 * ∑ a ∈ range t, (t - a) = t * (t + 1) := by
    rw [← sum_range_reflect (fun a ↦ t - a) t, mul_sum, ← sum_range_two_mul_succ]
    exact sum_congr rfl fun k hk ↦ congrArg (2 * ·) (by have := mem_range.mp hk; omega)
  have h2sum : 2 * (∑ a ∈ range t, ((t - a : ℕ) : ℤ)) = (t : ℤ) * ((t : ℤ) + 1) := by
    exact_mod_cast h2sum_nat
  rw [hterm]
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, ← sum_mul]
  -- Evaluate the constant `4 * c ^ 2` summand over the `∑_{a < t} (t - a)` block pairs.
  have hlead :
      (∑ a ∈ range t, ((t - a : ℕ) : ℤ)) * (4 * (c : ℤ) ^ 2) =
        2 * (t : ℤ) * ((t : ℤ) + 1) * (c : ℤ) ^ 2 := by
    calc (∑ a ∈ range t, ((t - a : ℕ) : ℤ)) * (4 * (c : ℤ) ^ 2)
      _ = 2 * (2 * ∑ a ∈ range t, ((t - a : ℕ) : ℤ)) * (c : ℤ) ^ 2 := by ring
      _ = 2 * (t : ℤ) * ((t : ℤ) + 1) * (c : ℤ) ^ 2 := by rw [h2sum]; ring
  rw [hlead]

private theorem two_mul_sum_blocks_le {c t : ℕ} {x y : ℕ → ℕ} {z m₁ m₂ : ℕ}
    (hx : ∀ a, x a ≤ c) (hy : ∀ b, y b ≤ c) (hz : z ≤ c)
    (hm₁ : m₁ = ∑ a ∈ range t, x a + ∑ b ∈ range t, y b + z)
    (hm₂ : m₁ + m₂ = c * (2 * t + 1)) :
    2 * ∑ a ∈ range t, ∑ b ∈ range (t - a), (x a * (c - y b) + (c - x a) * y b) ≤ m₁ * m₂ := by
  let u : ℕ → ℤ := fun a ↦ 2 * (x a : ℤ) - c
  let v : ℕ → ℤ := fun b ↦ 2 * (y b : ℤ) - c
  let w : ℤ := 2 * (z : ℤ) - c
  have hpoly := staircase_poly_le (c := (c : ℤ)) (Nat.cast_nonneg c) t u v w
    (fun a _ ↦ ⟨by dsimp only [u]; have := hx a; omega, by dsimp only [u]; have := hx a; omega⟩)
    (fun b _ ↦ ⟨by dsimp only [v]; have := hy b; omega, by dsimp only [v]; have := hy b; omega⟩)
    ⟨by dsimp only [w]; omega, by dsimp only [w]; omega⟩
  have hcut_int := eight_mul_sum_blocks_eq (t := t) hx hy
  have hprod_int :
      4 * ((m₁ : ℤ) * (m₂ : ℤ)) =
        (2 * (t : ℤ) + 1) ^ 2 * (c : ℤ) ^ 2 -
          (∑ a ∈ range t, u a + ∑ b ∈ range t, v b + w) ^ 2 := by
    have hsum_u : ∑ a ∈ range t, u a = 2 * (∑ a ∈ range t, (x a : ℤ)) - (t : ℤ) * c := by
      simp [u, sum_sub_distrib, ← mul_sum]
    have hsum_v : ∑ b ∈ range t, v b = 2 * (∑ b ∈ range t, (y b : ℤ)) - (t : ℤ) * c := by
      simp [v, sum_sub_distrib, ← mul_sum]
    have hm₁_z : (m₁ : ℤ) = ∑ a ∈ range t, (x a : ℤ) + ∑ b ∈ range t, (y b : ℤ) + z := by
      exact_mod_cast hm₁
    have hm_sum : (m₁ : ℤ) + (m₂ : ℤ) = (c : ℤ) * (2 * (t : ℤ) + 1) := by exact_mod_cast hm₂
    have hm₂_z : (m₂ : ℤ) = (c : ℤ) * (2 * (t : ℤ) + 1) - (m₁ : ℤ) := by linarith [hm_sum]
    rw [hm₂_z, hm₁_z, hsum_u, hsum_v]
    dsimp only [w]
    ring
  have hineq :
      (2 * ∑ a ∈ range t, ∑ b ∈ range (t - a), (x a * (c - y b) + (c - x a) * y b) : ℤ) ≤
        (m₁ * m₂ : ℤ) := by
    dsimp only [u, v] at hpoly
    push_cast at hcut_int ⊢
    -- Match the leading `c ^ 2` terms of `4 * (m₁ * m₂)` and `8 * cut` with the bound in `hpoly`.
    have hcoeff :
        (2 * (t : ℤ) + 1) ^ 2 * (c : ℤ) ^ 2 - 2 * (t : ℤ) * ((t : ℤ) + 1) * (c : ℤ) ^ 2 =
          (2 * (t : ℤ) ^ 2 + 2 * (t : ℤ) + 1) * (c : ℤ) ^ 2 := by ring
    linarith [hcoeff]
  exact Nat.cast_le.mp hineq

/-- **Kozlov's staircase cut-minimality theorem**: for all `c t : ℕ`, `staircase c t` is
cut-minimal (Kozlov, arXiv:1610.07136v2, Lemma 3.8 and Corollary 3.13). -/
@[simp]
theorem isCutMinimal_staircase (c t : ℕ) : (staircase c t).IsCutMinimal := by
  rw [isCutMinimal_iff_two_mul_card_between_le]
  intro S _
  let x : ℕ → ℕ := fun a ↦
    if h : a < t then #{r : Fin c | .inl (blockEquiv c t (⟨a, h⟩, r)) ∈ S} else 0
  let y : ℕ → ℕ := fun b ↦
    if h : b < t then #{r : Fin c | .inr (.inl (blockEquiv c t (⟨b, h⟩, r))) ∈ S} else 0
  let z : ℕ := #{r : Fin c | .inr (.inr r) ∈ S}
  have hx_le (a : ℕ) : x a ≤ c := by
    dsimp only [x]; split_ifs with h
    · exact (card_le_univ _).trans_eq (Fintype.card_fin c)
    · exact Nat.zero_le c
  have hy_le (b : ℕ) : y b ≤ c := by
    dsimp only [y]; split_ifs with h
    · exact (card_le_univ _).trans_eq (Fintype.card_fin c)
    · exact Nat.zero_le c
  have hz_le : z ≤ c := (card_le_univ _).trans_eq (Fintype.card_fin c)
  have hS_card : #S.toFinset = ∑ a ∈ range t, x a + ∑ b ∈ range t, y b + z := by
    rw [card_toFinset_staircase S, ← Fin.sum_univ_eq_sum_range (x ·) t,
      ← Fin.sum_univ_eq_sum_range (y ·) t]
    congr 2
    · exact sum_congr rfl fun ⟨a, ha⟩ _ ↦ by simp [x, ha]
    · exact sum_congr rfl fun ⟨b, hb⟩ _ ↦ by simp [y, hb]
  have hSc_card : #S.toFinset + #Sᶜ.toFinset = c * (2 * t + 1) := by
    have hcompl : Sᶜ.toFinset = S.toFinsetᶜ := by ext; simp
    rw [hcompl, add_comm, card_compl_add_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    ring
  have hcut_range :
      #((staircase c t).between S Sᶜ).edgeFinset =
        ∑ a ∈ range t, ∑ b ∈ range (t - a), (x a * (c - y b) + (c - x a) * y b) := by
    rw [card_between_staircase_eq S, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun ⟨a, ha⟩ _ ↦ ?_
    have hlt : ∀ b ∈ range (t - a), b < t := fun b hb ↦ by have := mem_range.mp hb; omega
    have hinner :
        ({b : Fin t | a + (b : ℕ) < t} : Finset (Fin t)) = (range (t - a)).attachFin hlt := by
      ext ⟨b, hb⟩; simp; omega
    conv_rhs => rw [← map_valEmbedding_attachFin hlt, sum_map]
    rw [hinner]
    refine sum_congr rfl fun ⟨b, hb⟩ _ ↦ ?_
    simp [x, y, ha, hb]
  rw [hcut_range]
  exact two_mul_sum_blocks_le hx_le hy_le hz_le hS_card hSc_card

/-! ### Odd-triangle count -/

/-- Three times the sum of squared vertex degrees of `staircase c t` is
`2 * (c * (2 * t + 1)) * #(staircase c t).edgeFinset`. -/
theorem three_mul_sum_degree_sq_staircase (c t : ℕ) :
    3 * ∑ v, (staircase c t).degree v ^ 2 =
      2 * (c * (2 * t + 1)) * #(staircase c t).edgeFinset := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [degree_staircase_inl, degree_staircase_inr_inl, degree_staircase_inr_inr,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, add_zero, ← two_mul]
  rw [Fin.sum_univ_eq_sum_range (fun l ↦ (c * (t - l / c)) ^ 2) (c * t), sum_range_mul_eq_sum_sum]
  have hpull :
      ∑ a ∈ range t, ∑ r ∈ range c, (c * (t - (c * a + r) / c)) ^ 2 =
        c ^ 3 * ∑ a ∈ range t, (t - a) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    have hinner :
        ∑ r ∈ range c, (c * (t - (c * a + r) / c)) ^ 2 = ∑ _r ∈ range c, (c * (t - a)) ^ 2 :=
      sum_congr rfl fun r hr ↦ by
        have hr' : r < c := mem_range.mp hr
        rw [Nat.mul_add_div (Nat.zero_lt_of_lt hr'), Nat.div_eq_of_lt hr', add_zero]
    rw [hinner, sum_const, card_range, smul_eq_mul]
    ring
  have hrefl : ∑ a ∈ range t, (t - a) ^ 2 = ∑ m ∈ range (t + 1), m ^ 2 := by
    rw [sum_range_succ', zero_pow (by decide), add_zero, ← sum_range_reflect (fun a ↦ (t - a) ^ 2)]
    refine sum_congr rfl fun k hk ↦ ?_
    have hkt : k < t := mem_range.mp hk
    congr 1
    omega
  have hsq6 := sum_range_id_sq_mul_six (t + 1)
  have h2t : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  rw [Nat.add_sub_cancel, h2t] at hsq6
  have hedge := two_mul_card_edgeFinset_staircase c t
  calc
    3 * (2 * ∑ a ∈ range t, ∑ r ∈ range c, (c * (t - (c * a + r) / c)) ^ 2)
      = c ^ 3 * ((∑ m ∈ range (t + 1), m ^ 2) * 6) := by
        rw [hpull, hrefl]
        ring
    _ = c * (2 * t + 1) * (c ^ 2 * t * (t + 1)) := by
        rw [hsq6]
        ring
    _ = 2 * (c * (2 * t + 1)) * #(staircase c t).edgeFinset := by
        rw [← hedge]
        ring

/-- Exact natural-number form of Kozlov's odd-triangle formula for `staircase c t`:
`3 * #(staircase c t).oddTriangleFinset = c * (2 * t + 1) * #(staircase c t).edgeFinset`
(Kozlov, arXiv:1610.07136v2, Lemma 3.10). It holds for any decidable equality on the vertices,
such as the one of a linear order chosen on them. -/
theorem three_mul_card_oddTriangleFinset_staircase (c t : ℕ)
    [DecidableEq (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)] :
    3 * #(staircase c t).oddTriangleFinset =
      c * (2 * t + 1) * #(staircase c t).edgeFinset := by
  have hodd := (staircase c t).card_oddTriangleFinset_add_sum_degree_sq (cliqueFree_staircase c t)
  have hcard : Fintype.card (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c) = c * (2 * t + 1) := by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    ring
  rw [hcard] at hodd
  have hdeg := three_mul_sum_degree_sq_staircase c t
  have h3 := congrArg (3 * ·) hodd
  rw [mul_add, hdeg] at h3
  linarith

/-- **Kozlov's staircase odd-triangle formula**: in `staircase c t` on `n = c * (2 * t + 1)`
vertices, the number of `3`-vertex subsets spanning an odd number of edges is
`(n / 3) * #(staircase c t).edgeFinset` over `ℝ`
(Kozlov, arXiv:1610.07136v2, equation (2.5) and Lemma 3.10). It holds for any decidable equality
on the vertices. -/
theorem card_oddTriangleFinset_staircase (c t : ℕ)
    [DecidableEq (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)] :
    (#(staircase c t).oddTriangleFinset : ℝ) =
      (c * (2 * t + 1) : ℝ) / 3 * #(staircase c t).edgeFinset := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (three_mul_card_oddTriangleFinset_staircase c t)
  push_cast at h
  linarith

end SimpleGraph
