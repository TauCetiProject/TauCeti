/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Staircase graphs

For `c t : ℕ`, the staircase graph `staircaseGraph c t` lives on
`Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c`: rows `inl i`, columns `inr (inl j)` and `c` isolated
vertices `inr (inr k)`. The row `i` and the column `j` are adjacent exactly when
`i < c * (t - j / c)`, and there are no other edges. Grouping rows and columns into blocks of `c`
consecutive indices, row block `a` is joined to column block `b` exactly when `a + b < t`, so the
column degrees are the `c`-fold blow-up of the staircase partition `(t, t - 1, …, 1)`.

These are the bipartite graphs `G_n(λ)` of D. N. Kozlov, *The first Cheeger constant of a
simplex*, arXiv:1610.07136v2, Definition 3.2 and §3.1, for `λ` the `c`-fold blow-up of the
staircase partition, on `n = c * (2 * t + 1)` vertices. Kozlov reads them as `𝔽₂`-valued
1-cochains on the complete complex and shows that they attain the lower bound `n / 3` for the first
coboundary Cheeger constant when `n` is not a power of two (Theorem 4.2 and Corollary 4.3). Two of
the graph-theoretic inputs to that computation are proved here:

* `TauCeti.card_edgeFinset_staircaseGraph`: the staircase graph has `c ^ 2 * (t + 1).choose 2`
  edges, that is `c² t (t + 1) / 2` (Kozlov, Lemma 3.12);
* `TauCeti.isCutMinimal_staircaseGraph`: the staircase graph is cut-minimal, so no switching
  along a cut decreases its number of edges (Kozlov, Lemma 3.8 with Corollary 3.13).

## Implementation notes

Cut-minimality is proved by induction on `t`. The staircase graph with parameter `t + 1` is
obtained from the one with parameter `t` by adding a row block joined to every column, and a column
block joined only to that new row block. For every cut, the pairs involving the new vertices
contain at least twice as many non-edges as edges, which is an inequality between quadratic
polynomials in the numbers of vertices of each kind on either side of the cut. For `c = 1` the
same two-vertex induction appears in the Lean development `dicipler-pixel/coboundary-k3-lean`.
-/

public section

open Finset

namespace TauCeti

/-! ### Arithmetic of the induction step -/

/-- The increment of one induction step is nonnegative. Here `r`, `r'` count the new row block on
either side of the cut, `k`, `k'` the new column block, `K`, `K'` the old columns, and `M`, `M'`
the old rows together with the isolated vertices. -/
private theorem two_mul_cross_le {r r' k k' M M' K K' c : ℕ} (hr : r + r' = c)
    (hk : k + k' = c) (h : M + M' = K + K' + c) :
    2 * r * (K' + k') + 2 * r' * (K + k) ≤
      (M + K) * (r' + k') + (M' + K') * (r + k) + (r + k) * (r' + k') := by
  subst hr
  rcases le_total k r with hkr | hrk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkr
    obtain rfl : k' = r' + d := by omega
    nlinarith
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrk
    obtain rfl : r' = k' + d := by omega
    nlinarith

/-! ### Sums over the staircase -/

/-- The sum of `f i j` over the pairs `(i, j)` that index an edge of `staircaseGraph c t`. -/
private def stairSum (c t : ℕ) (f : ℕ → ℕ → ℕ) : ℕ :=
  ∑ i ∈ range (c * t), ∑ j ∈ range (c * t), if i < c * (t - j / c) then f i j else 0

/-- Passing from `t` to `t + 1` adds the row block `i < c`, which meets every column, and shifts
the old rows by `c`. -/
private theorem stairSum_succ (c t : ℕ) (f : ℕ → ℕ → ℕ) :
    stairSum c (t + 1) f = ∑ i ∈ range c, ∑ j ∈ range (c * (t + 1)), f i j +
      stairSum c t fun i j ↦ f (c + i) j := by
  have hct : c * (t + 1) = c + c * t := by ring
  unfold stairSum
  rw [hct, sum_range_add]
  congr 1
  · refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ite_eq_left ?_
    rw [mem_range] at hi hj
    have hjt : j / c < t + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      nlinarith
    calc i < c := hi
      _ ≤ c * (t + 1 - j / c) := Nat.le_mul_of_pos_right c (by omega)
  · refine sum_congr rfl fun i hi ↦ ?_
    rw [mem_range] at hi
    have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
    -- The new column block meets no shifted row.
    have hzero : (∑ j ∈ range c, if c + i < c * (t + 1 - (c * t + j) / c) then
        f (c + i) (c * t + j) else 0) = 0 := by
      refine sum_eq_zero fun j hj ↦ ite_eq_right ?_
      rw [mem_range] at hj
      rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hj]
      simp
    rw [add_comm c (c * t), sum_range_add, hzero, add_zero]
    refine sum_congr rfl fun j hj ↦ ?_
    rw [mem_range] at hj
    have hjt : j / c < t := by
      rw [Nat.div_lt_iff_lt_mul hc]
      linarith [mul_comm c t]
    have : c * (t + 1 - j / c) = c + c * (t - j / c) := by
      rw [show t + 1 - j / c = (t - j / c) + 1 by omega]
      ring
    simp only [this, Nat.add_lt_add_iff_left]

/-- The staircase graph has `c ^ 2 * (t + 1).choose 2` edges, counted as a staircase sum. -/
private theorem stairSum_one (c t : ℕ) : stairSum c t (fun _ _ ↦ 1) = c ^ 2 * (t + 1).choose 2 := by
  induction t with
  | zero => simp [stairSum]
  | succ t ih =>
    rw [stairSum_succ, ih, Nat.choose_succ_succ (t + 1), Nat.choose_one_right]
    simp only [sum_const, card_range, smul_eq_mul, mul_one]
    ring

/-- The cut inequality for staircase sums: twice the number of edges `(i, j)` whose row and column
indicators differ is at most the product of the two sides of the cut, where the isolated vertices
contribute `m` and `m'`. -/
private theorem two_mul_stairSum_le {c m m' : ℕ} (hm : m + m' = c) (y : ℕ → Bool) (t : ℕ)
    (x : ℕ → Bool) : 2 * stairSum c t (fun i j ↦ if x i = y j then 0 else 1) ≤
      (#{i ∈ range (c * t) | x i} + #{j ∈ range (c * t) | y j} + m) *
        (#{i ∈ range (c * t) | ¬x i} + #{j ∈ range (c * t) | ¬y j} + m') := by
  induction t generalizing x with
  | zero => simp [stairSum]
  | succ t ih =>
    have h := ih fun i ↦ x (c + i)
    have hct : c * (t + 1) = c + c * t := by ring
    have hct' : c * (t + 1) = c * t + c := by ring
    -- Split the counts at the new row block and the new column block.
    have hx (p : Bool → Prop) [DecidablePred p] : #{i ∈ range (c * (t + 1)) | p (x i)} =
        #{i ∈ range c | p (x i)} + #{i ∈ range (c * t) | p (x (c + i))} := by
      simp only [card_filter]
      rw [hct, sum_range_add]
    have hy (p : Bool → Prop) [DecidablePred p] : #{j ∈ range (c * (t + 1)) | p (y j)} =
        #{j ∈ range (c * t) | p (y j)} + #{j ∈ range c | p (y (c * t + j))} := by
      simp only [card_filter]
      rw [hct', sum_range_add]
    have hr := card_filter_add_card_filter_not (s := range c) fun i ↦ x i
    have hk := card_filter_add_card_filter_not (s := range c) fun j ↦ y (c * t + j)
    have hR := card_filter_add_card_filter_not (s := range (c * t)) fun i ↦ x (c + i)
    have hK := card_filter_add_card_filter_not (s := range (c * t)) fun j ↦ y j
    rw [card_range] at hr hk hR hK
    rw [stairSum_succ, sum_sum_ite_eq_zero_one, hx (· = true), hx (¬· = true), hy (· = true),
      hy (¬· = true)]
    have hstep := two_mul_cross_le hr hk
      (M := #{i ∈ range (c * t) | x (c + i)} + m) (M' := #{i ∈ range (c * t) | ¬x (c + i)} + m')
      (K := #{j ∈ range (c * t) | y j}) (K' := #{j ∈ range (c * t) | ¬y j}) (by omega)
    nlinarith [h, hstep]

/-! ### The staircase graph -/

/-- **Kozlov's staircase graph.** On rows `inl i`, columns `inr (inl j)` and isolated vertices
`inr (inr k)`, the row `i` is adjacent to the column `j` exactly when `i < c * (t - j / c)`, and
there are no other edges. -/
def staircaseGraph (c t : ℕ) : SimpleGraph (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c) :=
  SimpleGraph.fromRel fun u v ↦ match u, v with
    | .inl i, .inr (.inl j) => (i : ℕ) < c * (t - j / c)
    | _, _ => False

variable {c t : ℕ}

/-- Two vertices are adjacent exactly when one is a row `i` and the other a column `j` with
`i < c * (t - j / c)`. -/
theorem staircaseGraph_adj {u v : Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c} :
    (staircaseGraph c t).Adj u v ↔ ∃ i j : Fin (c * t), (i : ℕ) < c * (t - j / c) ∧
      (u = .inl i ∧ v = .inr (.inl j) ∨ u = .inr (.inl j) ∧ v = .inl i) := by
  rcases u with _ | _ | _ <;> rcases v with _ | _ | _ <;> simp [staircaseGraph]

/-- A row and a column are adjacent according to the staircase condition. -/
@[simp, grind =]
theorem staircaseGraph_adj_inl_inr_inl (i j : Fin (c * t)) :
    (staircaseGraph c t).Adj (.inl i) (.inr (.inl j)) ↔ (i : ℕ) < c * (t - j / c) := by
  simp [staircaseGraph]

/-- A column and a row are adjacent according to the staircase condition. -/
@[simp, grind =]
theorem staircaseGraph_adj_inr_inl_inl (i j : Fin (c * t)) :
    (staircaseGraph c t).Adj (.inr (.inl j)) (.inl i) ↔ (i : ℕ) < c * (t - j / c) := by
  simp [staircaseGraph]

/-- No two rows are adjacent. -/
@[simp, grind .]
theorem not_staircaseGraph_adj_inl_inl (i i' : Fin (c * t)) :
    ¬(staircaseGraph c t).Adj (.inl i) (.inl i') := by
  simp [staircaseGraph]

/-- No two columns are adjacent. -/
@[simp, grind .]
theorem not_staircaseGraph_adj_inr_inl_inr_inl (j j' : Fin (c * t)) :
    ¬(staircaseGraph c t).Adj (.inr (.inl j)) (.inr (.inl j')) := by
  simp [staircaseGraph]

/-- The vertices `inr (inr k)` are isolated. -/
@[simp, grind .]
theorem not_staircaseGraph_adj_inr_inr_left (k : Fin c)
    (v : Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c) : ¬(staircaseGraph c t).Adj (.inr (.inr k)) v := by
  rcases v with _ | _ | _ <;> simp [staircaseGraph]

/-- The vertices `inr (inr k)` are isolated. -/
@[simp, grind .]
theorem not_staircaseGraph_adj_inr_inr_right (k : Fin c)
    (v : Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c) : ¬(staircaseGraph c t).Adj v (.inr (.inr k)) :=
  fun h ↦ not_staircaseGraph_adj_inr_inr_left k v h.symm

/-- The staircase graph is bipartite with the rows on one side and the columns on the other. -/
theorem isBipartiteWith_staircaseGraph :
    (staircaseGraph c t).IsBipartiteWith (Set.range Sum.inl) (Set.range fun j ↦ .inr (.inl j)) where
  disjoint := Set.disjoint_left.mpr <| by rintro _ ⟨i, rfl⟩ ⟨j, hj⟩; cases hj
  mem_of_adj u v h := by
    obtain ⟨i, j, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := staircaseGraph_adj.mp h
    · exact .inl ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    · exact .inr ⟨⟨j, rfl⟩, ⟨i, rfl⟩⟩

/-- The staircase graph is bipartite. -/
theorem isBipartite_staircaseGraph : (staircaseGraph c t).IsBipartite :=
  isBipartiteWith_staircaseGraph.isBipartite

instance : DecidableRel (staircaseGraph c t).Adj
  | .inl i, .inr (.inl j) => decidable_of_iff' _ (staircaseGraph_adj_inl_inr_inl i j)
  | .inr (.inl j), .inl i => decidable_of_iff' _ (staircaseGraph_adj_inr_inl_inl i j)
  | .inl _, .inl _ => isFalse (not_staircaseGraph_adj_inl_inl _ _)
  | .inr (.inl _), .inr (.inl _) => isFalse (not_staircaseGraph_adj_inr_inl_inr_inl _ _)
  | .inr (.inr _), _ => isFalse (not_staircaseGraph_adj_inr_inr_left _ _)
  | .inl _, .inr (.inr _) => isFalse (not_staircaseGraph_adj_inr_inr_right _ _)
  | .inr (.inl _), .inr (.inr _) => isFalse (not_staircaseGraph_adj_inr_inr_right _ _)

/-! ### Cuts of the staircase graph as staircase sums -/

/-- Membership of the rows in `s`, indexed by `ℕ`. -/
private def rowInd (s : Finset (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) (i : ℕ) : Bool :=
  if h : i < c * t then decide (.inl ⟨i, h⟩ ∈ s) else false

/-- Membership of the columns in `s`, indexed by `ℕ`. -/
private def colInd (s : Finset (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) (j : ℕ) : Bool :=
  if h : j < c * t then decide (.inr (.inl ⟨j, h⟩) ∈ s) else false

private theorem rowInd_val (s : Finset (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) (i : Fin (c * t)) :
    rowInd s i = decide (.inl i ∈ s) := by
  simp [rowInd]

private theorem colInd_val (s : Finset (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) (j : Fin (c * t)) :
    colInd s j = decide (.inr (.inl j) ∈ s) := by
  simp [colInd]

private theorem stairSum_eq_sum_fin (f : ℕ → ℕ → ℕ) :
    stairSum c t f = ∑ i : Fin (c * t), ∑ j : Fin (c * t),
      if (i : ℕ) < c * (t - j / c) then f i j else 0 := by
  rw [stairSum, ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun i _ ↦ (Fin.sum_univ_eq_sum_range (fun j ↦ _) _).symm

/-- The edges of the staircase graph from `s` to its complement are the edges whose row and column
lie on different sides. -/
private theorem sum_card_adj_eq_stairSum (s : Finset (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) :
    ∑ v ∈ s, #{w ∈ sᶜ | (staircaseGraph c t).Adj v w} =
      stairSum c t fun i j ↦ if rowInd s i = colInd s j then 0 else 1 := by
  rw [stairSum_eq_sum_fin, ← sum_ite_mem_eq]
  simp only [card_filter, ← sum_ite_mem_eq sᶜ, mem_compl]
  simp only [Fintype.sum_sum_type, staircaseGraph_adj_inl_inr_inl,
    staircaseGraph_adj_inr_inl_inl, rowInd_val, colInd_val, not_staircaseGraph_adj_inl_inl,
    not_staircaseGraph_adj_inr_inl_inr_inl, not_staircaseGraph_adj_inr_inr_left,
    not_staircaseGraph_adj_inr_inr_right, ite_false, ite_self, sum_const_zero, add_zero,
    zero_add, ite_sum_zero]
  -- Gather the row-to-column and column-to-row edges into one sum over rows and columns.
  rw [sum_comm (s := univ) (t := univ) (f := fun j i ↦ if Sum.inr (Sum.inl j) ∈ s then _ else 0),
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases hi : Sum.inl i ∈ s <;> by_cases hj : Sum.inr (Sum.inl j) ∈ s <;> simp [hi, hj]

private theorem card_eq_card_filter (s : Finset (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) :
    #s = #{i ∈ range (c * t) | rowInd s i} + #{j ∈ range (c * t) | colInd s j} +
      #{k | .inr (.inr k) ∈ s} := by
  simp only [card_filter]
  rw [card_eq_sum_ones, ← sum_ite_mem_eq, Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp [rowInd_val, colInd_val, add_assoc]

private theorem card_compl_eq_card_filter (s : Finset (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c)) :
    #sᶜ = #{i ∈ range (c * t) | ¬rowInd s i} + #{j ∈ range (c * t) | ¬colInd s j} +
      #{k | .inr (.inr k) ∉ s} := by
  simp only [card_filter]
  rw [card_eq_sum_ones, ← sum_ite_mem_eq, Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp [rowInd_val, colInd_val, add_assoc]

/-! ### Main results -/

/-- The staircase graph has `c ^ 2 * (t + 1).choose 2 = c² t (t + 1) / 2` edges. -/
theorem card_edgeFinset_staircaseGraph :
    #(staircaseGraph c t).edgeFinset = c ^ 2 * (t + 1).choose 2 := by
  set rows : Finset (Fin (c * t) ⊕ Fin (c * t) ⊕ Fin c) := {v | v.isLeft}
  -- Every edge joins a row to a column, so it crosses the cut of the rows.
  have hcut : (staircaseGraph c t).between ↑rows (↑rows)ᶜ = staircaseGraph c t := by
    ext v w
    simp only [SimpleGraph.between_adj, and_iff_left_iff_imp]
    intro h
    rcases v with _ | _ | _ <;> rcases w with _ | _ | _ <;> simp_all [rows]
  rw [← stairSum_one, ← congrArg card (SimpleGraph.edgeFinset_inj.mpr hcut),
    SimpleGraph.card_edgeFinset_between_compl, sum_card_adj_eq_stairSum]
  refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hi hj
  simp [rowInd, colInd, hi, hj, rows]

/-- **Staircase graphs are cut-minimal**: every cut contains at most as many edges of
`staircaseGraph c t` as non-edges. -/
@[simp, grind .]
theorem isCutMinimal_staircaseGraph : (staircaseGraph c t).IsCutMinimal := by
  rw [SimpleGraph.isCutMinimal_iff_two_mul_sum_card_le]
  intro s
  rw [sum_card_adj_eq_stairSum, card_eq_card_filter, card_compl_eq_card_filter]
  refine two_mul_stairSum_le ?_ (colInd s) t (rowInd s)
  rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]

end TauCeti
