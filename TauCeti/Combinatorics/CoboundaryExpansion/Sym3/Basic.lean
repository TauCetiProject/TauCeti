/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Group
public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Basic
public import TauCeti.GroupTheory.Perm.MovedNorm
import Mathlib.Algebra.BigOperators.Group.List.Basic
import TauCeti.Combinatorics.Optimization.Replication
import TauCeti.Data.Fin.Basic
import Mathlib.Tactic.GCongr

/-!
# Moved-point counts of `Sym(3)`-valued cochains on `K_k`

This file supplies kernel-computable natural-number forms of the triangle defect and the gauge
cost of a `Sym(3)`-valued 1-cochain on the complete complex on `Fin k`, given by a bare function
`α : Fin k → Fin k → Sym(3)` read on positively oriented pairs `u < v`:

* `Sym3.moved σ` is the number of points of `Fin 3` moved by `σ`, equal to
  `Equiv.Perm.movedNorm (Fin 3) σ` (`Sym3.moved_eq_movedNorm`);
* `Sym3.defect α` and `Sym3.cost α β` are the moved-point counts of the triangle holonomies and of
  the gauged edge terms, summed over the triangles `u < v < w` and the edges `u < v`.

`Sym3.defect_ofLt` and `Sym3.cost_ofLt` identify them with `Cochain.defect` and `Cochain.cost` of
the cochain `Cochain.ofLt (complete (Fin k)) α` under `movedNorm (Fin 3)`, so that bounds proved by
finite computation or by counting transfer to the gauge distance and the Cheeger constant of
`TauCeti.Cochain`.

`Sym3.cost_ge_of_forall_cons_one` reduces a lower bound for every gauge to the gauges pinned to `1`
at vertex `0`, which is what `decide +kernel` checks for the `k = 4` seed. `Sym3.cost_rep_ge` and
`Sym3.defect_rep` are the two counts of balanced replication that the upper bound
`h1 (complete V) (movedNorm (Fin 3)) ≤ card V / 3` needs.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.22090958, Lemma 6 and Corollary 7.
-/

-- `moved`, `edges`, `triangles`, `val`, `defect` and `cost` are evaluated by `decide +kernel`
-- for the `k = 4` seed, so their bodies are exposed.
@[expose] public section

open Finset Equiv

namespace TauCeti.Sym3

/-- Permutations of three points. -/
abbrev S3 := Perm (Fin 3)

/-- The Hamming count: how many of the three points `σ` moves. -/
def moved (σ : S3) : ℕ := (List.finRange 3).countP fun i => σ i ≠ i

/-- `moved σ` is the number of points of `Fin 3` moved by `σ`, i.e. the size of its support. -/
theorem moved_eq_card_support : ∀ σ : S3, moved σ = σ.support.card := by decide

/-- The Hamming count is the moved-point norm `Equiv.Perm.movedNorm (Fin 3)`. -/
theorem moved_eq_movedNorm (σ : S3) : (moved σ : ℝ) = Perm.movedNorm (Fin 3) σ := by
  rw [Perm.movedNorm_apply, moved_eq_card_support]

/-- The transposition of `0` and `1`. -/
def t01 : S3 := swap 0 1

/-- The transposition of `1` and `2`. -/
def t12 : S3 := swap 1 2

/-- The transposition of `0` and `2`. -/
def t02 : S3 := swap 0 2

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def c1 : S3 := swap 0 1 * swap 1 2

/-- The 3-cycle `0 ↦ 2 ↦ 1 ↦ 0`. -/
def c2 : S3 := swap 1 2 * swap 0 1

/-- The six elements of `Sym(3)`. -/
def S3list : List S3 := [1, t01, t12, t02, c1, c2]

/-- `S3list` lists every permutation of `Fin 3`. -/
theorem mem_S3list : ∀ σ : S3, σ ∈ S3list := by decide

variable {k : ℕ}

/-- Oriented edges `u < v` of `K_k`. -/
def edges (k : ℕ) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap fun u => ((List.finRange k).filter fun v => u < v).map fun v => (u, v)

/-- Triangles `u < v < w` of `K_k`. -/
def triangles (k : ℕ) : List (Fin k × Fin k × Fin k) :=
  (List.finRange k).flatMap fun u => (List.finRange k).flatMap fun v =>
    ((List.finRange k).filter fun w => u < v ∧ v < w).map fun w => (u, v, w)

/-- The value on an oriented pair, read on `u < v` and inverted on `u > v`. -/
def val (α : Fin k → Fin k → S3) (u v : Fin k) : S3 := if u < v then α u v else (α v u)⁻¹

/-- The triangle defect: moved points of the holonomy, summed over triangles `u < v < w`. -/
def defect (α : Fin k → Fin k → S3) : ℕ :=
  ((triangles k).map fun t => moved (val α t.1 t.2.1 * val α t.2.1 t.2.2 * val α t.2.2 t.1)).sum

/-- The cost of a gauge `β`: moved points of `β(u)⁻¹ α(u,v) β(v)`, summed over edges `u < v`. -/
def cost (α : Fin k → Fin k → S3) (β : Fin k → S3) : ℕ :=
  ((edges k).map fun e => moved ((β e.1)⁻¹ * α e.1 e.2 * β e.2)).sum

/-! ### Cost and defect as sums over vertices -/

private theorem sum_edges (g : Fin k → Fin k → ℕ) :
    ((edges k).map fun e => g e.1 e.2).sum =
      ∑ u : Fin k, ∑ v : Fin k, if u < v then g u v else 0 := by
  unfold edges
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  simp [Fin.sum_univ_def, List.sum_map_ite, Function.comp_def]

private theorem sum_triangles (g : Fin k → Fin k → Fin k → ℕ) :
    ((triangles k).map fun t => g t.1 t.2.1 t.2.2).sum =
      ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k, if u < v ∧ v < w then g u v w else 0 := by
  unfold triangles
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  rw [Function.comp_apply, List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map,
    Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun v _ => ?_)
  simp [Fin.sum_univ_def, List.sum_map_ite, Function.comp_def]

/-- The cost of a gauge as a double sum over ordered vertex pairs `u < v`. -/
theorem cost_eq_sum (α : Fin k → Fin k → S3) (β : Fin k → S3) :
    cost α β = ∑ u : Fin k, ∑ v : Fin k,
      if u < v then moved ((β u)⁻¹ * α u v * β v) else 0 :=
  sum_edges fun u v => moved ((β u)⁻¹ * α u v * β v)

/-- The triangle defect as a triple sum over vertex triples `u < v < w`. -/
theorem defect_eq_sum (α : Fin k → Fin k → S3) :
    defect α = ∑ u : Fin k, ∑ v : Fin k, ∑ w : Fin k,
      if u < v ∧ v < w then moved (val α u v * val α v w * val α w u) else 0 :=
  sum_triangles fun u v w => moved (val α u v * val α v w * val α w u)

/-! ### The counts are those of `Cochain.ofLt` -/

/-- `Sym3.cost` is `Cochain.cost` of `Cochain.ofLt` under the moved-point norm. -/
theorem cost_ofLt (α : Fin k → Fin k → S3) (β : Fin k → S3) :
    (Cochain.ofLt (TwoComplex.complete (Fin k)) α).cost (Perm.movedNorm (Fin 3)) β =
      cost α β := by
  rw [Cochain.cost_complete, Finset.sum_filter, Fintype.sum_prod_type, cost_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs with h
  · rw [Cochain.ofLt_apply_of_lt _ ((TwoComplex.adj_complete u v).mpr h.ne) h, moved_eq_movedNorm]
  · rfl

/-- `Sym3.defect` is `Cochain.defect` of `Cochain.ofLt` under the moved-point norm. -/
theorem defect_ofLt (α : Fin k → Fin k → S3) :
    (Cochain.ofLt (TwoComplex.complete (Fin k)) α).defect (Perm.movedNorm (Fin 3)) = defect α := by
  rw [Cochain.defect_complete, Finset.sum_filter, Fintype.sum_prod_type, defect_eq_sum]
  simp only [Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun w _ => ?_
  split_ifs with h
  · have huw : u < w := h.1.trans h.2
    rw [Cochain.holonomy_def, Cochain.ofLt_apply_of_lt _ ((TwoComplex.adj_complete u v).mpr h.1.ne)
      h.1, Cochain.ofLt_apply_of_lt _ ((TwoComplex.adj_complete v w).mpr h.2.ne) h.2,
      Cochain.ofLt_apply_of_gt _ ((TwoComplex.adj_complete w u).mpr huw.ne') huw,
      ← moved_eq_movedNorm]
    simp [val, h.1, h.2, not_lt.mpr huw.le]
  · rfl

/-! ### Pinned gauges -/

private theorem moved_conj (c x : S3) : moved (c⁻¹ * x * c) = moved x := by
  have h := Perm.movedNorm_conj c⁻¹ x
  rw [inv_inv, ← moved_eq_movedNorm, ← moved_eq_movedNorm] at h
  exact_mod_cast h

private theorem cost_mul_const (α : Fin k → Fin k → S3) (β : Fin k → S3) (c : S3) :
    cost α (fun v => β v * c) = cost α β := by
  unfold cost
  congr 1
  refine List.map_congr_left fun e _ => ?_
  have : (β e.1 * c)⁻¹ * α e.1 e.2 * (β e.2 * c) = c⁻¹ * ((β e.1)⁻¹ * α e.1 e.2 * β e.2) * c := by
    group
  rw [this, moved_conj]

/-- Every function `Fin n → Sym(3)`, as a list. -/
def funs : (n : ℕ) → List (Fin n → S3)
  | 0 => [Fin.elim0]
  | n + 1 => S3list.flatMap fun a => (funs n).map (Fin.cons a)

private theorem mem_funs : ∀ (n : ℕ) (f : Fin n → S3), f ∈ funs n
  | 0, f => by rw [funs, List.mem_singleton]; funext i; exact i.elim0
  | n + 1, f => by
    simp only [funs, List.mem_flatMap, List.mem_map]
    exact ⟨f 0, mem_S3list _, Fin.tail f, mem_funs n _, Fin.cons_self_tail f⟩

/-- If every gauge pinned to `1` at vertex `0` costs at least `D`, every gauge does: right
multiplication by a constant conjugates every edge term. -/
theorem cost_ge_of_forall_cons_one {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (D : ℕ)
    (h : (funs m).all (fun t => decide (D ≤ cost α (Fin.cons 1 t))) = true) (β : Fin (m + 1) → S3) :
    D ≤ cost α β := by
  rw [← cost_mul_const α β (β 0)⁻¹]
  set β' : Fin (m + 1) → S3 := fun v => β v * (β 0)⁻¹ with hβ'
  have hcons : β' = Fin.cons 1 (Fin.tail β') := by
    rw [← show β' 0 = 1 by simp [hβ']]; exact (Fin.cons_self_tail β').symm
  rw [hcons]
  simpa using List.all_eq_true.mp h (Fin.tail β') (mem_funs m _)

/-! ### Balanced replication

Replace each vertex of `K_k` by a block of `q` consecutive vertices of `K_{kq}`
(`finProdFinEquiv`), put `1` on the pairs inside a block and the seed value between blocks. These
are only the two counts the upper bound needs; the general cochain statements are the roadmap's
`Cochain.defect_replicate` and `Cochain.gaugeDist_replicate`. -/

section Replication

variable {q : ℕ}

/-- The block of a vertex of `K_{kq}`. -/
def blk (q : ℕ) (x : Fin (k * q)) : Fin k := (finProdFinEquiv.symm x).1

/-- Vertex `a` of block `i`. -/
def vert (q : ℕ) (i : Fin k) (a : Fin q) : Fin (k * q) := finProdFinEquiv (i, a)

@[simp] theorem blk_vert (i : Fin k) (a : Fin q) : blk q (vert q i a) = i := by simp [blk, vert]

private theorem sum_blocks (F : Fin (k * q) → ℕ) : ∑ x, F x = ∑ i, ∑ a, F (vert q i a) := by
  rw [← Equiv.sum_comp finProdFinEquiv F, Fintype.sum_prod_type]
  rfl

/-- Vertices are ordered block first, then position. -/
theorem vert_lt_iff (i j : Fin k) (a b : Fin q) :
    vert q i a < vert q j b ↔ i < j ∨ (i = j ∧ a < b) :=
  finProdFinEquiv_lt_finProdFinEquiv_iff (i, a) (j, b)

/-- The `q`-fold balanced replication of `α`. -/
def rep (q : ℕ) (α : Fin k → Fin k → S3) : Fin (k * q) → Fin (k * q) → S3 :=
  fun x y => if blk q x = blk q y then 1 else val α (blk q x) (blk q y)

private theorem moved_one : moved (1 : S3) = 0 := by decide

private theorem rep_tri (α : Fin k → Fin k → S3) (i j l : Fin k) (a b c : Fin q) :
    (if vert q i a < vert q j b ∧ vert q j b < vert q l c then
        moved (val (rep q α) (vert q i a) (vert q j b) * val (rep q α) (vert q j b) (vert q l c) *
          val (rep q α) (vert q l c) (vert q i a)) else 0) =
      if i < j ∧ j < l then moved (val α i j * val α j l * val α l i) else 0 := by
  by_cases hijl : i < j ∧ j < l
  · have h1 : vert q i a < vert q j b := (vert_lt_iff _ _ _ _).2 (Or.inl hijl.1)
    have h2 : vert q j b < vert q l c := (vert_lt_iff _ _ _ _).2 (Or.inl hijl.2)
    have hil : i < l := lt_trans hijl.1 hijl.2
    have h3 : ¬ vert q l c < vert q i a := not_lt.2 (lt_trans h1 h2).le
    simp only [h1, h2, hijl, and_self, ↓reduceIte]
    simp [val, rep, h1, h2, h3, hijl.1, hijl.2, hil, hijl.1.ne, hijl.2.ne, hil.ne, not_lt.2 hil.le]
  · simp only [hijl, ↓reduceIte]
    split_ifs with hord
    · have h3 : ¬ vert q l c < vert q i a := not_lt.2 (lt_trans hord.1 hord.2).le
      rcases (vert_lt_iff _ _ _ _).1 hord.1 with hij | ⟨rfl, _⟩
      · rcases (vert_lt_iff _ _ _ _).1 hord.2 with hjl | ⟨rfl, _⟩
        · exact absurd ⟨hij, hjl⟩ hijl
        · simp [val, rep, hord.1, hord.2, h3, hij.ne, moved_one]
      · simp [val, rep, hord.1, hord.2, h3, moved_one]
    · rfl

/-- Replication multiplies the defect by `q ^ 3`. -/
theorem defect_rep (q : ℕ) (α : Fin k → Fin k → S3) : defect (rep q α) = q ^ 3 * defect α := by
  rw [defect_eq_sum, defect_eq_sum]
  simp only [sum_blocks (q := q), rep_tri, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum]
  ring

private theorem rep_edge_le (α : Fin k → Fin k → S3) (γ : Fin (k * q) → S3) (i j : Fin k)
    (a b : Fin q) :
    (if i < j then moved ((γ (vert q i a))⁻¹ * α i j * γ (vert q j b)) else 0) ≤
      if vert q i a < vert q j b then
        moved ((γ (vert q i a))⁻¹ * rep q α (vert q i a) (vert q j b) * γ (vert q j b)) else 0 := by
  by_cases hij : i < j
  · simp only [(vert_lt_iff _ _ _ _).2 (Or.inl hij), hij, ↓reduceIte]
    simp [rep, val, hij, hij.ne]
  · simp only [hij, ↓reduceIte]
    exact Nat.zero_le _

/-- Every gauge of the replication costs at least `q ^ 2` times a lower bound `D` for the seed:
each section (one vertex per block) restricts the gauge to a gauge of the seed
(`Finset.card_sq_nsmul_le_sum_of_forall_le_sum`), and pairs inside a block cost at least `0`. -/
theorem cost_rep_ge (α : Fin k → Fin k → S3) (D : ℕ) (hD : ∀ β : Fin k → S3, D ≤ cost α β)
    (γ : Fin (k * q) → S3) : q ^ 2 * D ≤ cost (rep q α) γ := by
  set E := univ.filter fun e : Fin k × Fin k => e.1 < e.2
  set w : Fin k × Fin k → Fin q → Fin q → ℕ := fun e a b =>
    moved ((γ (vert q e.1 a))⁻¹ * α e.1 e.2 * γ (vert q e.2 b))
  have hsum (F : Fin k → Fin k → ℕ) :
      ∑ e ∈ E, F e.1 e.2 = ∑ i, ∑ j, if i < j then F i j else 0 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  have h := Finset.card_sq_nsmul_le_sum_of_forall_le_sum E
    (fun e he => (Finset.mem_filter.mp he).2.ne) w (d := D) fun s => by
      rw [hsum fun i j => w (i, j) (s i) (s j)]
      simpa only [w, cost_eq_sum] using hD fun i => γ (vert q i (s i))
  rw [Fintype.card_fin, smul_eq_mul] at h
  refine h.trans ?_
  rw [cost_eq_sum]
  simp only [sum_blocks (q := q)]
  calc ∑ e ∈ E, ∑ a, ∑ b, w e a b = ∑ i, ∑ j, ∑ a, ∑ b, if i < j then w (i, j) a b else 0 := by
        rw [hsum (fun i j => ∑ a, ∑ b, w (i, j) a b)]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
    _ = ∑ i, ∑ a, ∑ j, ∑ b, if i < j then w (i, j) a b else 0 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ _ := by
        gcongr with i _ a _ j _ b _
        exact rep_edge_le α γ i j a b

end Replication

end TauCeti.Sym3
