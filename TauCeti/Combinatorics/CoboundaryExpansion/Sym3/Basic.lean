/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum
public import TauCeti.GroupTheory.Perm.MovedNorm
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# `Sym(3)`-valued cochains on `K_k`: counts, exhaustion, and the witness for `k = 4`

The permutation coboundary constant of the complete complex is k/3 for every k ≥ 4 (Jeromie
Beasley, DOI 10.5281/zenodo.22090958, version DOI 10.5281/zenodo.23245792). This file supplies
the `k = 4` seed.

The `Sym3` files follow the Lean development of the paper in
https://github.com/dicipler-pixel/coboundary-k3-lean at commit
`34fac54a6d60eae744e7bc6a849d79c0c09409ad`.

Conventions follow the paper (Section 1). Permutations of `{0,1,2}` act on points;
the Hamming count `moved σ` is the number of points `σ` moves, a kernel-computable form of
`Equiv.Perm.movedNorm (Fin 3)` (`moved_eq_movedNorm`). A 1-cochain on the complete
complex `K_k` assigns `α u v` to each edge `u < v`, with `α(v,u) = α(u,v)⁻¹`. Its triangle
defect is `N = Σ_{u<v<w} moved(α(u,v) α(v,w) α(w,u))` and the cost of a gauge
`β : Fin k → Sym(3)` is `Σ_{u<v} moved(β(u)⁻¹ α(u,v) β(v))`; `D` is the minimum cost over every
gauge. Both are counts of moved points, so `N/D` is the paper's counting ratio.

This file proves, for the Appendix A witness at `k = 4`, the defect `N`, that no gauge costs
less than `D`, and that `D` is attained, so that `N/D = 4/3`: the upper half of Theorem 4 at the
seed. The lower half, the paper's Proposition 1 (Chapman–Lubotzky's Proposition 3.2), is proved
in `Sym3.Constant`.

The gauge minimum is checked by exhausting every gauge with `β(0) = 1`; `gauge_lower` proves that
this loses nothing, because right multiplication by a constant conjugates every edge term.
-/

-- The definitions of this file are evaluated by `decide +kernel` in `witness_k4`, so their
-- bodies are exposed.
@[expose] public section

namespace TauCeti.CoboundaryExpansion.Sym3

open Equiv

/-- Permutations of three points. -/
abbrev S3 := Perm (Fin 3)

/-- The Hamming count: how many of the three points `σ` moves. -/
def moved (σ : S3) : ℕ := (List.finRange 3).countP fun i => σ i ≠ i

/-- The transposition `(1 0 2)` in the paper's one-line notation. -/
def t01 : S3 := swap 0 1

/-- The transposition `(0 2 1)` in the paper's one-line notation. -/
def t12 : S3 := swap 1 2

/-- The transposition `(2 1 0)` in the paper's one-line notation. -/
def t02 : S3 := swap 0 2

-- One-line notation lists the images of `0, 1, 2`: `c1 = (1 2 0)` sends `0 ↦ 1 ↦ 2 ↦ 0`,
-- and `c2 = (2 0 1)` is its inverse, `0 ↦ 2 ↦ 1 ↦ 0`.

/-- The 3-cycle `(1 2 0)` in the paper's one-line notation. -/
def c1 : S3 := swap 0 1 * swap 1 2

/-- The 3-cycle `(2 0 1)` in the paper's one-line notation. -/
def c2 : S3 := swap 1 2 * swap 0 1

/-- The six elements of `Sym(3)`. -/
def S3list : List S3 := [1, t01, t12, t02, c1, c2]

theorem mem_S3list : ∀ σ : S3, σ ∈ S3list := by decide

/-- On `Sym(3)` the Hamming count is the size of the support. -/
theorem moved_eq_card_support : ∀ σ : S3, moved σ = σ.support.card := by decide

/-- The Hamming count is the moved-point norm `Equiv.Perm.movedNorm (Fin 3)`. -/
theorem moved_eq_movedNorm (σ : S3) : (moved σ : ℝ) = Perm.movedNorm (Fin 3) σ := by
  rw [Perm.movedNorm_apply, moved_eq_card_support]

/-- The Hamming count is conjugation invariant (`Equiv.Perm.movedNorm_conj`). -/
theorem moved_conj (c x : S3) : moved (c⁻¹ * x * c) = moved x := by
  have h := Perm.movedNorm_conj c⁻¹ x
  rw [inv_inv, ← moved_eq_movedNorm, ← moved_eq_movedNorm] at h
  exact_mod_cast h

/-! ## Cochains on the complete complex -/

variable {k : ℕ}

/-- Oriented edges `u < v`. -/
def edges (k : ℕ) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap fun u => ((List.finRange k).filter fun v => u < v).map fun v => (u, v)

/-- Triangles `u < v < w`. -/
def triangles (k : ℕ) : List (Fin k × Fin k × Fin k) :=
  (List.finRange k).flatMap fun u => (List.finRange k).flatMap fun v =>
    ((List.finRange k).filter fun w => u < v ∧ v < w).map fun w => (u, v, w)

/-- The value on an oriented edge, with `α(v,u) = α(u,v)⁻¹`. -/
def val (α : Fin k → Fin k → S3) (u v : Fin k) : S3 := if u < v then α u v else (α v u)⁻¹

/-- The triangle defect `N`: moved points of the holonomy, summed over triangles. -/
def defect (α : Fin k → Fin k → S3) : ℕ :=
  ((triangles k).map fun t => moved (val α t.1 t.2.1 * val α t.2.1 t.2.2 * val α t.2.2 t.1)).sum

/-- The cost of a gauge `β`: moved points of `β(u)⁻¹ α(u,v) β(v)`, summed over edges. -/
def cost (α : Fin k → Fin k → S3) (β : Fin k → S3) : ℕ :=
  ((edges k).map fun e => moved ((β e.1)⁻¹ * α e.1 e.2 * β e.2)).sum

/-- A constant right factor does not change the cost. -/
theorem cost_mul_const (α : Fin k → Fin k → S3) (β : Fin k → S3) (c : S3) :
    cost α (fun v => β v * c) = cost α β := by
  unfold cost
  congr 1
  apply List.map_congr_left
  intro e _
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

/-- **Exhaustion loses nothing.** If every gauge with `β(0) = 1` costs at least `D`, every
gauge does. -/
theorem gauge_lower {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (D : ℕ)
    (h : (funs m).all (fun t => decide (D ≤ cost α (Fin.cons 1 t))) = true) :
    ∀ β, D ≤ cost α β := by
  intro β
  rw [← cost_mul_const α β (β 0)⁻¹]
  set β' : Fin (m + 1) → S3 := fun v => β v * (β 0)⁻¹ with hβ'
  have h0 : β' 0 = 1 := by simp [hβ']
  have hcons : β' = Fin.cons 1 (Fin.tail β') := by
    rw [← h0]; exact (Fin.cons_self_tail β').symm
  rw [hcons]
  have := List.all_eq_true.mp h (Fin.tail β') (mem_funs m _)
  simpa using this

/-! ### Branch-and-bound exhaustion

Assign the gauge one vertex at a time. The cost of the edges whose endpoints are both assigned
can only grow as more vertices are assigned, so once it reaches `D` every completion costs at
least `D` and the branch is closed. `search_sound` proves this pruning loses nothing. -/

section Search

variable {k : ℕ} (α : Fin k → Fin k → S3)

/-- The term of edge `e` under a partial gauge `l` (vertex `v` gets `l[v]`). -/
def term (l : List S3) (e : Fin k × Fin k) : ℕ :=
  moved ((l.getD e.1 1)⁻¹ * α e.1 e.2 * l.getD e.2 1)

/-- The cost of the edges both of whose endpoints are assigned. -/
def pcost (l : List S3) : ℕ :=
  ((edges k).map fun e => if e.2.val < l.length then term α l e else 0).sum

private theorem mem_edges {e : Fin k × Fin k} (h : e ∈ edges k) : e.1 < e.2 := by
  simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨u, _, v, ⟨_, huv⟩, rfl⟩ := h
  exact huv

private theorem pcost_mono (l ext : List S3) : pcost α l ≤ pcost α (l ++ ext) := by
  apply List.sum_le_sum
  intro e he
  have h12 := mem_edges he
  split_ifs with h1 h2 h2
  · have h1' : e.1.val < l.length := lt_trans h12 h1
    simp only [term, List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h1']
    exact le_refl _
  · exact absurd (by simp; omega) h2
  · exact Nat.zero_le _
  · exact le_refl _

/-- The branch-and-bound search: `true` means every completion of `l` by `fuel` more vertices
costs at least `D`. -/
def search (D : ℕ) : ℕ → List S3 → Bool
  | 0, l => decide (D ≤ pcost α l)
  | f + 1, l => decide (D ≤ pcost α l) || S3list.all fun a => search D f (l ++ [a])

private theorem search_sound (D : ℕ) : ∀ (fuel : ℕ) (l : List S3), search α D fuel l = true →
    ∀ ext : List S3, ext.length = fuel → D ≤ pcost α (l ++ ext)
  | 0, l, h, ext, hl => by
    rw [List.length_eq_zero_iff.mp hl, List.append_nil]
    simpa [search] using h
  | f + 1, l, h, ext, hl => by
    simp only [search, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    rcases h with h | h
    · exact h.trans (pcost_mono α l ext)
    · obtain ⟨a, ext', rfl⟩ : ∃ a ext', ext = a :: ext' := by
        cases ext with
        | nil => simp at hl
        | cons a t => exact ⟨a, t, rfl⟩
      have := search_sound D f (l ++ [a]) (h a (mem_S3list a)) ext' (by simpa using hl)
      simpa using this

private theorem search_step (D f : ℕ) (l : List S3)
    (h : ∀ a ∈ S3list, search α D f (l ++ [a]) = true) : search α D (f + 1) l = true := by
  simp only [search, Bool.or_eq_true, List.all_eq_true]
  exact Or.inr h

theorem search_split (D f : ℕ) (l : List S3)
    (h1 : search α D f (l ++ [1]) = true) (h2 : search α D f (l ++ [t01]) = true)
    (h3 : search α D f (l ++ [t12]) = true) (h4 : search α D f (l ++ [t02]) = true)
    (h5 : search α D f (l ++ [c1]) = true) (h6 : search α D f (l ++ [c2]) = true) :
    search α D (f + 1) l = true := by
  apply search_step
  intro a ha
  simp only [S3list, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem pcost_ofFn {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (β : Fin (m + 1) → S3) :
    pcost α (List.ofFn β) = cost α β := by
  have hg : ∀ i : Fin (m + 1), (List.ofFn β).getD i 1 = β i := fun i => by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  unfold pcost cost
  congr 1
  apply List.map_congr_left
  intro e _
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [List.length_ofFn]; exact e.2.isLt))]
  simp only [term, hg]

/-- **Exhaustion loses nothing**, branch-and-bound form. -/
theorem gauge_lower_bb {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (D : ℕ)
    (h : search α D m [1] = true) : ∀ β, D ≤ cost α β := by
  intro β
  rw [← cost_mul_const α β (β 0)⁻¹]
  set β' : Fin (m + 1) → S3 := fun v => β v * (β 0)⁻¹ with hβ'
  have h0 : β' 0 = 1 := by simp [hβ']
  have := search_sound α D m [1] h (List.ofFn fun i : Fin m => β' i.succ) (by simp)
  rw [← pcost_ofFn]
  have e : List.ofFn β' = [1] ++ List.ofFn fun i : Fin m => β' i.succ := by
    rw [List.ofFn_succ, h0]; rfl
  rw [e]
  exact this

end Search

/-- A cochain from its list of non-identity edges. -/
def cochain (k : ℕ) (W : List ((ℕ × ℕ) × S3)) : Fin k → Fin k → S3 :=
  fun u v => ((W.lookup (u.val, v.val)).getD 1)

/-! ## The Appendix A witness at `k = 4` (gauged form) -/

/-- The Appendix A witness at `k = 4` (gauged form), the seed: `t12`, `t01`, `t02` on the edges
`{1,2}`, `{1,3}`, `{2,3}`. -/
def w4 : Fin 4 → Fin 4 → S3 := cochain 4 [((1, 2), t12), ((1, 3), t01), ((2, 3), t02)]

/-- **Theorem 4, k = 4.** `N = 8`, every gauge costs at least `6`, and `6` is attained:
`N/D = 4/3`. -/
theorem witness_k4 :
    defect w4 = 8 ∧ (∀ β, 6 ≤ cost w4 β) ∧ cost w4 (fun _ => 1) = 6 ∧ 8 * 3 = 4 * 6 :=
  ⟨by decide +kernel, gauge_lower w4 6 (by decide +kernel), by decide +kernel, by norm_num⟩

end TauCeti.CoboundaryExpansion.Sym3
