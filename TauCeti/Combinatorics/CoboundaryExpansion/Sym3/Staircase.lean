/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic
import TauCeti.Combinatorics.SimpleGraph.Staircase
import TauCeti.Combinatorics.SimpleGraph.OddTriple
import TauCeti.Order.Hom.PowersetCard
import TauCeti.GroupTheory.Perm.ParityRetract
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moved-point counts for Kozlov's staircase cochains

On `K_{2t+1}` with vertices numbered `0, 1, …, 2t`, the staircase cochain `Sym3.stair`, read on the
positively oriented pairs `p < q` (as `Sym3.val` and `Cochain.ofLt` do), puts the transposition
`t01` on the pairs with `p` odd and `q` even and `1` on the others. Writing
`vᵢ = 2i - 1` and `y_j = 2j`, its `t01`-edges join `vᵢ` to `y_j` exactly when `i ≤ j`: this is
Kozlov's staircase graph of the partition `(t, t - 1, …, 1)` with one isolated vertex `0`
(`SimpleGraph.staircase 1 t` up to relabelling).

The relabelling is an explicit graph isomorphism from `SimpleGraph.staircase 1 t`, along which
Kozlov's cut-minimality, edge count and odd-triangle count are transported:

* `Sym3.stair_cost_lower`: every `Sym(3)` gauge costs at least `t (t + 1)`. The parity retraction
  onto `{1, t01}` (`Equiv.Perm.movedNorm_parityRetract_le`) bounds the cost below by twice the
  `𝔽₂` cost of the sign pattern of the gauge, and cut-minimality of the staircase
  (`SimpleGraph.isCutMinimal_staircase`) bounds that below by the number `t (t + 1) / 2` of
  staircase edges (`SimpleGraph.two_mul_card_edgeFinset_staircase`).
* `Sym3.stair_defect_mul`: `3 N = (2 t + 1) · t (t + 1)` for the moved-point defect
  `N = defect (stair (2 t + 1))`. Each odd triangle (one with an odd number of staircase edges)
  contributes `2` to `N` and every other triangle `0`, so `N` is twice the odd-triangle count
  `1² + 2² + ⋯ + t²` (`SimpleGraph.three_mul_card_oddTriangleFinset_staircase`).

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Definition 3.2 and §3.1 (staircase graphs), Lemma 3.8 and Corollary 3.13 (cut-minimality),
  Lemma 3.10 (triangle count).
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.22090958, Corollary 7 and Theorem 8 (the `Sym(3)` transfer).
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: this file adapts the staircase cochain and its parity bound from
  `CoboundaryK3/Staircase.lean`, with the counting replaced by `SimpleGraph.staircase`.
-/

public section

namespace TauCeti.Sym3

open Finset

/-! ## Parity and the staircase -/

/-- The staircase edge predicate: `p` is odd and `q` is even. It does not compare `p` and `q`; it is
only read on pairs `p < q`. -/
def stEdge (p q : ℕ) : Bool := decide (p % 2 = 1) && decide (q % 2 = 0)

/-- **Kozlov's staircase cochain** on `K_k`, as a function read on positively oriented pairs
`p < q` (`Sym3.val`, `Cochain.ofLt`): `t01` when `p` is odd and `q` is even, the identity
otherwise. For `k = 2t + 1` this is the staircase of the partition `(t, …, 1)` with one loose
vertex `0`. -/
def stair (k : ℕ) : Fin k → Fin k → S3 := fun p q => if stEdge p.val q.val then t01 else 1

/-- The sign of a permutation of three points, as a Boolean (`true` for a transposition). -/
private def oddPerm (σ : S3) : Bool := decide (σ = t01) || decide (σ = t12) || decide (σ = t02)

/-- `oddPerm` is the sign: `true` exactly for the odd permutations. -/
private theorem oddPerm_eq_decide : ∀ σ : S3, oddPerm σ = decide (Equiv.Perm.sign σ = -1) := by
  decide

/-- The sign of a permutation as a Boolean is additive (`xor`) along products. -/
private theorem oddPerm_mul (σ τ : S3) : oddPerm (σ * τ) = xor (oddPerm σ) (oddPerm τ) := by
  rw [oddPerm_eq_decide, oddPerm_eq_decide, oddPerm_eq_decide, Equiv.Perm.sign_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hτ | hτ <;> simp [hσ, hτ, Units.ext_iff]

/-- `t01` is a transposition. -/
private theorem t01_isSwap : t01.IsSwap := Equiv.Perm.swap_isSwap_iff.mpr (by decide)

/-- The parity retraction onto `{1, t01}` moves `2` points on odd permutations and none on even
ones. -/
private theorem movedNorm_parityRetract_t01 (σ : S3) :
    Equiv.Perm.movedNorm (Fin 3) (Equiv.Perm.parityRetract t01_isSwap σ) =
      2 * (Bool.toNat (oddPerm σ) : ℝ) := by
  have ht := t01_isSwap
  rw [oddPerm_eq_decide]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rw [Equiv.Perm.parityRetract_of_sign_eq_one ht hσ, hσ]
    simp [Units.ext_iff]
  · rw [Equiv.Perm.parityRetract_of_sign_eq_neg_one ht hσ, ht.movedNorm, hσ]
    simp

/-- **Parity retraction, one edge.** An odd edge term moves at least two points
(`Equiv.Perm.movedNorm_parityRetract_le`). -/
private theorem st_par_bound (a b : S3) (e : Bool) :
    2 * Bool.toNat (xor (xor (oddPerm a) (oddPerm b)) e) ≤
      moved (a⁻¹ * (if e then t01 else 1) * b) := by
  have hodd :
      xor (xor (oddPerm a) (oddPerm b)) e = oddPerm (a⁻¹ * (if e then t01 else 1) * b) := by
    have ha : oddPerm a⁻¹ = oddPerm a := by
      rw [oddPerm_eq_decide, oddPerm_eq_decide, Equiv.Perm.sign_inv]
    have he : oddPerm (if e then t01 else 1) = e := by cases e <;> decide
    rw [oddPerm_mul, oddPerm_mul, ha, he]
    cases oddPerm a <;> cases oddPerm b <;> cases e <;> rfl
  rw [hodd]
  have h := Equiv.Perm.movedNorm_parityRetract_le t01_isSwap (a⁻¹ * (if e then t01 else 1) * b)
  rw [movedNorm_parityRetract_t01, ← moved_eq_movedNorm] at h
  exact_mod_cast h

/-- The holonomy of a triangle with `{1, t01}` labels moves `2` points exactly when an odd
number of its edges carry `t01`. -/
private theorem st_moved_tri (a b c : Bool) :
    moved ((if a then t01 else 1) * (if b then t01 else 1) * (if c then t01 else 1)⁻¹) =
      2 * Bool.toNat (xor (xor a b) c) := by
  cases a <;> cases b <;> cases c <;> decide

/-! ## The staircase graph on positions -/

/-- The staircase as a graph on `Fin n`: `p < q` are adjacent when `stEdge p q` holds. -/
private def stGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun p q => p < q ∧ stEdge p.val q.val = true

/-- Adjacency in `stGraph` is decidable. -/
private instance (n : ℕ) : DecidableRel (stGraph n).Adj := fun p q => by
  unfold stGraph
  infer_instance

/-- On a pair `p < q`, adjacency in `stGraph` is `stEdge`. -/
private theorem stGraph_adj_of_lt {n : ℕ} {p q : Fin n} (h : p < q) :
    decide ((stGraph n).Adj p q) = stEdge p.val q.val := by
  have hn : ¬ q < p := not_lt.mpr h.le
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp [stGraph, SimpleGraph.fromRel_adj, h, h.ne, hn]

/-- The relabelling of `SimpleGraph.staircase 1 t` onto the positions `0, …, 2t`: the rows go to
the odd positions, the columns to the nonzero even positions, the loose vertex to `0`. -/
private def stRelabel (t : ℕ) : Fin (1 * t) ⊕ Fin (1 * t) ⊕ Fin 1 → Fin (2 * t + 1)
  | .inl i => ⟨2 * i.val + 1, by have := i.isLt; omega⟩
  | .inr (.inl j) => ⟨2 * (t - j.val), by omega⟩
  | .inr (.inr _) => ⟨0, by omega⟩

/-- `stRelabel` is a bijection: odd positions are rows, nonzero even positions are columns. -/
private theorem stRelabel_bijective (t : ℕ) : Function.Bijective (stRelabel t) := by
  refine ⟨?_, fun p => ?_⟩
  · rintro (i | j | k) (i' | j' | k') h <;>
      simp only [stRelabel, Fin.ext_iff, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at h ⊢ <;>
      first
        | (have := i.isLt; have := i'.isLt; omega)
        | (have := j.isLt; have := j'.isLt; omega)
        | (have := k.isLt; have := k'.isLt; omega)
        | (have := i.isLt; have := j'.isLt; omega)
        | (have := j.isLt; have := i'.isLt; omega)
        | (have := j.isLt; omega)
        | (have := j'.isLt; omega)
  · have hp := p.isLt
    by_cases h0 : p.val = 0
    · exact ⟨.inr (.inr 0), Fin.ext (by simp [stRelabel, h0])⟩
    by_cases hodd : p.val % 2 = 1
    · exact ⟨.inl ⟨p.val / 2, by omega⟩, Fin.ext (by simp only [stRelabel]; omega)⟩
    · exact ⟨.inr (.inl ⟨t - p.val / 2, by omega⟩), Fin.ext (by simp only [stRelabel]; omega)⟩

/-- `stRelabel` carries the staircase adjacency `i + j < t` to `stEdge` on positions. -/
private theorem stRelabel_adj (t : ℕ) (a b : Fin (1 * t) ⊕ Fin (1 * t) ⊕ Fin 1) :
    (stGraph (2 * t + 1)).Adj (stRelabel t a) (stRelabel t b) ↔
      (SimpleGraph.staircase 1 t).Adj a b := by
  rcases a with i | j | k <;> rcases b with i' | j' | k' <;>
    simp [stGraph, SimpleGraph.fromRel_adj, stRelabel, stEdge, Fin.ext_iff] <;>
    omega

/-- `stGraph (2 t + 1)` is `SimpleGraph.staircase 1 t`, relabelled. -/
private noncomputable def stIso (t : ℕ) : SimpleGraph.staircase 1 t ≃g stGraph (2 * t + 1) where
  toEquiv := Equiv.ofBijective (stRelabel t) (stRelabel_bijective t)
  map_rel_iff' {a b} := stRelabel_adj t a b

/-- `2 · #edges = t (t + 1)`, from `SimpleGraph.two_mul_card_edgeFinset_staircase`. -/
private theorem two_mul_card_edgeFinset_stGraph (t : ℕ) :
    2 * #(stGraph (2 * t + 1)).edgeFinset = t * (t + 1) := by
  rw [← (stIso t).card_edgeFinset_eq, SimpleGraph.two_mul_card_edgeFinset_staircase]
  ring

/-! ## Counting edges and triangles on `Fin n` -/

/-- A finset of off-diagonal unordered pairs, counted over the pairs `u < v`. -/
private theorem card_eq_sum_lt {n : ℕ} (F : Finset (Sym2 (Fin n))) (hF : ∀ u, s(u, u) ∉ F) :
    #F = ∑ u : Fin n, ∑ v : Fin n, if u < v ∧ s(u, v) ∈ F then 1 else 0 := by
  rw [← Fintype.sum_prod_type' (fun u v => if u < v ∧ s(u, v) ∈ F then 1 else 0),
    ← Finset.card_filter]
  symm
  refine card_bij (fun p _ => s(p.1, p.2)) (fun p hp => (mem_filter.mp hp).2.2) ?_ ?_
  · rintro ⟨a, b⟩ ha ⟨a', b'⟩ hb h
    have ha' := (mem_filter.mp ha).2.1
    have hb' := (mem_filter.mp hb).2.1
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (ha'.trans hb') (lt_irrefl _)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rcases lt_trichotomy u v with h | rfl | h
      · exact ⟨(u, v), by simp [h, he], rfl⟩
      · exact absurd he (hF u)
      · exact ⟨(v, u), by simp [h, Sym2.eq_swap ▸ he], Sym2.eq_swap⟩

/-- A triangle is odd exactly when an odd number of its three pairs are edges
(`SimpleGraph.triple_mem_oddTripleFinset_iff`). -/
private theorem mem_oddTriangleFinset_triple {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] {a b c : Fin n} :
    {a, b, c} ∈ H.oddTriangleFinset ↔
      xor (xor (decide (H.Adj a b)) (decide (H.Adj b c))) (decide (H.Adj a c)) = true := by
  rw [SimpleGraph.mem_oddTriangleFinset, SimpleGraph.filter_edgeFinset_toFinset_subset,
    ← SimpleGraph.mem_oddTripleFinset, SimpleGraph.triple_mem_oddTripleFinset_iff]
  by_cases x : H.Adj a b <;> by_cases y : H.Adj b c <;> by_cases z : H.Adj a c <;> simp [x, y, z]

/-- The sorted triples `u < v < w` spanning an odd triangle. -/
private def oddTriples {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    Finset (Fin n × Fin n × Fin n) :=
  {p | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ {p.1, p.2.1, p.2.2} ∈ H.oddTriangleFinset}

/-- An odd triangle is the set of a unique sorted triple (`Set.powersetCard.ofLtTriple`). -/
private theorem card_oddTriples {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    #(oddTriples H) = #H.oddTriangleFinset := by
  refine card_bij (fun p _ => {p.1, p.2.1, p.2.2})
    (fun p hp => (mem_filter.mp hp).2.2.2) ?_ ?_
  · rintro ⟨a, b, c⟩ ha ⟨a', b', c'⟩ hb h
    obtain ⟨-, hab, hbc, -⟩ := mem_filter.mp ha
    obtain ⟨-, hab', hbc', -⟩ := mem_filter.mp hb
    have := Set.powersetCard.ofLtTriple.injective (a₁ := ⟨(a, b, c), hab, hbc⟩)
      (a₂ := ⟨(a', b', c'), hab', hbc'⟩)
      (Subtype.ext (by simpa only [Set.powersetCard.val_ofLtTriple] using h))
    simpa using congrArg Subtype.val this
  · intro s hs
    obtain ⟨a, b, c, hab, hbc, hs3⟩ :=
      Set.powersetCard.exists_lt_lt_val_eq ⟨s, (SimpleGraph.mem_oddTriangleFinset.mp hs).1⟩
    refine ⟨(a, b, c), ?_, hs3.symm⟩
    simp only [oddTriples, mem_filter, mem_univ, true_and]
    exact ⟨hab, hbc, hs3 ▸ hs⟩

/-- The odd triangles of a graph on `Fin n`, counted over the triples `u < v < w`. -/
private theorem card_oddTriangleFinset_eq_sum {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] :
    #H.oddTriangleFinset = ∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n, if u < v ∧ v < w then
      (xor (xor (decide (H.Adj u v)) (decide (H.Adj v w))) (decide (H.Adj u w))).toNat
      else 0 := by
  rw [← card_oddTriples, oddTriples, card_filter]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun w _ => ?_
  by_cases h : u < v ∧ v < w
  · simp only [h.1, h.2, true_and, mem_oddTriangleFinset_triple, Bool.toNat, Bool.cond_eq_ite,
      ↓reduceIte]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]

/-! ## The staircase cochain: gauge distance and defect -/

/-- **Cut-minimality, transported.** A `Sym(3)` gauge of the staircase on `K_{2t+1}` costs at
least twice the number `t (t + 1) / 2` of staircase edges: the parity retraction bounds each edge
term below by twice its `𝔽₂` term. Those terms count the symmetric difference of the staircase
edges `E` with the cut of the sign pattern `S` of the gauge, which has at least `#E` elements by
`SimpleGraph.isCutMinimal_staircase`, transported along `stIso`. -/
theorem stair_cost_lower (t : ℕ) (β : Fin (2 * t + 1) → S3) :
    t * (t + 1) ≤ cost (stair (2 * t + 1)) β := by
  let S : Set (Fin (2 * t + 1)) := {u | oddPerm (β u) = true}
  have hcm := (SimpleGraph.isCutMinimal_iff_card_le_card_symmDiff (stGraph (2 * t + 1))).mp
    ((stIso t).isCutMinimal_iff.mp (SimpleGraph.isCutMinimal_staircase 1 t)) S
  set F := symmDiff (stGraph (2 * t + 1)).edgeFinset
    ((⊤ : SimpleGraph (Fin (2 * t + 1))).between S Sᶜ).edgeFinset
  have hF : #F = ∑ u, ∑ v, if u < v then
      Bool.toNat (xor (xor (oddPerm (β u)) (oddPerm (β v))) (stEdge u.val v.val)) else 0 := by
    rw [card_eq_sum_lt F (fun u => by simp [F, mem_symmDiff])]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases huv : u < v
    · have he := stGraph_adj_of_lt huv
      rw [Bool.eq_iff_iff, decide_eq_true_iff] at he
      simp only [huv, true_and, ↓reduceIte, F, mem_symmDiff, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.between_adj, SimpleGraph.top_adj, he, huv.ne, ne_eq,
        not_false_eq_true, S, Set.mem_ofPred_eq, Set.mem_compl_iff]
      cases oddPerm (β u) <;> cases oddPerm (β v) <;> cases stEdge u.val v.val <;> simp
    · simp [huv]
  calc t * (t + 1) = 2 * #(stGraph (2 * t + 1)).edgeFinset :=
        (two_mul_card_edgeFinset_stGraph t).symm
    _ ≤ 2 * #F := Nat.mul_le_mul_left 2 hcm
    _ = ∑ u, ∑ v, if u < v then
          2 * (xor (xor (oddPerm (β u)) (oddPerm (β v))) (stEdge u.val v.val)).toNat
        else 0 := by
        rw [hF, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
    _ ≤ ∑ u, ∑ v, if u < v then moved ((β u)⁻¹ * stair (2 * t + 1) u v * β v) else 0 := by
        gcongr with u _ v _
        split_ifs
        · exact st_par_bound (β u) (β v) (stEdge u.val v.val)
        · exact le_rfl
    _ = cost (stair (2 * t + 1)) β := (cost_eq_sum _ _).symm

/-- The term of a triangle `u < v < w` in the staircase defect, as a parity of edge labels. -/
private theorem stair_tri_term (n : ℕ) (u v w : Fin n) :
    (if u < v ∧ v < w then
      moved (val (stair n) u v * val (stair n) v w * val (stair n) w u) else 0) =
      if u < v ∧ v < w then
        2 * Bool.toNat (xor (xor (decide ((stGraph n).Adj u v)) (decide ((stGraph n).Adj v w)))
          (decide ((stGraph n).Adj u w)))
      else 0 := by
  by_cases h : u < v ∧ v < w
  · rw [ite_eq_left h, ite_eq_left h, stGraph_adj_of_lt h.1, stGraph_adj_of_lt h.2,
      stGraph_adj_of_lt (h.1.trans h.2)]
    have huw : ¬ w < u := not_lt.mpr (h.1.trans h.2).le
    unfold Sym3.val
    rw [ite_eq_left h.1, ite_eq_left h.2, ite_eq_right huw]
    exact st_moved_tri (stEdge u.val v.val) (stEdge v.val w.val) (stEdge u.val w.val)
  · rw [ite_eq_right h, ite_eq_right h]

/-- The defect of the staircase is twice its number of odd triangles. -/
private theorem stair_defect (n : ℕ) : defect (stair n) = 2 * #(stGraph n).oddTriangleFinset := by
  rw [defect_eq_sum, card_oddTriangleFinset_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [stair_tri_term]
  split_ifs <;> simp

/-- **Defect of the staircase.** `3 N = (2 t + 1) · D` for the moved-point defect `N` and the
gauge lower bound `D = t (t + 1)`, from `SimpleGraph.three_mul_card_oddTriangleFinset_staircase`.
For `t ≥ 1` this is `N / D = (2 t + 1) / 3`; at `t = 0` both sides are `0`. -/
theorem stair_defect_mul (t : ℕ) :
    3 * defect (stair (2 * t + 1)) = (2 * t + 1) * (t * (t + 1)) := by
  have h := SimpleGraph.three_mul_card_oddTriangleFinset_staircase 1 t
  rw [(stIso t).card_oddTriangleFinset_eq, (stIso t).card_edgeFinset_eq] at h
  have hE := two_mul_card_edgeFinset_stGraph t
  rw [stair_defect]
  nlinarith

end TauCeti.Sym3
