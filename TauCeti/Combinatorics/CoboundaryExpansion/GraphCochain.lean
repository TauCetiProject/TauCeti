/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
public import TauCeti.Combinatorics.SimpleGraph.OddTriangles
import TauCeti.Algebra.BigOperators.Sym
import TauCeti.Algebra.Group.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.SwapGraph
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.Positivity

/-!
# Cochains of graphs with values in an involution

For a graph `G` on a finite linear order `V` and an involution `t` of a group `K`, the cochain
`Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1` carries `t` on the edges of `G`
and `1` elsewhere. With `t` the transposition of `Equiv.Perm (Fin 2)` these are all the binary
cochains, and the defect and gauge cost become counts of edges and triangles:

* `SimpleGraph.defect_ofLt_ite_adj`: the defect is `ℓ t` times the number of triangles spanning an
  odd number of edges of `G`;
* `SimpleGraph.cost_ofLt_ite_adj`: the gauge equal to `t` on a set `S` of vertices and `1` elsewhere
  costs `ℓ t` times the size of the symmetric difference of the edges of `G` with the cut edges of
  `S`;
* `TauCeti.Cochain.supportGraph`: the graph of edges on which a cochain is not `1`. For `t ≠ 1`
  the support graph of the cochain of `G` is `G` (`SimpleGraph.supportGraph_ofLt_ite_adj`), and
  every `Equiv.Perm (Fin 2)`-valued cochain on the complete complex is the cochain of its support
  graph (`TauCeti.Cochain.eq_ofLt_ite_supportGraph`), with defect and costs given by
  `TauCeti.Cochain.defect_eq_two_mul_card_oddTriangleFinset` and
  `TauCeti.Cochain.cost_eq_two_mul_card_symmDiff`.

For permutation coefficients `Equiv.Perm α` with the moved-point norm and a transposition `t`, every
gauge costs at least the cut gauge of its odd-sign vertices
(`SimpleGraph.two_mul_card_symmDiff_le_sum_filter_lt_movedNorm_ite_isSwap`), so the cheapest gauges
are the cuts. Hence:

* `SimpleGraph.isCutMinimal_iff_gaugeDist_eq`: `G` is cut-minimal exactly when the gauge distance
  of its cochain is `2 * #G.edgeFinset`;
* `SimpleGraph.h1_complete_movedNorm_le_of_isCutMinimal`: a cut-minimal graph `G` with an edge gives
  `h1 (complete V) (movedNorm α) ≤ #G.oddTriangleFinset / #G.edgeFinset`.

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136, Section 2
  (binary cochains as graphs, cut-minimality, equation (2.5)).
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792, Corollary 7 (the parity retraction).
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: the graph cochain and its parity bound adapt `CoboundaryK3/Basic.lean` and
  `CoboundaryK3/Staircase.lean`.
-/

public section

open Finset Equiv TauCeti TauCeti.TwoComplex
open scoped symmDiff

namespace SimpleGraph

variable {V K : Type*} [Fintype V] [LinearOrder V] [Group K] {t : K}

/-- The gauge cost of the cochain of `G` as a sum over the increasing pairs. -/
private theorem cost_ofLt_ite_adj_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ : GroupNorm K) (β : V → K) :
    (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).cost ℓ β =
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        ℓ ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then t else 1) * β e.2) := by
  rw [Cochain.cost_complete]
  refine sum_congr rfl fun e he => ?_
  have h := (mem_filter.mp he).2
  rw [Cochain.ofLt_apply_of_lt _ ((adj_complete _ _).mpr h.ne) h]

/-- **Defect of a graph cochain.** The cochain equal to an involution `t` on the edges of `G` and
`1` elsewhere has defect `ℓ t * #G.oddTriangleFinset`. -/
theorem defect_ofLt_ite_adj (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : GroupNorm K)
    (ht : t * t = 1) :
    (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).defect ℓ =
      ℓ t * #G.oddTriangleFinset := by
  rw [Cochain.defect_complete, sum_filter, card_oddTriangleFinset_eq_sum]
  simp only [Fintype.sum_prod_type]
  push_cast
  simp only [mul_sum]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => sum_congr rfl fun w _ => ?_
  by_cases h : u < v ∧ v < w
  · rw [ite_eq_left h, Cochain.holonomy_ofLt_complete _ h.1 h.2, ite_inv_of_mul_self ht,
      ite_mul_ite_mul_ite_of_mul_self ht]
    simp only [xor_comm (G.Adj v w)]
    by_cases hx : Xor (G.Adj u v) (Xor (G.Adj u w) (G.Adj v w)) <;> simp [h, hx]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]
    simp

/-- **Cost of a cut gauge.** Against the cochain equal to an involution `t` on the edges of `G`,
the gauge equal to `t` on `S` and `1` elsewhere costs `ℓ t` times the number of pairs that are
either edges of `G` or cross the cut `(S, Sᶜ)`, but not both. -/
theorem cost_ofLt_ite_adj (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : GroupNorm K)
    (ht : t * t = 1) (S : Set V) [DecidablePred (· ∈ S)] :
    (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).cost ℓ
        (fun u => if u ∈ S then t else 1) =
      ℓ t * #(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) := by
  rw [card_eq_sum_sum_ite_lt_of_forall_mk_notMem _ (fun u => by simp [mem_symmDiff]),
    Cochain.cost_complete, sum_filter, Fintype.sum_prod_type]
  push_cast
  simp only [mul_sum]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  by_cases huv : u < v
  · rw [Cochain.ofLt_apply_of_lt _ ((adj_complete u v).mpr huv.ne) huv,
      ite_inv_of_mul_self ht, ite_mul_ite_mul_ite_of_mul_self ht]
    by_cases ha : G.Adj u v <;> by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp [huv, huv.ne, ha, hu, hv, mem_symmDiff, between_adj]
  · simp [huv]

/-- The trivial gauge costs `ℓ t * #G.edgeFinset` against the cochain of `G`, so this bounds its
gauge distance. -/
theorem gaugeDist_ofLt_ite_adj_le (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : GroupNorm K) :
    (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).gaugeDist ℓ ≤
      ℓ t * #G.edgeFinset := by
  refine (Cochain.gaugeDist_le_cost _ _ 1).trans_eq ?_
  rw [Cochain.cost_complete, card_eq_sum_sum_ite_lt_of_forall_mk_notMem _ (by simp), sum_filter,
    Fintype.sum_prod_type]
  push_cast
  simp only [mul_sum]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  by_cases huv : u < v
  · rw [Cochain.ofLt_apply_of_lt _ ((adj_complete u v).mpr huv.ne) huv]
    by_cases ha : G.Adj u v <;> simp [huv, ha]
  · simp [huv]

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Parity retraction against a cut-minimal graph.** For a transposition `t`, every gauge costs
at least `2 * #G.edgeFinset` against the cochain equal to `t` on the edges of a cut-minimal `G`. -/
theorem two_mul_card_edgeFinset_le_cost {t : Perm α} (ht : t.IsSwap) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsCutMinimal) (β : V → Perm α) :
    (2 * #G.edgeFinset : ℝ) ≤
      (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).cost
        (Perm.movedNorm α) β := by
  rw [cost_ofLt_ite_adj_eq_sum]
  refine le_trans ?_ (G.two_mul_card_symmDiff_le_sum_filter_lt_movedNorm_ite_isSwap ht β)
  exact_mod_cast Nat.mul_le_mul_left 2 ((isCutMinimal_iff_card_le_card_symmDiff G).mp hG _)

/-- **Cut-minimality as a gauge distance.** For a transposition `t`, a graph `G` is cut-minimal
exactly when the cochain equal to `t` on its edges has gauge distance `2 * #G.edgeFinset`, the cost
of the trivial gauge. -/
theorem isCutMinimal_iff_gaugeDist_eq {t : Perm α} (ht : t.IsSwap) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.IsCutMinimal ↔
      (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).gaugeDist
        (Perm.movedNorm α) = 2 * #G.edgeFinset := by
  rw [Cochain.gaugeDist_def]
  simp only [cost_ofLt_ite_adj_eq_sum]
  exact (G.ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff ht).symm

/-- **Cut-minimal graphs bound the permutation constant.** For a cut-minimal graph `G` on `V` with
at least one edge,
`h1 (complete V) (movedNorm α) ≤ #G.oddTriangleFinset / #G.edgeFinset`. -/
theorem h1_complete_movedNorm_le_of_isCutMinimal (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsCutMinimal) (hE : 0 < #G.edgeFinset) :
    h1 (complete V) (Perm.movedNorm α) ≤ (#G.oddTriangleFinset : ℝ) / #G.edgeFinset := by
  rcases subsingleton_or_nontrivial α with hα | ⟨a, b, hab⟩
  · rw [h1_subsingleton]
    positivity
  set c := Cochain.ofLt (complete V) fun u v => if G.Adj u v then swap a b else 1
  have ht : (swap a b).IsSwap := ⟨a, b, hab, rfl⟩
  have hE' : (0 : ℝ) < 2 * #G.edgeFinset := by positivity
  have hgd : c.gaugeDist (Perm.movedNorm α) = 2 * #G.edgeFinset :=
    (G.isCutMinimal_iff_gaugeDist_eq ht).mp hG
  refine (h1_le_div (hgd ▸ hE')).trans_eq ?_
  rw [hgd, G.defect_ofLt_ite_adj _ (swap_mul_self a b), ht.movedNorm]
  exact mul_div_mul_left _ _ two_ne_zero

end Perm

end SimpleGraph

namespace TauCeti.Cochain

variable {V K : Type*} [Group K] {X : TwoComplex V}

/-- The support graph of a cochain: two vertices are adjacent when the cochain is not `1` on the
pair. -/
def supportGraph (α : Cochain X K) : SimpleGraph V where
  Adj u v := α u v ≠ 1
  symm := ⟨fun u v h => by rwa [α.apply_swap, Ne, inv_eq_one]⟩
  loopless := ⟨fun u h => h (α.apply_self u)⟩

@[simp] theorem supportGraph_adj (α : Cochain X K) {u v : V} :
    α.supportGraph.Adj u v ↔ α u v ≠ 1 := Iff.rfl

instance [DecidableEq K] (α : Cochain X K) : DecidableRel α.supportGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (α u v ≠ 1))

variable [Fintype V] [LinearOrder V]

/-- Every `Equiv.Perm (Fin 2)`-valued cochain on the complete complex is the transposition on the
edges of its support graph and `1` elsewhere. -/
theorem eq_ofLt_ite_supportGraph (α : Cochain (complete V) (Perm (Fin 2))) :
    α = Cochain.ofLt (complete V) fun u v => if α.supportGraph.Adj u v then swap 0 1 else 1 := by
  refine ext_of_lt fun u v huv hadj => ?_
  rw [ofLt_apply_of_lt _ hadj huv, perm_fin_two_eq_ite_fromRel α α.apply_self α.apply_swap u v]
  refine if_congr ?_ rfl rfl
  simp [SimpleGraph.fromRel_adj, huv.ne, α.apply_swap v u]

/-- The defect of an `Equiv.Perm (Fin 2)`-valued cochain on the complete complex is twice the
number of triangles spanning an odd number of edges of its support graph. -/
theorem defect_eq_two_mul_card_oddTriangleFinset (α : Cochain (complete V) (Perm (Fin 2))) :
    α.defect (Perm.movedNorm (Fin 2)) = 2 * #α.supportGraph.oddTriangleFinset := by
  conv_lhs => rw [α.eq_ofLt_ite_supportGraph]
  rw [SimpleGraph.defect_ofLt_ite_adj _ _ (swap_mul_self 0 1),
    Perm.IsSwap.movedNorm ⟨0, 1, by decide, rfl⟩]

/-- The cost of a gauge `β` against an `Equiv.Perm (Fin 2)`-valued cochain on the complete complex
is twice the number of pairs that are either edges of its support graph or cross the cut
`(S, Sᶜ)` of the vertices where `β` is not `1`, but not both. -/
theorem cost_eq_two_mul_card_symmDiff (α : Cochain (complete V) (Perm (Fin 2)))
    (β : V → Perm (Fin 2)) :
    α.cost (Perm.movedNorm (Fin 2)) β =
      2 * #(α.supportGraph.edgeFinset ∆
        ((⊤ : SimpleGraph V).between {u | β u ≠ 1} {u | β u ≠ 1}ᶜ).edgeFinset) := by
  conv_lhs => rw [α.eq_ofLt_ite_supportGraph]
  rw [SimpleGraph.cost_ofLt_ite_adj_eq_sum]
  exact α.supportGraph.sum_filter_lt_movedNorm_fin_two_ite_swap β

end TauCeti.Cochain

namespace SimpleGraph

variable {V K : Type*} [Fintype V] [LinearOrder V] [Group K]

/-- For `t ≠ 1`, the support graph of the cochain equal to `t` on the edges of `G` and `1` elsewhere
is `G`. -/
theorem supportGraph_ofLt_ite_adj (G : SimpleGraph V) [DecidableRel G.Adj] {t : K} (ht : t ≠ 1) :
    (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).supportGraph = G := by
  ext u v
  rw [Cochain.supportGraph_adj]
  rcases lt_trichotomy u v with h | rfl | h
  · rw [Cochain.ofLt_apply_of_lt _ ((adj_complete u v).mpr h.ne) h]
    by_cases huv : G.Adj u v <;> simp [huv, ht]
  · simp
  · rw [Cochain.ofLt_apply_of_gt _ ((adj_complete u v).mpr h.ne') h]
    by_cases huv : G.Adj v u <;> simp [huv, G.adj_comm u v, ht]

end SimpleGraph
