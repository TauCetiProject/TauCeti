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
import TauCeti.GroupTheory.Perm.ParityRetract
import Mathlib.Tactic.Linarith
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

For permutation coefficients `Equiv.Perm α` with the moved-point norm and a transposition `t`, the
parity retraction onto `{1, t}` (`Equiv.Perm.parityRetract`) does not increase any gauge cost, so
the cheapest gauges are the cuts. Hence:

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

/-- A product of three factors from `{1, t}`, the last inverted, is `t` exactly when an odd number
of the factors are `t`. -/
private theorem ite_mul_ite_mul_ite_inv (ht : t * t = 1) (p r s : Prop) [Decidable p]
    [Decidable r] [Decidable s] :
    (if p then t else 1) * (if r then t else 1) * (if s then t else 1)⁻¹ =
      if Xor p (Xor s r) then t else 1 := by
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  by_cases hp : p <;> by_cases hr : r <;> by_cases hs : s <;> simp [hp, hr, hs, hinv, ht]

/-- An edge term with gauge values in `{1, t}` is `t` exactly when an odd number of the edge label
and the two gauge values are `t`. -/
private theorem ite_inv_mul_ite_mul_ite (ht : t * t = 1) (p r s : Prop) [Decidable p]
    [Decidable r] [Decidable s] :
    (if r then t else 1)⁻¹ * (if p then t else 1) * (if s then t else 1) =
      if Xor p (Xor r s) then t else 1 := by
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  by_cases hp : p <;> by_cases hr : r <;> by_cases hs : s <;> simp [hp, hr, hs, hinv, ht]

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
  · rw [ite_eq_left h, Cochain.holonomy_ofLt_complete _ h.1 h.2, ite_mul_ite_mul_ite_inv ht]
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
      ite_inv_mul_ite_mul_ite ht]
    by_cases ha : G.Adj u v <;> by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp [huv, huv.ne, ha, hu, hv, mem_symmDiff, between_adj]
  · simp [huv]

/-- The trivial gauge costs `ℓ t * #G.edgeFinset` against the cochain of `G`, so this bounds its
gauge distance. -/
theorem gaugeDist_ofLt_ite_adj_le (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : GroupNorm K)
    (ht : t * t = 1) :
    (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).gaugeDist ℓ ≤
      ℓ t * #G.edgeFinset := by
  have h := G.cost_ofLt_ite_adj ℓ ht ∅
  have h0 : ((⊤ : SimpleGraph V).between ∅ ∅ᶜ).edgeFinset = ∅ :=
    edgeFinset_eq_empty.mpr (by ext; simp [between_adj])
  simp only [Set.mem_empty_iff_false, ite_false, h0] at h
  simp only [← bot_eq_empty, symmDiff_bot] at h
  exact h ▸ Cochain.gaugeDist_le_cost _ _ _

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Parity retraction against a cut-minimal graph.** For a transposition `t`, every gauge costs
at least `2 * #G.edgeFinset` against the cochain equal to `t` on the edges of a cut-minimal `G`. -/
theorem two_mul_card_edgeFinset_le_cost {t : Perm α} (ht : t.IsSwap) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsCutMinimal) (β : V → Perm α) :
    (2 * #G.edgeFinset : ℝ) ≤
      (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).cost
        (Perm.movedNorm α) β := by
  have ht1 : t * t = 1 := by obtain ⟨a, b, -, rfl⟩ := ht; exact swap_mul_self a b
  set c := Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1
  have hφc : c.map (Perm.parityRetract ht) = c := by
    refine Cochain.ext fun u v _ => ?_
    rw [Cochain.map_apply, Perm.parityRetract_eq_self_iff]
    rcases lt_trichotomy u v with h | rfl | h
    · rw [Cochain.ofLt_apply_of_lt _ ((adj_complete u v).mpr h.ne) h]
      split_ifs <;> simp
    · simp
    · rw [Cochain.ofLt_apply_of_gt _ ((adj_complete u v).mpr h.ne') h]
      split_ifs <;> simp [inv_eq_of_mul_eq_one_right ht1]
  refine le_trans ?_ (Cochain.cost_map_le (Perm.movedNorm_parityRetract_le ht) c β)
  -- The retracted gauge takes values in `{1, t}`: it is the cut gauge of the vertices sent to `t`.
  let S : Set V := {u | Perm.parityRetract ht (β u) = t}
  have hγ : Perm.parityRetract ht ∘ β = fun u => if u ∈ S then t else 1 := by
    funext u
    rcases (Perm.mem_range_parityRetract ht _).mp ⟨β u, rfl⟩ with h | h
    · have hu : u ∉ S := fun hu => by
        have h2 := ht.movedNorm
        rw [← hu, h, Perm.movedNorm_apply, Perm.support_one, card_empty] at h2
        norm_num at h2
      simp [hu, h]
    · simp [S, h]
  rw [hφc, hγ, G.cost_ofLt_ite_adj _ ht1, ht.movedNorm]
  exact_mod_cast Nat.mul_le_mul_left 2 ((isCutMinimal_iff_card_le_card_symmDiff G).mp hG S)

/-- **Cut-minimality as a gauge distance.** For a transposition `t`, a graph `G` is cut-minimal
exactly when the cochain equal to `t` on its edges has gauge distance `2 * #G.edgeFinset`, the cost
of the trivial gauge. -/
theorem isCutMinimal_iff_gaugeDist_eq {t : Perm α} (ht : t.IsSwap) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.IsCutMinimal ↔
      (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1).gaugeDist
        (Perm.movedNorm α) = 2 * #G.edgeFinset := by
  have ht1 : t * t = 1 := by obtain ⟨a, b, -, rfl⟩ := ht; exact swap_mul_self a b
  refine ⟨fun hG => le_antisymm ?_ ?_, fun h => ?_⟩
  · simpa [ht.movedNorm] using G.gaugeDist_ofLt_ite_adj_le (Perm.movedNorm α) ht1
  · exact (Cochain.le_gaugeDist_iff _ _).mpr (G.two_mul_card_edgeFinset_le_cost ht hG)
  · refine (isCutMinimal_iff_card_le_card_symmDiff G).mpr fun S _ => ?_
    have hS := Cochain.gaugeDist_le_cost (Perm.movedNorm α)
      (Cochain.ofLt (complete V) fun u v => if G.Adj u v then t else 1)
      (fun u => if u ∈ S then t else 1)
    rw [h, G.cost_ofLt_ite_adj _ ht1, ht.movedNorm] at hS
    exact_mod_cast (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).mp hS

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
  have key : ∀ σ : Perm (Fin 2), σ ≠ 1 → σ = swap 0 1 := by decide
  rw [ofLt_apply_of_lt _ hadj huv]
  by_cases h : α.supportGraph.Adj u v
  · rw [ite_eq_left h]
    exact key _ h
  · rw [ite_eq_right h]
    simpa using h

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
  have hβ : β = fun u => if u ∈ {u | β u ≠ 1} then swap 0 1 else 1 := by
    have key : ∀ σ : Perm (Fin 2), σ ≠ 1 → σ = swap 0 1 := by decide
    funext u
    by_cases h : β u = 1
    · simp [h]
    · simp [key _ h]
  conv_lhs => rw [α.eq_ofLt_ite_supportGraph, hβ]
  rw [SimpleGraph.cost_ofLt_ite_adj _ _ (swap_mul_self 0 1),
    Perm.IsSwap.movedNorm ⟨0, 1, by decide, rfl⟩]

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
