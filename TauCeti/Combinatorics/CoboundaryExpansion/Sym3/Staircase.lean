/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
public import TauCeti.Combinatorics.SimpleGraph.OddTriangles
import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic
import TauCeti.Combinatorics.SimpleGraph.Staircase
import TauCeti.Algebra.BigOperators.Sym
import TauCeti.GroupTheory.Perm.ParityRetract
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `Sym(3)` coboundary constant along Kozlov's staircase graphs

For a graph `G` on a finite linear order `V`, the cochain `Cochain.ofLt (complete V) f` with
`f u v = swap 0 1` on the edges of `G` and `1` elsewhere has defect `2 * #G.oddTriangleFinset`
(`SimpleGraph.defect_ofLt_ite_adj`). When `G` is cut-minimal every gauge costs at least
`2 * #G.edgeFinset`: the parity retraction onto `{1, swap 0 1}`
(`Equiv.Perm.parityRetract`, which fixes the cochain and does not increase the moved-point norm,
`Cochain.cost_map_le`) turns any gauge into a cut `S`, whose cost is twice the size of the
symmetric difference of the edges of `G` with the cut edges of `S`. Hence:

* `SimpleGraph.h1_complete_movedNorm_fin_three_le_of_isCutMinimal`: for a cut-minimal `G` with an
  edge,
  `h1 (complete V) (movedNorm (Fin 3)) ≤ #G.oddTriangleFinset / #G.edgeFinset`.
* `h1_complete_movedNorm_fin_three_le_of_card_eq_mul`: applied to Kozlov's staircase graph
  `SimpleGraph.staircase q t` on `q (2 t + 1)` vertices, which is cut-minimal
  (`SimpleGraph.isCutMinimal_staircase`) with
  `3 * #oddTriangleFinset = q (2 t + 1) * #edgeFinset`
  (`SimpleGraph.three_mul_card_oddTriangleFinset_staircase`), this gives
  `h1 (complete V) (movedNorm (Fin 3)) ≤ card V / 3` whenever `card V = q (2 t + 1)`, `q, t ≥ 1`.

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136,
  Definition 3.2 and §3.1 (staircase graphs), Lemma 3.8 and Corollary 3.13 (cut-minimality),
  Lemma 3.10 (triangle count).
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792,
  Corollary 7 and Theorem 8 (the `Sym(3)` transfer).
* Jeromie Beasley, `coboundary-k3-lean` (MIT), https://github.com/dicipler-pixel/coboundary-k3-lean,
  commit `7f5f2c6`: this file adapts the staircase cochain and its parity bound from
  `CoboundaryK3/Staircase.lean`, with the counting replaced by `SimpleGraph.staircase`.
-/

public section

namespace TauCeti

open Finset Equiv TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

namespace Sym3

/-- A `{1, swap 0 1}`-gauged edge term moves `2` points exactly when an odd number of the edge
label and the two gauge values are `swap 0 1`. -/
private theorem card_support_inv_mul_ite_mul {x y : Perm (Fin 3)} (hx : x = 1 ∨ x = swap 0 1)
    (hy : y = 1 ∨ y = swap 0 1) (p : Prop) [Decidable p] :
    #(x⁻¹ * (if p then swap 0 1 else 1) * y).support =
      if Xor p (Xor (x = swap 0 1) (y = swap 0 1)) then 2 else 0 := by
  have key : ∀ x y : Perm (Fin 3), x = 1 ∨ x = swap 0 1 → y = 1 ∨ y = swap 0 1 → ∀ b : Bool,
      #(x⁻¹ * (if b = true then swap 0 1 else 1) * y).support =
        if Xor (b = true) (Xor (x = swap 0 1) (y = swap 0 1)) then 2 else 0 := by
    decide +kernel
  by_cases hp : p
  · simpa [hp] using key x y hx hy true
  · simpa [hp] using key x y hx hy false

end Sym3

end TauCeti

namespace SimpleGraph

open Finset Equiv TauCeti TauCeti.TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- **Parity retraction against a cut-minimal graph.** Every gauge costs at least
`2 * #G.edgeFinset` against the cochain equal to `swap 0 1` on the edges of a cut-minimal `G`. -/
private theorem two_mul_card_edgeFinset_le_cost (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsCutMinimal) (β : V → Perm (Fin 3)) :
    (2 * #G.edgeFinset : ℝ) ≤
      (Cochain.ofLt (complete V) fun u v => if G.Adj u v then swap 0 1 else 1).cost
        (Perm.movedNorm (Fin 3)) β := by
  set α := Cochain.ofLt (complete V) fun u v => if G.Adj u v then (swap 0 1 : Perm (Fin 3)) else 1
  have ht : (swap 0 1 : Perm (Fin 3)).IsSwap := Perm.swap_isSwap_iff.mpr (by decide)
  have hφα : α.map (Perm.parityRetract ht) = α := by
    refine Cochain.ext fun u v _ => ?_
    rw [Cochain.map_apply, Perm.parityRetract_eq_self_iff]
    rcases lt_trichotomy u v with h | rfl | h
    · rw [Cochain.ofLt_apply_of_lt _ ((adj_complete u v).mpr h.ne) h]
      split_ifs <;> simp
    · simp
    · rw [Cochain.ofLt_apply_of_gt _ ((adj_complete u v).mpr h.ne') h]
      split_ifs <;> simp
  refine le_trans ?_ (Cochain.cost_map_le (Perm.movedNorm_parityRetract_le ht) α β)
  rw [hφα]
  set γ := Perm.parityRetract ht ∘ β
  have hγ : ∀ u, γ u = 1 ∨ γ u = swap 0 1 := fun u =>
    (Perm.mem_range_parityRetract ht _).mp ⟨β u, rfl⟩
  let S : Set V := {u | γ u = swap 0 1}
  have hcm := (SimpleGraph.isCutMinimal_iff_card_le_card_symmDiff G).mp hG S
  set F := symmDiff G.edgeFinset ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset
  have hF : (#F : ℝ) = ∑ u, ∑ v,
      if u < v ∧ Xor (G.Adj u v) (Xor (γ u = swap 0 1) (γ v = swap 0 1)) then 1 else 0 := by
    rw [card_eq_sum_sum_ite_lt_of_forall_mk_notMem F (fun u => by simp [F, mem_symmDiff])]
    push_cast
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    by_cases huv : u < v
    · have hne := huv.ne
      by_cases ha : G.Adj u v <;> by_cases hu : γ u = swap 0 1 <;>
        by_cases hv : γ v = swap 0 1 <;>
        simp [huv, hne, ha, hu, hv, F, S, mem_symmDiff, SimpleGraph.between_adj]
    · simp [huv]
  rw [Cochain.cost_complete, sum_filter, Fintype.sum_prod_type]
  calc (2 * #G.edgeFinset : ℝ) ≤ 2 * #F := by exact_mod_cast Nat.mul_le_mul_left 2 hcm
    _ = ∑ u, ∑ v, if u < v then Perm.movedNorm (Fin 3) ((γ u)⁻¹ * α u v * γ v) else 0 := by
      rw [hF, mul_sum]
      refine sum_congr rfl fun u _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun v _ => ?_
      by_cases huv : u < v
      · rw [Cochain.ofLt_apply_of_lt _ ((adj_complete u v).mpr huv.ne) huv, Perm.movedNorm_apply,
          TauCeti.Sym3.card_support_inv_mul_ite_mul (hγ u) (hγ v)]
        by_cases hx : Xor (G.Adj u v) (Xor (γ u = swap 0 1) (γ v = swap 0 1)) <;> simp [huv, hx]
      · simp [huv]

/-- **Cut-minimal graphs bound the `Sym(3)` constant.** For a cut-minimal graph `G` on `V` with at
least one edge, `h1 (complete V) (movedNorm (Fin 3)) ≤ #G.oddTriangleFinset / #G.edgeFinset`. -/
theorem h1_complete_movedNorm_fin_three_le_of_isCutMinimal (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsCutMinimal) (hE : 0 < #G.edgeFinset) :
    h1 (complete V) (Perm.movedNorm (Fin 3)) ≤
      (#G.oddTriangleFinset : ℝ) / #G.edgeFinset := by
  set α := Cochain.ofLt (complete V) fun u v => if G.Adj u v then (swap 0 1 : Perm (Fin 3)) else 1
  have hE' : (0 : ℝ) < 2 * #G.edgeFinset := by positivity
  have hgd : (2 * #G.edgeFinset : ℝ) ≤ α.gaugeDist (Perm.movedNorm (Fin 3)) :=
    (α.le_gaugeDist_iff _).mpr (G.two_mul_card_edgeFinset_le_cost hG)
  refine (h1_le_div (hE'.trans_le hgd)).trans ?_
  rw [defect_ofLt_ite_adj]
  calc (2 * #G.oddTriangleFinset : ℝ) / α.gaugeDist (Perm.movedNorm (Fin 3)) ≤
        2 * #G.oddTriangleFinset / (2 * #G.edgeFinset) :=
        div_le_div_of_nonneg_left (by positivity) hE' hgd
    _ = #G.oddTriangleFinset / #G.edgeFinset := mul_div_mul_left _ _ two_ne_zero

end SimpleGraph

namespace TauCeti

open Finset Equiv TwoComplex

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- **The staircase upper bound.** If `card V = q (2 t + 1)` with `q, t ≥ 1`, then
`h1 (complete V) (movedNorm (Fin 3)) ≤ card V / 3`, witnessed by Kozlov's staircase graph
`SimpleGraph.staircase q t`. -/
theorem h1_complete_movedNorm_fin_three_le_of_card_eq_mul {q t : ℕ} (hq : 0 < q) (ht : 0 < t)
    (hV : Fintype.card V = q * (2 * t + 1)) :
    h1 (complete V) (Perm.movedNorm (Fin 3)) ≤ (Fintype.card V : ℝ) / 3 := by
  let W := Fin (q * t) ⊕ Fin (q * t) ⊕ Fin q
  let _ : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  have hW : Fintype.card W = q * (2 * t + 1) := by
    simp only [W, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [h1_complete_eq_of_card_eq Perm.isConjInvariant_movedNorm (hV.trans hW.symm)]
  have hE2 := SimpleGraph.two_mul_card_edgeFinset_staircase q t
  have hO := SimpleGraph.three_mul_card_oddTriangleFinset_staircase q t
  have hE : 0 < #(SimpleGraph.staircase q t).edgeFinset := by
    have : 0 < q ^ 2 * t * (t + 1) := by positivity
    omega
  refine (SimpleGraph.h1_complete_movedNorm_fin_three_le_of_isCutMinimal _
    (SimpleGraph.isCutMinimal_staircase q t) hE).trans_eq ?_
  have hE' : (0 : ℝ) < #(SimpleGraph.staircase q t).edgeFinset := by exact_mod_cast hE
  rw [hV, div_eq_div_iff hE'.ne' (by norm_num)]
  have h := congrArg (Nat.cast (R := ℝ)) hO
  push_cast at h ⊢
  -- the two odd-triangle counts differ only in their `DecidableEq W` instances
  refine (mul_comm _ _).trans ?_
  convert h

end TauCeti
