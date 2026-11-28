/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Binary
public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.ParityRetract
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# Parity-retracted gauges and cut-minimality

Specializing `SimpleGraph.toCochain` (from
`TauCeti.Combinatorics.CoboundaryExpansion.Cochain.SimpleGraph`) to a finite symmetric group
`Equiv.Perm α` and a transposition `ht : t.IsSwap` under `Equiv.Perm.movedNorm α` connects
permutation gauges to cut-minimality and binary cochains via `Equiv.Perm.parityRetract`:

* for any gauge `β : V → Equiv.Perm α` with odd-sign vertex set
  `S := {w | Equiv.Perm.sign (β w) = -1}`, retracting the gauged edge label produces the
  cut-switched edge label of `G ∆ (⊤ : SimpleGraph V).between S Sᶜ` and yields
  `2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset ≤
    (G.toCochain ht.mul_self_eq_one).cost (Equiv.Perm.movedNorm α) β`
  (`SimpleGraph.two_mul_card_symmDiff_le_cost_movedNorm_toCochain`);
* `SimpleGraph.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq` characterizes cut-minimality by
  `(G.toCochain ht.mul_self_eq_one).gaugeDist (Equiv.Perm.movedNorm α) = 2 * #G.edgeFinset`, so
  any cut-minimal graph with an edge bounds the permutation Cheeger constant
  (`SimpleGraph.h1_complete_movedNorm_le_of_isCutMinimal`), and via
  `TauCeti.simpleGraphEquivPermFinTwo` (from `Cochain.Binary`) transports `Cochain.cost`,
  `Cochain.defect`, and `Cochain.gaugeDist` to cut-switched edge counts, `#G.oddTripleFinset`,
  and cut-minimality (`TauCeti.Cochain.cost_movedNorm_fin_two`,
  `TauCeti.Cochain.defect_movedNorm_fin_two`,
  `TauCeti.Cochain.isCutMinimal_supportGraph_fin_two_iff`).

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, Section 2.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, doi:10.5281/zenodo.23245792, Section 2, Corollary 7, and Theorem 8.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

section SwapGauge

variable {V α : Type*} [Fintype α] [DecidableEq α]

/-- Applying `Equiv.Perm.parityRetract ht` to a gauged transposition edge label
`(β u)⁻¹ * (if G.Adj u v then t else 1) * β v` produces the cut-switched edge label corresponding
to `{w | Equiv.Perm.sign (β w) = -1}`. -/
theorem parityRetract_inv_mul_ite_adj_mul [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : Equiv.Perm α} (ht : t.IsSwap) (β : V → Equiv.Perm α) (u v : V) :
    Equiv.Perm.parityRetract ht ((β u)⁻¹ * (if G.Adj u v then t else 1) * β v) =
      if (G ∆ (⊤ : SimpleGraph V).between {w | Equiv.Perm.sign (β w) = -1}
        {w | Equiv.Perm.sign (β w) = -1}ᶜ).Adj u v then t else 1 := by
  have hedge :
      Equiv.Perm.parityRetract ht (if G.Adj u v then t else 1) = if G.Adj u v then t else 1 := by
    split_ifs <;> simp
  rw [map_mul, map_mul, map_inv, Equiv.Perm.parityRetract_eq_ite_sign_eq_neg_one ht (β u),
    Equiv.Perm.parityRetract_eq_ite_sign_eq_neg_one ht (β v), hedge]
  exact G.ite_mem_inv_mul_ite_adj_mul ht.mul_self_eq_one {w | Equiv.Perm.sign (β w) = -1} u v

/-- Under the trivial gauge `1`, the moved-point cost of `G.toCochain ht.mul_self_eq_one` equals
`2 * #G.edgeFinset`. -/
theorem cost_movedNorm_toCochain_one [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [Fintype G.edgeSet] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self_eq_one).cost (Equiv.Perm.movedNorm α) 1 = 2 * #G.edgeFinset := by
  rw [G.cost_toCochain_one (Equiv.Perm.movedNorm α) ht.mul_self_eq_one, ht.movedNorm, mul_comm]

/-- Evaluating the moved-point cost of `G.toCochain ht.mul_self_eq_one` on the `{1, t}`-valued
cut gauge of `S` gives twice the switched edge count
`#(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset`. -/
theorem cost_movedNorm_toCochain_ite_mem [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    (S : Set V) [DecidablePred (· ∈ S)] :
    (G.toCochain ht.mul_self_eq_one).cost (Equiv.Perm.movedNorm α)
        (fun v ↦ if v ∈ S then t else 1) =
      2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
  rw [G.cost_toCochain_ite_mem (Equiv.Perm.movedNorm α) ht.mul_self_eq_one S,
    ht.movedNorm, mul_comm]

/-- Evaluating the moved-point defect of `G.toCochain ht.mul_self_eq_one` gives twice
`#G.oddTripleFinset`. -/
theorem defect_movedNorm_toCochain [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self_eq_one).defect (Equiv.Perm.movedNorm α) = 2 * #G.oddTripleFinset := by
  rw [G.defect_toCochain (Equiv.Perm.movedNorm α) ht.mul_self_eq_one, ht.movedNorm, mul_comm]

/-- For any transposition `t` and any `Equiv.Perm α`-valued vertex gauge `β`, the moved-point cost
of `G.toCochain ht.mul_self_eq_one` under `β` is at least `2` times the edge count of `G` switched
by the odd-sign cut `{w | Equiv.Perm.sign (β w) = -1}`. -/
theorem two_mul_card_symmDiff_le_cost_movedNorm_toCochain [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    (β : V → Equiv.Perm α) :
    2 * (#(G ∆ (⊤ : SimpleGraph V).between {w | Equiv.Perm.sign (β w) = -1}
      {w | Equiv.Perm.sign (β w) = -1}ᶜ).edgeFinset : ℝ) ≤
      (G.toCochain ht.mul_self_eq_one).cost (Equiv.Perm.movedNorm α) β := by
  have hcomp : Equiv.Perm.parityRetract ht ∘ β =
      fun w ↦ if w ∈ {x | Equiv.Perm.sign (β x) = -1} then t else 1 :=
    funext fun w ↦ Equiv.Perm.parityRetract_eq_ite_sign_eq_neg_one ht (β w)
  have hle :=
    (G.toCochain ht.mul_self_eq_one).cost_map_le (Equiv.Perm.movedNorm_parityRetract_le ht) β
  simp only [SimpleGraph.map_toCochain, Equiv.Perm.parityRetract_self] at hle
  rwa [hcomp, G.cost_movedNorm_toCochain_ite_mem ht {w | Equiv.Perm.sign (β w) = -1}] at hle

/-- Whenever `G ∆ (⊤ : SimpleGraph V).between S Sᶜ` is cut-minimal, the `Equiv.Perm α` gauge
distance of `G.toCochain ht.mul_self_eq_one` equals
`2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset`. -/
theorem gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    {S : Set V} [DecidablePred (· ∈ S)]
    (hS : (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).IsCutMinimal) :
    (G.toCochain ht.mul_self_eq_one).gaugeDist (Equiv.Perm.movedNorm α) =
      2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
  refine le_antisymm ?_ (((G.toCochain ht.mul_self_eq_one).le_gaugeDist_iff _).mpr fun β ↦ ?_)
  · exact ((G.toCochain ht.mul_self_eq_one).gaugeDist_le_cost _
      (fun v ↦ if v ∈ S then t else 1)).trans_eq (G.cost_movedNorm_toCochain_ite_mem ht S)
  · let T : Set V := {w | Equiv.Perm.sign (β w) = -1}
    have hcard : #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset ≤
        #(G ∆ (⊤ : SimpleGraph V).between T Tᶜ).edgeFinset := by
      classical
      exact (hS.card_edgeFinset_le_symmDiff_top_between (S ∆ T)).trans_eq
        (card_edgeFinset_congr_of_eq <| by
          rw [symmDiff_top_between_symmDiff, symmDiff_symmDiff_cancel_left])
    have hcardR : (2 : ℝ) * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset ≤
        2 * #(G ∆ (⊤ : SimpleGraph V).between T Tᶜ).edgeFinset := by
      exact_mod_cast Nat.mul_le_mul_left 2 hcard
    exact hcardR.trans (G.two_mul_card_symmDiff_le_cost_movedNorm_toCochain ht β)

/-- Every finite ordered graph admits a finset cut switching it to a cut-minimal graph whose
doubled edge count equals the `Equiv.Perm α` gauge distance of `G.toCochain ht.mul_self_eq_one`. -/
theorem exists_finset_isCutMinimal_and_gaugeDist_movedNorm_toCochain_eq [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    ∃ s : Finset V, (G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).IsCutMinimal ∧
      (G.toCochain ht.mul_self_eq_one).gaugeDist (Equiv.Perm.movedNorm α) =
        2 * #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset := by
  obtain ⟨s, hs⟩ := G.exists_finset_isCutMinimal_symmDiff_top_between
  exact ⟨s, hs, G.gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff ht hs⟩

/-- **Cut-minimality via transposition gauge distance**: a finite ordered graph `G` is cut-minimal
if and only if the `Equiv.Perm α` gauge distance of `G.toCochain ht.mul_self_eq_one` equals
`2 * #G.edgeFinset` (Kozlov, Section 2; Beasley, Corollary 7). -/
theorem isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    {t : Equiv.Perm α} (ht : t.IsSwap) :
    G.IsCutMinimal ↔
      (G.toCochain ht.mul_self_eq_one).gaugeDist (Equiv.Perm.movedNorm α) = 2 * #G.edgeFinset := by
  classical
  constructor
  · intro hG
    have hG' : (G ∆ (⊤ : SimpleGraph V).between (∅ : Set V) (∅ : Set V)ᶜ).IsCutMinimal := by
      simpa using hG
    rw [G.gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff ht hG']
    exact congrArg (fun n : ℕ ↦ (2 : ℝ) * n) (card_edgeFinset_congr_of_eq (by simp))
  · intro h
    rw [isCutMinimal_iff_forall_finset_card_edgeFinset_le_symmDiff_top_between]
    intro s
    have hle := ((G.toCochain ht.mul_self_eq_one).gaugeDist_le_cost (Equiv.Perm.movedNorm α)
      (fun v ↦ if v ∈ (s : Set V) then t else 1)).trans_eq
      (G.cost_movedNorm_toCochain_ite_mem ht (s : Set V))
    rw [h] at hle
    norm_cast at hle
    exact (card_edgeFinset_congr_of_eq rfl).trans_le
      ((Nat.le_of_mul_le_mul_left hle two_pos).trans_eq (card_edgeFinset_congr_of_eq rfl))

/-- The `Equiv.Perm α` gauge distance of `G.toCochain ht.mul_self_eq_one` vanishes if and only if
`G` is a complete-graph cut. -/
theorem gaugeDist_movedNorm_toCochain_eq_zero_iff [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self_eq_one).gaugeDist (Equiv.Perm.movedNorm α) = 0 ↔
      ∃ S : Set V, G = (⊤ : SimpleGraph V).between S Sᶜ :=
  ((G.toCochain ht.mul_self_eq_one).gaugeDist_eq_zero_iff_isCoboundary _).trans
    (G.isCoboundary_toCochain_iff ht.mul_self_eq_one ht.isCycle.ne_one)

/-- **Cut-minimal graphs bound the permutation constant.** For a cut-minimal graph `G` on `V` with
at least one edge,
`h1 (complete V) (movedNorm α) ≤ #G.oddTripleFinset / #G.edgeFinset`. -/
theorem h1_complete_movedNorm_le_of_isCutMinimal [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsCutMinimal) (hE : 0 < #G.edgeFinset) :
    TauCeti.h1 (TauCeti.TwoComplex.complete V) (Equiv.Perm.movedNorm α) ≤
      (#G.oddTripleFinset : ℝ) / #G.edgeFinset := by
  rcases subsingleton_or_nontrivial α with hα | ⟨a, b, hab⟩
  · rw [TauCeti.h1_subsingleton]
    positivity
  have ht : (Equiv.swap a b).IsSwap := ⟨a, b, hab, rfl⟩
  have hE' : (0 : ℝ) < 2 * #G.edgeFinset := by positivity
  have hgd :
      (G.toCochain ht.mul_self_eq_one).gaugeDist (Equiv.Perm.movedNorm α) = 2 * #G.edgeFinset :=
    (G.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq ht).mp hG
  refine (TauCeti.h1_le_div (hgd ▸ hE')).trans_eq ?_
  rw [hgd, G.defect_movedNorm_toCochain ht]
  exact mul_div_mul_left _ _ two_ne_zero

end SwapGauge

end SimpleGraph

namespace TauCeti

section PermFinTwo

/-- **Ambient-degree invariance of transposition gauge distance**: the `Equiv.Perm α` gauge distance
of `G.toCochain ht.mul_self_eq_one` depends only on `G`, and coincides with the `Equiv.Perm (Fin 2)`
gauge distance of `simpleGraphEquivPermFinTwo V G`. -/
theorem _root_.SimpleGraph.gaugeDist_movedNorm_toCochain_eq_fin_two
    {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self_eq_one).gaugeDist (Equiv.Perm.movedNorm α) =
      (simpleGraphEquivPermFinTwo V G).gaugeDist (Equiv.Perm.movedNorm (Fin 2)) := by
  classical
  obtain ⟨s, hs⟩ := G.exists_finset_isCutMinimal_symmDiff_top_between
  rw [simpleGraphEquivPermFinTwo_eq_toCochain,
    G.gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff ht hs,
    G.gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff
      Equiv.Perm.isSwap_swap_zero_one_fin_two hs]

/-- **Cut-minimality via binary gauge distance**: a finite ordered graph `G` is cut-minimal if and
only if the `Equiv.Perm (Fin 2)` gauge distance of `simpleGraphEquivPermFinTwo V G` equals
`2 * #G.edgeFinset`. -/
theorem _root_.SimpleGraph.isCutMinimal_iff_gaugeDist_movedNorm_fin_two_eq
    {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.IsCutMinimal ↔
      (simpleGraphEquivPermFinTwo V G).gaugeDist (Equiv.Perm.movedNorm (Fin 2)) =
        2 * #G.edgeFinset := by
  rw [simpleGraphEquivPermFinTwo_eq_toCochain]
  exact G.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq Equiv.Perm.isSwap_swap_zero_one_fin_two

/-- **Binary edge-set cost bridge**: for any `Equiv.Perm (Fin 2)`-valued `1`-cochain `α` on
`TwoComplex.complete V` and gauge `β`, `α.cost (Equiv.Perm.movedNorm (Fin 2)) β` equals twice the
edge count of the support graph of `α` switched by the cut `{w | β w ≠ 1}`. -/
theorem Cochain.cost_movedNorm_fin_two {V : Type*} [Fintype V] [LinearOrder V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) (β : V → Equiv.Perm (Fin 2)) :
    α.cost (Equiv.Perm.movedNorm (Fin 2)) β =
      2 * #(α.supportGraph ∆
        (⊤ : SimpleGraph V).between {w | β w ≠ 1} {w | β w ≠ 1}ᶜ).edgeFinset := by
  have hβ : β = fun v ↦ if v ∈ {w | β w ≠ 1} then Equiv.swap 0 1 else 1 :=
    funext fun v ↦ Equiv.Perm.eq_ite_ne_one_fin_two (β v)
  conv_lhs => rw [← α.toCochain_supportGraph, hβ]
  exact α.supportGraph.cost_movedNorm_toCochain_ite_mem
    Equiv.Perm.isSwap_swap_zero_one_fin_two {w | β w ≠ 1}

/-- **Binary odd-triple defect bridge**: for any `Equiv.Perm (Fin 2)`-valued `1`-cochain `α` on
`TwoComplex.complete V`, `α.defect (Equiv.Perm.movedNorm (Fin 2))` equals twice the number of odd
triples of its support graph `α.supportGraph`. -/
theorem Cochain.defect_movedNorm_fin_two {V : Type*} [Fintype V] [LinearOrder V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    α.defect (Equiv.Perm.movedNorm (Fin 2)) =
      2 * #α.supportGraph.oddTripleFinset := by
  conv_lhs => rw [← α.toCochain_supportGraph]
  exact α.supportGraph.defect_movedNorm_toCochain Equiv.Perm.isSwap_swap_zero_one_fin_two

/-- **Binary cut-minimality characterization**: the support graph of
`α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))` is cut-minimal if and only if
`α.gaugeDist (Equiv.Perm.movedNorm (Fin 2))` equals twice its edge count. -/
theorem Cochain.isCutMinimal_supportGraph_fin_two_iff {V : Type*}
    [Fintype V] [LinearOrder V] (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    α.supportGraph.IsCutMinimal ↔
      α.gaugeDist (Equiv.Perm.movedNorm (Fin 2)) = 2 * #α.supportGraph.edgeFinset := by
  rw [α.supportGraph.isCutMinimal_iff_gaugeDist_movedNorm_fin_two_eq,
    simpleGraphEquivPermFinTwo_eq_toCochain, α.toCochain_supportGraph]

end PermFinTwo

end TauCeti
