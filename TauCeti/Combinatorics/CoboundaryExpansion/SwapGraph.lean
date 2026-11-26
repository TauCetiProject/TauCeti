/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
public import TauCeti.GroupTheory.Perm.DistErr.Basic
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Filter
import TauCeti.Algebra.Group.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Basic
import TauCeti.Combinatorics.SimpleGraph.OddTriple
import TauCeti.Combinatorics.SimpleGraph.OrderedEdges
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.DistErr.Invariance
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.GroupTheory.Perm.ParityRetract

/-!
# Transposition-labelled graph cochains, cut-minimality, and cross-degree gauge bounds

Given a simple graph `G` on a linearly ordered finite vertex type `V` and a transposition `τ` in a
symmetric group `Equiv.Perm A`, assigning `τ` to edges of `G` and `1` to non-edges produces an
inversion-symmetric permutation edge assignment whose holonomy and gauge costs reduce to graph
combinatorics via the transposition-holonomy and parity-retracted edge bounds in
`TauCeti.GroupTheory.Perm.MovedNorm` and `TauCeti.GroupTheory.Perm.ParityRetract`:

* **Binary edge-set dictionary, degree-independent gauge distance, and cut-minimality**
  (`TauCeti.perm_fin_two_eq_ite_fromRel`,
  `SimpleGraph.sum_filter_lt_movedNorm_triple_ite_isSwap`,
  `SimpleGraph.sum_filter_lt_movedNorm_ite_isSwap_of_forall_eq_one_or`,
  `SimpleGraph.ciInf_sum_filter_lt_movedNorm_ite_isSwap`, and
  `SimpleGraph.ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff`): loop-free
  inversion-symmetric `Perm (Fin 2)` assignments correspond bijectively to simple graphs, the
  triangle holonomy defect equals twice the number of `3`-vertex subsets spanning an odd number of
  edges, the `movedNorm` gauge-cost infimum over `V → Perm A` equals twice the minimum cut-toggled
  edge count independently of `A` and `τ`, and this infimum equals `2 * #G.edgeFinset` if and only
  if `G.IsCutMinimal`.
* **Cross-degree gauge optimization for cut-minimal graphs and Kozlov's parameters**
  (`SimpleGraph.ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff`,
  `SimpleGraph.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_isCutMinimal`,
  `SimpleGraph.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_pos`,
  `SimpleGraph.normalized_defect_div_ciInf₂_distErr_three_ite_isSwap_eq_card_div_three`,
  `TauCeti.eight_mul_half_lt_three_mul_choose_two_kozlov`, and
  `SimpleGraph.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_kozlov`): when `G.IsCutMinimal` and
  `8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2`, no unequal-degree gauge in `Perm (Fin m)`
  (`m ≠ 3`) beats the degree-`3` transposition gauge-cost infimum `2 * #G.edgeFinset / 3`, giving a
  strictly positive global cross-degree infimum whenever `G.edgeFinset.Nonempty` and normalized
  ratio `Fintype.card V / 3` whenever the odd-triangle count is
  `(Fintype.card V / 3) * #G.edgeFinset`. In particular, for Kozlov's parameters
  `Fintype.card V = q * (2 * t + 1)` and `#G.edgeFinset = q ^ 2 * t * (t + 1) / 2` (`q, t ≥ 1`), the
  global cross-degree infimum over all gauge degrees `m + 2 ≥ 2` equals
  `q ^ 2 * t * (t + 1) / 3`.

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, Section 2 and
  Theorem 4.2.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Section 2.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, doi:10.5281/zenodo.23245792, Corollary 7, Theorem 8, and Proposition 10.
-/

public section

open Equiv Equiv.Perm Finset
open scoped symmDiff

/-! ### Binary edge-set dictionary, degree-independent gauge distance, and cut-minimality -/

namespace TauCeti

/-- Every loop-free inversion-symmetric assignment `α : V → V → Perm (Fin 2)` agrees everywhere with
the `Equiv.swap 0 1` edge indicator of `SimpleGraph.fromRel (fun a b => α a b ≠ 1)`. -/
theorem perm_fin_two_eq_ite_fromRel {V : Type*} [DecidableEq V] (α : V → V → Perm (Fin 2))
    (hdiag : ∀ v, α v v = 1) (hinv : ∀ u v, α v u = (α u v)⁻¹) (u v : V) :
    α u v = if (SimpleGraph.fromRel fun a b => α a b ≠ 1).Adj u v then Equiv.swap 0 1 else 1 := by
  by_cases huv : u = v
  · subst huv
    simp [hdiag u]
  · have hsymm : α v u ≠ 1 ↔ α u v ≠ 1 := by rw [hinv u v, inv_ne_one]
    rcases eq_one_or_swap_fin_two (α u v) with h | h
    · simp [SimpleGraph.fromRel_adj, huv, hsymm, h]
    · have hne : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by decide
      simp [SimpleGraph.fromRel_adj, huv, hsymm, h, hne]

end TauCeti

namespace SimpleGraph

section GraphBridge

variable {V A : Type*} [Fintype V] [LinearOrder V] [Fintype A] [DecidableEq A]

/-- For any transposition `τ : Perm A`, the moved-point triangle defect of the `τ`-labelled graph
`G` equals twice the number of `3`-element subsets of `V` spanning an odd number of edges in `G`. -/
theorem sum_filter_lt_movedNorm_triple_ite_isSwap (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm A} (hτ : τ.IsSwap) :
    (∑ t ∈ ({t : V × V × V | t.1 < t.2.1 ∧ t.2.1 < t.2.2} : Finset (V × V × V)),
        movedNorm A ((if G.Adj t.1 t.2.1 then τ else 1) *
          (if G.Adj t.2.1 t.2.2 then τ else 1) * (if G.Adj t.2.2 t.1 then τ else 1))) =
      2 * (#{s ∈ (univ : Finset V).powersetCard 3 |
        Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} : ℝ) := by
  simp_rw [movedNorm_mul_triple_ite_isSwap hτ]
  rw [sum_ite_zero_eq_nsmul, nsmul_eq_mul, mul_comm _ (2 : ℝ), filter_filter,
    ← G.card_filter_lt_xor_adj_triple_eq_card_powersetCard_three_odd]
  congr 3
  ext t
  simp [and_assoc]

/-- Variant of `SimpleGraph.sum_filter_lt_movedNorm_triple_ite_isSwap` using `(α u w)⁻¹` on the
third edge of each increasing triple `(u, v, w)`. -/
theorem sum_filter_lt_movedNorm_triple_ite_inv_isSwap (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm A} (hτ : τ.IsSwap) :
    (∑ t ∈ ({t : V × V × V | t.1 < t.2.1 ∧ t.2.1 < t.2.2} : Finset (V × V × V)),
        movedNorm A ((if G.Adj t.1 t.2.1 then τ else 1) *
          (if G.Adj t.2.1 t.2.2 then τ else 1) * (if G.Adj t.1 t.2.2 then τ else 1)⁻¹)) =
      2 * (#{s ∈ (univ : Finset V).powersetCard 3 |
        Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} : ℝ) := by
  refine (sum_congr rfl fun t _ => ?_).trans (G.sum_filter_lt_movedNorm_triple_ite_isSwap hτ)
  rw [TauCeti.ite_inv_of_mul_self hτ.mul_self_eq_one]
  simp only [G.adj_comm t.1 t.2.2]

/-- For a `{1, τ}`-valued vertex gauge `β`, the moved-point gauge cost of the `τ`-labelled graph `G`
equals twice the number of edges after toggling the cut `{v | β v ≠ 1}`. -/
theorem sum_filter_lt_movedNorm_ite_isSwap_of_forall_eq_one_or (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm A} (hτ : τ.IsSwap) {β : V → Perm A}
    (hβ : ∀ v, β v = 1 ∨ β v = τ) :
    (∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2)) =
      2 * (#(G.edgeFinset ∆
        ((⊤ : SimpleGraph V).between {v | β v ≠ 1} {v | β v ≠ 1}ᶜ).edgeFinset) : ℝ) := by
  have hcongr (e : V × V) :
      movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2) =
        if Xor (G.Adj e.1 e.2) (Xor (β e.1 ≠ 1) (β e.2 ≠ 1)) then 2 else 0 :=
    movedNorm_inv_mul_ite_mul_of_eq_one_or hτ (hβ e.1) (hβ e.2) _
  simp_rw [hcongr]
  rw [sum_ite_zero_eq_nsmul, nsmul_eq_mul, mul_comm _ (2 : ℝ), filter_filter,
    ← G.card_filter_lt_xor_adj_eq_card_symmDiff_edgeFinset {v | β v ≠ 1}]
  rfl

/-- Evaluating the `τ`-labelled graph `G` at the indicator gauge `fun v => if v ∈ S then τ else 1`
gives moved-point cost `2 * #(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset)`. -/
theorem sum_filter_lt_movedNorm_ite_isSwap_indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm A} (hτ : τ.IsSwap) (S : Set V) [DecidablePred (· ∈ S)] :
    (∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        movedNorm A ((if e.1 ∈ S then τ else 1)⁻¹ *
          (if G.Adj e.1 e.2 then τ else 1) * (if e.2 ∈ S then τ else 1))) =
      2 * (#(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) : ℝ) := by
  let β : V → Perm A := fun v => if v ∈ S then τ else 1
  have hβ (v : V) : β v = 1 ∨ β v = τ := by
    dsimp only [β]
    split_ifs <;> simp
  have hset : {v : V | β v ≠ 1} = S := by
    ext v
    simp [β, hτ.isCycle.ne_one]
  have heq :
      ((⊤ : SimpleGraph V).between {v | β v ≠ 1} {v | β v ≠ 1}ᶜ).edgeFinset =
        ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
    ext e
    simp [hset]
  simpa only [β, heq] using G.sum_filter_lt_movedNorm_ite_isSwap_of_forall_eq_one_or hτ hβ

/-- At the trivial gauge `fun _ => 1`, the moved-point cost of the `τ`-labelled graph `G` equals
`2 * #G.edgeFinset`. -/
theorem sum_filter_lt_movedNorm_ite_isSwap_one (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm A} (hτ : τ.IsSwap) :
    (∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        movedNorm A (if G.Adj e.1 e.2 then τ else 1)) =
      2 * (#G.edgeFinset : ℝ) := by
  have hcongr (e : V × V) :
      movedNorm A (if G.Adj e.1 e.2 then τ else 1) = if G.Adj e.1 e.2 then 2 else 0 := by
    split_ifs <;> simp [hτ.movedNorm]
  simp_rw [hcongr]
  rw [sum_ite_zero_eq_nsmul, nsmul_eq_mul, mul_comm _ (2 : ℝ), filter_filter,
    G.card_filter_lt_adj_eq_card_edgeFinset]

/-- In `Perm (Fin 2)`, every gauge `β : V → Perm (Fin 2)` has moved-point cost equal to twice the
edge count of `G` after toggling the cut `{v | β v ≠ 1}`. -/
theorem sum_filter_lt_movedNorm_fin_two_ite_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : V → Perm (Fin 2)) :
    (∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        movedNorm (Fin 2) ((β e.1)⁻¹ *
          (if G.Adj e.1 e.2 then Equiv.swap 0 1 else 1) * β e.2)) =
      2 * (#(G.edgeFinset ∆
        ((⊤ : SimpleGraph V).between {v | β v ≠ 1} {v | β v ≠ 1}ᶜ).edgeFinset) : ℝ) :=
  G.sum_filter_lt_movedNorm_ite_isSwap_of_forall_eq_one_or
    (swap_isSwap_iff.mpr (by decide : (0 : Fin 2) ≠ 1)) fun v => eq_one_or_swap_fin_two (β v)

/-- For an arbitrary gauge `β : V → Perm A`, the moved-point cost of the `τ`-labelled graph `G` is
at least twice the edge count after toggling the cut `{v | sign (β v) = -1}` of odd-sign vertices.
-/
theorem two_mul_card_symmDiff_le_sum_filter_lt_movedNorm_ite_isSwap (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm A} (hτ : τ.IsSwap) (β : V → Perm A) :
    2 * (#(G.edgeFinset ∆
        ((⊤ : SimpleGraph V).between {v | sign (β v) = -1}
          {v | sign (β v) = -1}ᶜ).edgeFinset) : ℝ) ≤
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2) := by
  have hsum := sum_le_sum fun e (_ : e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V))) =>
    ite_xor_sign_le_movedNorm_inv_mul_ite_mul hτ (β e.1) (β e.2) (G.Adj e.1 e.2)
  rw [sum_ite_zero_eq_nsmul, nsmul_eq_mul, mul_comm _ (2 : ℝ), filter_filter] at hsum
  have hcard := G.card_filter_lt_xor_adj_eq_card_symmDiff_edgeFinset {v | sign (β v) = -1}
  exact (congrArg (fun n : ℕ => 2 * (n : ℝ)) hcard.symm).trans_le hsum

/-- The moved-point gauge-cost infimum of a `τ`-labelled graph `G` over `V → Perm A` equals twice
the infimum of cut-toggled edge counts, independently of the ambient set `A` and transposition `τ`.
-/
theorem ciInf_sum_filter_lt_movedNorm_ite_isSwap (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm A} (hτ : τ.IsSwap) :
    (⨅ β : V → Perm A,
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2)) =
      2 * ⨅ S : Finset V,
        (#(G.edgeFinset ∆
          ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset) : ℝ) := by
  let cost (β : V → Perm A) : ℝ :=
    ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
      movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2)
  let cutCard (S : Finset V) : ℝ :=
    #(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset)
  have hbdd_cost : BddBelow (Set.range cost) :=
    ⟨0, by rintro _ ⟨β, rfl⟩; exact sum_nonneg fun _ _ => apply_nonneg (movedNorm A) _⟩
  have hbdd_cut : BddBelow (Set.range cutCard) :=
    ⟨0, by rintro _ ⟨S, rfl⟩; exact Nat.cast_nonneg _⟩
  refine le_antisymm ?_ ?_
  · have hdiv : (⨅ β, cost β) / 2 ≤ ⨅ S, cutCard S := by
      refine le_ciInf fun S => (div_le_iff₀' (by norm_num : (0 : ℝ) < 2)).mpr ?_
      refine (ciInf_le hbdd_cost (fun v => if v ∈ (S : Set V) then τ else 1)).trans_eq ?_
      exact G.sum_filter_lt_movedNorm_ite_isSwap_indicator hτ (S : Set V)
    exact (div_le_iff₀' (by norm_num : (0 : ℝ) < 2)).mp hdiv
  · refine le_ciInf fun β => ?_
    let S : Finset V := {v : V | sign (β v) = -1}
    have hS :
        ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset =
          ((⊤ : SimpleGraph V).between {v | sign (β v) = -1}
            {v | sign (β v) = -1}ᶜ).edgeFinset := by
      ext e
      simp [S]
    refine (mul_le_mul_of_nonneg_left (ciInf_le hbdd_cut S) (by norm_num)).trans ?_
    dsimp only [cutCard, cost]
    rw [hS]
    exact G.two_mul_card_symmDiff_le_sum_filter_lt_movedNorm_ite_isSwap hτ β

/-- Any two transpositions `τ₁ : Perm A` and `τ₂ : Perm B` induce the same moved-point gauge-cost
infimum on `G`. -/
theorem ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq {B : Type*} [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) [DecidableRel G.Adj] {τ₁ : Perm A} {τ₂ : Perm B}
    (hτ₁ : τ₁.IsSwap) (hτ₂ : τ₂.IsSwap) :
    (⨅ β : V → Perm A,
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ₁ else 1) * β e.2)) =
      ⨅ β : V → Perm B,
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          movedNorm B ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ₂ else 1) * β e.2) := by
  rw [G.ciInf_sum_filter_lt_movedNorm_ite_isSwap hτ₁,
    G.ciInf_sum_filter_lt_movedNorm_ite_isSwap hτ₂]

/-- The moved-point gauge-cost infimum of a `τ`-labelled graph `G` over `V → Perm A` equals
`2 * #G.edgeFinset` if and only if `G` is cut-minimal. -/
theorem ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm A} (hτ : τ.IsSwap) :
    (⨅ β : V → Perm A,
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2)) =
      2 * (#G.edgeFinset : ℝ) ↔ G.IsCutMinimal := by
  let f (S : Finset V) : ℕ :=
    #(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset)
  have hcast : ((⨅ S, f S : ℕ) : ℝ) = ⨅ S, (f S : ℝ) := by
    simpa only [iInf, ← Set.range_comp, Function.comp_def] using
      (Set.finite_range f).map_sInf_of_monotone (Set.range_nonempty f) Nat.mono_cast
  rw [G.ciInf_sum_filter_lt_movedNorm_ite_isSwap hτ,
    mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0), ← hcast, Nat.cast_inj,
    G.ciInf_card_symmDiff_edgeFinset_eq_iff]

/-- A cut-minimal graph `G` with at least one edge has strictly positive moved-point gauge-cost
infimum for any transposition `τ : Perm A`. -/
theorem ciInf_sum_filter_lt_movedNorm_ite_isSwap_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm A} (hτ : τ.IsSwap) (hcut : G.IsCutMinimal) (hne : G.edgeFinset.Nonempty) :
    0 < ⨅ β : V → Perm A,
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2) := by
  have hEpos : (0 : ℝ) < #G.edgeFinset := Nat.cast_pos.mpr hne.card_pos
  rw [(G.ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff hτ).mpr hcut]
  positivity

/-- When `G` is cut-minimal with at least one edge and its odd-edge `3`-subsets number
`(Fintype.card V / 3) * #G.edgeFinset`, the `τ`-labelled graph `G` in `Perm A` has defect-to-gauge
ratio `Fintype.card V / 3`. -/
theorem defect_div_ciInf_movedNorm_ite_isSwap_eq_card_div_three (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm A} (hτ : τ.IsSwap) (hcut : G.IsCutMinimal)
    (hne : G.edgeFinset.Nonempty)
    (hodd : (#{s ∈ (univ : Finset V).powersetCard 3 |
        Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} : ℝ) =
      (Fintype.card V : ℝ) / 3 * #G.edgeFinset) :
    ((∑ t ∈ ({t : V × V × V | t.1 < t.2.1 ∧ t.2.1 < t.2.2} : Finset (V × V × V)),
        movedNorm A ((if G.Adj t.1 t.2.1 then τ else 1) *
          (if G.Adj t.2.1 t.2.2 then τ else 1) * (if G.Adj t.2.2 t.1 then τ else 1))) /
      ⨅ β : V → Perm A,
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2)) =
      (Fintype.card V : ℝ) / 3 := by
  have hEpos : (0 : ℝ) < #G.edgeFinset := Nat.cast_pos.mpr hne.card_pos
  rw [(G.ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff hτ).mpr hcut,
    G.sum_filter_lt_movedNorm_triple_ite_isSwap hτ, hodd]
  have h2E : (2 * (#G.edgeFinset : ℝ)) ≠ 0 := by positivity
  field_simp [h2E]

end GraphBridge

/-! ### Equal-degree and cross-degree (`distErr`) optimization for cut-minimal graphs -/

section CrossDegree

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- In equal degree `n`, the `distErr` gauge-cost infimum of a `τ`-labelled graph `G` (`τ.IsSwap`)
equals `2 / n` times the minimum cut-toggled edge count. -/
theorem ciInf_sum_filter_lt_distErr_ite_isSwap {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm (Fin n)} (hτ : τ.IsSwap) :
    (⨅ β : V → Perm (Fin n),
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)) =
      2 * (⨅ S : Finset V,
        (#(G.edgeFinset ∆
          ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset) : ℝ)) / n := by
  have hn2 : 2 ≤ n := hτ.two_le
  have : NeZero n := ⟨by omega⟩
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let mcost (β : V → Perm (Fin n)) : ℝ :=
    ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
      movedNorm (Fin n) ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2)
  have hterm (β : V → Perm (Fin n)) :
      (∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)) = mcost β / n := by
    simp_rw [distErr_mul_inv_eq_movedNorm_div, div_eq_mul_inv, ← sum_mul, mcost]
  simp_rw [hterm]
  have hbdd : BddBelow (Set.range mcost) :=
    ⟨0, by rintro _ ⟨β, rfl⟩; exact sum_nonneg fun _ _ => apply_nonneg (movedNorm (Fin n)) _⟩
  rw [← G.ciInf_sum_filter_lt_movedNorm_ite_isSwap hτ]
  simpa only [OrderIso.divRight₀_apply] using
    ((OrderIso.divRight₀ (n : ℝ) hn_pos).map_ciInf hbdd).symm

/-- In equal degree `n`, the `distErr` gauge-cost infimum of a `τ`-labelled graph `G` (`τ.IsSwap`)
equals `2 * #G.edgeFinset / n` if and only if `G` is cut-minimal. -/
theorem ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff {n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm (Fin n)} (hτ : τ.IsSwap) :
    (⨅ β : V → Perm (Fin n),
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)) =
      2 * (#G.edgeFinset : ℝ) / n ↔ G.IsCutMinimal := by
  have hn2 : 2 ≤ n := hτ.two_le
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [G.ciInf_sum_filter_lt_distErr_ite_isSwap hτ, div_left_inj₀ hn_ne,
    ← G.ciInf_sum_filter_lt_movedNorm_ite_isSwap hτ,
    G.ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff hτ]

/-- If `G` is cut-minimal and `8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2`, then every gauge
`β : V → Perm (Fin m)` of every degree `m : ℕ` has cross-degree cost at least
`2 * #G.edgeFinset / 3` against a `Perm (Fin 3)` transposition labelling of `G`. -/
theorem two_mul_card_div_three_le_sum_filter_lt_distErr_three_ite_isSwap (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm (Fin 3)} (hτ : τ.IsSwap) (hcut : G.IsCutMinimal)
    (hdens : 8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2) {m : ℕ}
    (β : V → Perm (Fin m)) :
    2 * (#G.edgeFinset : ℝ) / 3 ≤
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹) := by
  by_cases hm : m = 3
  · subst hm
    have hbdd : BddBelow (Set.range fun β' : V → Perm (Fin 3) =>
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then τ else 1) (β' e.1 * (β' e.2)⁻¹)) :=
      ⟨0, by rintro _ ⟨β', rfl⟩; exact sum_nonneg fun _ _ => distErr_nonneg _ _⟩
    exact ((G.ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff hτ).mpr hcut).symm.trans_le
      (ciInf_le hbdd β)
  · refine le_trans ?_
      (TauCeti.choose_two_div_four_le_sum_filter_lt_distErr_three_of_ne
        (fun u v => if G.Adj u v then τ else 1) β hm)
    have hdens' : 8 * (#G.edgeFinset : ℝ) ≤ 3 * ((Fintype.card V).choose 2 : ℝ) := by
      exact_mod_cast hdens
    linarith

/-- If `G` is cut-minimal and `8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2`, then the global
cross-degree gauge-cost infimum over all gauge degrees `m + 2 ≥ 2` for a `Perm (Fin 3)`
transposition labelling of `G` equals `2 * #G.edgeFinset / 3`, attained in equal degree `3`. -/
theorem ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_isCutMinimal (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm (Fin 3)} (hτ : τ.IsSwap) (hcut : G.IsCutMinimal)
    (hdens : 8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)) =
      2 * (#G.edgeFinset : ℝ) / 3 := by
  let f (m : ℕ) : ℝ := ⨅ β : V → Perm (Fin (m + 2)),
    ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
      distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)
  have hf_ge (m : ℕ) : 2 * (#G.edgeFinset : ℝ) / 3 ≤ f m :=
    le_ciInf (G.two_mul_card_div_three_le_sum_filter_lt_distErr_three_ite_isSwap hτ hcut hdens)
  have hbdd : BddBelow (Set.range f) :=
    ⟨2 * (#G.edgeFinset : ℝ) / 3, by rintro _ ⟨m, rfl⟩; exact hf_ge m⟩
  refine le_antisymm ?_ (le_ciInf hf_ge)
  exact (ciInf_le hbdd 1).trans_eq ((G.ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff hτ).mpr hcut)

/-- If `G` is cut-minimal with `8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2` and at least one
edge, then its `Perm (Fin 3)` transposition labelling has strictly positive global cross-degree
gauge-cost infimum over all gauge degrees `m + 2 ≥ 2`. -/
theorem ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_pos (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm (Fin 3)} (hτ : τ.IsSwap) (hcut : G.IsCutMinimal)
    (hdens : 8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2) (hne : G.edgeFinset.Nonempty) :
    0 < ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹) := by
  have hEpos : (0 : ℝ) < #G.edgeFinset := Nat.cast_pos.mpr hne.card_pos
  rw [G.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_isCutMinimal hτ hcut hdens]
  positivity

/-- If `G` is cut-minimal with `8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2`, at least one
edge, and odd-edge `3`-subset count `(Fintype.card V / 3) * #G.edgeFinset`, then its `Perm (Fin 3)`
transposition labelling has normalized cross-degree defect-to-gauge ratio `Fintype.card V / 3`. -/
theorem normalized_defect_div_ciInf₂_distErr_three_ite_isSwap_eq_card_div_three
    (G : SimpleGraph V) [DecidableRel G.Adj] {τ : Perm (Fin 3)} (hτ : τ.IsSwap)
    (hcut : G.IsCutMinimal) (hdens : 8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2)
    (hne : G.edgeFinset.Nonempty)
    (hodd : (#{s ∈ (univ : Finset V).powersetCard 3 |
        Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} : ℝ) =
      (Fintype.card V : ℝ) / 3 * #G.edgeFinset) :
    (((∑ tr ∈ ({tr : V × V × V | tr.1 < tr.2.1 ∧ tr.2.1 < tr.2.2} : Finset (V × V × V)),
        movedNorm (Fin 3) ((if G.Adj tr.1 tr.2.1 then τ else 1) *
          (if G.Adj tr.2.1 tr.2.2 then τ else 1) *
            (if G.Adj tr.2.2 tr.1 then τ else 1))) / 3) /
      ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)) =
      (Fintype.card V : ℝ) / 3 := by
  have hEpos : (0 : ℝ) < #G.edgeFinset := Nat.cast_pos.mpr hne.card_pos
  rw [G.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_isCutMinimal hτ hcut hdens,
    G.sum_filter_lt_movedNorm_triple_ite_isSwap hτ, hodd]
  have hEne : (#G.edgeFinset : ℝ) ≠ 0 := hEpos.ne'
  field_simp [hEne]

end CrossDegree

end SimpleGraph

/-! ### Kozlov parameter arithmetic and cross-degree staircase consequences -/

private theorem two_mul_cast_half_kozlov (q t : ℕ) :
    2 * ((q ^ 2 * t * (t + 1) / 2 : ℕ) : ℝ) = (q : ℝ) ^ 2 * t * (t + 1) := by
  have heven : 2 ∣ q ^ 2 * t * (t + 1) := by
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right (Nat.even_mul_succ_self t).two_dvd _
  have hnat : 2 * (q ^ 2 * t * (t + 1) / 2) = q ^ 2 * t * (t + 1) := by
    rw [mul_comm, Nat.div_mul_cancel heven]
  exact_mod_cast hnat

namespace TauCeti

/-- For `1 ≤ q` and `1 ≤ t`, eight times Kozlov's staircase edge count `q ^ 2 * t * (t + 1) / 2` is
strictly smaller than three times `(q * (2 * t + 1)).choose 2`. -/
theorem eight_mul_half_lt_three_mul_choose_two_kozlov {q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) :
    8 * (q ^ 2 * t * (t + 1) / 2) < 3 * (q * (2 * t + 1)).choose 2 := by
  have heven_t : 2 ∣ q ^ 2 * t * (t + 1) := by
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right (Nat.even_mul_succ_self t).two_dvd _
  have heven_c : 2 ∣ (q * (2 * t + 1)) * (q * (2 * t + 1) - 1) :=
    (Nat.even_mul_pred_self (q * (2 * t + 1))).two_dvd
  rw [Nat.choose_two_right]
  refine lt_of_mul_lt_mul_right ?_ (by decide : 0 ≤ 2)
  rw [mul_assoc 8, Nat.div_mul_cancel heven_t, mul_assoc 3, Nat.div_mul_cancel heven_c]
  rcases Nat.exists_eq_add_of_le' hq with ⟨q', rfl⟩
  rcases Nat.exists_eq_add_of_le' ht with ⟨t', rfl⟩
  have hsub : (q' + 1) * (2 * (t' + 1) + 1) - 1 = 2 * q' * t' + 3 * q' + 2 * t' + 2 := by
    have hexp : (q' + 1) * (2 * (t' + 1) + 1) = (2 * q' * t' + 3 * q' + 2 * t' + 2) + 1 := by
      ring
    omega
  rw [hsub]
  have hlt : 6 * (t' + 1) + 3 < (q' + 1) * (4 * (t' + 1) ^ 2 + 4 * (t' + 1) + 3) := by nlinarith
  have hdiff : 3 * ((q' + 1) * (2 * (t' + 1) + 1) * (2 * q' * t' + 3 * q' + 2 * t' + 2)) =
      8 * ((q' + 1) ^ 2 * (t' + 1) * (t' + 1 + 1)) +
        (q' + 1) * ((q' + 1) * (4 * (t' + 1) ^ 2 + 4 * (t' + 1) + 3) -
          (6 * (t' + 1) + 3)) := by
    zify [hlt.le]
    ring
  have hpos : 0 < (q' + 1) *
      ((q' + 1) * (4 * (t' + 1) ^ 2 + 4 * (t' + 1) + 3) - (6 * (t' + 1) + 3)) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hlt)
  omega

/-- On a vertex set of size `q * (2 * t + 1)` (`1 ≤ q`, `1 ≤ t`), every unequal-degree gauge
`β : V → Perm (Fin m)` (`m ≠ 3`) has cross-degree cost strictly exceeding
`q ^ 2 * t * (t + 1) / 3` against any degree-`3` edge assignment `α`. -/
theorem lt_sum_filter_lt_distErr_three_of_kozlov_of_ne {V : Type*} [Fintype V] [LinearOrder V]
    {q t m : ℕ} (α : V → V → Perm (Fin 3)) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (hV : Fintype.card V = q * (2 * t + 1)) (β : V → Perm (Fin m)) (hm : m ≠ 3) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 <
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  have hdens : 8 * (q ^ 2 * t * (t + 1) / 2) < 3 * (Fintype.card V).choose 2 := by
    rw [hV]
    exact eight_mul_half_lt_three_mul_choose_two_kozlov hq ht
  have hlt := two_mul_div_three_lt_sum_filter_lt_distErr_three_of_ne α hdens β hm
  rwa [two_mul_cast_half_kozlov] at hlt

end TauCeti

namespace SimpleGraph

section Kozlov

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- For any cut-minimal graph `G` with Kozlov's parameters `Fintype.card V = q * (2 * t + 1)` and
`#G.edgeFinset = q ^ 2 * t * (t + 1) / 2` (`1 ≤ q`, `1 ≤ t`), the global cross-degree gauge-cost
infimum over all gauge degrees `m + 2 ≥ 2` equals `q ^ 2 * t * (t + 1) / 3`. -/
theorem ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_kozlov {q t : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm (Fin 3)} (hτ : τ.IsSwap) (hcut : G.IsCutMinimal)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hV : Fintype.card V = q * (2 * t + 1))
    (hE : #G.edgeFinset = q ^ 2 * t * (t + 1) / 2) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)) =
      (q : ℝ) ^ 2 * t * (t + 1) / 3 := by
  have hdens : 8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2 := by
    rw [hE, hV]
    exact (TauCeti.eight_mul_half_lt_three_mul_choose_two_kozlov hq ht).le
  rw [G.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_isCutMinimal hτ hcut hdens, hE,
    two_mul_cast_half_kozlov]

/-- Under Kozlov's staircase hypotheses (`1 ≤ q`, `1 ≤ t`), the `Perm (Fin 3)`
transposition-labelled graph `G` has strictly positive global cross-degree gauge-cost infimum. -/
theorem ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_pos_of_kozlov {q t : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm (Fin 3)} (hτ : τ.IsSwap) (hcut : G.IsCutMinimal)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hV : Fintype.card V = q * (2 * t + 1))
    (hE : #G.edgeFinset = q ^ 2 * t * (t + 1) / 2) :
    0 < ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹) := by
  have hdens : 8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2 := by
    rw [hE, hV]
    exact (TauCeti.eight_mul_half_lt_three_mul_choose_two_kozlov hq ht).le
  have h2le : 1 * 1 * 2 ≤ q ^ 2 * t * (t + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow 2 q hq) ht) (by omega)
  have hne : G.edgeFinset.Nonempty := card_pos.mp (by omega)
  exact G.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_pos hτ hcut hdens hne

/-- Under Kozlov's staircase hypotheses together with odd-triangle count
`(Fintype.card V / 3) * #G.edgeFinset`, the `Perm (Fin 3)` transposition-labelled graph `G` has
normalized cross-degree defect-to-gauge ratio `Fintype.card V / 3`. -/
theorem normalized_defect_div_ciInf₂_distErr_three_ite_isSwap_eq_of_kozlov {q t : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] {τ : Perm (Fin 3)} (hτ : τ.IsSwap)
    (hcut : G.IsCutMinimal) (hq : 1 ≤ q) (ht : 1 ≤ t) (hV : Fintype.card V = q * (2 * t + 1))
    (hE : #G.edgeFinset = q ^ 2 * t * (t + 1) / 2)
    (hodd : (#{s ∈ (univ : Finset V).powersetCard 3 |
        Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} : ℝ) =
      (Fintype.card V : ℝ) / 3 * #G.edgeFinset) :
    (((∑ tr ∈ ({tr : V × V × V | tr.1 < tr.2.1 ∧ tr.2.1 < tr.2.2} : Finset (V × V × V)),
        movedNorm (Fin 3) ((if G.Adj tr.1 tr.2.1 then τ else 1) *
          (if G.Adj tr.2.1 tr.2.2 then τ else 1) *
            (if G.Adj tr.2.2 tr.1 then τ else 1))) / 3) /
      ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)) =
      (Fintype.card V : ℝ) / 3 := by
  have hdens : 8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2 := by
    rw [hE, hV]
    exact (TauCeti.eight_mul_half_lt_three_mul_choose_two_kozlov hq ht).le
  have h2le : 1 * 1 * 2 ≤ q ^ 2 * t * (t + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow 2 q hq) ht) (by omega)
  have hne : G.edgeFinset.Nonempty := card_pos.mp (by omega)
  exact G.normalized_defect_div_ciInf₂_distErr_three_ite_isSwap_eq_card_div_three
    hτ hcut hdens hne hodd

end Kozlov

end SimpleGraph
