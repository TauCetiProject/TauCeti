/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
public import TauCeti.Data.Fin.Basic
public import TauCeti.GroupTheory.Perm.ParityRetract
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Transposition cochains, parity-retracted gauges, and four-vertex binary exactness

Given a simple graph `G` on a vertex type `V` and an element `c` of order at most two (`c * c = 1`)
in a group `Γ`, assigning `c` to adjacent vertex pairs and `1` to non-adjacent pairs defines a
skew-symmetric `Γ`-valued edge labelling on the complete graph on `V`:

* conjugating edge values by a binary vertex gauge `v ↦ if v ∈ S then c else 1` switches `G` to
  `G ∆ (⊤ : SimpleGraph V).between S Sᶜ` (`SimpleGraph.ite_mem_inv_mul_ite_adj_mul`);
* the directed triangle holonomy around `(u, v, w)` equals `c` when `(u, v, w)` spans an odd
  number of edges of `G` and `1` otherwise (`SimpleGraph.ite_adj_mul_ite_adj_mul_ite_adj`).

Specializing `Γ` to a finite symmetric group `Equiv.Perm α` and `c` to a transposition
`ht : t.IsSwap` under `Equiv.Perm.movedNorm α` connects arbitrary `Equiv.Perm α`-valued gauges to
cut-minimality via `Equiv.Perm.parityRetract`:

* retracting the gauged edge `(β u)⁻¹ * (if G.Adj u v then t else 1) * β v` gives the binary gauge
  of the odd-sign cut `{w | Equiv.Perm.sign (β w) = -1}`, yielding the lower bound
  `2 * #(G ∆ (⊤).between S Sᶜ).edgeFinset ≤ cost(β)` for every `Equiv.Perm α`-valued gauge `β`
  (`SimpleGraph.two_mul_card_symmDiff_le_sum_movedNorm`);
* the gauge-cost infimum over `β : V → Equiv.Perm α` is attained by a `{1, t}`-valued cut gauge at
  any cut-minimal switching of `G` (`SimpleGraph.iInf_sum_movedNorm_eq_of_isCutMinimal_symmDiff`),
  so it coincides with the infimum over `Subgroup.zpowers t`
  (`SimpleGraph.iInf_sum_movedNorm_zpowers_eq`) and with the `Equiv.Perm (Fin 2)` infimum
  (`SimpleGraph.iInf_sum_movedNorm_eq_iInf_fin_two`);
* `G` is cut-minimal if and only if its transposition gauge-cost infimum equals `2 * #G.edgeFinset`
  (`SimpleGraph.isCutMinimal_iff_iInf_sum_movedNorm_eq`), and has zero gauge-cost infimum if and
  only if `G` is a complete-graph cut (`SimpleGraph.iInf_sum_movedNorm_eq_zero_iff`);
* when `Fintype.card V = 4`, cut-switching invariance of triangle parity combined with the
  degree-`1` bound on four-vertex cut-minimal graphs gives the exact identity
  `defect = 2 * gaugeDist` for every graph `G` and every transposition `t`, and hence for every
  skew-symmetric `Equiv.Perm (Fin 2)`-valued edge labelling
  (`SimpleGraph.sum_movedNorm_holonomy_eq_two_mul_iInf_of_card_eq_four`,
  `TauCeti.sum_movedNorm_perm_fin_two_holonomy_eq_two_mul_iInf_of_card_eq_four`).

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, Section 2.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, doi:10.5281/zenodo.23245792, Section 2, Corollary 7, and Theorem 8.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

section Involution

variable {V Γ : Type*}

/-- When `c * c = 1`, reversing `(u, v)` inverts `if G.Adj u v then c else 1`. -/
theorem ite_adj_inv_of_mul_self_eq_one [Group Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v : V) :
    (if G.Adj v u then c else 1) = (if G.Adj u v then c else 1)⁻¹ := by
  simp only [G.adj_comm]
  split_ifs <;> simp [inv_eq_of_mul_eq_one_right hc]

/-- Conjugating an involution edge labelling of `G` by the `{1, c}`-valued indicator of `S` switches
`G` by the complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ`. -/
theorem ite_mem_inv_mul_ite_adj_mul [DecidableEq V] [Group Γ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (S : Set V) [DecidablePred (· ∈ S)] (u v : V) :
    (if u ∈ S then c else 1)⁻¹ * (if G.Adj u v then c else 1) * (if v ∈ S then c else 1) =
      if (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj u v then c else 1 := by
  simp only [symmDiff_adj, top_between_compl_adj]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hadj : G.Adj u v <;>
    simp [hu, hv, hadj, hc, inv_eq_of_mul_eq_one_right hc]

/-- When `c * c = 1`, the directed holonomy product around `(u, v, w)` equals `c` if `(u, v, w)`
spans an odd number of edges of `G` and `1` otherwise. -/
theorem ite_adj_mul_ite_adj_mul_ite_adj [Monoid Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v w : V) :
    (if G.Adj u v then c else 1) * (if G.Adj v w then c else 1) * (if G.Adj w u then c else 1) =
      if Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u)) then c else 1 := by
  by_cases h1 : G.Adj u v <;> by_cases h2 : G.Adj v w <;> by_cases h3 : G.Adj w u <;>
    simp [h1, h2, h3, hc]

/-- Summing a group seminorm of `if G.Adj u v then c else 1` over strictly increasing pairs `(u, v)`
yields `#G.edgeFinset * ℓ c`. -/
theorem sum_filter_lt_apply_ite_adj {R F : Type*} [Fintype V] [LinearOrder V] [Group Γ]
    [Semiring R] [PartialOrder R] [FunLike F Γ R] [GroupSeminormClass F Γ R]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet] (ℓ : F) (c : Γ) :
    (∑ p : V × V with p.1 < p.2, ℓ (if G.Adj p.1 p.2 then c else 1)) = #G.edgeFinset * ℓ c := by
  simp_rw [apply_ite ℓ, map_one_eq_zero ℓ, ← sum_filter, filter_filter, sum_const, nsmul_eq_mul,
    G.card_edgeFinset_eq_card_filter_lt]

/-- Summing a group seminorm of an involution edge labelling gauged by `S` over strictly increasing
pairs gives `#(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset * ℓ c`. -/
theorem sum_filter_lt_ite_mem_inv_mul_ite_adj_mul {R F : Type*} [Fintype V] [LinearOrder V]
    [Group Γ] [Semiring R] [PartialOrder R] [FunLike F Γ R] [GroupSeminormClass F Γ R]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : F) {c : Γ} (hc : c * c = 1)
    (S : Set V) [DecidablePred (· ∈ S)] :
    (∑ p : V × V with p.1 < p.2,
      ℓ ((if p.1 ∈ S then c else 1)⁻¹ * (if G.Adj p.1 p.2 then c else 1) *
        (if p.2 ∈ S then c else 1))) =
      #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset * ℓ c := by
  simp_rw [G.ite_mem_inv_mul_ite_adj_mul hc S]
  exact (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).sum_filter_lt_apply_ite_adj ℓ c

/-- Summing a group seminorm of the directed triangle holonomies of an involution edge labelling
over strictly increasing vertex triples counts odd-edge triples weighted by `ℓ c`. -/
theorem sum_filter_lt_triple_ite_adj_mul {R F : Type*} [Fintype V] [LinearOrder V]
    [Group Γ] [Semiring R] [PartialOrder R] [FunLike F Γ R] [GroupSeminormClass F Γ R]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : F) {c : Γ} (hc : c * c = 1) :
    (∑ p : V × V × V with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      ℓ ((if G.Adj p.1 p.2.1 then c else 1) * (if G.Adj p.2.1 p.2.2 then c else 1) *
        (if G.Adj p.2.2 p.1 then c else 1))) =
      #{p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
        Xor (G.Adj p.1 p.2.1) (Xor (G.Adj p.2.1 p.2.2) (G.Adj p.2.2 p.1))} * ℓ c := by
  simp_rw [G.ite_adj_mul_ite_adj_mul_ite_adj hc, apply_ite ℓ, map_one_eq_zero ℓ, ← sum_filter,
    filter_filter, sum_const, nsmul_eq_mul]
  congr 3
  ext p
  simp only [mem_filter, mem_univ, true_and, and_assoc]

end Involution

section SwapGauge

private theorem bddBelow_range_of_nonneg {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    BddBelow (Set.range f) :=
  ⟨0, Set.forall_mem_range.mpr hf⟩

variable {V α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
private theorem isSwap_mul_self {t : Equiv.Perm α} (ht : t.IsSwap) : t * t = 1 := by
  obtain ⟨a, b, _, rfl⟩ := ht
  simp

/-- Applying `Equiv.Perm.parityRetract ht` to a gauged transposition edge `(β u)⁻¹ * α u v * β v`
produces the binary cut-switched edge corresponding to `{w | Equiv.Perm.sign (β w) = -1}`. -/
theorem parityRetract_inv_mul_ite_adj_mul [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : Equiv.Perm α} (ht : t.IsSwap) (β : V → Equiv.Perm α) (u v : V) :
    Equiv.Perm.parityRetract ht ((β u)⁻¹ * (if G.Adj u v then t else 1) * β v) =
      if (G ∆ (⊤ : SimpleGraph V).between {w | Equiv.Perm.sign (β w) = -1}
        {w | Equiv.Perm.sign (β w) = -1}ᶜ).Adj u v then t else 1 := by
  have hret (w : V) :
      Equiv.Perm.parityRetract ht (β w) =
        if w ∈ {x | Equiv.Perm.sign (β x) = -1} then t else 1 := by
    rw [Equiv.Perm.parityRetract_apply]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (β w)) with h | h <;>
      simp [h, (by decide : (1 : ℤˣ) ≠ -1), (by decide : (-1 : ℤˣ) ≠ 1)]
  have hedge :
      Equiv.Perm.parityRetract ht (if G.Adj u v then t else 1) = if G.Adj u v then t else 1 := by
    split_ifs <;> simp
  rw [map_mul, map_mul, map_inv, hret u, hret v, hedge,
    G.ite_mem_inv_mul_ite_adj_mul (isSwap_mul_self ht)]

/-- For any transposition `t` and any `Equiv.Perm α`-valued vertex gauge `β`, the moved-point gauge
cost of `G` under `β` is at least `2` times the edge count of `G` switched by the odd-sign cut of
`β`. -/
theorem two_mul_card_symmDiff_le_sum_movedNorm [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    (β : V → Equiv.Perm α) :
    2 * (#(G ∆ (⊤ : SimpleGraph V).between {w | Equiv.Perm.sign (β w) = -1}
      {w | Equiv.Perm.sign (β w) = -1}ᶜ).edgeFinset : ℝ) ≤
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2) := by
  calc 2 * (#(G ∆ (⊤ : SimpleGraph V).between {w | Equiv.Perm.sign (β w) = -1}
          {w | Equiv.Perm.sign (β w) = -1}ᶜ).edgeFinset : ℝ)
      = ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm α
            (Equiv.Perm.parityRetract ht
              ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2)) := by
        simp_rw [G.parityRetract_inv_mul_ite_adj_mul ht β]
        rw [(G ∆ _).sum_filter_lt_apply_ite_adj (Equiv.Perm.movedNorm α) t, ht.movedNorm, mul_comm]
    _ ≤ ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2) :=
        sum_le_sum fun p _ ↦ Equiv.Perm.movedNorm_parityRetract_le ht _

/-- Evaluating the moved-point gauge cost on the binary cut gauge of `S` gives twice the switched
edge count `#(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset`. -/
theorem sum_movedNorm_ite_mem_inv_mul_ite_adj_mul [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    (S : Set V) [DecidablePred (· ∈ S)] :
    (∑ p : V × V with p.1 < p.2,
      Equiv.Perm.movedNorm α
        ((if p.1 ∈ S then t else 1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) *
          (if p.2 ∈ S then t else 1))) =
      2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
  rw [G.sum_filter_lt_ite_mem_inv_mul_ite_adj_mul (Equiv.Perm.movedNorm α) (isSwap_mul_self ht) S,
    ht.movedNorm, mul_comm]

/-- Evaluating the moved-point holonomy defect of a transposition edge labelling gives twice the
number of strictly increasing odd-edge vertex triples. -/
theorem sum_movedNorm_triple_ite_adj_mul [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (∑ p : V × V × V with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      Equiv.Perm.movedNorm α
        ((if G.Adj p.1 p.2.1 then t else 1) * (if G.Adj p.2.1 p.2.2 then t else 1) *
          (if G.Adj p.2.2 p.1 then t else 1))) =
      2 * #{p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
        Xor (G.Adj p.1 p.2.1) (Xor (G.Adj p.2.1 p.2.2) (G.Adj p.2.2 p.1))} := by
  rw [G.sum_filter_lt_triple_ite_adj_mul (Equiv.Perm.movedNorm α) (isSwap_mul_self ht),
    ht.movedNorm, mul_comm]

/-- Whenever `G ∆ (⊤ : SimpleGraph V).between S Sᶜ` is cut-minimal, the infimum of the moved-point
gauge cost over all `β : V → Equiv.Perm α` equals
`2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset`. -/
theorem iInf_sum_movedNorm_eq_of_isCutMinimal_symmDiff [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    {S : Set V} [DecidablePred (· ∈ S)]
    (hS : (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).IsCutMinimal) :
    (⨅ β : V → Equiv.Perm α,
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2)) =
      2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
  refine le_antisymm ?_ (le_ciInf fun β ↦ ?_)
  · refine (ciInf_le (bddBelow_range_of_nonneg fun _ ↦ sum_nonneg fun _ _ ↦ apply_nonneg _ _)
      (fun v ↦ if v ∈ S then t else 1)).trans_eq ?_
    exact G.sum_movedNorm_ite_mem_inv_mul_ite_adj_mul ht S
  · let T : Set V := {w | Equiv.Perm.sign (β w) = -1}
    have hcard : #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset ≤
        #(G ∆ (⊤ : SimpleGraph V).between T Tᶜ).edgeFinset := by
      classical
      have heq : (G ∆ (⊤ : SimpleGraph V).between S Sᶜ ∆
          (⊤ : SimpleGraph V).between (S ∆ T) (S ∆ T)ᶜ).edgeFinset =
          (G ∆ (⊤ : SimpleGraph V).between T Tᶜ).edgeFinset :=
        coe_injective <| by
          rw [coe_edgeFinset, coe_edgeFinset, symmDiff_top_between_symmDiff,
            symmDiff_symmDiff_cancel_left]
      have hle := hS.card_edgeFinset_le_symmDiff_top_between (S ∆ T)
      exact heq ▸ hle
    have hcardR : (2 : ℝ) * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset ≤
        2 * #(G ∆ (⊤ : SimpleGraph V).between T Tᶜ).edgeFinset := by
      exact_mod_cast Nat.mul_le_mul_left 2 hcard
    exact hcardR.trans (G.two_mul_card_symmDiff_le_sum_movedNorm ht β)

/-- Every finite ordered graph admits a finset cut switching it to a cut-minimal graph whose
doubled edge count equals the `Equiv.Perm α` gauge-cost infimum. -/
theorem exists_finset_iInf_sum_movedNorm_eq [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    ∃ s : Finset V, (G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).IsCutMinimal ∧
      (⨅ β : V → Equiv.Perm α,
        ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2)) =
        2 * #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset := by
  obtain ⟨s, hs⟩ := G.exists_finset_isCutMinimal_symmDiff_top_between
  exact ⟨s, hs, G.iInf_sum_movedNorm_eq_of_isCutMinimal_symmDiff ht hs⟩

/-- **Ambient-degree invariance of transposition gauge distance**: the `Equiv.Perm α` gauge-cost
infimum of a transposition edge labelling depends only on `G`, and coincides with the
`Equiv.Perm (Fin 2)` gauge-cost infimum. -/
theorem iInf_sum_movedNorm_eq_iInf_fin_two [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (⨅ β : V → Equiv.Perm α,
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2)) =
      ⨅ β : V → Equiv.Perm (Fin 2),
        ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm (Fin 2)
            ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then Equiv.swap 0 1 else 1) * β p.2) := by
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one
  obtain ⟨s, hs⟩ := G.exists_finset_isCutMinimal_symmDiff_top_between
  rw [G.iInf_sum_movedNorm_eq_of_isCutMinimal_symmDiff ht hs,
    G.iInf_sum_movedNorm_eq_of_isCutMinimal_symmDiff hswap hs]

/-- **Parity-retraction gauge equality**: for a transposition edge labelling, restricting gauges
from `Equiv.Perm α` to the two-element subgroup `Subgroup.zpowers t` does not change the gauge-cost
infimum (Beasley, Corollary 7). -/
theorem iInf_sum_movedNorm_zpowers_eq [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (⨅ β : V → Subgroup.zpowers t,
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm α
          (((β p.1 : Equiv.Perm α))⁻¹ * (if G.Adj p.1 p.2 then t else 1) *
            (β p.2 : Equiv.Perm α))) =
      ⨅ β : V → Equiv.Perm α,
        ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2) := by
  have hbdd : BddBelow (Set.range fun β : V → Equiv.Perm α ↦
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2)) :=
    bddBelow_range_of_nonneg fun _ ↦ sum_nonneg fun _ _ ↦ apply_nonneg _ _
  have hbddZ : BddBelow (Set.range fun β : V → Subgroup.zpowers t ↦
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm α
          (((β p.1 : Equiv.Perm α))⁻¹ * (if G.Adj p.1 p.2 then t else 1) *
            (β p.2 : Equiv.Perm α))) :=
    bddBelow_range_of_nonneg fun _ ↦ sum_nonneg fun _ _ ↦ apply_nonneg _ _
  obtain ⟨s, -, hval⟩ := G.exists_finset_iInf_sum_movedNorm_eq ht
  refine le_antisymm ?_ (le_ciInf fun β ↦ ciInf_le hbdd fun v ↦ (β v : Equiv.Perm α))
  rw [hval]
  let β₀ : V → Subgroup.zpowers t :=
    fun v ↦ if v ∈ (s : Set V) then ⟨t, Subgroup.mem_zpowers t⟩ else 1
  have hcoe (v : V) : (β₀ v : Equiv.Perm α) = if v ∈ (s : Set V) then t else 1 := by
    simp only [β₀]
    split_ifs <;> rfl
  refine (ciInf_le hbddZ β₀).trans_eq ?_
  simp_rw [hcoe]
  exact G.sum_movedNorm_ite_mem_inv_mul_ite_adj_mul ht (s : Set V)

/-- **Cut-minimality via transposition gauge distance**: a finite ordered graph `G` is cut-minimal
if and only if the `Equiv.Perm α` gauge-cost infimum of its transposition edge labelling equals
`2 * #G.edgeFinset` (Kozlov, Section 2; Beasley, Corollary 7). -/
theorem isCutMinimal_iff_iInf_sum_movedNorm_eq [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    {t : Equiv.Perm α} (ht : t.IsSwap) :
    G.IsCutMinimal ↔
      (⨅ β : V → Equiv.Perm α,
        ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2)) =
        2 * #G.edgeFinset := by
  have hbot : (⊤ : SimpleGraph V).between (∅ : Set V) (∅ : Set V)ᶜ = ⊥ := by
    ext u v
    rw [top_between_compl_adj]
    simp
  constructor
  · intro hG
    have hG' : (G ∆ (⊤ : SimpleGraph V).between (∅ : Set V) (∅ : Set V)ᶜ).IsCutMinimal := by
      rw [hbot, symmDiff_bot]
      exact hG
    have heq : #(G ∆ (⊤ : SimpleGraph V).between (∅ : Set V) (∅ : Set V)ᶜ).edgeFinset =
        #G.edgeFinset :=
      congrArg card <| coe_injective <| by rw [coe_edgeFinset, coe_edgeFinset, hbot, symmDiff_bot]
    rw [G.iInf_sum_movedNorm_eq_of_isCutMinimal_symmDiff ht hG', heq]
  · intro h
    rw [isCutMinimal_iff_forall_finset]
    intro s
    have hfintype : #(@edgeFinset _ G (fintypeEdgeSet G)) = #G.edgeFinset :=
      congrArg card <| coe_injective <| by rw [coe_edgeFinset, coe_edgeFinset]
    rw [hfintype]
    have hle : (2 : ℝ) * #G.edgeFinset ≤
        2 * #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset := by
      rw [← h, ← G.sum_movedNorm_ite_mem_inv_mul_ite_adj_mul ht (s : Set V)]
      exact ciInf_le (bddBelow_range_of_nonneg fun _ ↦ sum_nonneg fun _ _ ↦ apply_nonneg _ _)
        fun v ↦ if v ∈ (s : Set V) then t else 1
    have hle' : 2 * #G.edgeFinset ≤
        2 * #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset := by
      exact_mod_cast hle
    omega

/-- The `Equiv.Perm α` gauge-cost infimum of a transposition edge labelling vanishes if and only if
`G` is a complete-graph cut. -/
theorem iInf_sum_movedNorm_eq_zero_iff [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (⨅ β : V → Equiv.Perm α,
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2)) = 0 ↔
      ∃ S : Set V, G = (⊤ : SimpleGraph V).between S Sᶜ := by
  constructor
  · intro h0
    obtain ⟨s, -, hval⟩ := G.exists_finset_iInf_sum_movedNorm_eq ht
    rw [h0] at hval
    have hcard : #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset = 0 := by
      have : 2 * #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset = 0 := by
        exact_mod_cast hval.symm
      omega
    rw [card_eq_zero, edgeFinset_eq_empty, symmDiff_eq_bot] at hcard
    exact ⟨s, hcard⟩
  · rintro ⟨S, rfl⟩
    classical
    let s : Finset V := S.toFinset
    have hbot : (⊤ : SimpleGraph V).between S Sᶜ ∆
        (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ = ⊥ := by
      ext u v
      simp [s]
    have hcm : ((⊤ : SimpleGraph V).between S Sᶜ ∆
        (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).IsCutMinimal :=
      hbot ▸ isCutMinimal_bot
    have hcard : #((⊤ : SimpleGraph V).between S Sᶜ ∆
        (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset = 0 := by
      rw [card_eq_zero, edgeFinset_eq_empty]
      exact hbot
    rw [((⊤ : SimpleGraph V).between S Sᶜ).iInf_sum_movedNorm_eq_of_isCutMinimal_symmDiff ht hcm,
      hcard]
    simp

/-- **Four-vertex transposition exactness**: on a four-element linearly ordered vertex type, every
graph `G` and every transposition `t` satisfy `defect = 2 * gaugeDist`, so every non-coboundary
`{1, t}`-valued cochain has coboundary expansion ratio `2`. -/
theorem sum_movedNorm_holonomy_eq_two_mul_iInf_of_card_eq_four [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 4)
    {t : Equiv.Perm α} (ht : t.IsSwap) :
    (∑ p : V × V × V with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      Equiv.Perm.movedNorm α
        ((if G.Adj p.1 p.2.1 then t else 1) * (if G.Adj p.2.1 p.2.2 then t else 1) *
          (if G.Adj p.2.2 p.1 then t else 1))) =
      2 * ⨅ β : V → Equiv.Perm α,
        ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then t else 1) * β p.2) := by
  obtain ⟨s, hs, hval⟩ := G.exists_finset_iInf_sum_movedNorm_eq ht
  rw [G.sum_movedNorm_triple_ite_adj_mul ht, hval,
    ← G.card_filter_lt_triple_xor_symmDiff_top_between (s : Set V),
    hs.card_filter_lt_triple_xor_of_card_le_four hV.le, hV]
  push_cast
  ring

/-- On at least three vertices, the transposition edge labelling of a single edge `u ≠ v` has
moved-point gauge-cost infimum `2`. -/
theorem iInf_sum_movedNorm_edge_of_three_le_card [Fintype V] [LinearOrder V]
    (hV : 3 ≤ Fintype.card V) {u v : V} (huv : u ≠ v) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (⨅ β : V → Equiv.Perm α,
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm α ((β p.1)⁻¹ * (if (edge u v).Adj p.1 p.2 then t else 1) * β p.2)) =
      2 := by
  have hcard : #(edge u v).edgeFinset = 1 := by
    have : (edge u v).edgeFinset = {s(u, v)} :=
      coe_injective <| by rw [coe_edgeFinset, coe_singleton, edgeSet_edge_of_ne huv]
    rw [this, card_singleton]
  rw [((edge u v).isCutMinimal_iff_iInf_sum_movedNorm_eq ht).mp
    (isCutMinimal_edge_of_three_le_card hV u v), hcard]
  norm_num

/-- On four vertices, the transposition edge labelling of a single edge `u ≠ v` has holonomy defect
sum `4`. -/
theorem sum_movedNorm_triple_edge_of_card_eq_four [Fintype V] [LinearOrder V]
    (hV : Fintype.card V = 4) {u v : V} (huv : u ≠ v) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (∑ p : V × V × V with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      Equiv.Perm.movedNorm α
        ((if (edge u v).Adj p.1 p.2.1 then t else 1) *
          (if (edge u v).Adj p.2.1 p.2.2 then t else 1) *
          (if (edge u v).Adj p.2.2 p.1 then t else 1))) = 4 := by
  rw [(edge u v).sum_movedNorm_holonomy_eq_two_mul_iInf_of_card_eq_four hV ht,
    iInf_sum_movedNorm_edge_of_three_le_card (by omega) huv ht]
  norm_num

end SwapGauge

end SimpleGraph

namespace TauCeti

section PermFinTwo

private theorem perm_fin_two_eq_ite_ne_one (σ : Equiv.Perm (Fin 2)) :
    σ = if σ ≠ 1 then Equiv.swap 0 1 else 1 := by
  rcases σ.eq_one_or_swap_fin_two with rfl | rfl <;> decide

/-- Simple graphs on `V` are in bijection with skew-symmetric `Equiv.Perm (Fin 2)`-valued edge
labellings on `V`: adjacent pairs carry `Equiv.swap 0 1` and non-adjacent pairs carry `1`. -/
noncomputable def simpleGraphEquivPermFinTwo (V : Type*) :
    SimpleGraph V ≃
      {α : V → V → Equiv.Perm (Fin 2) // (∀ u, α u u = 1) ∧ ∀ u v, α v u = (α u v)⁻¹} where
  toFun G :=
    ⟨fun u v ↦ open Classical in if G.Adj u v then Equiv.swap 0 1 else 1,
      ⟨fun u ↦ by classical simp, fun u v ↦ by
        classical
        exact G.ite_adj_inv_of_mul_self_eq_one (by decide) u v⟩⟩
  invFun α :=
    { Adj u v := α.1 u v ≠ 1
      symm := ⟨fun u v h ↦ by
        rw [α.2.2 u v, inv_ne_one]
        exact h⟩
      loopless := ⟨fun u h ↦ h (α.2.1 u)⟩ }
  left_inv G := by
    ext u v
    classical
    by_cases h : G.Adj u v <;> simp [h]
  right_inv α := Subtype.ext <| funext₂ fun u v ↦ by
    dsimp only
    conv_rhs => rw [perm_fin_two_eq_ite_ne_one (α.1 u v)]
    congr!

/-- `TauCeti.simpleGraphEquivPermFinTwo` labels adjacent pairs by `Equiv.swap 0 1` and non-adjacent
pairs by `1`. -/
@[simp]
theorem simpleGraphEquivPermFinTwo_apply {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) :
    (simpleGraphEquivPermFinTwo V G).1 u v =
      if G.Adj u v then Equiv.swap 0 1 else 1 := by
  simp only [simpleGraphEquivPermFinTwo, Equiv.coe_fn_mk]
  congr!

/-- The inverse of `TauCeti.simpleGraphEquivPermFinTwo` makes `u` and `v` adjacent precisely when
their edge label is non-identity. -/
@[simp]
theorem simpleGraphEquivPermFinTwo_symm_adj {V : Type*}
    (α : {α : V → V → Equiv.Perm (Fin 2) // (∀ u, α u u = 1) ∧ ∀ u v, α v u = (α u v)⁻¹})
    (u v : V) :
    ((simpleGraphEquivPermFinTwo V).symm α).Adj u v ↔ α.1 u v ≠ 1 :=
  (Iff.rfl)

/-- Adjacency in `(simpleGraphEquivPermFinTwo V).symm α` is decidable because equality in
`Equiv.Perm (Fin 2)` is decidable. -/
instance instDecidableRelSimpleGraphEquivPermFinTwoSymm {V : Type*}
    (α : {α : V → V → Equiv.Perm (Fin 2) // (∀ u, α u u = 1) ∧ ∀ u v, α v u = (α u v)⁻¹}) :
    DecidableRel ((simpleGraphEquivPermFinTwo V).symm α).Adj :=
  fun u v ↦ inferInstanceAs (Decidable (α.1 u v ≠ 1))

/-- For any skew-symmetric `Equiv.Perm (Fin 2)`-valued edge labelling `α` and vertex gauge `β`, the
moved-point gauge cost equals twice the edge count of the support graph of `α` switched by the
support cut `{w | β w ≠ 1}` of `β`. -/
theorem sum_movedNorm_perm_fin_two_gauge {V : Type*} [Fintype V] [LinearOrder V]
    (α : {α : V → V → Equiv.Perm (Fin 2) // (∀ u, α u u = 1) ∧ ∀ u v, α v u = (α u v)⁻¹})
    (β : V → Equiv.Perm (Fin 2)) :
    (∑ p : V × V with p.1 < p.2,
      Equiv.Perm.movedNorm (Fin 2) ((β p.1)⁻¹ * α.1 p.1 p.2 * β p.2)) =
      2 * #(((simpleGraphEquivPermFinTwo V).symm α) ∆
        (⊤ : SimpleGraph V).between {w | β w ≠ 1} {w | β w ≠ 1}ᶜ).edgeFinset := by
  let G := (simpleGraphEquivPermFinTwo V).symm α
  have hα (u v : V) : α.1 u v = if G.Adj u v then Equiv.swap 0 1 else 1 :=
    perm_fin_two_eq_ite_ne_one (α.1 u v)
  have hβ (u : V) : β u = if u ∈ {w | β w ≠ 1} then Equiv.swap 0 1 else 1 :=
    perm_fin_two_eq_ite_ne_one (β u)
  rw [Finset.sum_congr rfl fun p _ ↦ by rw [hα p.1 p.2, hβ p.1, hβ p.2]]
  exact G.sum_movedNorm_ite_mem_inv_mul_ite_adj_mul
    (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one) {w | β w ≠ 1}

/-- For any `Equiv.Perm (Fin 2)`-valued edge labelling `α`, the moved-point holonomy defect sum
equals twice the number of strictly increasing vertex triples spanning an odd number of
non-identity edges. -/
theorem sum_movedNorm_perm_fin_two_holonomy {V : Type*} [Fintype V] [LinearOrder V]
    (α : V → V → Equiv.Perm (Fin 2)) :
    (∑ p : V × V × V with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      Equiv.Perm.movedNorm (Fin 2) (α p.1 p.2.1 * α p.2.1 p.2.2 * α p.2.2 p.1)) =
      2 * #{p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
        Xor (α p.1 p.2.1 ≠ 1) (Xor (α p.2.1 p.2.2 ≠ 1) (α p.2.2 p.1 ≠ 1))} := by
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one
  have hne : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by decide
  have hmul (x y z : Equiv.Perm (Fin 2)) :
      Equiv.Perm.movedNorm (Fin 2) (x * y * z) =
        if Xor (x ≠ 1) (Xor (y ≠ 1) (z ≠ 1)) then 2 else 0 := by
    rcases x.eq_one_or_swap_fin_two with rfl | rfl <;>
      rcases y.eq_one_or_swap_fin_two with rfl | rfl <;>
      rcases z.eq_one_or_swap_fin_two with rfl | rfl <;>
      simp [hne, hswap.movedNorm]
  simp_rw [hmul, ← sum_filter, filter_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 3
  ext p
  simp only [mem_filter, mem_univ, true_and, and_assoc]

/-- **Four-vertex binary cochain exactness**: on a four-element linearly ordered vertex type, every
`Equiv.Perm (Fin 2)`-valued edge labelling satisfying `α v u = (α u v)⁻¹` satisfies
`defect = 2 * gaugeDist`. -/
theorem sum_movedNorm_perm_fin_two_holonomy_eq_two_mul_iInf_of_card_eq_four
    {V : Type*} [Fintype V] [LinearOrder V] (hV : Fintype.card V = 4)
    (α : V → V → Equiv.Perm (Fin 2)) (hsymm : ∀ u v, α v u = (α u v)⁻¹) :
    (∑ p : V × V × V with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      Equiv.Perm.movedNorm (Fin 2) (α p.1 p.2.1 * α p.2.1 p.2.2 * α p.2.2 p.1)) =
      2 * ⨅ β : V → Equiv.Perm (Fin 2),
        ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm (Fin 2) ((β p.1)⁻¹ * α p.1 p.2 * β p.2) := by
  let α' : {f : V → V → Equiv.Perm (Fin 2) // (∀ u, f u u = 1) ∧ ∀ u v, f v u = (f u v)⁻¹} :=
    ⟨fun u v ↦ if u = v then 1 else α u v,
      ⟨fun u ↦ by simp, fun u v ↦ by
        by_cases h : v = u
        · simp [h]
        · simp [h, Ne.symm h, hsymm u v]⟩⟩
  let G := (simpleGraphEquivPermFinTwo V).symm α'
  have hα {u v : V} (huv : u ≠ v) : α u v = if G.Adj u v then Equiv.swap 0 1 else 1 := by
    have h1 : α'.1 u v = α u v := by simp [α', huv]
    have h2 := perm_fin_two_eq_ite_ne_one (α'.1 u v)
    exact h1 ▸ h2
  have hlhs : (∑ p : V × V × V with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
      Equiv.Perm.movedNorm (Fin 2) (α p.1 p.2.1 * α p.2.1 p.2.2 * α p.2.2 p.1)) =
      ∑ p : V × V × V with p.1 < p.2.1 ∧ p.2.1 < p.2.2,
        Equiv.Perm.movedNorm (Fin 2)
          ((if G.Adj p.1 p.2.1 then Equiv.swap 0 1 else 1) *
            (if G.Adj p.2.1 p.2.2 then Equiv.swap 0 1 else 1) *
            (if G.Adj p.2.2 p.1 then Equiv.swap 0 1 else 1)) :=
    Finset.sum_congr rfl fun p hp ↦ by
      obtain ⟨h12, h23⟩ := (Finset.mem_filter.mp hp).2
      rw [hα h12.ne, hα h23.ne, hα (h12.trans h23).ne']
  have hrhs : (⨅ β : V → Equiv.Perm (Fin 2),
      ∑ p : V × V with p.1 < p.2,
        Equiv.Perm.movedNorm (Fin 2) ((β p.1)⁻¹ * α p.1 p.2 * β p.2)) =
      ⨅ β : V → Equiv.Perm (Fin 2),
        ∑ p : V × V with p.1 < p.2,
          Equiv.Perm.movedNorm (Fin 2)
            ((β p.1)⁻¹ * (if G.Adj p.1 p.2 then Equiv.swap 0 1 else 1) * β p.2) :=
    iInf_congr fun β ↦ Finset.sum_congr rfl fun p hp ↦ by
      rw [hα (Finset.mem_filter.mp hp).2.ne]
  rw [hlhs, hrhs]
  exact G.sum_movedNorm_holonomy_eq_two_mul_iInf_of_card_eq_four hV
    (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one)

end PermFinTwo

end TauCeti
