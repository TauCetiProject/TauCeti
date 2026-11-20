/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
public import TauCeti.GroupTheory.Perm.ParityRetract
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.Combinatorics.SimpleGraph.Finite
import TauCeti.Data.Fin.Basic

/-!
# Transposition cochains, parity-retracted gauges, and four-vertex binary exactness

Given a simple graph `G` on a finite vertex type `V` and an element `c` satisfying `c * c = 1` in a
group `Γ`, `SimpleGraph.toCochain` packages the `{1, c}`-valued edge indicator of `G` as a
`1`-cochain on `TwoComplex.complete V`:

* acting on `G.toCochain hc` by the `{1, c}`-valued indicator gauge of `S : Set V` switches `G` to
  `G ∆ (⊤ : SimpleGraph V).between S Sᶜ` (`SimpleGraph.smul_ite_mem_toCochain`), with cost
  `#(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset * ℓ c` (`SimpleGraph.cost_toCochain_ite_mem`);
* the holonomy around `(u, v, w)` equals `c` when an odd number of the pairs `(u, v)`, `(v, w)`,
  and `(w, u)` are adjacent in `G` and `1` otherwise (`SimpleGraph.holonomy_toCochain`), so the
  cochain defect equals `#G.oddTriangleFinset * ℓ c` (`SimpleGraph.defect_toCochain`).

Specializing `Γ` to a finite symmetric group `Equiv.Perm α` and `c` to a transposition
`ht : t.IsSwap` under `Equiv.Perm.movedNorm α` connects permutation gauges to cut-minimality and
binary cochains via `Equiv.Perm.parityRetract`:

* for any gauge `β : V → Equiv.Perm α` with odd-sign vertex set
  `S := {w | Equiv.Perm.sign (β w) = -1}`, retracting the gauged edge label produces the
  cut-switched edge label of `G ∆ (⊤ : SimpleGraph V).between S Sᶜ` and yields
  `2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset ≤
    (G.toCochain ht.mul_self).cost (Equiv.Perm.movedNorm α) β`
  (`SimpleGraph.two_mul_card_symmDiff_le_cost_movedNorm_toCochain`);
* embedding any `Subgroup.zpowers t`-valued cochain on an arbitrary two-complex `X` into
  `Equiv.Perm α` preserves `Cochain.gaugeDist` relative to the restricted moved-point norm
  (`TauCeti.Cochain.gaugeDist_map_zpowers_subtype`);
* `TauCeti.simpleGraphEquivPermFinTwo` identifies `SimpleGraph V` with
  `Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))`, transporting `Cochain.cost`,
  `Cochain.defect`, and `Cochain.gaugeDist` to cut-switched edge counts, `#G.oddTriangleFinset`,
  and cut-minimality (`TauCeti.Cochain.cost_movedNorm_fin_two`,
  `TauCeti.Cochain.defect_movedNorm_fin_two`,
  `SimpleGraph.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq`,
  `TauCeti.Cochain.isCutMinimal_symm_simpleGraphEquivPermFinTwo_iff`);
* when `Fintype.card V ≤ 4`, cut-switching invariance of `oddTriangleFinset` combined with the
  degree-`1` bound on cut-minimal graphs gives `defect = (Fintype.card V - 2) * gaugeDist` on
  `TwoComplex.complete V`, and hence evaluates `TauCeti.h1` on four vertices to `2` for both
  `Equiv.Perm.movedNorm (Fin 2)` and `Subgroup.zpowers t`
  (`TauCeti.h1_complete_movedNorm_fin_two_of_card_eq_four`,
  `TauCeti.h1_complete_zpowers_swap_of_card_eq_four`).

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
theorem ite_adj_eq_inv_of_mul_self_eq_one [Group Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
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

/-- When `c * c = 1`, the directed product around `(u, v, w)` equals `c` if an odd number of the
pairs `(u, v)`, `(v, w)`, and `(w, u)` are adjacent in `G` (equivalently, if `{u, v, w}` spans an
odd number of edges when `u`, `v`, `w` are pairwise distinct), and `1` otherwise. -/
theorem ite_adj_mul_ite_adj_mul_ite_adj [Monoid Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v w : V) :
    (if G.Adj u v then c else 1) * (if G.Adj v w then c else 1) * (if G.Adj w u then c else 1) =
      if Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u)) then c else 1 := by
  by_cases h1 : G.Adj u v <;> by_cases h2 : G.Adj v w <;> by_cases h3 : G.Adj w u <;>
    simp [h1, h2, h3, hc]

/-- The `Γ`-valued `1`-cochain on `TwoComplex.complete V` associated to a simple graph `G` and an
element `c : Γ` satisfying `c * c = 1`, assigning `c` to adjacent vertex pairs and `1` to
non-adjacent pairs. -/
noncomputable def toCochain [Fintype V] [Group Γ] (G : SimpleGraph V) {c : Γ} (hc : c * c = 1) :
    TauCeti.Cochain (TauCeti.TwoComplex.complete V) Γ :=
  open Classical in
  TauCeti.Cochain.ofFn (TauCeti.TwoComplex.complete V)
    (fun u v ↦ if G.Adj u v then c else 1)
    fun u v _ ↦ G.ite_adj_eq_inv_of_mul_self_eq_one hc u v

/-- `G.toCochain hc` takes the value `c` on adjacent vertices. -/
@[simp, grind =]
theorem toCochain_apply_of_adj [Fintype V] [Group Γ] {G : SimpleGraph V} {c : Γ}
    (hc : c * c = 1) {u v : V} (h : G.Adj u v) :
    G.toCochain hc u v = c := by
  simp [toCochain, (TauCeti.TwoComplex.adj_complete u v).mpr h.ne, h]

/-- `G.toCochain hc` takes the value `1` on non-adjacent vertices. -/
@[simp, grind =]
theorem toCochain_apply_of_not_adj [Fintype V] [Group Γ] {G : SimpleGraph V} {c : Γ}
    (hc : c * c = 1) {u v : V} (h : ¬ G.Adj u v) :
    G.toCochain hc u v = 1 := by
  rcases eq_or_ne u v with rfl | huv
  · exact (G.toCochain hc).apply_self u
  · simp [toCochain, (TauCeti.TwoComplex.adj_complete u v).mpr huv, h]

/-- Explicit `ite` evaluation of `G.toCochain hc` when adjacency in `G` is decidable. -/
theorem toCochain_apply [Fintype V] [Group Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v : V) :
    G.toCochain hc u v = if G.Adj u v then c else 1 := by
  by_cases h : G.Adj u v <;> simp [h]

/-- The empty graph induces the trivial `1`-cochain. -/
@[simp]
theorem bot_toCochain [Fintype V] [Group Γ] {c : Γ} (hc : c * c = 1) :
    (⊥ : SimpleGraph V).toCochain hc = 1 := by
  ext u v _
  simp

/-- A single-edge graph `SimpleGraph.edge u v` induces `Cochain.singleEdge` on
`TwoComplex.complete V`. -/
theorem edge_toCochain [Fintype V] [Group Γ] (u v : V) {c : Γ} (hc : c * c = 1) :
    (edge u v).toCochain hc =
      TauCeti.Cochain.singleEdge (TauCeti.TwoComplex.complete V) u v c := by
  rcases eq_or_ne u v with rfl | huv
  · have he : edge u u = ⊥ := by
      ext x y
      simp
    rw [he, bot_toCochain hc,
      TauCeti.Cochain.singleEdge_of_not_adj ((TauCeti.TwoComplex.complete V).not_adj_self u)]
  · ext x y _
    by_cases h₁ : x = u ∧ y = v
    · obtain ⟨hx, hy⟩ := h₁
      rw [hx, hy, toCochain_apply_of_adj hc ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩),
        TauCeti.Cochain.singleEdge_apply_self ((TauCeti.TwoComplex.adj_complete u v).mpr huv)]
    · by_cases h₂ : x = v ∧ y = u
      · obtain ⟨hx, hy⟩ := h₂
        rw [hx, hy, toCochain_apply_of_adj hc ((edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩),
          TauCeti.Cochain.singleEdge_apply_swap ((TauCeti.TwoComplex.adj_complete u v).mpr huv),
          inv_eq_of_mul_eq_one_right hc]
      · have hnadj : ¬ (edge u v).Adj x y := by
          rw [edge_adj]
          rintro ⟨h | h, -⟩
          · exact h₁ h
          · exact h₂ h
        rw [toCochain_apply_of_not_adj hc hnadj, TauCeti.Cochain.singleEdge_apply_of_ne c h₁ h₂]

/-- Pushing `G.toCochain hc` forward along a group homomorphism `φ` yields `G.toCochain` for
`φ c`. -/
@[simp]
theorem map_toCochain {H : Type*} [Fintype V] [Group Γ] [Group H] (G : SimpleGraph V)
    {c : Γ} (hc : c * c = 1) (φ : Γ →* H) :
    (G.toCochain hc).map φ = G.toCochain (by rw [← map_mul, hc, map_one] : φ c * φ c = 1) := by
  ext u v _
  by_cases h : G.Adj u v <;> simp [h]

/-- Acting on `G.toCochain hc` by the `{1, c}`-valued indicator gauge of `S` switches `G` by the
complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ`. -/
theorem smul_ite_mem_toCochain [Fintype V] [Group Γ] (G : SimpleGraph V)
    {c : Γ} (hc : c * c = 1) (S : Set V) [DecidablePred (· ∈ S)] :
    (fun v ↦ if v ∈ S then c else 1) • G.toCochain hc =
      (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).toCochain hc := by
  classical
  ext u v _
  rw [TauCeti.Cochain.smul_apply_complete, G.toCochain_apply hc, (G ∆ _).toCochain_apply hc]
  exact G.ite_mem_inv_mul_ite_adj_mul hc S u v

/-- The holonomy of `G.toCochain hc` around `(u, v, w)` equals `c` if an odd number of the pairs
`(u, v)`, `(v, w)`, and `(w, u)` are adjacent in `G` (equivalently, if `{u, v, w}` spans an odd
number of edges when `u`, `v`, `w` are pairwise distinct), and `1` otherwise. -/
theorem holonomy_toCochain [Fintype V] [Group Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v w : V) :
    (G.toCochain hc).holonomy u v w =
      if Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u)) then c else 1 := by
  simp only [TauCeti.Cochain.holonomy_def, G.toCochain_apply hc]
  exact G.ite_adj_mul_ite_adj_mul_ite_adj hc u v w

/-- Under the trivial gauge `1`, the cost of `G.toCochain hc` equals `#G.edgeFinset * ℓ c`. -/
theorem cost_toCochain_one [Fintype V] [LinearOrder V] [Group Γ] (G : SimpleGraph V)
    [Fintype G.edgeSet] (ℓ : GroupNorm Γ) {c : Γ} (hc : c * c = 1) :
    (G.toCochain hc).cost ℓ 1 = #G.edgeFinset * ℓ c := by
  classical
  rw [TauCeti.Cochain.cost_complete, G.card_edgeFinset_eq_card_filter_lt]
  simp_rw [Pi.one_apply, inv_one, one_mul, mul_one, G.toCochain_apply hc, apply_ite ℓ,
    map_one_eq_zero ℓ, ← sum_filter, filter_filter, sum_const, nsmul_eq_mul]

/-- Under the `{1, c}`-valued indicator gauge of `S`, the cost of `G.toCochain hc` equals
`#(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset * ℓ c`. -/
theorem cost_toCochain_ite_mem [Fintype V] [LinearOrder V] [Group Γ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ℓ : GroupNorm Γ) {c : Γ} (hc : c * c = 1)
    (S : Set V) [DecidablePred (· ∈ S)] :
    (G.toCochain hc).cost ℓ (fun v ↦ if v ∈ S then c else 1) =
      #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset * ℓ c := by
  have hsmul := (G.toCochain hc).cost_smul ℓ (fun v ↦ if v ∈ S then c else 1) 1
  rw [mul_one, G.smul_ite_mem_toCochain hc S, (G ∆ _).cost_toCochain_one ℓ hc] at hsmul
  exact hsmul.symm

/-- The defect of `G.toCochain hc` equals `#G.oddTriangleFinset * ℓ c`. -/
theorem defect_toCochain [Fintype V] [LinearOrder V] [Group Γ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ℓ : GroupNorm Γ) {c : Γ} (hc : c * c = 1) :
    (G.toCochain hc).defect ℓ = #G.oddTriangleFinset * ℓ c := by
  rw [TauCeti.Cochain.defect_complete]
  simp_rw [G.holonomy_toCochain hc, apply_ite ℓ, map_one_eq_zero ℓ, ← sum_filter, filter_filter,
    sum_const, nsmul_eq_mul, G.card_oddTriangleFinset_eq_card_filter_lt]
  congr 3
  ext p
  simp only [mem_filter, mem_univ, true_and, and_assoc]

end Involution

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
  have hret (w : V) :
      Equiv.Perm.parityRetract ht (β w) =
        if w ∈ {x | Equiv.Perm.sign (β x) = -1} then t else 1 := by
    rw [Equiv.Perm.parityRetract_apply]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (β w)) with h | h <;>
      simp [h, (by decide : (1 : ℤˣ) ≠ -1), (by decide : (-1 : ℤˣ) ≠ 1)]
  have hedge :
      Equiv.Perm.parityRetract ht (if G.Adj u v then t else 1) = if G.Adj u v then t else 1 := by
    split_ifs <;> simp
  rw [map_mul, map_mul, map_inv, hret u, hret v, hedge, G.ite_mem_inv_mul_ite_adj_mul ht.mul_self]

/-- Pushing `G.toCochain ht.mul_self` forward along `Equiv.Perm.parityRetract ht` fixes it. -/
theorem map_parityRetract_toCochain [Fintype V] (G : SimpleGraph V) {t : Equiv.Perm α}
    (ht : t.IsSwap) :
    (G.toCochain ht.mul_self).map (Equiv.Perm.parityRetract ht) = G.toCochain ht.mul_self := by
  simp

/-- Under the trivial gauge `1`, the moved-point cost of `G.toCochain ht.mul_self` equals
`2 * #G.edgeFinset`. -/
theorem cost_movedNorm_toCochain_one [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [Fintype G.edgeSet] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self).cost (Equiv.Perm.movedNorm α) 1 = 2 * #G.edgeFinset := by
  rw [G.cost_toCochain_one (Equiv.Perm.movedNorm α) ht.mul_self, ht.movedNorm, mul_comm]

/-- Evaluating the moved-point cost of `G.toCochain ht.mul_self` on the `{1, t}`-valued cut gauge
of `S` gives twice the switched edge count `#(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset`. -/
theorem cost_movedNorm_toCochain_ite_mem [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    (S : Set V) [DecidablePred (· ∈ S)] :
    (G.toCochain ht.mul_self).cost (Equiv.Perm.movedNorm α) (fun v ↦ if v ∈ S then t else 1) =
      2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
  rw [G.cost_toCochain_ite_mem (Equiv.Perm.movedNorm α) ht.mul_self S, ht.movedNorm, mul_comm]

/-- Evaluating the moved-point defect of `G.toCochain ht.mul_self` gives twice
`#G.oddTriangleFinset`. -/
theorem defect_movedNorm_toCochain [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self).defect (Equiv.Perm.movedNorm α) = 2 * #G.oddTriangleFinset := by
  rw [G.defect_toCochain (Equiv.Perm.movedNorm α) ht.mul_self, ht.movedNorm, mul_comm]

/-- For any transposition `t` and any `Equiv.Perm α`-valued vertex gauge `β`, the moved-point cost
of `G.toCochain ht.mul_self` under `β` is at least `2` times the edge count of `G` switched by the
odd-sign cut `{w | Equiv.Perm.sign (β w) = -1}`. -/
theorem two_mul_card_symmDiff_le_cost_movedNorm_toCochain [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    (β : V → Equiv.Perm α) :
    2 * (#(G ∆ (⊤ : SimpleGraph V).between {w | Equiv.Perm.sign (β w) = -1}
      {w | Equiv.Perm.sign (β w) = -1}ᶜ).edgeFinset : ℝ) ≤
      (G.toCochain ht.mul_self).cost (Equiv.Perm.movedNorm α) β := by
  have hcomp : Equiv.Perm.parityRetract ht ∘ β =
      fun w ↦ if w ∈ {x | Equiv.Perm.sign (β x) = -1} then t else 1 := by
    ext w
    rw [Function.comp_apply, Equiv.Perm.parityRetract_apply]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (β w)) with h | h <;>
      simp [h, (by decide : (1 : ℤˣ) ≠ -1), (by decide : (-1 : ℤˣ) ≠ 1)]
  have hle := (G.toCochain ht.mul_self).cost_map_le (Equiv.Perm.movedNorm_parityRetract_le ht) β
  rwa [G.map_parityRetract_toCochain ht, hcomp,
    G.cost_movedNorm_toCochain_ite_mem ht {w | Equiv.Perm.sign (β w) = -1}] at hle

/-- Whenever `G ∆ (⊤ : SimpleGraph V).between S Sᶜ` is cut-minimal, the `Equiv.Perm α` gauge
distance of `G.toCochain ht.mul_self` equals
`2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset`. -/
theorem gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap)
    {S : Set V} [DecidablePred (· ∈ S)]
    (hS : (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).IsCutMinimal) :
    (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) =
      2 * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
  refine le_antisymm ?_ (((G.toCochain ht.mul_self).le_gaugeDist_iff _).mpr fun β ↦ ?_)
  · exact ((G.toCochain ht.mul_self).gaugeDist_le_cost _ (fun v ↦ if v ∈ S then t else 1)).trans_eq
      (G.cost_movedNorm_toCochain_ite_mem ht S)
  · let T : Set V := {w | Equiv.Perm.sign (β w) = -1}
    have hcard : #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset ≤
        #(G ∆ (⊤ : SimpleGraph V).between T Tᶜ).edgeFinset := by
      classical
      have heq : (G ∆ (⊤ : SimpleGraph V).between S Sᶜ ∆
          (⊤ : SimpleGraph V).between (S ∆ T) (S ∆ T)ᶜ).edgeFinset =
          (G ∆ (⊤ : SimpleGraph V).between T Tᶜ).edgeFinset :=
        edgeFinset_inj.mpr (by rw [symmDiff_top_between_symmDiff, symmDiff_symmDiff_cancel_left])
      exact heq ▸ hS.card_edgeFinset_le_symmDiff_top_between (S ∆ T)
    have hcardR : (2 : ℝ) * #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset ≤
        2 * #(G ∆ (⊤ : SimpleGraph V).between T Tᶜ).edgeFinset := by
      exact_mod_cast Nat.mul_le_mul_left 2 hcard
    exact hcardR.trans (G.two_mul_card_symmDiff_le_cost_movedNorm_toCochain ht β)

/-- Every finite ordered graph admits a finset cut switching it to a cut-minimal graph whose
doubled edge count equals the `Equiv.Perm α` gauge distance of `G.toCochain ht.mul_self`. -/
theorem exists_finset_isCutMinimal_and_gaugeDist_movedNorm_toCochain_eq [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : Equiv.Perm α} (ht : t.IsSwap) :
    ∃ s : Finset V, (G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).IsCutMinimal ∧
      (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) =
        2 * #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset := by
  obtain ⟨s, hs⟩ := G.exists_finset_isCutMinimal_symmDiff_top_between
  exact ⟨s, hs, G.gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff ht hs⟩

/-- **Cut-minimality via transposition gauge distance**: a finite ordered graph `G` is cut-minimal
if and only if the `Equiv.Perm α` gauge distance of `G.toCochain ht.mul_self` equals
`2 * #G.edgeFinset` (Kozlov, Section 2; Beasley, Corollary 7). -/
theorem isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    {t : Equiv.Perm α} (ht : t.IsSwap) :
    G.IsCutMinimal ↔
      (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) = 2 * #G.edgeFinset := by
  classical
  have hbot : (⊤ : SimpleGraph V).between (∅ : Set V) (∅ : Set V)ᶜ = ⊥ := by
    ext u v
    rw [top_between_compl_adj]
    simp
  constructor
  · intro hG
    have hG' : (G ∆ (⊤ : SimpleGraph V).between (∅ : Set V) (∅ : Set V)ᶜ).IsCutMinimal := by
      rwa [hbot, symmDiff_bot]
    have heq : #(G ∆ (⊤ : SimpleGraph V).between (∅ : Set V) (∅ : Set V)ᶜ).edgeFinset =
        #G.edgeFinset :=
      congrArg card (coe_injective (by rw [coe_edgeFinset, coe_edgeFinset, hbot, symmDiff_bot]))
    rw [G.gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff ht hG', heq]
  · intro h
    rw [isCutMinimal_iff_forall_finset_card_edgeFinset_le_symmDiff_top_between]
    intro s
    have hfintype : #(@edgeFinset _ G G.fintypeEdgeSet) = #G.edgeFinset :=
      congrArg card (coe_injective (by simp))
    rw [hfintype]
    have hle : (2 : ℝ) * #G.edgeFinset ≤
        2 * #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset := by
      rw [← h, ← G.cost_movedNorm_toCochain_ite_mem ht (s : Set V)]
      exact (G.toCochain ht.mul_self).gaugeDist_le_cost _ _
    have hle' : 2 * #G.edgeFinset ≤
        2 * #(G ∆ (⊤ : SimpleGraph V).between (s : Set V) (s : Set V)ᶜ).edgeFinset := by
      exact_mod_cast hle
    omega

omit [Fintype α] in
/-- For any transposition `t : Equiv.Perm α`, `G.toCochain ht.mul_self` is a coboundary on
`TwoComplex.complete V` if and only if `G` is a complete-graph cut. -/
theorem isCoboundary_toCochain_iff [Fintype V] [Finite α] (G : SimpleGraph V) {t : Equiv.Perm α}
    (ht : t.IsSwap) :
    (G.toCochain ht.mul_self).IsCoboundary ↔
      ∃ S : Set V, G = (⊤ : SimpleGraph V).between S Sᶜ := by
  cases nonempty_fintype α
  rw [TauCeti.Cochain.isCoboundary_iff_exists_smul_eq_one]
  constructor
  · rintro ⟨β, hβ⟩
    classical
    let S : Set V := {w | Equiv.Perm.sign (β w) = -1}
    have hcomp : Equiv.Perm.parityRetract ht ∘ β = fun w ↦ if w ∈ S then t else 1 := by
      ext w
      rw [Function.comp_apply, Equiv.Perm.parityRetract_apply]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (β w)) with h | h <;>
        simp [S, h, (by decide : (1 : ℤˣ) ≠ -1), (by decide : (-1 : ℤˣ) ≠ 1)]
    have hmap := congrArg (TauCeti.Cochain.map (Equiv.Perm.parityRetract ht)) hβ
    rw [TauCeti.Cochain.map_smul, TauCeti.Cochain.map_one, G.map_parityRetract_toCochain ht,
      hcomp, G.smul_ite_mem_toCochain ht.mul_self S] at hmap
    refine ⟨S, symmDiff_eq_bot.mp ?_⟩
    ext u v
    simp only [bot_adj, iff_false]
    intro hadj
    exact ht.isCycle.ne_one
      ((toCochain_apply_of_adj ht.mul_self hadj).symm.trans
        (congrFun (congrFun (congrArg TauCeti.Cochain.toFun hmap) u) v))
  · rintro ⟨S, rfl⟩
    classical
    refine ⟨fun v ↦ if v ∈ S then t else 1, ?_⟩
    rw [smul_ite_mem_toCochain _ ht.mul_self S, symmDiff_self, bot_toCochain]

/-- The `Equiv.Perm α` gauge distance of `G.toCochain ht.mul_self` vanishes if and only if `G` is a
complete-graph cut. -/
theorem gaugeDist_movedNorm_toCochain_eq_zero_iff [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) = 0 ↔
      ∃ S : Set V, G = (⊤ : SimpleGraph V).between S Sᶜ :=
  ((G.toCochain ht.mul_self).gaugeDist_eq_zero_iff_isCoboundary _).trans
    (G.isCoboundary_toCochain_iff ht)

/-- **Transposition exactness on at most four vertices**: on a vertex type of size at most four,
every graph `G` and every transposition `t` satisfy
`(G.toCochain ht.mul_self).defect (Equiv.Perm.movedNorm α) =
  ((Fintype.card V - 2 : ℕ) : ℝ) * (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α)`. -/
theorem defect_movedNorm_toCochain_eq_card_sub_two_mul_gaugeDist_of_card_le_four
    [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : Fintype.card V ≤ 4)
    {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self).defect (Equiv.Perm.movedNorm α) =
      ((Fintype.card V - 2 : ℕ) : ℝ) *
        (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) := by
  classical
  obtain ⟨s, hs, hval⟩ := G.exists_finset_isCutMinimal_and_gaugeDist_movedNorm_toCochain_eq ht
  rw [G.defect_movedNorm_toCochain ht, hval, ← G.oddTriangleFinset_symmDiff_top_between (s : Set V),
    hs.card_oddTriangleFinset_of_card_le_four hV]
  push_cast
  ring

end SwapGauge

end SimpleGraph

namespace TauCeti

namespace Cochain

section SingleEdge

variable {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]

/-- On `TwoComplex.complete V`, the `Equiv.Perm.movedNorm α` defect of `Cochain.singleEdge` at any
distinct vertices `u ≠ v` and transposition `t` equals `2 * (Fintype.card V - 2 : ℕ)`. -/
theorem defect_movedNorm_singleEdge {u v : V} (huv : u ≠ v) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (singleEdge (TwoComplex.complete V) u v t).defect (Equiv.Perm.movedNorm α) =
      2 * ((Fintype.card V - 2 : ℕ) : ℝ) := by
  classical
  have hcard : #(SimpleGraph.edge u v).edgeFinset = 1 := by
    have : (SimpleGraph.edge u v).edgeFinset = {s(u, v)} :=
      coe_injective <| by
        rw [SimpleGraph.coe_edgeFinset, coe_singleton, SimpleGraph.edgeSet_edge_of_ne huv]
    rw [this, card_singleton]
  have hdeg (w : V) : (SimpleGraph.edge u v).degree w ≤ 1 :=
    ((SimpleGraph.edge u v).degree_le_card_edgeFinset (v := w)).trans_eq hcard
  rw [← SimpleGraph.edge_toCochain u v ht.mul_self,
    (SimpleGraph.edge u v).defect_movedNorm_toCochain ht,
    (SimpleGraph.edge u v).card_oddTriangleFinset_of_degree_le_one hdeg, hcard, mul_one]

/-- On `TwoComplex.complete V` with `3 ≤ Fintype.card V`, the `Equiv.Perm.movedNorm α` gauge
distance of `Cochain.singleEdge` at `u ≠ v` and any transposition `t` equals `2`. -/
theorem gaugeDist_movedNorm_singleEdge_of_three_le_card (hV : 3 ≤ Fintype.card V) {u v : V}
    (huv : u ≠ v) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (singleEdge (TwoComplex.complete V) u v t).gaugeDist (Equiv.Perm.movedNorm α) = 2 := by
  classical
  have hcard : #(SimpleGraph.edge u v).edgeFinset = 1 := by
    have : (SimpleGraph.edge u v).edgeFinset = {s(u, v)} :=
      coe_injective <| by
        rw [SimpleGraph.coe_edgeFinset, coe_singleton, SimpleGraph.edgeSet_edge_of_ne huv]
    rw [this, card_singleton]
  rw [← SimpleGraph.edge_toCochain u v ht.mul_self,
    ((SimpleGraph.edge u v).isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq ht).mp
      (SimpleGraph.isCutMinimal_edge_of_three_le_card hV u v), hcard, Nat.cast_one, mul_one]

end SingleEdge

section ZPowers

/-- Every `Subgroup.zpowers c`-valued `1`-cochain on `TwoComplex.complete V` for an element
`c * c = 1` embeds into `Γ` as `G.toCochain hc` for some simple graph `G`. -/
theorem exists_map_zpowers_subtype_eq_toCochain {V Γ : Type*} [Fintype V] [Group Γ]
    {c : Γ} (hc : c * c = 1) (γ : Cochain (TwoComplex.complete V) (Subgroup.zpowers c)) :
    ∃ G : SimpleGraph V, γ.map (Subgroup.zpowers c).subtype = G.toCochain hc := by
  rcases eq_or_ne c 1 with rfl | hc1
  · refine ⟨⊥, ?_⟩
    ext u v _
    rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one (by simp)).mp (γ u v).property with h | h <;>
      simp [h]
  · let G : SimpleGraph V :=
      { Adj u v := γ u v ≠ 1
        symm := ⟨fun u v h ↦ by rwa [γ.apply_swap u v, inv_ne_one]⟩
        loopless := ⟨fun u h ↦ h (γ.apply_self u)⟩ }
    refine ⟨G, ?_⟩
    ext u v _
    rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one (sq c ▸ hc)).mp (γ u v).property with h | h
    · have h1 : γ u v = 1 := Subtype.ext h
      rw [map_apply, Subgroup.coe_subtype, h,
        SimpleGraph.toCochain_apply_of_not_adj hc (by simp [G, h1])]
    · have hadj : G.Adj u v := fun h1 ↦
        hc1 (h.symm.trans (congrArg Subtype.val h1))
      rw [map_apply, Subgroup.coe_subtype, h, SimpleGraph.toCochain_apply_of_adj hc hadj]

/-- **Parity-retraction subgroup gauge equality**: for any `Subgroup.zpowers t`-valued `1`-cochain
`γ` on a two-complex `X`, embedding `γ` into `Equiv.Perm α` does not change its moved-point gauge
distance (Beasley, Corollary 7). -/
theorem gaugeDist_map_zpowers_subtype {V α : Type*} [Fintype V] [LinearOrder V]
    [Fintype α] [DecidableEq α] {X : TwoComplex V} {t : Equiv.Perm α} (ht : t.IsSwap)
    (γ : Cochain X (Subgroup.zpowers t)) :
    (γ.map (Subgroup.zpowers t).subtype).gaugeDist (Equiv.Perm.movedNorm α) =
      γ.gaugeDist ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) := by
  let ρ : Equiv.Perm α →* Subgroup.zpowers t :=
    (Equiv.Perm.parityRetract ht).codRestrict (Subgroup.zpowers t) fun σ ↦ by
      rw [Equiv.Perm.parityRetract_apply]
      split_ifs
      · exact one_mem _
      · exact Subgroup.mem_zpowers t
  have hρ_id : ρ.comp (Subgroup.zpowers t).subtype = MonoidHom.id (Subgroup.zpowers t) := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one (sq t ▸ ht.mul_self)).mp x.property with
      hx | hx <;>
      simp [ρ, hx]
  have hmap : (γ.map (Subgroup.zpowers t).subtype).map ρ = γ := by
    rw [map_map, hρ_id, map_id]
  have hle := (γ.map (Subgroup.zpowers t).subtype).gaugeDist_map_le
    (ℓ_G := Equiv.Perm.movedNorm α)
    (ℓ_H := (Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective)
    (φ := ρ)
    fun g ↦ by
      rw [GroupNorm.comp_apply, Subgroup.coe_subtype]
      exact Equiv.Perm.movedNorm_parityRetract_le ht g
  rw [hmap] at hle
  exact le_antisymm (γ.gaugeDist_map_subtype_le (Equiv.Perm.movedNorm α) (Subgroup.zpowers t)) hle

/-- **Subgroup cochain exactness on at most four vertices**: on a vertex type of size at most four,
every `Subgroup.zpowers t`-valued `1`-cochain `γ` on `TwoComplex.complete V` for a transposition `t`
satisfies `γ.defect ℓ = ((Fintype.card V - 2 : ℕ) : ℝ) * γ.gaugeDist ℓ` under the restricted
moved-point norm `ℓ := (Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective`. -/
theorem defect_zpowers_swap_eq_card_sub_two_mul_gaugeDist_of_card_le_four
    {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]
    (hV : Fintype.card V ≤ 4) {t : Equiv.Perm α} (ht : t.IsSwap)
    (γ : Cochain (TwoComplex.complete V) (Subgroup.zpowers t)) :
    γ.defect ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) =
      ((Fintype.card V - 2 : ℕ) : ℝ) *
        γ.gaugeDist ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) := by
  obtain ⟨G, hmap⟩ := γ.exists_map_zpowers_subtype_eq_toCochain ht.mul_self
  rw [← γ.defect_map_subtype (Equiv.Perm.movedNorm α) (Subgroup.zpowers t),
    ← γ.gaugeDist_map_zpowers_subtype ht, hmap]
  exact G.defect_movedNorm_toCochain_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV ht

end ZPowers

end Cochain

section PermFinTwo

/-- Simple graphs on a finite vertex type `V` are in bijection with `Equiv.Perm (Fin 2)`-valued
`1`-cochains on `TwoComplex.complete V`: adjacent vertex pairs carry `Equiv.swap 0 1` and
non-adjacent pairs carry `1`. -/
noncomputable def simpleGraphEquivPermFinTwo (V : Type*) [Fintype V] :
    SimpleGraph V ≃ Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2)) where
  toFun G := G.toCochain (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one).mul_self
  invFun α :=
    { Adj u v := α u v ≠ 1
      symm := ⟨fun u v h ↦ by rwa [α.apply_swap u v, inv_ne_one]⟩
      loopless := ⟨fun u h ↦ h (α.apply_self u)⟩ }
  left_inv G := by
    ext u v
    by_cases h : G.Adj u v <;> simp [h]
  right_inv α := by
    ext u v _
    rcases (α u v).eq_one_or_swap_fin_two with h | h <;> simp [h]

/-- `TauCeti.simpleGraphEquivPermFinTwo` agrees with `SimpleGraph.toCochain` at `Equiv.swap 0 1`. -/
theorem simpleGraphEquivPermFinTwo_eq_toCochain {V : Type*} [Fintype V] (G : SimpleGraph V) :
    simpleGraphEquivPermFinTwo V G =
      G.toCochain (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one).mul_self :=
  (rfl)

/-- `TauCeti.simpleGraphEquivPermFinTwo` assigns `Equiv.swap 0 1` to adjacent vertices. -/
@[simp, grind =]
theorem simpleGraphEquivPermFinTwo_apply_of_adj {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : G.Adj u v) :
    simpleGraphEquivPermFinTwo V G u v = Equiv.swap 0 1 :=
  SimpleGraph.toCochain_apply_of_adj
    (Equiv.Perm.swap_isSwap_iff.mpr (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)).mul_self h

/-- `TauCeti.simpleGraphEquivPermFinTwo` assigns `1` to non-adjacent vertices. -/
@[simp, grind =]
theorem simpleGraphEquivPermFinTwo_apply_of_not_adj {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : ¬ G.Adj u v) :
    simpleGraphEquivPermFinTwo V G u v = 1 :=
  SimpleGraph.toCochain_apply_of_not_adj
    (Equiv.Perm.swap_isSwap_iff.mpr (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)).mul_self h

/-- Explicit `ite` evaluation of `TauCeti.simpleGraphEquivPermFinTwo` when `G.Adj` is decidable. -/
theorem simpleGraphEquivPermFinTwo_apply {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) :
    simpleGraphEquivPermFinTwo V G u v = if G.Adj u v then Equiv.swap 0 1 else 1 :=
  G.toCochain_apply
    (Equiv.Perm.swap_isSwap_iff.mpr (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)).mul_self u v

/-- The inverse of `TauCeti.simpleGraphEquivPermFinTwo` makes `u` and `v` adjacent precisely when
`α u v ≠ 1`. -/
@[simp, grind =]
theorem simpleGraphEquivPermFinTwo_symm_adj {V : Type*} [Fintype V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) (u v : V) :
    ((simpleGraphEquivPermFinTwo V).symm α).Adj u v ↔ α u v ≠ 1 :=
  (Iff.rfl)

/-- Adjacency in `(simpleGraphEquivPermFinTwo V).symm α` is decidable because equality in
`Equiv.Perm (Fin 2)` is decidable. -/
instance instDecidableRelSimpleGraphEquivPermFinTwoSymm {V : Type*} [Fintype V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    DecidableRel ((simpleGraphEquivPermFinTwo V).symm α).Adj :=
  fun u v ↦ inferInstanceAs (Decidable (α u v ≠ 1))

/-- **Ambient-degree invariance of transposition gauge distance**: the `Equiv.Perm α` gauge distance
of `G.toCochain ht.mul_self` depends only on `G`, and coincides with the `Equiv.Perm (Fin 2)` gauge
distance of `simpleGraphEquivPermFinTwo V G`. -/
theorem _root_.SimpleGraph.gaugeDist_movedNorm_toCochain_eq_fin_two
    {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) =
      (simpleGraphEquivPermFinTwo V G).gaugeDist (Equiv.Perm.movedNorm (Fin 2)) := by
  classical
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one
  obtain ⟨s, hs⟩ := G.exists_finset_isCutMinimal_symmDiff_top_between
  rw [simpleGraphEquivPermFinTwo_eq_toCochain,
    G.gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff ht hs,
    G.gaugeDist_movedNorm_toCochain_eq_of_isCutMinimal_symmDiff hswap hs]

/-- **Cut-minimality via binary gauge distance**: a finite ordered graph `G` is cut-minimal if and
only if the `Equiv.Perm (Fin 2)` gauge distance of `simpleGraphEquivPermFinTwo V G` equals
`2 * #G.edgeFinset`. -/
theorem _root_.SimpleGraph.isCutMinimal_iff_gaugeDist_movedNorm_fin_two_eq
    {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.IsCutMinimal ↔
      (simpleGraphEquivPermFinTwo V G).gaugeDist (Equiv.Perm.movedNorm (Fin 2)) =
        2 * #G.edgeFinset := by
  rw [simpleGraphEquivPermFinTwo_eq_toCochain]
  exact G.isCutMinimal_iff_gaugeDist_movedNorm_toCochain_eq
    (Equiv.Perm.swap_isSwap_iff.mpr (Fin.zero_ne_one : (0 : Fin 2) ≠ 1))

/-- **Binary edge-set cost bridge**: for any `Equiv.Perm (Fin 2)`-valued `1`-cochain `α` on
`TwoComplex.complete V` and gauge `β`, `α.cost (Equiv.Perm.movedNorm (Fin 2)) β` equals twice the
edge count of the support graph of `α` switched by the cut `{w | β w ≠ 1}`. -/
theorem Cochain.cost_movedNorm_fin_two {V : Type*} [Fintype V] [LinearOrder V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) (β : V → Equiv.Perm (Fin 2)) :
    α.cost (Equiv.Perm.movedNorm (Fin 2)) β =
      2 * #(((simpleGraphEquivPermFinTwo V).symm α) ∆
        (⊤ : SimpleGraph V).between {w | β w ≠ 1} {w | β w ≠ 1}ᶜ).edgeFinset := by
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one
  have hβ : β = fun v ↦ if v ∈ {w | β w ≠ 1} then Equiv.swap 0 1 else 1 :=
    funext fun v ↦ Equiv.Perm.eq_ite_ne_one_fin_two (β v)
  conv_lhs =>
    rw [← (simpleGraphEquivPermFinTwo V).apply_symm_apply α,
      simpleGraphEquivPermFinTwo_eq_toCochain, hβ]
  exact ((simpleGraphEquivPermFinTwo V).symm α).cost_movedNorm_toCochain_ite_mem hswap {w | β w ≠ 1}

/-- **Binary odd-triangle defect bridge**: for any `Equiv.Perm (Fin 2)`-valued `1`-cochain `α` on
`TwoComplex.complete V`, `α.defect (Equiv.Perm.movedNorm (Fin 2))` equals twice the number of odd
triangles of its support graph `(simpleGraphEquivPermFinTwo V).symm α`. -/
theorem Cochain.defect_movedNorm_fin_two {V : Type*} [Fintype V] [LinearOrder V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    α.defect (Equiv.Perm.movedNorm (Fin 2)) =
      2 * #((simpleGraphEquivPermFinTwo V).symm α).oddTriangleFinset := by
  conv_lhs =>
    rw [← (simpleGraphEquivPermFinTwo V).apply_symm_apply α,
      simpleGraphEquivPermFinTwo_eq_toCochain]
  exact ((simpleGraphEquivPermFinTwo V).symm α).defect_movedNorm_toCochain
    (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one)

/-- **Binary cut-minimality characterization**: the support graph of
`α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))` is cut-minimal if and only if
`α.gaugeDist (Equiv.Perm.movedNorm (Fin 2))` equals twice its edge count. -/
theorem Cochain.isCutMinimal_symm_simpleGraphEquivPermFinTwo_iff {V : Type*}
    [Fintype V] [LinearOrder V] (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    ((simpleGraphEquivPermFinTwo V).symm α).IsCutMinimal ↔
      α.gaugeDist (Equiv.Perm.movedNorm (Fin 2)) =
        2 * #((simpleGraphEquivPermFinTwo V).symm α).edgeFinset := by
  rw [((simpleGraphEquivPermFinTwo V).symm α).isCutMinimal_iff_gaugeDist_movedNorm_fin_two_eq,
    (simpleGraphEquivPermFinTwo V).apply_symm_apply]

/-- An `Equiv.Perm (Fin 2)`-valued `1`-cochain on `TwoComplex.complete V` is a coboundary if and
only if its support graph is a complete-graph cut. -/
theorem Cochain.isCoboundary_fin_two_iff {V : Type*} [Fintype V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    α.IsCoboundary ↔
      ∃ S : Set V, (simpleGraphEquivPermFinTwo V).symm α = (⊤ : SimpleGraph V).between S Sᶜ := by
  conv_lhs =>
    rw [← (simpleGraphEquivPermFinTwo V).apply_symm_apply α,
      simpleGraphEquivPermFinTwo_eq_toCochain]
  exact ((simpleGraphEquivPermFinTwo V).symm α).isCoboundary_toCochain_iff
    (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one)

/-- **Binary cochain exactness on at most four vertices**: on a vertex type of size at most four,
every `α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))` satisfies
`α.defect (Equiv.Perm.movedNorm (Fin 2)) =
  ((Fintype.card V - 2 : ℕ) : ℝ) * α.gaugeDist (Equiv.Perm.movedNorm (Fin 2))`. -/
theorem Cochain.defect_movedNorm_fin_two_eq_card_sub_two_mul_gaugeDist_of_card_le_four
    {V : Type*} [Fintype V] [LinearOrder V] (hV : Fintype.card V ≤ 4)
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    α.defect (Equiv.Perm.movedNorm (Fin 2)) =
      ((Fintype.card V - 2 : ℕ) : ℝ) * α.gaugeDist (Equiv.Perm.movedNorm (Fin 2)) := by
  let G := (simpleGraphEquivPermFinTwo V).symm α
  rw [← (simpleGraphEquivPermFinTwo V).apply_symm_apply α, simpleGraphEquivPermFinTwo_eq_toCochain]
  exact G.defect_movedNorm_toCochain_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV
    (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one)

/-- On `TwoComplex.complete V` with `Fintype.card V ≤ 4`, the binary Cheeger constant
`h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2))` equals `(Fintype.card V - 2 : ℕ)`. -/
theorem h1_complete_movedNorm_fin_two_of_card_le_four {V : Type*} [Fintype V] [LinearOrder V]
    (hV : Fintype.card V ≤ 4) :
    h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2)) = (Fintype.card V - 2 : ℕ) := by
  by_cases hV3 : 3 ≤ Fintype.card V
  · have : Nontrivial (Equiv.Perm (Fin 2)) := ⟨⟨1, Equiv.swap 0 1, by decide⟩⟩
    obtain ⟨α₀, hα₀⟩ := exists_gaugeDist_pos_complete hV3 (Equiv.Perm.movedNorm (Fin 2))
    refine le_antisymm ?_ (le_h1_of_forall ⟨α₀, hα₀⟩ fun α hα ↦ ?_)
    · exact (h1_le_div hα₀).trans_eq (by
        rw [α₀.defect_movedNorm_fin_two_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV,
          mul_div_cancel_right₀ _ hα₀.ne'])
    · rw [α.defect_movedNorm_fin_two_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV,
        mul_div_cancel_right₀ _ hα.ne']
  · have hV2 : Fintype.card V ≤ 2 := by omega
    have hsub : Fintype.card V - 2 = 0 := by omega
    rw [hsub, Nat.cast_zero]
    refine h1_eq_zero_of_forall_gaugeDist_eq_zero fun α ↦ ?_
    classical
    let G := (simpleGraphEquivPermFinTwo V).symm α
    obtain ⟨s, hs, hval⟩ := G.exists_finset_isCutMinimal_and_gaugeDist_movedNorm_toCochain_eq
      (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one)
    rw [← (simpleGraphEquivPermFinTwo V).apply_symm_apply α,
      simpleGraphEquivPermFinTwo_eq_toCochain, hval, hs.edgeFinset_eq_empty_of_card_le_two hV2,
      card_empty, Nat.cast_zero, mul_zero]

/-- **Four-vertex binary Cheeger constant**: when `Fintype.card V = 4`,
`h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2)) = 2`. -/
theorem h1_complete_movedNorm_fin_two_of_card_eq_four {V : Type*} [Fintype V] [LinearOrder V]
    (hV : Fintype.card V = 4) :
    h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2)) = 2 := by
  rw [h1_complete_movedNorm_fin_two_of_card_le_four hV.le, hV]
  norm_cast

/-- On `TwoComplex.complete V` with `Fintype.card V ≤ 4`, the Cheeger constant of the two-element
subgroup `Subgroup.zpowers t` generated by a transposition `t` under the restricted moved-point norm
equals `(Fintype.card V - 2 : ℕ)`. -/
theorem h1_complete_zpowers_swap_of_card_le_four {V α : Type*} [Fintype V] [LinearOrder V]
    [Fintype α] [DecidableEq α] (hV : Fintype.card V ≤ 4) {t : Equiv.Perm α} (ht : t.IsSwap) :
    h1 (TwoComplex.complete V)
        ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) =
      (Fintype.card V - 2 : ℕ) := by
  by_cases hV3 : 3 ≤ Fintype.card V
  · have : Nontrivial (Subgroup.zpowers t) :=
      ⟨⟨1, ⟨t, Subgroup.mem_zpowers t⟩, fun h ↦
        ht.isCycle.ne_one (congrArg Subtype.val h).symm⟩⟩
    obtain ⟨γ₀, hγ₀⟩ := exists_gaugeDist_pos_complete hV3
      ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective)
    refine le_antisymm ?_ (le_h1_of_forall ⟨γ₀, hγ₀⟩ fun γ hγ ↦ ?_)
    · exact (h1_le_div hγ₀).trans_eq (by
        rw [γ₀.defect_zpowers_swap_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV ht,
          mul_div_cancel_right₀ _ hγ₀.ne'])
    · rw [γ.defect_zpowers_swap_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV ht,
        mul_div_cancel_right₀ _ hγ.ne']
  · have hV2 : Fintype.card V ≤ 2 := by omega
    have hsub : Fintype.card V - 2 = 0 := by omega
    rw [hsub, Nat.cast_zero]
    refine h1_eq_zero_of_forall_gaugeDist_eq_zero fun γ ↦ ?_
    classical
    obtain ⟨G, hmap⟩ := γ.exists_map_zpowers_subtype_eq_toCochain ht.mul_self
    obtain ⟨s, hs, hval⟩ := G.exists_finset_isCutMinimal_and_gaugeDist_movedNorm_toCochain_eq ht
    rw [← γ.gaugeDist_map_zpowers_subtype ht, hmap, hval,
      hs.edgeFinset_eq_empty_of_card_le_two hV2, card_empty, Nat.cast_zero, mul_zero]

/-- **Four-vertex transposition-subgroup Cheeger constant**: when `Fintype.card V = 4`, the Cheeger
constant of `Subgroup.zpowers t` under the restricted moved-point norm equals `2`. -/
theorem h1_complete_zpowers_swap_of_card_eq_four {V α : Type*} [Fintype V] [LinearOrder V]
    [Fintype α] [DecidableEq α] (hV : Fintype.card V = 4) {t : Equiv.Perm α} (ht : t.IsSwap) :
    h1 (TwoComplex.complete V)
        ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) = 2 := by
  rw [h1_complete_zpowers_swap_of_card_le_four hV.le ht, hV]
  norm_cast

end PermFinTwo

end TauCeti
