/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import TauCeti.Combinatorics.SimpleGraph.OrderedEdges
public import TauCeti.GroupTheory.Perm.DistErr.Basic
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Data.Finset.Prod
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.DistErr.Invariance
import TauCeti.GroupTheory.Perm.ParityRetract

/-!
# Transposition-labelled graph cochains, cut-minimality, and cross-degree gauge bounds

Given a simple graph `G` on a linearly ordered finite vertex type `V` and a transposition `τ` in a
symmetric group `Equiv.Perm A`, assigning `τ` to edges of `G` and `1` to non-edges produces an
inversion-symmetric permutation edge assignment whose holonomy and gauge costs reduce to graph
combinatorics:

* **Transposition holonomy and parity-retracted edge bounds**
  (`Equiv.Perm.movedNorm_mul_triple_ite_isSwap`,
  `Equiv.Perm.movedNorm_inv_mul_ite_mul_of_eq_one_or`, and
  `Equiv.Perm.ite_xor_sign_le_movedNorm_inv_mul_ite_mul`): the `movedNorm` of a triple product of
  `{1, τ}` factors detects `Xor` parity (`2` on odd parity, `0` on even parity), `{1, τ}`-valued
  gauges toggle edges by `Xor`, and `Equiv.Perm.parityRetract` bounds the `movedNorm` under any
  gauge in `Equiv.Perm A` from below by the cut of odd-sign vertices.
* **Binary edge-set dictionary, degree-independent gauge distance, and cut-minimality**
  (`TauCeti.perm_fin_two_eq_ite_fromRel`, `TauCeti.fromRel_ite_ne_one`,
  `TauCeti.sum_filter_lt_movedNorm_triple_ite_isSwap`,
  `TauCeti.sum_filter_lt_movedNorm_ite_isSwap_of_forall_eq_one_or`,
  `TauCeti.ciInf_sum_filter_lt_movedNorm_ite_isSwap`, and
  `TauCeti.ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff`): loop-free
  inversion-symmetric `Perm (Fin 2)` assignments correspond bijectively to simple graphs, the
  triangle holonomy defect equals twice the number of `3`-vertex subsets spanning an odd number of
  edges, the `movedNorm` gauge-cost infimum over `V → Perm A` equals twice the minimum cut-toggled
  edge count independently of `A` and `τ`, and this infimum equals `2 * #G.edgeFinset` if and only
  if `G.IsCutMinimal`.
* **Cross-degree gauge optimization for cut-minimal graphs and Kozlov's parameters**
  (`TauCeti.ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff`,
  `TauCeti.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_isCutMinimal`,
  `TauCeti.six_mul_add_three_lt_mul_four_mul_sq_add`, and
  `TauCeti.ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_kozlov`): when `G.IsCutMinimal` and
  `8 * #G.edgeFinset ≤ 3 * (Fintype.card V).choose 2`, no unequal-degree gauge in `Perm (Fin m)`
  (`m ≠ 3`) beats the degree-`3` transposition gauge-cost infimum `2 * #G.edgeFinset / 3`. In
  particular, for Kozlov's parameters `Fintype.card V = q * (2 * t + 1)` and
  `#G.edgeFinset = q ^ 2 * t * (t + 1) / 2` (`q, t ≥ 1`), the global cross-degree infimum over all
  gauge degrees `m + 2 ≥ 2` equals `q ^ 2 * t * (t + 1) / 3`, with ratio `Fintype.card V / 3`
  whenever the odd-triangle count is `(Fintype.card V / 3) * #G.edgeFinset`.

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, Section 2 and
  Theorem 4.2.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Section 2.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, doi:10.5281/zenodo.23245792, Corollary 7, Theorem 8, and Proposition 10.
-/

public section

open Finset
open scoped symmDiff

private theorem ite_inv_of_mul_self {G : Type*} [Group G] {t : G} (ht : t * t = 1)
    (p : Prop) [Decidable p] : (if p then t else 1)⁻¹ = if p then t else 1 := by
  split_ifs
  · exact inv_eq_of_mul_eq_one_right ht
  · exact inv_one

private theorem ite_mul_ite_mul_ite_of_mul_self {G : Type*} [Group G] {t : G} (ht : t * t = 1)
    (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    (if p then t else 1) * (if q then t else 1) * (if r then t else 1) =
      if Xor p (Xor q r) then t else 1 := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp [hp, hq, hr, Xor, ht]

namespace Equiv.Perm

variable {A : Type*} [Fintype A] [DecidableEq A] {τ : Perm A}

/-! ### Transposition holonomy and parity-retracted edge bounds -/

/-- Multiplying three `{1, τ}` indicators of a transposition `τ` gives moved-point norm `2` when an
odd number of the three conditions hold, and `0` otherwise. -/
theorem movedNorm_mul_triple_ite_isSwap (hτ : τ.IsSwap) (p q r : Prop) [Decidable p]
    [Decidable q] [Decidable r] :
    movedNorm A ((if p then τ else 1) * (if q then τ else 1) * (if r then τ else 1)) =
      if Xor p (Xor q r) then 2 else 0 := by
  have hτ₂ : τ * τ = 1 := by
    rcases hτ with ⟨x, y, -, rfl⟩
    exact Equiv.swap_mul_self x y
  rw [ite_mul_ite_mul_ite_of_mul_self hτ₂]
  split_ifs <;> simp [hτ.movedNorm]

/-- Variant of `Equiv.Perm.movedNorm_mul_triple_ite_isSwap` with the third indicator inverted,
matching the `α u v * α v w * (α u w)⁻¹` triangle-holonomy convention. -/
theorem movedNorm_mul_triple_ite_inv_isSwap (hτ : τ.IsSwap) (p q r : Prop) [Decidable p]
    [Decidable q] [Decidable r] :
    movedNorm A ((if p then τ else 1) * (if q then τ else 1) * (if r then τ else 1)⁻¹) =
      if Xor p (Xor q r) then 2 else 0 := by
  have hτ₂ : τ * τ = 1 := by
    rcases hτ with ⟨x, y, -, rfl⟩
    exact Equiv.swap_mul_self x y
  rw [ite_inv_of_mul_self hτ₂, movedNorm_mul_triple_ite_isSwap hτ]

/-- For `{1, τ}`-valued endpoints `b₁` and `b₂`, gauge-conjugating a `{1, τ}` indicator gives
moved-point norm `2` when `p` differs from `Xor (b₁ ≠ 1) (b₂ ≠ 1)`, and `0` otherwise. -/
theorem movedNorm_inv_mul_ite_mul_of_eq_one_or (hτ : τ.IsSwap) {b₁ b₂ : Perm A}
    (hb₁ : b₁ = 1 ∨ b₁ = τ) (hb₂ : b₂ = 1 ∨ b₂ = τ) (p : Prop) [Decidable p] :
    movedNorm A (b₁⁻¹ * (if p then τ else 1) * b₂) =
      if Xor p (Xor (b₁ ≠ 1) (b₂ ≠ 1)) then 2 else 0 := by
  have hτ₂ : τ * τ = 1 := by
    rcases hτ with ⟨x, y, -, rfl⟩
    exact Equiv.swap_mul_self x y
  have hτ_inv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ₂
  have hτ_ne : τ ≠ 1 := hτ.isCycle.ne_one
  rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;> by_cases hp : p <;>
    simp [hp, hτ₂, hτ_inv, hτ_ne, hτ.movedNorm, Xor]

/-- For arbitrary `g h : Perm A`, retracting along `Equiv.Perm.parityRetract` bounds the moved-point
norm of `g⁻¹ * (if p then τ else 1) * h` from below by the `{0, 2}` parity indicator of the signs of
`g` and `h`. -/
theorem ite_xor_sign_le_movedNorm_inv_mul_ite_mul (hτ : τ.IsSwap) (g h : Perm A) (p : Prop)
    [Decidable p] :
    (if Xor p (Xor (sign g = -1) (sign h = -1)) then (2 : ℝ) else 0) ≤
      movedNorm A (g⁻¹ * (if p then τ else 1) * h) := by
  let r := parityRetract hτ
  have hle := movedNorm_parityRetract_le hτ (g⁻¹ * (if p then τ else 1) * h)
  have hmap : r (g⁻¹ * (if p then τ else 1) * h) = (r g)⁻¹ * (if p then τ else 1) * r h := by
    rw [map_mul, map_mul, map_inv]
    congr 2
    split_ifs <;> simp [r]
  have hr (σ : Perm A) : (r σ = 1 ∨ r σ = τ) ∧ (r σ ≠ 1 ↔ sign σ = -1) := by
    rcases Int.units_eq_one_or (sign σ) with hσ | hσ
    · simp [r, hσ, Units.ext_iff]
    · simp [r, hσ, hτ.isCycle.ne_one]
  rw [hmap, movedNorm_inv_mul_ite_mul_of_eq_one_or hτ (hr g).1 (hr h).1 p] at hle
  simpa only [(hr g).2, (hr h).2] using hle

end Equiv.Perm

namespace TauCeti

open Equiv Equiv.Perm

/-! ### Binary edge-set dictionary, degree-independent gauge distance, and cut-minimality -/

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

/-- Recovering a simple graph from its `{1, t}` edge indicator (`t ≠ 1`) returns the original
graph. -/
theorem fromRel_ite_ne_one {V M : Type*} [One M] (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : M} (ht : t ≠ 1) :
    SimpleGraph.fromRel (fun u v => (if G.Adj u v then t else 1) ≠ 1) = G := by
  simp [ht]

section GraphBridge

variable {V A : Type*} [Fintype V] [LinearOrder V] [Fintype A] [DecidableEq A]

private theorem sum_ite_two_zero {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P] :
    (∑ x ∈ s, if P x then (2 : ℝ) else 0) = 2 * (#{x ∈ s | P x} : ℝ) := by
  have hterm (x : ι) : (if P x then (2 : ℝ) else 0) = 2 * if P x then (1 : ℝ) else 0 := by
    split_ifs <;> ring
  simp_rw [hterm, ← mul_sum, sum_boole]

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
  rw [sum_ite_two_zero, filter_filter,
    ← G.card_filter_lt_xor_adj_triple_eq_card_powersetCard_three_odd]
  congr 3
  ext t
  simp [and_assoc]

/-- Variant of `TauCeti.sum_filter_lt_movedNorm_triple_ite_isSwap` using `(α u w)⁻¹` on the third
edge of each increasing triple `(u, v, w)`. -/
theorem sum_filter_lt_movedNorm_triple_ite_inv_isSwap (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm A} (hτ : τ.IsSwap) :
    (∑ t ∈ ({t : V × V × V | t.1 < t.2.1 ∧ t.2.1 < t.2.2} : Finset (V × V × V)),
        movedNorm A ((if G.Adj t.1 t.2.1 then τ else 1) *
          (if G.Adj t.2.1 t.2.2 then τ else 1) * (if G.Adj t.1 t.2.2 then τ else 1)⁻¹)) =
      2 * (#{s ∈ (univ : Finset V).powersetCard 3 |
        Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} : ℝ) := by
  have hτ₂ : τ * τ = 1 := by
    rcases hτ with ⟨x, y, -, rfl⟩
    exact Equiv.swap_mul_self x y
  refine (sum_congr rfl fun t _ => ?_).trans (sum_filter_lt_movedNorm_triple_ite_isSwap G hτ)
  rw [ite_inv_of_mul_self hτ₂]
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
  rw [sum_ite_two_zero, filter_filter,
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
    change (if v ∈ S then τ else 1) ≠ 1 ↔ v ∈ S
    split_ifs with hv <;> simp [hv, hτ.isCycle.ne_one]
  have heq :
      ((⊤ : SimpleGraph V).between {v | β v ≠ 1} {v | β v ≠ 1}ᶜ).edgeFinset =
        ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
    ext e
    simp [hset]
  simpa only [β, heq] using sum_filter_lt_movedNorm_ite_isSwap_of_forall_eq_one_or G hτ hβ

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
  rw [sum_ite_two_zero, filter_filter, G.card_filter_lt_adj_eq_card_edgeFinset]

/-- In `Perm (Fin 2)`, every gauge `β : V → Perm (Fin 2)` has moved-point cost equal to twice the
edge count of `G` after toggling the cut `{v | β v ≠ 1}`. -/
theorem sum_filter_lt_movedNorm_fin_two_ite_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : V → Perm (Fin 2)) :
    (∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        movedNorm (Fin 2) ((β e.1)⁻¹ *
          (if G.Adj e.1 e.2 then Equiv.swap 0 1 else 1) * β e.2)) =
      2 * (#(G.edgeFinset ∆
        ((⊤ : SimpleGraph V).between {v | β v ≠ 1} {v | β v ≠ 1}ᶜ).edgeFinset) : ℝ) :=
  sum_filter_lt_movedNorm_ite_isSwap_of_forall_eq_one_or G
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
  rw [sum_ite_two_zero, filter_filter] at hsum
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
      exact sum_filter_lt_movedNorm_ite_isSwap_indicator G hτ (S : Set V)
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
    exact two_mul_card_symmDiff_le_sum_filter_lt_movedNorm_ite_isSwap G hτ β

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
  rw [ciInf_sum_filter_lt_movedNorm_ite_isSwap G hτ₁,
    ciInf_sum_filter_lt_movedNorm_ite_isSwap G hτ₂]

/-- The moved-point gauge-cost infimum of a `τ`-labelled graph `G` over `V → Perm A` equals
`2 * #G.edgeFinset` if and only if `G` is cut-minimal. -/
theorem ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm A} (hτ : τ.IsSwap) :
    (⨅ β : V → Perm A,
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2)) =
      2 * (#G.edgeFinset : ℝ) ↔ G.IsCutMinimal := by
  rw [ciInf_sum_filter_lt_movedNorm_ite_isSwap G hτ,
    mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0), G.ciInf_card_symmDiff_edgeFinset_eq_iff]

/-- A cut-minimal graph `G` with at least one edge has strictly positive moved-point gauge-cost
infimum for any transposition `τ : Perm A`. -/
theorem ciInf_sum_filter_lt_movedNorm_ite_isSwap_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    {τ : Perm A} (hτ : τ.IsSwap) (hcut : G.IsCutMinimal) (hne : G.edgeFinset.Nonempty) :
    0 < ⨅ β : V → Perm A,
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        movedNorm A ((β e.1)⁻¹ * (if G.Adj e.1 e.2 then τ else 1) * β e.2) := by
  have hEpos : (0 : ℝ) < #G.edgeFinset := Nat.cast_pos.mpr hne.card_pos
  rw [(ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff G hτ).mpr hcut]
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
  rw [(ciInf_sum_filter_lt_movedNorm_ite_isSwap_eq_two_mul_card_iff G hτ).mpr hcut,
    sum_filter_lt_movedNorm_triple_ite_isSwap G hτ, hodd]
  have h2E : (2 * (#G.edgeFinset : ℝ)) ≠ 0 := by positivity
  field_simp [h2E]

end GraphBridge

/-! ### Equal-degree and cross-degree (`distErr`) optimization for cut-minimal graphs -/

section CrossDegree

variable {V : Type*} [Fintype V] [LinearOrder V]

private theorem two_le_of_isSwap_fin {n : ℕ} {τ : Perm (Fin n)} (hτ : τ.IsSwap) : 2 ≤ n := by
  have h2 : #τ.support = 2 := card_support_eq_two.mpr hτ
  have hle : #τ.support ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
  omega

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
  have hn2 : 2 ≤ n := two_le_of_isSwap_fin hτ
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
  rw [← ciInf_sum_filter_lt_movedNorm_ite_isSwap G hτ]
  refine le_antisymm ?_ ?_
  · refine (le_div_iff₀ hn_pos).mpr (le_ciInf fun β => ?_)
    exact (mul_le_mul_of_nonneg_right (ciInf_le ⟨0, by
      rintro _ ⟨β', rfl⟩
      exact div_nonneg (sum_nonneg fun _ _ => apply_nonneg (movedNorm (Fin n)) _) hn_pos.le⟩ β)
      hn_pos.le).trans_eq (div_mul_cancel₀ _ hn_pos.ne')
  · exact le_ciInf fun β => div_le_div_of_nonneg_right (ciInf_le hbdd β) hn_pos.le

/-- In equal degree `n`, the `distErr` gauge-cost infimum of a `τ`-labelled graph `G` (`τ.IsSwap`)
equals `2 * #G.edgeFinset / n` if and only if `G` is cut-minimal. -/
theorem ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff {n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] {τ : Perm (Fin n)} (hτ : τ.IsSwap) :
    (⨅ β : V → Perm (Fin n),
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then τ else 1) (β e.1 * (β e.2)⁻¹)) =
      2 * (#G.edgeFinset : ℝ) / n ↔ G.IsCutMinimal := by
  have hn2 : 2 ≤ n := two_le_of_isSwap_fin hτ
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [ciInf_sum_filter_lt_distErr_ite_isSwap G hτ, div_left_inj₀ hn_ne,
    mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0), G.ciInf_card_symmDiff_edgeFinset_eq_iff]

/-- In `Perm (Fin 2)` at `Equiv.swap 0 1`, the `distErr` gauge-cost infimum equals `#G.edgeFinset`
if and only if `G` is cut-minimal. -/
theorem ciInf_sum_filter_lt_distErr_fin_two_ite_swap_eq_card_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (⨅ β : V → Perm (Fin 2),
        ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
          distErr (if G.Adj e.1 e.2 then Equiv.swap (0 : Fin 2) 1 else 1) (β e.1 * (β e.2)⁻¹)) =
      (#G.edgeFinset : ℝ) ↔ G.IsCutMinimal := by
  have h := ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff G
    (swap_isSwap_iff.mpr (by decide : (0 : Fin 2) ≠ 1))
  norm_num at h
  exact h

/-- Comparing any degree-`3` edge assignment on `V` against a degree-`2` gauge incurs total
distance with errors at least `(Fintype.card V).choose 2 / 3`. -/
theorem choose_two_div_three_le_sum_filter_lt_distErr_three_two (α : V → V → Perm (Fin 3))
    (β : V → Perm (Fin 2)) :
    ((Fintype.card V).choose 2 : ℝ) / 3 ≤
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  set E : Finset (V × V) := {p : V × V | p.1 < p.2}
  have hcard : #E = (Fintype.card V).choose 2 := Fintype.card_product_filter_lt
  have h := E.card_nsmul_le_sum _ _ fun e _ =>
    one_div_three_le_distErr_three_two (α e.1 e.2) (β e.1 * (β e.2)⁻¹)
  simpa [hcard, nsmul_eq_mul, div_eq_mul_inv] using h

/-- Comparing any degree-`3` edge assignment on `V` against a gauge of any unequal degree `m ≠ 3`
incurs total distance with errors at least `(Fintype.card V).choose 2 / 4`. -/
theorem choose_two_div_four_le_sum_filter_lt_distErr_three_of_ne {m : ℕ}
    (α : V → V → Perm (Fin 3)) (β : V → Perm (Fin m)) (hne : m ≠ 3) :
    ((Fintype.card V).choose 2 : ℝ) / 4 ≤
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  set E : Finset (V × V) := {p : V × V | p.1 < p.2}
  have hcard : #E = (Fintype.card V).choose 2 := Fintype.card_product_filter_lt
  simpa [hcard] using E.card_div_four_le_sum_distErr_three_of_ne
    (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹) hne

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
    exact ((ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff G hτ).mpr hcut).symm.trans_le
      (ciInf_le hbdd β)
  · refine le_trans ?_
      (choose_two_div_four_le_sum_filter_lt_distErr_three_of_ne
        (fun u v => if G.Adj u v then τ else 1) β hm)
    have hdens' : 8 * (#G.edgeFinset : ℝ) ≤ 3 * ((Fintype.card V).choose 2 : ℝ) := by
      exact_mod_cast hdens
    linarith

/-- Whenever `8 * r < 3 * (Fintype.card V).choose 2`, every unequal-degree gauge
`β : V → Perm (Fin m)` (`m ≠ 3`) has cross-degree cost strictly exceeding `2 * r / 3` against any
degree-`3` edge assignment `α`. -/
theorem two_mul_div_three_lt_sum_filter_lt_distErr_three_of_ne {r m : ℕ}
    (α : V → V → Perm (Fin 3)) (hr : 8 * r < 3 * (Fintype.card V).choose 2)
    (β : V → Perm (Fin m)) (hm : m ≠ 3) :
    2 * (r : ℝ) / 3 <
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  refine lt_of_lt_of_le ?_ (choose_two_div_four_le_sum_filter_lt_distErr_three_of_ne α β hm)
  have hr' : 8 * (r : ℝ) < 3 * ((Fintype.card V).choose 2 : ℝ) := by exact_mod_cast hr
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
    le_ciInf (two_mul_card_div_three_le_sum_filter_lt_distErr_three_ite_isSwap G hτ hcut hdens)
  have hbdd : BddBelow (Set.range f) :=
    ⟨2 * (#G.edgeFinset : ℝ) / 3, by rintro _ ⟨m, rfl⟩; exact hf_ge m⟩
  refine le_antisymm ?_ (le_ciInf hf_ge)
  exact (ciInf_le hbdd 1).trans_eq ((ciInf_sum_filter_lt_distErr_ite_isSwap_eq_iff G hτ).mpr hcut)

/-! ### Kozlov parameter arithmetic and cross-degree staircase consequences -/

/-- Polynomial inequality comparing Kozlov's degree-`3` staircase cost with the `1 / 4` cross-degree
mismatch baseline: for `1 ≤ q` and `1 ≤ t`, `6 * t + 3 < q * (4 * t ^ 2 + 4 * t + 3)`. -/
theorem six_mul_add_three_lt_mul_four_mul_sq_add {q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) :
    6 * t + 3 < q * (4 * t ^ 2 + 4 * t + 3) := by
  rcases Nat.exists_eq_add_of_le' hq with ⟨q', rfl⟩
  rcases Nat.exists_eq_add_of_le' ht with ⟨t', rfl⟩
  nlinarith

/-- Weak form of `TauCeti.six_mul_add_three_lt_mul_four_mul_sq_add`. -/
theorem six_mul_add_three_le_mul_four_mul_sq_add {q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) :
    6 * t + 3 ≤ q * (4 * t ^ 2 + 4 * t + 3) :=
  (six_mul_add_three_lt_mul_four_mul_sq_add hq ht).le

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
  have hdiff : 3 * ((q' + 1) * (2 * (t' + 1) + 1) * (2 * q' * t' + 3 * q' + 2 * t' + 2)) =
      8 * ((q' + 1) ^ 2 * (t' + 1) * (t' + 1 + 1)) +
        (q' + 1) * ((q' + 1) * (4 * (t' + 1) ^ 2 + 4 * (t' + 1) + 3) -
          (6 * (t' + 1) + 3)) := by
    have hlt := six_mul_add_three_le_mul_four_mul_sq_add hq ht
    zify [hlt]
    ring
  have hpos : 0 < (q' + 1) *
      ((q' + 1) * (4 * (t' + 1) ^ 2 + 4 * (t' + 1) + 3) - (6 * (t' + 1) + 3)) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt (six_mul_add_three_lt_mul_four_mul_sq_add hq ht))
  omega

private theorem two_mul_cast_half_kozlov (q t : ℕ) :
    2 * ((q ^ 2 * t * (t + 1) / 2 : ℕ) : ℝ) = (q : ℝ) ^ 2 * t * (t + 1) := by
  have heven : 2 ∣ q ^ 2 * t * (t + 1) := by
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right (Nat.even_mul_succ_self t).two_dvd _
  have hnat : 2 * (q ^ 2 * t * (t + 1) / 2) = q ^ 2 * t * (t + 1) := by
    rw [mul_comm, Nat.div_mul_cancel heven]
  exact_mod_cast hnat

/-- On a vertex set of size `q * (2 * t + 1)` (`1 ≤ q`, `1 ≤ t`), every unequal-degree gauge
`β : V → Perm (Fin m)` (`m ≠ 3`) has cross-degree cost strictly exceeding
`q ^ 2 * t * (t + 1) / 3` against any degree-`3` edge assignment `α`. -/
theorem lt_sum_filter_lt_distErr_three_of_kozlov_of_ne {q t m : ℕ} (α : V → V → Perm (Fin 3))
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hV : Fintype.card V = q * (2 * t + 1)) (β : V → Perm (Fin m))
    (hm : m ≠ 3) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 <
      ∑ e ∈ ({p : V × V | p.1 < p.2} : Finset (V × V)),
        distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  have hdens : 8 * (q ^ 2 * t * (t + 1) / 2) < 3 * (Fintype.card V).choose 2 := by
    rw [hV]
    exact eight_mul_half_lt_three_mul_choose_two_kozlov hq ht
  have hlt := two_mul_div_three_lt_sum_filter_lt_distErr_three_of_ne α hdens β hm
  rwa [two_mul_cast_half_kozlov] at hlt

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
    exact (eight_mul_half_lt_three_mul_choose_two_kozlov hq ht).le
  rw [ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_isCutMinimal G hτ hcut hdens, hE,
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
  have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  rw [ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_kozlov G hτ hcut hq ht hV hE]
  positivity

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
  have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  rw [ciInf₂_sum_filter_lt_distErr_three_ite_isSwap_of_kozlov G hτ hcut hq ht hV hE,
    sum_filter_lt_movedNorm_triple_ite_isSwap G hτ, hodd, hE]
  have h2E := two_mul_cast_half_kozlov q t
  have hD_pos : 0 < (q : ℝ) ^ 2 * t * (t + 1) / 3 := by positivity
  have hnum : 2 * ((Fintype.card V : ℝ) / 3 * ((q ^ 2 * t * (t + 1) / 2 : ℕ) : ℝ)) / 3 =
      (Fintype.card V : ℝ) / 3 * ((q : ℝ) ^ 2 * t * (t + 1) / 3) := by
    calc 2 * ((Fintype.card V : ℝ) / 3 * ((q ^ 2 * t * (t + 1) / 2 : ℕ) : ℝ)) / 3
        = (Fintype.card V : ℝ) / 9 * (2 * ((q ^ 2 * t * (t + 1) / 2 : ℕ) : ℝ)) := by ring
      _ = (Fintype.card V : ℝ) / 3 * ((q : ℝ) ^ 2 * t * (t + 1) / 3) := by rw [h2E]; ring
  rw [hnum, mul_div_cancel_right₀ _ hD_pos.ne']

end CrossDegree

end TauCeti
