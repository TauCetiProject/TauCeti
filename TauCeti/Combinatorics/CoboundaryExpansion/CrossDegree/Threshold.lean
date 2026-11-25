/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Cochain
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unequal-degree thresholds and staircase cross-degree bounds

Comparing a degree-`n` permutation cochain against a vertex gauge of unequal degree `m ≠ n` incurs
at least `1 / (n + 1)` per edge (`1 / 4` when `n = 3`, with sharper bounds `1 / 3` at `m = 2` and
`1 - 3 / m` for `5 ≤ m`). Whenever the equal-degree gauge-cost infimum lies at or below this
unequal-degree baseline, no gauge in a different symmetric group can beat the cochain's own degree.
This file develops that threshold principle for `Finset` pair sums and `TauCeti.Cochain` and
applies it to the staircase threshold at `q * (2 * t + 1)` vertices:

* **Unequal-degree threshold exactness**
  (`Finset.ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one`,
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_ciInf_of_le_card_div_add_one`,
  `Finset.ciInf₂_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div_of_le`,
  `TauCeti.Cochain.card_div_add_one_le_costErr_of_ne`,
  `TauCeti.Cochain.gaugeDistErr_eq_ciInf_sum_edgeCost_div_of_le`, and
  `TauCeti.Cochain.gaugeDistErr_eq_gaugeDist_div_of_le`): on any two-complex `X` over `[Fintype V]`
  and `[LinearOrder V]`, if the equal-degree `movedNorm (Fin n)` unoriented edge-cost infimum (or
  `α.gaugeDist (movedNorm (Fin n))`) for `2 ≤ n` is at most `n * #X.edges / (n + 1)`
  (`3 * #X.edges / 4` when `n = 3`), then `α.gaugeDistErr` equals `1 / n` times that infimum
  (`α.gaugeDist (movedNorm (Fin n)) / n`).
* **Staircase threshold comparison at `Fintype.card V = q * (2 * t + 1)`**
  (`TauCeti.mul_two_mul_add_one_choose_two_div_four_sub`,
  `TauCeti.sq_mul_mul_add_one_div_three_lt_choose_two_div_four`,
  `TauCeti.sq_mul_mul_add_one_div_three_le_choose_two_div_four`,
  `TauCeti.sq_mul_mul_add_one_div_three_lt_ciInf_sum_distErr_three_of_ne`,
  `TauCeti.ciInf₂_sum_distErr_three_eq_ciInf_sum_movedNorm_div_three_of_card_eq`,
  `TauCeti.Cochain.sq_mul_mul_add_one_div_three_lt_ciInf_costErr_three_of_ne`, and
  `TauCeti.Cochain.gaugeDistErr_eq_gaugeDist_div_three_of_card_eq`): the slack between the
  complete-graph `1 / 4` baseline `((q * (2 * t + 1)).choose 2 : ℝ) / 4` and the explicit threshold
  `q ^ 2 * t * (t + 1) / 3` equals `q * (q * (4 * t ^ 2 + 4 * t + 3) - (6 * t + 3)) / 24`, which is
  nonnegative for all `q, t : ℕ` and strictly positive whenever `1 ≤ q` and `1 ≤ t`. Hence every
  degree-`3` cochain on `complete V` whose `movedNorm (Fin 3)` gauge distance is at most
  `q ^ 2 * t * (t + 1)` has `α.gaugeDistErr = α.gaugeDist (movedNorm (Fin 3)) / 3` (on Kozlov's
  staircase graph witness in `Sym3/Staircase.lean`,
  `h1_complete_movedNorm_fin_three_le_of_card_eq_mul` already bounds
  `h1 (complete V) (movedNorm (Fin 3))` above by `card V / 3`).

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Section 3.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Proposition 10.
-/

public section

open Finset

namespace Finset

open Equiv Equiv.Perm TauCeti

variable {V : Type*} {n : ℕ}

/-! ### Unequal-degree threshold exactness -/

/-- Whenever the equal-degree `distErr` gauge-cost infimum on `E` is at most `#E / (n + 1)`, it is a
lower bound for the degree-`m` gauge-cost infimum in every degree `m : ℕ`. -/
theorem ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one (E : Finset (V × V))
    (α : V → V → Perm (Fin n))
    (hle : (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      (#E : ℝ) / (n + 1))
    (m : ℕ) :
    (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      ⨅ β : V → Perm (Fin m), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  rcases eq_or_ne m n with rfl | hmn
  · exact le_rfl
  · refine le_ciInf fun β => hle.trans ?_
    exact E.card_div_add_one_le_sum_distErr_of_ne (fun e => α e.1 e.2)
      (fun e => β e.1 * (β e.2)⁻¹) hmn.symm

/-- When `2 ≤ n` and the equal-degree `distErr` gauge-cost infimum on `E` is at most `#E / (n + 1)`,
the global cross-degree infimum over all gauge degrees `m + 2 ≥ 2` equals the equal-degree infimum.
-/
theorem ciInf₂_sum_distErr_mul_inv_eq_ciInf_of_le_card_div_add_one (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n)
    (hle : (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      (#E : ℝ) / (n + 1)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      ⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) :=
  le_antisymm (E.ciInf₂_sum_distErr_mul_inv_le_ciInf_of_le α hn)
    (le_ciInf fun m => E.ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one α hle (m + 2))

/-- When `2 ≤ n` and the equal-degree `movedNorm (Fin n)` gauge-cost infimum on `E` is at most
`n * #E / (n + 1)`, the global cross-degree infimum over all `m + 2 ≥ 2` equals `1 / n` times the
`movedNorm (Fin n)` infimum. -/
theorem ciInf₂_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div_of_le (E : Finset (V × V))
    (α : V → V → Perm (Fin n)) (hn : 2 ≤ n)
    (hle : (⨅ β : V → Perm (Fin n),
        ∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) ≤
      (n : ℝ) * #E / (n + 1)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      (⨅ β : V → Perm (Fin n),
        ∑ e ∈ E, movedNorm (Fin n) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) / n := by
  have : NeZero n := ⟨by omega⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  have hle' : (⨅ β : V → Perm (Fin n), ∑ e ∈ E, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) ≤
      (#E : ℝ) / (n + 1) := by
    rw [E.ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div α, div_le_iff₀ hn_pos]
    exact hle.trans_eq (by ring)
  rw [E.ciInf₂_sum_distErr_mul_inv_eq_ciInf_of_le_card_div_add_one α hn hle',
    E.ciInf_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div α]

end Finset

namespace TauCeti

open Equiv Equiv.Perm TwoComplex

/-! ### Staircase cross-degree comparison at `q * (2 * t + 1)` -/

/-- For `1 ≤ q` and `1 ≤ t`, the staircase polynomial inequality
`6 * t + 3 + 2 * q ≤ q * (4 * t ^ 2 + 4 * t + 3)` holds in `ℕ`. -/
private theorem six_mul_add_three_add_two_mul_le {q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) :
    6 * t + 3 + 2 * q ≤ q * (4 * t ^ 2 + 4 * t + 3) := by
  rcases Nat.exists_eq_add_of_le' hq with ⟨q', rfl⟩
  rcases Nat.exists_eq_add_of_le' ht with ⟨t', rfl⟩
  nlinarith

/-- Exact algebraic identity for the slack between the complete-graph `1 / 4` unequal-degree
baseline on `q * (2 * t + 1)` vertices and the explicit threshold `q ^ 2 * t * (t + 1) / 3`. -/
theorem mul_two_mul_add_one_choose_two_div_four_sub (q t : ℕ) :
    ((q * (2 * t + 1)).choose 2 : ℝ) / 4 - (q : ℝ) ^ 2 * t * (t + 1) / 3 =
      (q : ℝ) * ((q : ℝ) * (4 * (t : ℝ) ^ 2 + 4 * t + 3) - (6 * t + 3)) / 24 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- When `1 ≤ q` and `1 ≤ t`, the complete-graph `1 / 4` baseline on `q * (2 * t + 1)` vertices
strictly exceeds the explicit threshold `q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_choose_two_div_four {q t : ℕ}
    (hq : 1 ≤ q) (ht : 1 ≤ t) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 < ((q * (2 * t + 1)).choose 2 : ℝ) / 4 := by
  have hpoly : ((6 * t + 3 + 2 * q : ℕ) : ℝ) ≤ ((q * (4 * t ^ 2 + 4 * t + 3) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (six_mul_add_three_add_two_mul_le hq ht)
  push_cast at hpoly
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsub := mul_two_mul_add_one_choose_two_div_four_sub q t
  nlinarith

/-- For all `q, t : ℕ` (including `q = 0` and `t = 0`), the explicit threshold
`q ^ 2 * t * (t + 1) / 3` is at most the `1 / 4` complete-graph baseline
`((q * (2 * t + 1)).choose 2 : ℝ) / 4`. -/
theorem sq_mul_mul_add_one_div_three_le_choose_two_div_four (q t : ℕ) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 ≤ ((q * (2 * t + 1)).choose 2 : ℝ) / 4 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne t 0 with rfl | ht0
  · simp only [Nat.cast_zero, mul_zero, zero_add, mul_one, zero_div]
    positivity
  exact (sq_mul_mul_add_one_div_three_lt_choose_two_div_four
    (Nat.pos_of_ne_zero hq0) (Nat.pos_of_ne_zero ht0)).le

/-- For all `q, t : ℕ`, the explicit threshold `q ^ 2 * t * (t + 1)` is at most
`3 * (q * (2 * t + 1)).choose 2 / (3 + 1)`. -/
private theorem sq_mul_mul_add_one_le_three_mul_choose_two_div_four (q t : ℕ) :
    (q : ℝ) ^ 2 * t * (t + 1) ≤ (3 : ℕ) * ((q * (2 * t + 1)).choose 2 : ℝ) / ((3 : ℕ) + 1) := by
  have hbase := sq_mul_mul_add_one_div_three_le_choose_two_div_four q t
  rw [Nat.cast_ofNat]
  linarith

section StaircaseGraph

variable {V : Type*} [Fintype V] [LinearOrder V] {q t m : ℕ}

/-- On `Fintype.card V = q * (2 * t + 1)` vertices with `1 ≤ q` and `1 ≤ t`, every unequal-degree
(`m ≠ 3`) vertex gauge `β : V → Perm (Fin m)` against any degree-`3` assignment has complete-graph
cross-degree pair cost strictly greater than `q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_sum_distErr_three_of_ne
    (hcard : Fintype.card V = q * (2 * t + 1)) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (α : V → V → Perm (Fin 3)) (β : V → Perm (Fin m)) (hm : m ≠ 3) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 <
      ∑ e : V × V with e.1 < e.2, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  have hlt := sq_mul_mul_add_one_div_three_lt_choose_two_div_four hq ht
  have hbase := (univ.filter fun p : V × V => p.1 < p.2).card_div_four_le_sum_distErr_three_of_ne
    (fun e => α e.1 e.2) (fun e => β e.1 * (β e.2)⁻¹) hm
  rw [Fintype.card_product_filter_lt, hcard] at hbase
  exact hlt.trans_le hbase

/-- On `Fintype.card V = q * (2 * t + 1)` vertices with `1 ≤ q` and `1 ≤ t`, the degree-`m`
(`m ≠ 3`) cross-degree gauge-cost infimum of any degree-`3` assignment strictly exceeds
`q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_ciInf_sum_distErr_three_of_ne
    (hcard : Fintype.card V = q * (2 * t + 1)) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (α : V → V → Perm (Fin 3)) (hm : m ≠ 3) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 <
      ⨅ β : V → Perm (Fin m),
        ∑ e : V × V with e.1 < e.2, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹) := by
  obtain ⟨β₀, hβ₀⟩ :=
    (univ.filter fun p : V × V => p.1 < p.2).exists_eq_ciInf_sum_distErr_mul_inv α m
  rw [← hβ₀]
  exact sq_mul_mul_add_one_div_three_lt_sum_distErr_three_of_ne hcard hq ht α β₀ hm

/-- For every `q, t : ℕ`, if `Fintype.card V = q * (2 * t + 1)` and `α : V → V → Perm (Fin 3)` has
`movedNorm (Fin 3)` complete-graph gauge-cost infimum at most `q ^ 2 * t * (t + 1)`, then its global
cross-degree gauge-cost infimum over all `m + 2 ≥ 2` equals `1 / 3` times its `movedNorm (Fin 3)`
infimum. -/
theorem ciInf₂_sum_distErr_three_eq_ciInf_sum_movedNorm_div_three_of_card_eq
    (hcard : Fintype.card V = q * (2 * t + 1)) (α : V → V → Perm (Fin 3))
    (hle : (⨅ β : V → Perm (Fin 3),
        ∑ e : V × V with e.1 < e.2, movedNorm (Fin 3) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) ≤
      (q : ℝ) ^ 2 * t * (t + 1)) :
    (⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))),
        ∑ e : V × V with e.1 < e.2, distErr (α e.1 e.2) (β e.1 * (β e.2)⁻¹)) =
      (⨅ β : V → Perm (Fin 3),
        ∑ e : V × V with e.1 < e.2, movedNorm (Fin 3) ((β e.1)⁻¹ * α e.1 e.2 * β e.2)) / 3 := by
  have h := (univ.filter fun p : V × V => p.1 < p.2
    ).ciInf₂_sum_distErr_mul_inv_eq_ciInf_sum_movedNorm_div_of_le α (by decide)
      (hle.trans (by
        rw [Fintype.card_product_filter_lt, hcard]
        exact sq_mul_mul_add_one_le_three_mul_choose_two_div_four q t))
  simpa only [Nat.cast_ofNat] using h

end StaircaseGraph

/-! ### Cochain thresholds and staircase exactness -/

namespace Cochain

section CochainThreshold

variable {V : Type*} [Fintype V] [LinearOrder V] {X : TwoComplex V} {n m : ℕ}

private theorem card_filter_lt_mem_edges_eq (X : TwoComplex V) :
    (#(univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges) : ℝ) =
      #X.edges := by
  simpa using X.sum_filter_lt_mem_edges (fun _ => (1 : ℝ))

/-- Every gauge of unequal degree `m ≠ n` against a degree-`n` cochain on `X` incurs `costErr` at
least `#X.edges / (n + 1)`. -/
theorem card_div_add_one_le_costErr_of_ne (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) (hm : m ≠ n) :
    (#X.edges : ℝ) / (n + 1) ≤ α.costErr β := by
  rw [← card_filter_lt_mem_edges_eq X]
  exact α.card_div_add_one_le_costErr β hm.symm

/-- Whenever the equal-degree `costErr` infimum on `X` is at most `#X.edges / (n + 1)`, it is a
lower bound for the degree-`m` `costErr` infimum in every degree `m : ℕ`. -/
theorem ciInf_costErr_le_of_le_card_div_add_one (α : Cochain X (Perm (Fin n)))
    (hle : (⨅ β : V → Perm (Fin n), α.costErr β) ≤ (#X.edges : ℝ) / (n + 1)) (m : ℕ) :
    (⨅ β : V → Perm (Fin n), α.costErr β) ≤ ⨅ β : V → Perm (Fin m), α.costErr β := by
  set E := univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges
  simp_rw [costErr_def] at hle ⊢
  rw [← card_filter_lt_mem_edges_eq X] at hle
  exact E.ciInf_sum_distErr_mul_inv_le_of_le_card_div_add_one α hle m

/-- When `2 ≤ n` and the equal-degree `costErr` infimum on `X` is at most `#X.edges / (n + 1)`,
`α.gaugeDistErr` equals the equal-degree `costErr` infimum. -/
theorem gaugeDistErr_eq_ciInf_costErr_of_le (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n)
    (hle : (⨅ β : V → Perm (Fin n), α.costErr β) ≤ (#X.edges : ℝ) / (n + 1)) :
    α.gaugeDistErr = ⨅ β : V → Perm (Fin n), α.costErr β := by
  refine le_antisymm (α.gaugeDistErr_le_ciInf_costErr hn) ?_
  rw [gaugeDistErr_def]
  exact le_ciInf fun m => α.ciInf_costErr_le_of_le_card_div_add_one hle (m + 2)

/-- When `2 ≤ n` and the equal-degree `movedNorm (Fin n)` unoriented edge-sum infimum on `X` is at
most `n * #X.edges / (n + 1)`, `α.gaugeDistErr` equals `1 / n` times that infimum. -/
theorem gaugeDistErr_eq_ciInf_sum_edgeCost_div_of_le (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n)
    (hle : (⨅ β : V → Perm (Fin n), ∑ e ∈ X.edges, α.edgeCost (movedNorm (Fin n)) β e) ≤
      (n : ℝ) * #X.edges / (n + 1)) :
    α.gaugeDistErr =
      (⨅ β : V → Perm (Fin n), ∑ e ∈ X.edges, α.edgeCost (movedNorm (Fin n)) β e) / n := by
  have : NeZero n := ⟨by omega⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  have hle' : (⨅ β : V → Perm (Fin n), α.costErr β) ≤ (#X.edges : ℝ) / (n + 1) := by
    rw [α.ciInf_costErr_eq_gaugeDist_div, α.gaugeDist_eq_ciInf_sum_edgeCost, div_le_iff₀ hn_pos]
    exact hle.trans_eq (by ring)
  rw [α.gaugeDistErr_eq_ciInf_costErr_of_le hn hle', α.ciInf_costErr_eq_gaugeDist_div,
    α.gaugeDist_eq_ciInf_sum_edgeCost]

/-- When `2 ≤ n` and `α.gaugeDist (movedNorm (Fin n)) ≤ n * #X.edges / (n + 1)`,
`α.gaugeDistErr` equals `α.gaugeDist (movedNorm (Fin n)) / n`. -/
theorem gaugeDistErr_eq_gaugeDist_div_of_le
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n)
    (hle : α.gaugeDist (movedNorm (Fin n)) ≤ (n : ℝ) * #X.edges / (n + 1)) :
    α.gaugeDistErr = α.gaugeDist (movedNorm (Fin n)) / n := by
  rw [α.gaugeDist_eq_ciInf_sum_edgeCost (movedNorm (Fin n))] at hle ⊢
  exact α.gaugeDistErr_eq_ciInf_sum_edgeCost_div_of_le hn hle

end CochainThreshold

section CochainStaircase

variable {V : Type*} [Fintype V] [LinearOrder V] {q t m : ℕ}

/-- On `Fintype.card V = q * (2 * t + 1)` vertices with `1 ≤ q` and `1 ≤ t`, the degree-`m`
(`m ≠ 3`) `costErr` infimum of any degree-`3` cochain on `complete V` strictly exceeds
`q ^ 2 * t * (t + 1) / 3`. -/
theorem sq_mul_mul_add_one_div_three_lt_ciInf_costErr_three_of_ne
    (hcard : Fintype.card V = q * (2 * t + 1)) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (α : Cochain (complete V) (Perm (Fin 3))) (hm : m ≠ 3) :
    (q : ℝ) ^ 2 * t * (t + 1) / 3 < ⨅ β : V → Perm (Fin m), α.costErr β := by
  simp_rw [costErr_complete]
  exact sq_mul_mul_add_one_div_three_lt_ciInf_sum_distErr_three_of_ne hcard hq ht α hm

/-- For every `q, t : ℕ`, if `Fintype.card V = q * (2 * t + 1)` and `α` is a degree-`3` cochain on
`complete V` with `α.gaugeDist (movedNorm (Fin 3)) ≤ q ^ 2 * t * (t + 1)`, then
`α.gaugeDistErr = α.gaugeDist (movedNorm (Fin 3)) / 3`. -/
theorem gaugeDistErr_eq_gaugeDist_div_three_of_card_eq
    (hcard : Fintype.card V = q * (2 * t + 1)) (α : Cochain (complete V) (Perm (Fin 3)))
    (hle : α.gaugeDist (movedNorm (Fin 3)) ≤ (q : ℝ) ^ 2 * t * (t + 1)) :
    α.gaugeDistErr = α.gaugeDist (movedNorm (Fin 3)) / 3 := by
  have h := α.gaugeDistErr_eq_gaugeDist_div_of_le (by decide)
    (hle.trans (by
      rw [card_edges_complete, hcard]
      exact sq_mul_mul_add_one_le_three_mul_choose_two_div_four q t))
  simpa only [Nat.cast_ofNat] using h

end CochainStaircase

end Cochain

end TauCeti

end
