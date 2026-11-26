/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Complete
public import TauCeti.GroupTheory.Perm.DistErr.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Replication
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import TauCeti.Combinatorics.CoboundaryExpansion.GraphCochain
import TauCeti.Combinatorics.SimpleGraph.Staircase
import TauCeti.GroupTheory.Perm.DistErr.Invariance

/-!
# The cross-degree coboundary constant

Chapman and Lubotzky compare a permutation cochain with gauges of every degree. The cross-degree
cost `TauCeti.Cochain.costErr`, the cross-degree distance `TauCeti.Cochain.gaugeDistErr` and the
cross-degree Cheeger constant `TauCeti.h1Err` are defined in
`TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.CheegerConstant`, together with the star
bound `TauCeti.card_div_three_le_h1Err_of_three_le_card`. This file computes the constant on the
complete complex.

In equal degree the cost is the moved-point cost divided by the degree
(`TauCeti.Cochain.costErr_eq_cost_div`), so `gaugeDistErr` is at most `gaugeDist / n`
(`TauCeti.Cochain.gaugeDistErr_le_gaugeDist_div`). The cost is invariant under relabelling
the complete complex, so `h1Err (complete V)` depends only on `Fintype.card V`
(`TauCeti.h1Err_complete_eq_of_card_eq`).

On the complete complex:

* `TauCeti.Cochain.gaugeDistErr_ofLt_lex_seed`: the `k = 4` seed `TauCeti.Sym3.seed`, replicated
  along `Fin 4 ×ₗ ι`, has no cheaper gauge in any degree: its cross-degree distance is
  `2 * (card ι) ^ 2`, while its defect is `8 * (card ι) ^ 3`;
* `TauCeti.h1Err_complete`: hence `h1Err (complete V) = card V / 3` whenever `3 ≤ card V`. When
  `card V` is not a multiple of `4`, Kozlov's staircase graph `SimpleGraph.staircase q t` on
  `q (2 t + 1)` vertices is the witness: gauges of degree `3` cost at least `2 / 3` per edge of the
  graph by cut-minimality, and gauges of any other degree cost at least `1 / 4` per edge of the
  complete complex, which is more.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117,
  equations (2.8) and (2.9) and Proposition 3.2.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, Zenodo, doi:10.5281/zenodo.23245792, Proposition 10.
* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136, Definition 3.2,
  Lemma 3.8 and Corollary 3.13 (the staircase graphs and their cut-minimality).
-/

public section

open Finset Equiv Equiv.Perm

namespace TauCeti

open TwoComplex

namespace Cochain

/-! ### The cross-degree cost and distance -/

section CrossDegree

variable {V : Type*} [Fintype V] [LinearOrder V] {X : TwoComplex V} {n m : ℕ}

/-- The cross-degree cost of an `ofLt` cochain on the complete complex reads the defining function
on the increasing pairs. -/
theorem costErr_ofLt_complete (f : V → V → Perm (Fin n)) (β : V → Perm (Fin m)) :
    (ofLt (complete V) f).costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2), distErr (f p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_complete]
  exact sum_congr rfl fun p hp => by
    rw [ofLt_apply_of_lt _ ((adj_complete _ _).mpr (mem_filter.mp hp).2.ne) (mem_filter.mp hp).2]

/-- In equal nonzero degree, the cross-degree cost is the moved-point cost divided by the
degree. -/
theorem costErr_eq_cost_div [NeZero n] (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    α.costErr β = α.cost (movedNorm (Fin n)) β / n := by
  rw [← mul_costErr_eq_cost, mul_div_cancel_left₀ _ (NeZero.ne _ : (n : ℝ) ≠ 0)]

/-- For a cochain of degree `n + 2`, the gauges of its own degree show that the cross-degree
distance is at most the moved-point gauge distance divided by the degree. -/
theorem gaugeDistErr_le_gaugeDist_div (α : Cochain X (Perm (Fin (n + 2)))) :
    α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) := by
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact α.mul_gaugeDistErr_le_gaugeDist (by omega)

end CrossDegree

/-! ### Relabelling the complete complex -/

section Relabel

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W] {n m : ℕ}

/-- On the complete complex, twice the cross-degree cost is the sum over all ordered pairs of
distinct vertices, since reversing a pair inverts both arguments of `distErr`. -/
private theorem two_mul_costErr_complete (α : Cochain (complete V) (Perm (Fin n)))
    (β : V → Perm (Fin m)) :
    2 * α.costErr β = ∑ p : V × V, if p.1 ≠ p.2 then
      distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) else 0 := by
  have hsplit : univ.filter (fun p : V × V => p.1 ≠ p.2) =
      univ.filter (fun p : V × V => p.1 < p.2) ∪ univ.filter (fun p : V × V => p.2 < p.1) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_union]
    exact ne_iff_lt_or_gt
  rw [← sum_filter, hsplit, sum_union (disjoint_filter.mpr fun p _ h h' => lt_asymm h h'),
    costErr_complete, two_mul]
  congr 1
  refine sum_nbij' Prod.swap Prod.swap (by simp) (by simp) (by simp) (by simp) fun p _ => ?_
  rw [α.apply_swap p.2 p.1, ← distErr_inv_inv]
  simp

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` pulls the gauge back along `e` in
`costErr`. -/
@[simp] theorem costErr_relabelComplete (α : Cochain (complete V) (Perm (Fin n)))
    (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabelComplete e).costErr γ = α.costErr (γ ∘ e) := by
  suffices h : 2 * (α.relabelComplete e).costErr γ = 2 * α.costErr (γ ∘ e) by linarith
  rw [two_mul_costErr_complete, two_mul_costErr_complete, ← (e.prodCongr e).sum_comp]
  simp

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_relabelComplete (α : Cochain (complete V) (Perm (Fin n)))
    (e : V ≃ W) : (α.relabelComplete e).gaugeDistErr = α.gaugeDistErr := by
  rw [gaugeDistErr_def, gaugeDistErr_def]
  refine iInf_congr fun m => ?_
  exact ((Equiv.arrowCongr e (Equiv.refl _)).iInf_congr fun β => by simp [Function.comp_def]).symm

end Relabel

end Cochain

/-! ### The cross-degree Cheeger constant -/

section Constant

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

/-- When every cochain of degree at least `2` is a coboundary, the ratio set is empty and
`h1Err X = 0`. -/
theorem h1Err_eq_zero_of_forall_isCoboundary {X : TwoComplex V}
    (h : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), α.IsCoboundary) : h1Err X = 0 :=
  h1Err_eq_zero_of_forall_gaugeDistErr_eq_zero fun n α =>
    (α.gaugeDistErr_eq_zero_iff_isCoboundary (by omega)).mpr (h n α)

/-- `h1Err` on the complete complex is preserved along any bijection `V ≃ W`. -/
theorem h1Err_complete_congr (e : V ≃ W) : h1Err (complete V) = h1Err (complete W) := by
  rw [h1Err_def, h1Err_def]
  congr 1
  ext r
  refine exists_congr fun n => ((Cochain.relabelCompleteEquiv e).exists_congr fun α => ?_)
  simp [α.defect_relabelComplete isConjInvariant_movedNorm e]

/-- `h1Err (complete V)` depends on `V` only through `Fintype.card V`. -/
theorem h1Err_complete_eq_of_card_eq (hcard : Fintype.card V = Fintype.card W) :
    h1Err (complete V) = h1Err (complete W) :=
  h1Err_complete_congr (Fintype.equivOfCardEq hcard)

end Constant

/-! ### Witnesses and the value on the complete complex -/

namespace Cochain

/-- The `k = 4` seed has cross-degree distance `2`, attained by the identity gauge in degree
`3`. -/
theorem gaugeDistErr_ofLt_seed : (ofLt (complete (Fin 4)) Sym3.seed).gaugeDistErr = 2 := by
  simp only [gaugeDistErr_def, costErr_ofLt_complete]
  exact ciInf₂_sum_distErr_fin_four_of_eq_setOf_isSwap _ Sym3.seed_zero_of_pos
    Sym3.insert_seed_eq_setOf_isSwap

/-- Replicating the `k = 4` seed along `Fin 4 ×ₗ ι`, with `1` inside clusters, multiplies its
cross-degree distance by `(card ι) ^ 2`: no gauge of any degree is cheaper than the replicated
identity gauge. -/
theorem gaugeDistErr_ofLt_lex_seed (ι : Type*) [Fintype ι] [LinearOrder ι] :
    (ofLt (complete (Fin 4 ×ₗ ι)) fun x y =>
        if (ofLex x).1 = (ofLex y).1 then 1 else Sym3.seed (ofLex x).1 (ofLex y).1).gaugeDistErr =
      2 * (Fintype.card ι : ℝ) ^ 2 := by
  simp only [gaugeDistErr_def, costErr_ofLt_complete]
  exact ciInf₂_sum_distErr_lex_fin_four_of_eq_setOf_isSwap _ Sym3.seed_zero_of_pos
    Sym3.insert_seed_eq_setOf_isSwap

end Cochain

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The upper bound `h1Err (complete V) ≤ card V / 3` when `card V = 4 q` with `q ≥ 1`, from the
seed replicated along `Fin 4 ×ₗ Fin q`, with defect `8 q ^ 3` and cross-degree distance
`2 q ^ 2`. -/
private theorem h1Err_complete_le_of_card_eq_four_mul {q : ℕ} (hq : 0 < q)
    (hV : Fintype.card V = 4 * q) : h1Err (complete V) ≤ (Fintype.card V : ℝ) / 3 := by
  rw [h1Err_complete_eq_of_card_eq (W := Fin 4 ×ₗ Fin q) (by simp [hV])]
  have hD := Cochain.gaugeDistErr_ofLt_lex_seed (Fin q)
  rw [Fintype.card_fin] at hD
  have hpos : (0 : ℝ) < 2 * (q : ℝ) ^ 2 := by positivity
  refine (h1Err_le_div (n := 1) (hD ▸ hpos)).trans_eq ?_
  rw [hD, Cochain.defect_ofLt_lex, Sym3.defect_ofLt_seed, Fintype.card_fin, hV]
  have hq' : (q : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- In Kozlov's staircase cochain on `n = q (2 t + 1)` vertices (`t ≥ 1`, `q ≥ 1`), the number of
edges, `#E = q ^ 2 t (t + 1) / 2`, satisfies `2 #E / 3 ≤ (n choose 2) / 4`: gauges of a degree other
than `3` cost at least the second quantity. -/
private theorem two_mul_div_three_le_choose_two_div_four {q t e : ℕ} (hq : 0 < q) (ht : 0 < t)
    (he : 2 * e = q ^ 2 * t * (t + 1)) :
    (2 * e : ℝ) / 3 ≤ ((q * (2 * t + 1)).choose 2 : ℕ) / 4 := by
  have he' : (2 * e : ℝ) = q ^ 2 * t * (t + 1) := by exact_mod_cast he
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rw [Nat.cast_choose_two, he', div_le_div_iff₀ (by norm_num) (by norm_num)]
  push_cast
  -- the difference is `q ((q - 1) (4 t ^ 2 + 4 t + 3) + 2 t (2 t - 1)) / 2`
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ q)
    (add_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ q - 1) (by positivity : (0 : ℝ) ≤
      4 * t ^ 2 + 4 * t + 3)) (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * t)
        (by linarith : (0 : ℝ) ≤ 2 * t - 1)))]

/-- The upper bound `h1Err (complete V) ≤ card V / 3` when `card V = q (2 t + 1)` with `q, t ≥ 1`,
from Kozlov's staircase graph `SimpleGraph.staircase q t` with `swap 0 1` on its edges. Gauges of
degree `3` cost at least `2 #E / 3` by cut-minimality, and gauges of any other degree cost at least
`1 / 4` on each of the `n choose 2` edges of the complete complex, which is more. -/
private theorem h1Err_complete_le_of_card_eq_mul {q t : ℕ} (hq : 0 < q) (ht : 0 < t)
    (hV : Fintype.card V = q * (2 * t + 1)) : h1Err (complete V) ≤ (Fintype.card V : ℝ) / 3 := by
  let W := Fin (q * t) ⊕ Fin (q * t) ⊕ Fin q
  let _ : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  have hW : Fintype.card W = q * (2 * t + 1) := by
    simp only [W, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [h1Err_complete_eq_of_card_eq (hV.trans hW.symm)]
  set G := SimpleGraph.staircase q t
  set α := Cochain.ofLt (complete W) fun u v => if G.Adj u v then (swap 0 1 : Perm (Fin 3)) else 1
  have hE2 := SimpleGraph.two_mul_card_edgeFinset_staircase q t
  have hD : (2 * #G.edgeFinset : ℝ) / 3 ≤ α.gaugeDistErr := by
    refine α.le_gaugeDistErr_iff.mpr fun m β => ?_
    rcases eq_or_ne m 1 with rfl | hm
    · rw [Cochain.costErr_eq_cost_div]
      exact div_le_div_of_nonneg_right
        (G.two_mul_card_edgeFinset_le_cost ⟨0, 1, by decide, rfl⟩
          (SimpleGraph.isCutMinimal_staircase q t) β)
        (Nat.cast_nonneg _)
    · rw [Cochain.costErr_ofLt_complete]
      refine le_trans ?_ (card_div_four_le_sum_distErr_three_of_ne _
        (fun p : W × W => if G.Adj p.1 p.2 then swap 0 1 else 1)
        (fun p : W × W => β p.1 * (β p.2)⁻¹) (by omega))
      rw [Fintype.card_product_filter_lt, hW]
      exact two_mul_div_three_le_choose_two_div_four hq ht hE2
  have hpos : (0 : ℝ) < 2 * #G.edgeFinset / 3 := by
    have : 0 < 2 * #G.edgeFinset := hE2 ▸ by positivity
    have : 0 < #G.edgeFinset := by omega
    positivity
  refine (h1Err_le_div (n := 1) (hpos.trans_le hD)).trans ?_
  refine (div_le_div_of_nonneg_left (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hpos
    hD).trans_eq ?_
  rw [SimpleGraph.defect_ofLt_ite_adj _ _ (swap_mul_self 0 1),
    Perm.IsSwap.movedNorm ⟨0, 1, by decide, rfl⟩, SimpleGraph.card_oddTriangleFinset_staircase, hV]
  have hE' : (#G.edgeFinset : ℝ) ≠ 0 := by linarith
  push_cast
  field_simp
  ring

/-- The cross-degree coboundary constant of the complete complex is `card V / 3` whenever
`3 ≤ card V` (Beasley, Proposition 10). The lower bound is the cross-degree star bound. For the
upper bound, `card V` is `4 q` or `q (2 t + 1)` with `q, t ≥ 1`: the replicated `k = 4` seed and
Kozlov's staircase graph attain the bound. -/
theorem h1Err_complete (hV : 3 ≤ Fintype.card V) :
    h1Err (complete V) = (Fintype.card V : ℝ) / 3 := by
  refine le_antisymm ?_ (card_div_three_le_h1Err_of_three_le_card hV)
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < Fintype.card V) with
    ⟨q, hq⟩ | ⟨p, hp, ⟨q, hq⟩, t, rfl⟩
  · exact h1Err_complete_le_of_card_eq_four_mul (by omega) hq
  · have ht : 0 < t := by have := hp.one_lt; omega
    have hq0 : 0 < q := Nat.pos_of_ne_zero fun h => by simp [h] at hq; omega
    exact h1Err_complete_le_of_card_eq_mul hq0 ht (by rw [hq]; ring)

end TauCeti
