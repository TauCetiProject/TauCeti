/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Complete
public import TauCeti.GroupTheory.Perm.DistErr.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Replication
import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.Sym3.Staircase
import TauCeti.Combinatorics.SimpleGraph.Staircase
import TauCeti.GroupTheory.Perm.DistErr.Invariance

/-!
# The cross-degree coboundary constant

Chapman and Lubotzky compare a permutation cochain with gauges of every degree. For a cochain `α`
on a two-complex `X` with values in `Equiv.Perm (Fin n)` and a gauge `β : V → Equiv.Perm (Fin m)`
of possibly different degree:

* `TauCeti.Cochain.costErr α β` sums the distance with errors `Equiv.Perm.distErr` from `α u v` to
  `β u * (β v)⁻¹` over the edges `u < v` of `X`;
* `TauCeti.Cochain.gaugeDistErr α` is the infimum of `costErr` over all gauge degrees `m + 2 ≥ 2`
  and all gauges of that degree;
* `TauCeti.h1Err X` is the infimum, over cochain degrees `n + 2 ≥ 2` and cochains `α` with
  `0 < α.gaugeDistErr`, of `(α.defect (movedNorm (Fin (n + 2))) / (n + 2)) / α.gaugeDistErr`.

In equal degree the cost is the moved-point cost divided by the degree
(`TauCeti.Cochain.natCast_mul_costErr_eq_cost`), so `gaugeDistErr` is at most `gaugeDist / n`.
In different degrees every edge costs at least `1 / (n + 1)`, so for degrees `n ≥ 2` the
cross-degree distance is positive exactly on the non-coboundaries
(`TauCeti.Cochain.gaugeDistErr_pos_iff_not_isCoboundary`). The cost is invariant under relabelling
the complete complex, so `h1Err (complete V)` depends only on `Fintype.card V`
(`TauCeti.h1Err_complete_eq_of_card_eq`).

On the complete complex:

* `TauCeti.card_mul_gaugeDistErr_le`: the star gauge, which has the cochain's own degree, gives the
  star bound `card V * gaugeDistErr α ≤ 3 * defect α / n`;
* `TauCeti.card_div_three_le_h1Err`: hence `card V / 3 ≤ h1Err (complete V)` when
  `3 ≤ card V`;
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

/-- The cross-degree cost of a gauge `β` of degree `m` against a cochain `α` of degree `n`: the
sum of the distances with errors from `α u v` to `β u * (β v)⁻¹` over the edges `u < v`. -/
noncomputable def costErr (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
    distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)

theorem costErr_def (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := (rfl)

/-- On the complete complex, `costErr` sums over all strictly increasing vertex pairs. -/
theorem costErr_complete (α : Cochain (complete V) (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2), distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_def]
  refine sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_edges_complete, card_pair_eq_two_iff,
    and_iff_left_iff_imp]
  exact LT.lt.ne

/-- The cross-degree cost of an `ofLt` cochain on the complete complex reads the defining function
on the increasing pairs. -/
theorem costErr_ofLt_complete (f : V → V → Perm (Fin n)) (β : V → Perm (Fin m)) :
    (ofLt (complete V) f).costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2), distErr (f p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_complete]
  exact sum_congr rfl fun p hp => by
    rw [ofLt_apply_of_lt _ ((adj_complete _ _).mpr (mem_filter.mp hp).2.ne) (mem_filter.mp hp).2]

theorem costErr_nonneg (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    0 ≤ α.costErr β :=
  sum_nonneg fun _ _ => distErr_nonneg _ _

/-- In equal degree, the degree times the cross-degree cost is the moved-point cost. -/
theorem natCast_mul_costErr_eq_cost (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    (n : ℝ) * α.costErr β = α.cost (movedNorm (Fin n)) β := by
  rw [costErr_def, cost_def, mul_sum]
  exact sum_congr rfl fun _ _ => mul_distErr_mul_inv_eq_movedNorm _ _ _

/-- In equal nonzero degree, the cross-degree cost is the moved-point cost divided by the
degree. -/
theorem costErr_eq_cost_div [NeZero n] (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    α.costErr β = α.cost (movedNorm (Fin n)) β / n := by
  rw [← natCast_mul_costErr_eq_cost, mul_div_cancel_left₀ _ (NeZero.ne _ : (n : ℝ) ≠ 0)]

/-- The cross-degree gauge distance of `α`: the infimum of `costErr` over all gauge degrees
`m + 2 ≥ 2` and all gauges of that degree. -/
noncomputable def gaugeDistErr (α : Cochain X (Perm (Fin n))) : ℝ :=
  ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β

theorem gaugeDistErr_def (α : Cochain X (Perm (Fin n))) :
    α.gaugeDistErr = ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β := (rfl)

private theorem bddBelow_range_costErr (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    BddBelow (Set.range fun β : V → Perm (Fin m) => α.costErr β) :=
  ⟨0, by rintro _ ⟨β, rfl⟩; exact α.costErr_nonneg β⟩

private theorem bddBelow_range_iInf_costErr (α : Cochain X (Perm (Fin n))) :
    BddBelow (Set.range fun m : ℕ => ⨅ β : V → Perm (Fin (m + 2)), α.costErr β) :=
  ⟨0, by rintro _ ⟨m, rfl⟩; exact Real.iInf_nonneg (α.costErr_nonneg)⟩

theorem gaugeDistErr_nonneg (α : Cochain X (Perm (Fin n))) : 0 ≤ α.gaugeDistErr :=
  Real.iInf_nonneg fun _ => Real.iInf_nonneg (α.costErr_nonneg)

theorem gaugeDistErr_le_costErr (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin (m + 2))) :
    α.gaugeDistErr ≤ α.costErr β :=
  (ciInf_le α.bddBelow_range_iInf_costErr m).trans (ciInf_le (α.bddBelow_range_costErr _) β)

theorem le_gaugeDistErr_iff (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    c ≤ α.gaugeDistErr ↔ ∀ (m : ℕ) (β : V → Perm (Fin (m + 2))), c ≤ α.costErr β := by
  rw [gaugeDistErr_def, le_ciInf_iff α.bddBelow_range_iInf_costErr]
  exact forall_congr' fun m => le_ciInf_iff (α.bddBelow_range_costErr _)

theorem gaugeDistErr_lt_iff (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    α.gaugeDistErr < c ↔ ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β < c := by
  simpa using (α.le_gaugeDistErr_iff (c := c)).not

/-- For a cochain of degree `n + 2`, the gauges of its own degree show that the cross-degree
distance is at most the moved-point gauge distance divided by the degree. -/
theorem gaugeDistErr_le_gaugeDist_div (α : Cochain X (Perm (Fin (n + 2)))) :
    α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) := by
  rw [le_div_iff₀ (by positivity), le_gaugeDist_iff]
  intro β
  rw [← natCast_mul_costErr_eq_cost, mul_comm]
  exact mul_le_mul_of_nonneg_left (α.gaugeDistErr_le_costErr β) (Nat.cast_nonneg _)

/-- A cochain of degree `n + 2 ≥ 2` has positive cross-degree distance exactly when it is not a
coboundary. Gauges of another degree cost at least `1 / (n + 3)` on each edge, and gauges of the
cochain's own degree cost at least `gaugeDist / (n + 2)`. -/
theorem gaugeDistErr_pos_iff_not_isCoboundary (α : Cochain X (Perm (Fin (n + 2)))) :
    0 < α.gaugeDistErr ↔ ¬ α.IsCoboundary := by
  refine ⟨fun h hα => ?_, fun hα => ?_⟩
  · have hle := α.gaugeDistErr_le_gaugeDist_div
    rw [hα.gaugeDist_eq_zero, zero_div] at hle
    linarith
  have hD : 0 < α.gaugeDist (movedNorm (Fin (n + 2))) :=
    (α.gaugeDist_pos_iff_not_isCoboundary _).mpr hα
  -- the identity gauge has positive cost, so `X` has an edge
  have hE : (univ.filter fun p : V × V =>
      p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges).Nonempty := by
    refine nonempty_of_sum_ne_zero (f := fun p : V × V =>
      movedNorm (Fin (n + 2)) (((1 : V → Perm (Fin (n + 2))) p.1)⁻¹ * α p.1 p.2 *
        (1 : V → Perm (Fin (n + 2))) p.2)) ?_
    have hle := α.gaugeDist_le_cost (movedNorm (Fin (n + 2))) 1
    rw [cost_def] at hle
    exact (hD.trans_le hle).ne'
  have hc : 0 < min (1 / ((n + 2 : ℕ) + 1 : ℝ)) (α.gaugeDist (movedNorm (Fin (n + 2))) /
      (n + 2 : ℕ)) :=
    lt_min (by positivity) (by positivity)
  refine hc.trans_le ((α.le_gaugeDistErr_iff).mpr fun m β => ?_)
  rcases eq_or_ne m n with rfl | hmn
  · rw [costErr_eq_cost_div]
    exact (min_le_right _ _).trans
      (div_le_div_of_nonneg_right (α.gaugeDist_le_cost _ β) (Nat.cast_nonneg _))
  · refine (min_le_left _ _).trans ((div_le_div_of_nonneg_right ?_ (by positivity)).trans
      (card_div_add_one_le_sum_distErr_of_ne _ (fun p : V × V => α p.1 p.2)
        (fun p : V × V => β p.1 * (β p.2)⁻¹) (by omega)))
    exact_mod_cast hE.card_pos

/-- A cochain of degree `n + 2 ≥ 2` has cross-degree distance zero exactly when it is a
coboundary. -/
theorem gaugeDistErr_eq_zero_iff_isCoboundary (α : Cochain X (Perm (Fin (n + 2)))) :
    α.gaugeDistErr = 0 ↔ α.IsCoboundary := by
  rw [← not_iff_not, ← α.gaugeDistErr_pos_iff_not_isCoboundary]
  exact α.gaugeDistErr_nonneg.lt_iff_ne'.symm

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

/-- The cross-degree coboundary Cheeger constant of Chapman and Lubotzky: the infimum, over cochain
degrees `n + 2 ≥ 2` and cochains `α` of that degree with `0 < α.gaugeDistErr`, of the moved-point
defect divided by the degree and by the cross-degree distance. An empty ratio set gives `0`. -/
noncomputable def h1Err (X : TwoComplex V) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
    r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr}

theorem h1Err_def (X : TwoComplex V) :
    h1Err X = sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))),
      0 < α.gaugeDistErr ∧
        r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr} := (rfl)

private theorem bddBelow_setOf_h1Err (X : TwoComplex V) :
    BddBelow {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      r = α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr} :=
  ⟨0, by
    rintro r ⟨n, α, hα, rfl⟩
    exact div_nonneg (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hα.le⟩

/-- The cross-degree Cheeger constant is nonnegative. -/
theorem h1Err_nonneg (X : TwoComplex V) : 0 ≤ h1Err X :=
  Real.sInf_nonneg fun _ ⟨_, α, hα, hr⟩ =>
    hr ▸ div_nonneg (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hα.le

/-- Every cochain of degree `n + 2` at positive cross-degree distance bounds `h1Err X` above. -/
theorem h1Err_le_div {X : TwoComplex V} {n : ℕ} {α : Cochain X (Perm (Fin (n + 2)))}
    (hα : 0 < α.gaugeDistErr) :
    h1Err X ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr :=
  csInf_le (bddBelow_setOf_h1Err X) ⟨n, α, hα, rfl⟩

/-- When some cochain of degree at least `2` has positive cross-degree distance, `c ≤ h1Err X`
holds iff `c` bounds every cross-degree expansion ratio from below. -/
theorem le_h1Err_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    c ≤ h1Err X ↔ ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
      c ≤ α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr := by
  obtain ⟨n₀, α₀, hα₀⟩ := hne
  rw [h1Err_def, le_csInf_iff (bddBelow_setOf_h1Err X) ⟨_, n₀, α₀, hα₀, rfl⟩]
  exact ⟨fun h n α hα => h _ ⟨n, α, hα, rfl⟩, fun h _ ⟨n, α, hα, hr⟩ => hr ▸ h n α hα⟩

/-- When every cochain of degree at least `2` is a coboundary, the ratio set is empty and
`h1Err X = 0`. -/
theorem h1Err_eq_zero_of_forall_isCoboundary {X : TwoComplex V}
    (h : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), α.IsCoboundary) : h1Err X = 0 := by
  have h' : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), ¬ 0 < α.gaugeDistErr := fun n α => by
    rw [α.gaugeDistErr_pos_iff_not_isCoboundary, not_not]
    exact h n α
  simp [h1Err_def, h']

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

/-! ### The star bound -/

section StarBound

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

/-- The cross-degree star bound: for a cochain of degree `n + 2` on `complete V`,
`card V * gaugeDistErr α ≤ 3 * defect α / (n + 2)`. The star gauges have the cochain's own
degree. -/
theorem card_mul_gaugeDistErr_le (α : Cochain (complete V) (Perm (Fin (n + 2)))) :
    (Fintype.card V : ℝ) * α.gaugeDistErr ≤
      3 * (α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ)) := by
  calc (Fintype.card V : ℝ) * α.gaugeDistErr
      ≤ Fintype.card V * (α.gaugeDist (movedNorm (Fin (n + 2))) / (n + 2 : ℕ)) :=
        mul_le_mul_of_nonneg_left α.gaugeDistErr_le_gaugeDist_div (Nat.cast_nonneg _)
    _ = (Fintype.card V * α.gaugeDist (movedNorm (Fin (n + 2)))) / (n + 2 : ℕ) := by ring
    _ ≤ 3 * α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) :=
        div_le_div_of_nonneg_right (card_mul_gaugeDist_le _ isConjInvariant_movedNorm α)
          (Nat.cast_nonneg _)
    _ = 3 * (α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ)) := by ring

/-- Ratio form of the cross-degree star bound for a cochain at positive cross-degree distance. -/
theorem Cochain.card_div_three_le_defect_div_div_gaugeDistErr
    {α : Cochain (complete V) (Perm (Fin (n + 2)))} (hα : 0 < α.gaugeDistErr) :
    (Fintype.card V : ℝ) / 3 ≤
      α.defect (movedNorm (Fin (n + 2))) / (n + 2 : ℕ) / α.gaugeDistErr := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hα, mul_comm _ (3 : ℝ)]
  exact card_mul_gaugeDistErr_le α

/-- The cross-degree star bound on the Cheeger constant: `card V / 3 ≤ h1Err (complete V)` whenever
`3 ≤ card V`. A single non-identity edge gives a cochain at positive cross-degree distance. -/
theorem card_div_three_le_h1Err (hV : 3 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) / 3 ≤ h1Err (complete V) := by
  obtain ⟨α, hα⟩ := exists_not_isCoboundary_complete (G := Perm (Fin (0 + 2))) hV
  exact (le_h1Err_iff ⟨0, α, α.gaugeDistErr_pos_iff_not_isCoboundary.mpr hα⟩).mpr
    fun _ _ hα => Cochain.card_div_three_le_defect_div_div_gaugeDistErr hα

end StarBound

/-! ### Witnesses and the value on the complete complex -/

namespace Cochain

/-- The `k = 4` seed has cross-degree distance `2`, attained by the identity gauge in degree
`3`. -/
theorem gaugeDistErr_ofLt_seed : (ofLt (complete (Fin 4)) Sym3.seed).gaugeDistErr = 2 := by
  simp only [gaugeDistErr_def, costErr_ofLt_complete]
  exact ciInf₂_sum_distErr_fin_four_of_eq_setOf_isSwap _ Sym3.seed_zero_of_pos
    Sym3.setOf_seed_eq_setOf_isSwap

/-- Replicating the `k = 4` seed along `Fin 4 ×ₗ ι`, with `1` inside clusters, multiplies its
cross-degree distance by `(card ι) ^ 2`: no gauge of any degree is cheaper than the replicated
identity gauge. -/
theorem gaugeDistErr_ofLt_lex_seed (ι : Type*) [Fintype ι] [LinearOrder ι] :
    (ofLt (complete (Fin 4 ×ₗ ι)) fun x y =>
        if (ofLex x).1 = (ofLex y).1 then 1 else Sym3.seed (ofLex x).1 (ofLex y).1).gaugeDistErr =
      2 * (Fintype.card ι : ℝ) ^ 2 := by
  simp only [gaugeDistErr_def, costErr_ofLt_complete]
  exact ciInf₂_sum_distErr_lex_fin_four_of_eq_setOf_isSwap _ Sym3.seed_zero_of_pos
    Sym3.setOf_seed_eq_setOf_isSwap

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
  have hO := SimpleGraph.three_mul_card_oddTriangleFinset_staircase q t
  have hD : (2 * #G.edgeFinset : ℝ) / 3 ≤ α.gaugeDistErr := by
    refine α.le_gaugeDistErr_iff.mpr fun m β => ?_
    rcases eq_or_ne m 1 with rfl | hm
    · rw [Cochain.costErr_eq_cost_div]
      exact div_le_div_of_nonneg_right
        (G.two_mul_card_edgeFinset_le_cost (SimpleGraph.isCutMinimal_staircase q t) β)
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
  rw [SimpleGraph.defect_ofLt_ite_adj, hV]
  have hE' : (#G.edgeFinset : ℝ) ≠ 0 := by linarith
  have h := congrArg (Nat.cast (R := ℝ)) hO
  push_cast at h ⊢
  field_simp
  -- the two odd-triangle counts differ only in their `DecidableEq W` instances
  convert h using 1
  · rw [mul_comm]
    congr!
  · ring

/-- The cross-degree coboundary constant of the complete complex is `card V / 3` whenever
`3 ≤ card V` (Beasley, Proposition 10). The lower bound is the cross-degree star bound. For the
upper bound, `card V` is `4 q` or `q (2 t + 1)` with `q, t ≥ 1`: the replicated `k = 4` seed and
Kozlov's staircase graph attain the bound. -/
theorem h1Err_complete (hV : 3 ≤ Fintype.card V) :
    h1Err (complete V) = (Fintype.card V : ℝ) / 3 := by
  refine le_antisymm ?_ (card_div_three_le_h1Err hV)
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < Fintype.card V) with
    ⟨q, hq⟩ | ⟨p, hp, ⟨q, hq⟩, t, rfl⟩
  · exact h1Err_complete_le_of_card_eq_four_mul (by omega) hq
  · have ht : 0 < t := by have := hp.one_lt; omega
    have hq0 : 0 < q := Nat.pos_of_ne_zero fun h => by simp [h] at hq; omega
    exact h1Err_complete_le_of_card_eq_mul hq0 ht (by rw [hq]; ring)

end TauCeti
