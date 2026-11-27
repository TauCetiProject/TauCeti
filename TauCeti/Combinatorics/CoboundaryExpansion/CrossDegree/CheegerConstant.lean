/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.GroupTheory.Perm.DistErr.Invariance
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import Mathlib.Tactic.Linarith

/-!
# The cross-degree coboundary Cheeger constant

Chapman and Lubotzky compare a permutation cochain of degree `n` with coboundaries of any degree
`m`, measuring each edge by the distance with errors `Equiv.Perm.distErr`. For a cochain
`α : Cochain X (Equiv.Perm (Fin n))` on a two-complex `X` over a finite linearly ordered `V`:

* `Cochain.costErr α β` is the cross-degree cost of a gauge `β : V → Equiv.Perm (Fin m)`, the sum
  of `distErr (α u v) (β u * (β v)⁻¹)` over the edges `u < v` of `X`;
* `Cochain.gaugeDistErr α` is its infimum over all gauge degrees `m ≥ 2` and all gauges of that
  degree;
* `h1Err X` is the infimum, over cochain degrees `n ≥ 2` and cochains with positive
  `gaugeDistErr`, of `(α.defect (movedNorm (Fin n)) / n) / α.gaugeDistErr`. As for `h1`, an empty
  ratio set gives `0`.

In equal degree the cross-degree cost is the moved-point cost divided by the degree
(`Cochain.mul_costErr_eq_cost`), so `n * gaugeDistErr α ≤ gaugeDist α`. In unequal degree each
edge costs at least `1 / (n + 1)`. Hence, for `n ≥ 2`, `gaugeDistErr α` is positive exactly when
`α` is not a coboundary (`Cochain.gaugeDistErr_pos_iff_not_isCoboundary`).

The star gauges of a cochain have the cochain's own degree, so the star bound
`card_mul_gaugeDist_le` carries over: `card V * gaugeDistErr α ≤ 3 * (defect α / n)` on
`complete V` (`card_mul_gaugeDistErr_le`). Hence `card V / 3 ≤ h1Err (complete V)` whenever some
cochain has positive cross-degree gauge distance (`card_div_three_le_h1Err`), which holds as soon
as `3 ≤ card V` (`card_div_three_le_h1Err_of_three_le_card`).

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117,
  equations (2.8) and (2.9) and Proposition 3.2.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.23245792, version 7, Proposition 10.
-/

public section

open Finset Equiv Equiv.Perm

namespace TauCeti

open TwoComplex

namespace Cochain

variable {V : Type*} [Fintype V] [LinearOrder V] {X : TwoComplex V} {n : ℕ}

/-! ### The cross-degree cost -/

/-- The cross-degree cost of a gauge `β` of degree `m` against a cochain `α` of degree `n`: the
sum of `distErr (α u v) (β u * (β v)⁻¹)` over the edges `u < v` of `X`. -/
noncomputable def costErr {m : ℕ} (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
    distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹)

theorem costErr_def {m : ℕ} (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := (rfl)

/-- On the complete complex, `costErr` sums over all strictly increasing vertex pairs. -/
theorem costErr_complete {m : ℕ} (α : Cochain (complete V) (Perm (Fin n)))
    (β : V → Perm (Fin m)) :
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
theorem costErr_ofLt_complete (f : V → V → Perm (Fin n)) {m : ℕ} (β : V → Perm (Fin m)) :
    (ofLt (complete V) f).costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2), distErr (f p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_complete]
  exact sum_congr rfl fun p hp => by
    rw [ofLt_apply_of_lt _ ((adj_complete _ _).mpr (mem_filter.mp hp).2.ne) (mem_filter.mp hp).2]

theorem costErr_nonneg {m : ℕ} (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    0 ≤ α.costErr β :=
  sum_nonneg fun _ _ => distErr_nonneg _ _

/-- In equal degree, `n` times the cross-degree cost is the moved-point cost. -/
theorem mul_costErr_eq_cost (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    (n : ℝ) * α.costErr β = α.cost (movedNorm (Fin n)) β := by
  rw [costErr_def, cost_def, mul_sum]
  exact sum_congr rfl fun p _ => mul_distErr_mul_inv_eq_movedNorm _ _ _

/-- In unequal degree, every edge `u < v` of `X` costs at least `1 / (n + 1)`. -/
theorem card_div_add_one_le_costErr {m : ℕ} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) (hnm : n ≠ m) :
    (#(univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges) : ℝ) /
      ((n : ℝ) + 1) ≤ α.costErr β :=
  card_div_add_one_le_sum_distErr_of_ne _ _ _ hnm

/-! ### The cross-degree gauge distance -/

/-- The cross-degree gauge distance of `α`: the infimum of `α.costErr β` over all gauge degrees
`m + 2 ≥ 2` and all gauges `β` of that degree. -/
noncomputable def gaugeDistErr (α : Cochain X (Perm (Fin n))) : ℝ :=
  ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β

theorem gaugeDistErr_def (α : Cochain X (Perm (Fin n))) :
    α.gaugeDistErr = ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β := (rfl)

private theorem bddBelow_range_iInf_costErr (α : Cochain X (Perm (Fin n))) :
    BddBelow (Set.range fun m : ℕ => ⨅ β : V → Perm (Fin (m + 2)), α.costErr β) :=
  ⟨0, by rintro _ ⟨m, rfl⟩; exact Real.iInf_nonneg fun β => α.costErr_nonneg β⟩

private theorem bddBelow_range_costErr {m : ℕ} (α : Cochain X (Perm (Fin n))) :
    BddBelow (Set.range fun β : V → Perm (Fin m) => α.costErr β) :=
  ⟨0, by rintro _ ⟨β, rfl⟩; exact α.costErr_nonneg β⟩

theorem gaugeDistErr_nonneg (α : Cochain X (Perm (Fin n))) : 0 ≤ α.gaugeDistErr :=
  Real.iInf_nonneg fun _ => Real.iInf_nonneg fun β => α.costErr_nonneg β

/-- `c ≤ α.gaugeDistErr` if and only if every gauge of every degree `m + 2 ≥ 2` costs at
least `c`. -/
theorem le_gaugeDistErr_iff (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    c ≤ α.gaugeDistErr ↔ ∀ (m : ℕ) (β : V → Perm (Fin (m + 2))), c ≤ α.costErr β := by
  rw [gaugeDistErr_def, le_ciInf_iff (α.bddBelow_range_iInf_costErr)]
  exact forall_congr' fun m => le_ciInf_iff α.bddBelow_range_costErr

/-- `α.gaugeDistErr < c` if and only if some gauge of some degree `m + 2 ≥ 2` costs less
than `c`. -/
theorem gaugeDistErr_lt_iff (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    α.gaugeDistErr < c ↔ ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β < c := by
  simpa only [not_le, not_forall, exists_prop] using (α.le_gaugeDistErr_iff (c := c)).not

/-- Every gauge of degree at least `2` bounds the cross-degree gauge distance from above. -/
theorem gaugeDistErr_le_costErr (α : Cochain X (Perm (Fin n))) {m : ℕ} (hm : 2 ≤ m)
    (β : V → Perm (Fin m)) : α.gaugeDistErr ≤ α.costErr β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact (ciInf_le α.bddBelow_range_iInf_costErr k).trans (ciInf_le α.bddBelow_range_costErr β)

/-- For a cochain of degree `n ≥ 2`, `n * α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin n))`:
gauges of the cochain's own degree are among those admitted by `gaugeDistErr`. -/
theorem mul_gaugeDistErr_le_gaugeDist (hn : 2 ≤ n) (α : Cochain X (Perm (Fin n))) :
    (n : ℝ) * α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin n)) := by
  refine (α.le_gaugeDist_iff _).mpr fun β => ?_
  rw [← α.mul_costErr_eq_cost β]
  exact mul_le_mul_of_nonneg_left (α.gaugeDistErr_le_costErr hn β) (Nat.cast_nonneg n)

/-- A coboundary of degree `n ≥ 2` has cross-degree gauge distance zero. -/
theorem IsCoboundary.gaugeDistErr_eq_zero {α : Cochain X (Perm (Fin n))} (hα : α.IsCoboundary)
    (hn : 2 ≤ n) : α.gaugeDistErr = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := α.mul_gaugeDistErr_le_gaugeDist hn
  rw [hα.gaugeDist_eq_zero] at h
  exact le_antisymm (by nlinarith [α.gaugeDistErr_nonneg]) α.gaugeDistErr_nonneg

/-- A cochain that is not a coboundary has positive cross-degree gauge distance: gauges of the
cochain's own degree cost at least `gaugeDist / n`, and gauges of any other degree cost at least
`1 / (n + 1)` on each edge. -/
theorem gaugeDistErr_pos_of_not_isCoboundary {α : Cochain X (Perm (Fin n))}
    (hα : ¬ α.IsCoboundary) : 0 < α.gaugeDistErr := by
  set E := univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges
  have hgd : 0 < α.gaugeDist (movedNorm (Fin n)) :=
    (α.gaugeDist_pos_iff_not_isCoboundary _).mpr hα
  have hE : (0 : ℝ) < #E := by
    have h := hgd.trans_le (α.gaugeDist_le_cost _ 1)
    rw [cost_def] at h
    exact_mod_cast card_pos.mpr (nonempty_of_sum_ne_zero h.ne')
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine (div_pos (lt_min hgd hE) hn).trans_le ((α.le_gaugeDistErr_iff).mpr fun m β => ?_)
  rw [div_le_iff₀ hn]
  by_cases hnm : n = m + 2
  · subst hnm
    have h := (α.gaugeDist_le_cost _ β).trans_eq (α.mul_costErr_eq_cost β).symm
    nlinarith [min_le_left (α.gaugeDist (movedNorm (Fin (m + 2)))) (#E : ℝ), α.costErr_nonneg β]
  · have h := α.card_div_add_one_le_costErr β hnm
    rw [div_le_iff₀ hn] at h
    exact (min_le_right _ _).trans h

/-- For a cochain of degree `n ≥ 2`, positive cross-degree gauge distance characterizes the
non-coboundaries. -/
theorem gaugeDistErr_pos_iff_not_isCoboundary (hn : 2 ≤ n) (α : Cochain X (Perm (Fin n))) :
    0 < α.gaugeDistErr ↔ ¬ α.IsCoboundary :=
  ⟨fun h hα => h.ne' (hα.gaugeDistErr_eq_zero hn), gaugeDistErr_pos_of_not_isCoboundary⟩

/-- For a cochain of degree `n ≥ 2`, the cross-degree gauge distance vanishes exactly on
coboundaries. -/
theorem gaugeDistErr_eq_zero_iff_isCoboundary (hn : 2 ≤ n) (α : Cochain X (Perm (Fin n))) :
    α.gaugeDistErr = 0 ↔ α.IsCoboundary :=
  ⟨fun h => by_contra fun hα => (gaugeDistErr_pos_of_not_isCoboundary hα).ne' h,
    fun hα => hα.gaugeDistErr_eq_zero hn⟩

end Cochain

/-! ### The cross-degree Cheeger constant -/

section Constant

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The cross-degree first coboundary Cheeger constant of `X` (Chapman–Lubotzky II, (2.8)–(2.9)),
in the counting convention: the infimum of
`(α.defect (movedNorm (Fin n)) / n) / α.gaugeDistErr` over cochain degrees `n ≥ 2` and cochains
`α` of degree `n` at positive cross-degree gauge distance. -/
noncomputable def h1Err (X : TwoComplex V) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
    r = α.defect (movedNorm (Fin (n + 2))) / ((n + 2 : ℕ) : ℝ) / α.gaugeDistErr}

theorem h1Err_def (X : TwoComplex V) :
    h1Err X =
      sInf {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
        r = α.defect (movedNorm (Fin (n + 2))) / ((n + 2 : ℕ) : ℝ) / α.gaugeDistErr} :=
  (rfl)

private theorem bddBelow_setOf_h1Err (X : TwoComplex V) :
    BddBelow {r : ℝ | ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      r = α.defect (movedNorm (Fin (n + 2))) / ((n + 2 : ℕ) : ℝ) / α.gaugeDistErr} :=
  ⟨0, by
    rintro r ⟨n, α, hα, rfl⟩
    exact div_nonneg (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hα.le⟩

/-- The cross-degree Cheeger constant is nonnegative. -/
theorem h1Err_nonneg (X : TwoComplex V) : 0 ≤ h1Err X :=
  Real.sInf_nonneg fun _ ⟨_, α, hα, hr⟩ =>
    hr ▸ div_nonneg (div_nonneg (α.defect_nonneg _) (Nat.cast_nonneg _)) hα.le

/-- Every cochain of degree `n + 2` at positive cross-degree gauge distance gives an upper bound
on `h1Err X`. -/
theorem h1Err_le_div {X : TwoComplex V} {n : ℕ} {α : Cochain X (Perm (Fin (n + 2)))}
    (hα : 0 < α.gaugeDistErr) :
    h1Err X ≤ α.defect (movedNorm (Fin (n + 2))) / ((n + 2 : ℕ) : ℝ) / α.gaugeDistErr :=
  csInf_le (bddBelow_setOf_h1Err X) ⟨n, α, hα, rfl⟩

/-- When some cochain has positive cross-degree gauge distance, `c ≤ h1Err X` holds iff `c`
bounds every cross-degree expansion ratio from below. -/
theorem le_h1Err_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    c ≤ h1Err X ↔ ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr →
      c ≤ α.defect (movedNorm (Fin (n + 2))) / ((n + 2 : ℕ) : ℝ) / α.gaugeDistErr := by
  obtain ⟨n₀, α₀, hα₀⟩ := hne
  rw [h1Err_def, le_csInf_iff (bddBelow_setOf_h1Err X) ⟨_, n₀, α₀, hα₀, rfl⟩]
  exact ⟨fun h n α hα => h _ ⟨n, α, hα, rfl⟩, fun h _ ⟨n, α, hα, hr⟩ => hr ▸ h n α hα⟩

/-- When some cochain has positive cross-degree gauge distance, `h1Err X < c` holds iff some
such cochain has cross-degree expansion ratio strictly below `c`. -/
theorem h1Err_lt_iff {X : TwoComplex V}
    (hne : ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) {c : ℝ} :
    h1Err X < c ↔ ∃ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr ∧
      α.defect (movedNorm (Fin (n + 2))) / ((n + 2 : ℕ) : ℝ) / α.gaugeDistErr < c := by
  simpa only [not_le, not_forall, exists_prop] using (le_h1Err_iff hne (c := c)).not

/-- When every cochain of every degree `n + 2 ≥ 2` has cross-degree gauge distance zero, the
ratio set is empty and `h1Err X = 0`. -/
theorem h1Err_eq_zero_of_forall_gaugeDistErr_eq_zero {X : TwoComplex V}
    (h : ∀ (n : ℕ) (α : Cochain X (Perm (Fin (n + 2)))), α.gaugeDistErr = 0) : h1Err X = 0 := by
  simp [h1Err_def, h]

end Constant

/-! ### The star bound in the cross-degree convention -/

section StarBound

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

/-- The star bound in the cross-degree convention: for a cochain of degree `n ≥ 2` on
`complete V`, `card V * gaugeDistErr α ≤ 3 * (defect α / n)`. The star gauges have the cochain's
own degree, where the cross-degree cost is the moved-point cost divided by `n`. -/
theorem card_mul_gaugeDistErr_le (hn : 2 ≤ n) (α : Cochain (complete V) (Perm (Fin n))) :
    (Fintype.card V : ℝ) * α.gaugeDistErr ≤ 3 * (α.defect (movedNorm (Fin n)) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [mul_div_assoc', le_div_iff₀ hn']
  calc (Fintype.card V : ℝ) * α.gaugeDistErr * n
      = (Fintype.card V : ℝ) * (n * α.gaugeDistErr) := by ring
    _ ≤ (Fintype.card V : ℝ) * α.gaugeDist (movedNorm (Fin n)) :=
        mul_le_mul_of_nonneg_left (α.mul_gaugeDistErr_le_gaugeDist hn) (Nat.cast_nonneg _)
    _ ≤ 3 * α.defect (movedNorm (Fin n)) := card_mul_gaugeDist_le _ isConjInvariant_movedNorm α

/-- Pointwise ratio form of the cross-degree star bound for a cochain of degree `n ≥ 2` at
positive cross-degree gauge distance. -/
theorem Cochain.card_div_three_le_defect_div_div_gaugeDistErr (hn : 2 ≤ n)
    {α : Cochain (complete V) (Perm (Fin n))} (hα : 0 < α.gaugeDistErr) :
    (Fintype.card V : ℝ) / 3 ≤ α.defect (movedNorm (Fin n)) / n / α.gaugeDistErr := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hα, mul_comm _ (3 : ℝ)]
  exact card_mul_gaugeDistErr_le hn α

/-- The cross-degree star bound as a lower bound on `h1Err (complete V)`, whenever some cochain
of degree at least `2` has positive cross-degree gauge distance. -/
theorem card_div_three_le_h1Err
    (hne : ∃ (n : ℕ) (α : Cochain (complete V) (Perm (Fin (n + 2)))), 0 < α.gaugeDistErr) :
    (Fintype.card V : ℝ) / 3 ≤ h1Err (complete V) :=
  (le_h1Err_iff hne).mpr fun n _ hα =>
    Cochain.card_div_three_le_defect_div_div_gaugeDistErr (by omega) hα

/-- On `complete V` with `3 ≤ card V`, some `Perm (Fin 2)`-valued cochain has positive
cross-degree gauge distance. -/
theorem exists_gaugeDistErr_pos_complete (hV : 3 ≤ Fintype.card V) :
    ∃ α : Cochain (complete V) (Perm (Fin 2)), 0 < α.gaugeDistErr := by
  obtain ⟨α, hα⟩ := exists_not_isCoboundary_complete (G := Perm (Fin 2)) hV
  exact ⟨α, Cochain.gaugeDistErr_pos_of_not_isCoboundary hα⟩

/-- For `3 ≤ card V`, the cross-degree Cheeger constant of the complete complex is at least
`card V / 3`. -/
theorem card_div_three_le_h1Err_of_three_le_card (hV : 3 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) / 3 ≤ h1Err (complete V) := by
  obtain ⟨α, hα⟩ := exists_gaugeDistErr_pos_complete hV
  exact card_div_three_le_h1Err ⟨0, α, hα⟩

end StarBound

end TauCeti

end
