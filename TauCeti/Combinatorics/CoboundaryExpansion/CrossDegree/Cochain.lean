/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Invariance

/-!
# Attainment, invariance, and unoriented edge sums for `costErr`, `gaugeDistErr`, and `h1Err`

This file extends `TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.CheegerConstant` with
unoriented edge representations, `movedNorm` infimum identities, linear-order independence,
vertex-relabelling and degree-`2` gauge invariance, attainment, and uniform `1 / (n + 1)`
non-coboundary lower bounds for `Cochain.costErr`, `Cochain.gaugeDistErr`, and `TauCeti.h1Err`:

* **Unoriented edge representation and linear-order independence** (`Cochain.edgeCostErr`,
  `Cochain.costErr_eq_sum_edges`, `Cochain.costErr_congr_linearOrder`,
  `Cochain.gaugeDistErr_congr_linearOrder`, and `TauCeti.h1Err_congr_linearOrder`): `costErr`
  equals the unoriented sum of `edgeCostErr` over `X.edges`, so `costErr`, `gaugeDistErr`, and
  `h1Err` do not depend on the `LinearOrder` chosen on `V`.
* **Equal-degree `movedNorm` rescaling and upper bounds** (`Cochain.costErr_eq_cost_div`,
  `Cochain.mul_ciInf_costErr_eq_gaugeDist`, `Cochain.ciInf_costErr_eq_gaugeDist_div`,
  `Cochain.gaugeDistErr_le_ciInf_costErr`, and `Cochain.gaugeDistErr_le_gaugeDist_div`): in equal
  nonzero degree `n`, `costErr` and its gauge infimum equal `cost (movedNorm (Fin n)) / n` and
  `gaugeDist (movedNorm (Fin n)) / n`, so for `2 ≤ n` we have
  `α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin n)) / n`.
* **Relabelling invariance and degree-`2` gauge invariance** (`Cochain.costErr_relabel`,
  `Cochain.costErr_relabelComplete`, `Cochain.ciInf_costErr_relabel`,
  `Cochain.ciInf_costErr_relabelComplete`, `Cochain.gaugeDistErr_relabel`,
  `Cochain.gaugeDistErr_relabelComplete`, `Cochain.ciInf_costErr_smul_of_le`,
  `Cochain.gaugeDistErr_smul`, `TauCeti.h1Err_relabel`, `TauCeti.h1Err_complete_congr`, and
  `TauCeti.h1Err_complete_eq_of_card_eq`): `costErr`, `gaugeDistErr`, and `h1Err` are invariant
  under arbitrary vertex bijections `V ≃ W`, and transforming a degree-`2` cochain by a degree-`2`
  vertex gauge preserves `gaugeDistErr`.
* **Attainment across fixed and variable gauge degrees** (`Cochain.exists_costErr_eq_ciInf` and
  `Cochain.exists_costErr_eq_gaugeDistErr`): both the fixed-degree infimum of `costErr` and the
  global infimum `gaugeDistErr` over all degrees `m + 2 ≥ 2` are attained.
* **Uniform `1 / (n + 1)` non-coboundary gap**
  (`Cochain.one_div_add_one_le_costErr_of_not_isCoboundary` and
  `Cochain.one_div_add_one_le_gaugeDistErr_of_not_isCoboundary`): every non-coboundary cochain of
  degree `n` incurs `costErr` and `gaugeDistErr` at least `1 / (n + 1)`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, §2.2,
  equations (2.8)–(2.9) and the display after (2.9), pp. 6–7.
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Zenodo, doi:10.5281/zenodo.23245792, Section 2 and Proposition 10.
-/

public section

open Finset

namespace TauCeti

open Equiv Equiv.Perm TwoComplex

namespace Cochain

section UnorientedEdgeCostErr

variable {V W : Type*} {n m : ℕ}

/-- Reversing a vertex pair inverts both `α u v` and the gauge quotient `β u * (β v)⁻¹`, leaving
the edge term `distErr` unchanged. -/
theorem distErr_apply_mul_inv_swap {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) (u v : V) :
    distErr (α v u) (β v * (β u)⁻¹) = distErr (α u v) (β u * (β v)⁻¹) := by
  rw [α.apply_swap u v, distErr_inv_mul_inv]

/-- The cross-degree gauge cost contribution of an unoriented edge `e`, or `0` if `e ∉ X.edges`. -/
noncomputable def edgeCostErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) (e : Finset V) : ℝ :=
  X.edgeEval (fun u v => distErr (α u v) (β u * (β v)⁻¹)) e

/-- Evaluating `edgeCostErr` on any edge `e ∈ X.edges` via its two distinct endpoints. -/
theorem edgeCostErr_of_mem_edges {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) {e : Finset V} (he : e ∈ X.edges) {u v : V} (huv : u ≠ v)
    (hu : u ∈ e) (hv : v ∈ e) :
    α.edgeCostErr β e = distErr (α u v) (β u * (β v)⁻¹) :=
  X.edgeEval_of_mem_edges (fun a b _ => α.distErr_apply_mul_inv_swap β a b) he huv hu hv

/-- Evaluating `edgeCostErr` directly on a pair `{u, v} ∈ X.edges`. -/
@[simp, grind =] theorem edgeCostErr_pair [DecidableEq V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) {u v : V}
    (he : ({u, v} : Finset V) ∈ X.edges) :
    α.edgeCostErr β {u, v} = distErr (α u v) (β u * (β v)⁻¹) :=
  X.edgeEval_pair (fun a b _ => α.distErr_apply_mul_inv_swap β a b) he

@[simp] theorem edgeCostErr_of_notMem_edges {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) {e : Finset V} (he : e ∉ X.edges) : α.edgeCostErr β e = 0 :=
  X.edgeEval_of_notMem_edges _ he

theorem edgeCostErr_nonneg {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin m)) (e : Finset V) : 0 ≤ α.edgeCostErr β e :=
  X.edgeEval_nonneg (fun _ _ => distErr_nonneg _ _) e

@[simp] theorem edgeCostErr_relabel {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (γ : W → Perm (Fin m)) (e : V ≃ W) (s : Finset W) :
    (α.relabel e).edgeCostErr γ s = α.edgeCostErr (γ ∘ e) (s.map e.symm.toEmbedding) := by
  rw [edgeCostErr, edgeCostErr, X.edgeEval_relabel e
    (fun u v _ => (α.relabel e).distErr_apply_mul_inv_swap γ u v)]
  congr 1; funext u v; simp [relabel_apply]

@[simp 1100] theorem edgeCostErr_relabel_map {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (γ : W → Perm (Fin m)) (e : V ≃ W) (s : Finset V) :
    (α.relabel e).edgeCostErr γ (s.map e.toEmbedding) = α.edgeCostErr (γ ∘ e) s := by
  rw [edgeCostErr, edgeCostErr, X.edgeEval_relabel_map e
    (fun u v _ => (α.relabel e).distErr_apply_mul_inv_swap γ u v)]
  congr 1; funext u v; simp [relabel_apply]

/-- Multiplying the equal-degree `edgeCostErr` of `e` by `n` recovers `edgeCost (movedNorm (Fin n))`
on `e`. -/
theorem mul_edgeCostErr_eq_edgeCost {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (β : V → Perm (Fin n)) (e : Finset V) :
    (n : ℝ) * α.edgeCostErr β e = α.edgeCost (movedNorm (Fin n)) β e := by
  by_cases he : e ∈ X.edges
  · rw [α.edgeCostErr_of_mem_edges β he (X.edgePair_ne ⟨e, he⟩)
        (X.edgePair_fst_mem ⟨e, he⟩) (X.edgePair_snd_mem ⟨e, he⟩),
      α.edgeCost_of_mem_edges (movedNorm (Fin n)) β he (X.edgePair_ne ⟨e, he⟩)
        (X.edgePair_fst_mem ⟨e, he⟩) (X.edgePair_snd_mem ⟨e, he⟩),
      mul_distErr_mul_inv_eq_movedNorm, movedNorm_apply]
  · simp [he]

end UnorientedEdgeCostErr

section CrossDegree

variable {V W : Type*} [Fintype V] [LinearOrder V] {X : TwoComplex V} {n m : ℕ}

/-- `costErr` equals the sum of `edgeCostErr` over the unoriented edges `X.edges`. -/
theorem costErr_eq_sum_edges (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β = ∑ e ∈ X.edges, α.edgeCostErr β e := by
  rw [costErr_def, ← X.sum_filter_lt_mem_edges (α.edgeCostErr β)]
  exact sum_congr rfl fun p hp => (α.edgeCostErr_pair β (mem_filter.mp hp).2.2).symm

theorem ciInf_costErr_nonneg (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    0 ≤ ⨅ β : V → Perm (Fin m), α.costErr β :=
  Real.iInf_nonneg α.costErr_nonneg

theorem bddBelow_costErr_range (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    BddBelow (Set.range (α.costErr (m := m))) :=
  ⟨0, Set.forall_mem_range.mpr α.costErr_nonneg⟩

theorem bddBelow_ciInf_costErr_range (α : Cochain X (Perm (Fin n))) :
    BddBelow (Set.range fun m : ℕ => ⨅ β : V → Perm (Fin (m + 2)), α.costErr β) :=
  ⟨0, Set.forall_mem_range.mpr fun m => α.ciInf_costErr_nonneg (m + 2)⟩

@[simp] theorem costErr_one_one [NeZero n] :
    (1 : Cochain X (Perm (Fin n))).costErr (1 : V → Perm (Fin n)) = 0 := by
  simp [costErr_def]

/-- In equal nonzero degree `n`, `costErr` equals `cost` with respect to `movedNorm (Fin n)`
divided by `n`. -/
theorem costErr_eq_cost_div [NeZero n] (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    α.costErr β = α.cost (movedNorm (Fin n)) β / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, α.mul_costErr_eq_cost β]

/-- In equal degree `n`, multiplying the `costErr` gauge infimum by `n` recovers
`gaugeDist (movedNorm (Fin n))`. -/
theorem mul_ciInf_costErr_eq_gaugeDist (α : Cochain X (Perm (Fin n))) :
    (n : ℝ) * (⨅ β : V → Perm (Fin n), α.costErr β) = α.gaugeDist (movedNorm (Fin n)) := by
  rw [Real.mul_iInf_of_nonneg (Nat.cast_nonneg n), gaugeDist_def]
  exact iInf_congr (α.mul_costErr_eq_cost)

/-- In equal nonzero degree `n`, the `costErr` gauge infimum equals `gaugeDist (movedNorm (Fin n))`
divided by `n`. -/
theorem ciInf_costErr_eq_gaugeDist_div [NeZero n] (α : Cochain X (Perm (Fin n))) :
    (⨅ β : V → Perm (Fin n), α.costErr β) = α.gaugeDist (movedNorm (Fin n)) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, α.mul_ciInf_costErr_eq_gaugeDist]

/-- Every gauge degree `m ≥ 2` bounds `α.gaugeDistErr` from above by its fixed-degree `costErr`
infimum. -/
theorem gaugeDistErr_le_ciInf_costErr (α : Cochain X (Perm (Fin n))) (hm : 2 ≤ m) :
    α.gaugeDistErr ≤ ⨅ β : V → Perm (Fin m), α.costErr β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [gaugeDistErr_def]
  exact ciInf_le α.bddBelow_ciInf_costErr_range k

/-- When `2 ≤ n`, the cross-degree gauge distance is at most `1 / n` times the equal-degree
`movedNorm (Fin n)` gauge distance. -/
theorem gaugeDistErr_le_gaugeDist_div (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n) :
    α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin n)) / n := by
  have : NeZero n := ⟨by omega⟩
  exact (α.gaugeDistErr_le_ciInf_costErr hn).trans_eq α.ciInf_costErr_eq_gaugeDist_div

/-- `gaugeDist ℓ` equals the infimum of unoriented edge-cost sums over `X.edges`. -/
theorem gaugeDist_eq_ciInf_sum_edgeCost {G : Type*} [Group G] (ℓ : GroupNorm G)
    (α : Cochain X G) :
    α.gaugeDist ℓ = ⨅ β : V → G, ∑ e ∈ X.edges, α.edgeCost ℓ β e := by
  rw [gaugeDist_def]
  exact iInf_congr fun β => α.cost_eq_sum_edges ℓ β

/-- Relabelling a cochain along `e : V ≃ W` pulls the gauge back along `e` in `costErr`. -/
@[simp] theorem costErr_relabel [Fintype W] [LinearOrder W] (α : Cochain X (Perm (Fin n)))
    (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabel e).costErr γ = α.costErr (γ ∘ e) := by
  rw [costErr_eq_sum_edges, costErr_eq_sum_edges, X.sum_edges_relabel e]
  exact sum_congr rfl fun s _ => α.edgeCostErr_relabel_map γ e s

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` pulls the gauge back along `e` in
`costErr`. -/
@[simp] theorem costErr_relabelComplete [Fintype W] [LinearOrder W]
    (α : Cochain (complete V) (Perm (Fin n))) (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabelComplete e).costErr γ = α.costErr (γ ∘ e) :=
  (Cochain.congr_complex (fun _ δ => δ.costErr γ) (relabel_complete e).symm
    fun _ _ => by simp).trans (α.costErr_relabel γ e)

/-- Relabelling a cochain along `e : V ≃ W` preserves the degree-`m` `costErr` infimum. -/
theorem ciInf_costErr_relabel [Fintype W] [LinearOrder W] (α : Cochain X (Perm (Fin n)))
    (e : V ≃ W) (m : ℕ) :
    (⨅ γ : W → Perm (Fin m), (α.relabel e).costErr γ) =
      ⨅ β : V → Perm (Fin m), α.costErr β :=
  (Equiv.arrowCongr e.symm (Equiv.refl (Perm (Fin m)))).iInf_congr fun γ =>
    (α.costErr_relabel γ e).symm

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves the degree-`m` `costErr`
infimum. -/
theorem ciInf_costErr_relabelComplete [Fintype W] [LinearOrder W]
    (α : Cochain (complete V) (Perm (Fin n))) (e : V ≃ W) (m : ℕ) :
    (⨅ γ : W → Perm (Fin m), (α.relabelComplete e).costErr γ) =
      ⨅ β : V → Perm (Fin m), α.costErr β :=
  (Equiv.arrowCongr e.symm (Equiv.refl (Perm (Fin m)))).iInf_congr fun γ =>
    (α.costErr_relabelComplete γ e).symm

/-- Relabelling a cochain along `e : V ≃ W` preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_relabel [Fintype W] [LinearOrder W] (α : Cochain X (Perm (Fin n)))
    (e : V ≃ W) :
    (α.relabel e).gaugeDistErr = α.gaugeDistErr := by
  simp_rw [gaugeDistErr_def]
  exact iInf_congr fun m => α.ciInf_costErr_relabel e (m + 2)

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_relabelComplete [Fintype W] [LinearOrder W]
    (α : Cochain (complete V) (Perm (Fin n))) (e : V ≃ W) :
    (α.relabelComplete e).gaugeDistErr = α.gaugeDistErr :=
  (Cochain.congr_complex (fun _ γ => γ.gaugeDistErr) (relabel_complete e).symm
    fun _ _ => by simp).trans (α.gaugeDistErr_relabel e)

/-- When `n ≤ m`, the degree-`m` `costErr` infimum is invariant under the equal-degree gauge
action on `α`. -/
theorem ciInf_costErr_smul_of_le (γ : V → Perm (Fin n)) (α : Cochain X (Perm (Fin n)))
    (hnm : n ≤ m) :
    (⨅ β : V → Perm (Fin m), (γ • α).costErr β) = ⨅ β : V → Perm (Fin m), α.costErr β := by
  set E := univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges
  have hL (β : V → Perm (Fin m)) :
      (γ • α).costErr β =
        ∑ p ∈ E, distErr ((γ p.1)⁻¹ * α p.1 p.2 * γ p.2) (β p.1 * (β p.2)⁻¹) := by
    rw [costErr_def]
    refine sum_congr rfl fun p hp => ?_
    rw [smul_apply_of_adj γ α ((X.adj_iff_pair_mem_edges p.1 p.2).mpr (mem_filter.mp hp).2.2)]
  simp_rw [hL, costErr_def]
  exact E.ciInf_sum_distErr_inv_mul_mul_of_le α γ hnm

/-- Transforming a degree-`2` cochain by a degree-`2` gauge preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_smul (γ : V → Perm (Fin 2)) (α : Cochain X (Perm (Fin 2))) :
    (γ • α).gaugeDistErr = α.gaugeDistErr := by
  simp_rw [gaugeDistErr_def]
  exact iInf_congr fun m => ciInf_costErr_smul_of_le γ α (Nat.le_add_left 2 m)

/-- For every fixed gauge degree `m : ℕ`, `α.costErr` attains its infimum over
`V → Perm (Fin m)`. -/
theorem exists_costErr_eq_ciInf (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    ∃ β : V → Perm (Fin m), α.costErr β = ⨅ γ : V → Perm (Fin m), α.costErr γ := by
  set E := univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges
  simp_rw [costErr_def]
  exact E.exists_eq_ciInf_sum_distErr_mul_inv α m

/-- The cross-degree gauge distance `gaugeDistErr` is always attained by some gauge of some degree
`m + 2 ≥ 2`. -/
theorem exists_costErr_eq_gaugeDistErr (α : Cochain X (Perm (Fin n))) :
    ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β = α.gaugeDistErr := by
  set E := univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges
  simp_rw [gaugeDistErr_def, costErr_def]
  exact E.exists_eq_ciInf₂_sum_distErr_mul_inv α

private theorem exists_eq_mul_inv_filter_lt_iff_isCoboundary (α : Cochain X (Perm (Fin n))) :
    (∃ γ : V → Perm (Fin n),
        ∀ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
          α p.1 p.2 = γ p.1 * (γ p.2)⁻¹) ↔
      α.IsCoboundary := by
  rw [isCoboundary_def]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, fun u v huv => ?_⟩
    rcases lt_trichotomy u v with h | rfl | h
    · exact hγ (u, v) (mem_filter.mpr ⟨mem_univ _, h, (X.adj_iff_pair_mem_edges u v).mp huv⟩)
    · exact (huv.ne rfl).elim
    · have hvu : α v u = γ v * (γ u)⁻¹ := hγ (v, u)
        (mem_filter.mpr ⟨mem_univ _, h, (X.adj_iff_pair_mem_edges v u).mp huv.symm⟩)
      rw [α.apply_swap v u, hvu, mul_inv_rev, inv_inv]
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, fun p hp =>
      hγ p.1 p.2 ((X.adj_iff_pair_mem_edges p.1 p.2).mpr (mem_filter.mp hp).2.2)⟩

/-- Every non-coboundary cochain of degree `n` incurs `costErr` at least `1 / (n + 1)` against any
gauge of any degree `m`. -/
theorem one_div_add_one_le_costErr_of_not_isCoboundary {α : Cochain X (Perm (Fin n))}
    (hncob : ¬ α.IsCoboundary) (β : V → Perm (Fin m)) :
    1 / ((n : ℝ) + 1) ≤ α.costErr β := by
  rw [costErr_def]
  exact (univ.filter fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges
    ).one_div_add_one_le_sum_distErr_mul_inv_of_not_exists α β
      (mt (exists_eq_mul_inv_filter_lt_iff_isCoboundary α).mp hncob)

/-- Every non-coboundary cochain of degree `n` has `gaugeDistErr` at least `1 / (n + 1)`. -/
theorem one_div_add_one_le_gaugeDistErr_of_not_isCoboundary {α : Cochain X (Perm (Fin n))}
    (hncob : ¬ α.IsCoboundary) :
    1 / ((n : ℝ) + 1) ≤ α.gaugeDistErr :=
  (α.le_gaugeDistErr_iff).mpr fun _ β =>
    one_div_add_one_le_costErr_of_not_isCoboundary hncob β

@[simp] theorem gaugeDistErr_one (hn : 2 ≤ n) :
    (1 : Cochain X (Perm (Fin n))).gaugeDistErr = 0 :=
  isCoboundary_one.gaugeDistErr_eq_zero hn

end CrossDegree

section LinearOrderInvariance

/-- `costErr` does not depend on the `LinearOrder` chosen on `V`. -/
theorem costErr_congr_linearOrder {V : Type*} [Fintype V] (l₁ l₂ : LinearOrder V)
    {X : TwoComplex V} {n m : ℕ} (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    @costErr V _ l₁ X n m α β = @costErr V _ l₂ X n m α β :=
  (@costErr_eq_sum_edges V _ l₁ X n m α β).trans (@costErr_eq_sum_edges V _ l₂ X n m α β).symm

/-- `gaugeDistErr` does not depend on the `LinearOrder` chosen on `V`. -/
theorem gaugeDistErr_congr_linearOrder {V : Type*} [Fintype V] (l₁ l₂ : LinearOrder V)
    {X : TwoComplex V} {n : ℕ} (α : Cochain X (Perm (Fin n))) :
    @gaugeDistErr V _ l₁ X n α = @gaugeDistErr V _ l₂ X n α := by
  simp only [@gaugeDistErr_def V _ l₁ X n α, @gaugeDistErr_def V _ l₂ X n α,
    costErr_congr_linearOrder l₁ l₂ α]

end LinearOrderInvariance

end Cochain

section CrossDegreeCheegerInvariance

variable {V W : Type*}

/-- `h1Err` does not depend on the `LinearOrder` chosen on `V`. -/
theorem h1Err_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) (X : TwoComplex V) :
    @h1Err V _ l₁ X = @h1Err V _ l₂ X := by
  simp only [@h1Err_def V _ l₁ X, @h1Err_def V _ l₂ X,
    Cochain.gaugeDistErr_congr_linearOrder l₁ l₂,
    Cochain.defect_congr_linearOrder l₁ l₂ isConjInvariant_movedNorm]

/-- Relabelling `X` along `e : V ≃ W` preserves `h1Err`. -/
@[simp] theorem h1Err_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (X : TwoComplex V) (e : V ≃ W) : h1Err (X.relabel e) = h1Err X := by
  rw [h1Err_def, h1Err_def]; congr 1; ext r
  refine exists_congr fun n => ?_
  exact ((Cochain.relabelEquiv X e).exists_congr fun α => by
    simp [α.defect_relabel isConjInvariant_movedNorm e]).symm

/-- `h1Err` on the complete complex is preserved along any bijection `V ≃ W`. -/
theorem h1Err_complete_congr [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (e : V ≃ W) : h1Err (complete V) = h1Err (complete W) := by
  rw [← relabel_complete e, h1Err_relabel (complete V) e]

/-- `h1Err (complete V)` depends on `V` only through `Fintype.card V`. -/
theorem h1Err_complete_eq_of_card_eq [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (hcard : Fintype.card V = Fintype.card W) : h1Err (complete V) = h1Err (complete W) :=
  h1Err_complete_congr (Fintype.equivOfCardEq hcard)

end CrossDegreeCheegerInvariance

end TauCeti

end
