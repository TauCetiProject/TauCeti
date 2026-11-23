/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Invariance
public import TauCeti.Combinatorics.CoboundaryExpansion.CrossDegree.Invariance

/-!
# Cross-degree cochain distance `costErr` and `gaugeDistErr`

This file introduces the Chapman–Lubotzky cross-degree gauge cost and gauge distance for
permutation-valued 1-cochains on an arbitrary `TwoComplex V` (`Cochain.edgeCostErr`,
`Cochain.costErr`, and `Cochain.gaugeDistErr`):

* **Intrinsic definition and ordered comparison** (`Cochain.edgeCostErr`, `Cochain.costErr`,
  `Cochain.costErr_eq_sum_filter_lt`, and `Cochain.costErr_complete`): `Cochain.costErr` is defined
  intrinsically over `X.edges` without ambient `Fintype` or `LinearOrder` assumptions on `V`, and
  equals the ordered pair sum over strictly increasing edge pairs `u < v` whenever `[Fintype V]`
  and `[LinearOrder V]` are present.
* **Equal-degree `movedNorm` rescaling and upper bounds** (`Cochain.mul_costErr_eq_cost`,
  `Cochain.costErr_eq_cost_div`, `Cochain.ciInf_costErr_eq_gaugeDist_div`, and
  `Cochain.gaugeDistErr_le_gaugeDist_div`): in equal nonzero degree `n`, `costErr` equals
  `cost (movedNorm (Fin n)) / n`, and for `2 ≤ n` the cross-degree gauge distance `gaugeDistErr`
  is bounded above by `gaugeDist (movedNorm (Fin n)) / n`.
* **Relabelling invariance and degree-`2` gauge invariance** (`Cochain.costErr_relabel`,
  `Cochain.costErr_relabelComplete`, `Cochain.gaugeDistErr_relabel`,
  `Cochain.gaugeDistErr_relabelComplete`, and `Cochain.gaugeDistErr_smul`): `costErr` and
  `gaugeDistErr` are invariant under arbitrary vertex bijections `V ≃ W`, and transforming a
  degree-`2` cochain by a degree-`2` vertex gauge preserves `gaugeDistErr`.
* **Attainment across fixed and variable gauge degrees** (`Cochain.exists_costErr_eq_ciInf` and
  `Cochain.exists_costErr_eq_gaugeDistErr`): on any `TwoComplex V` over an arbitrary (possibly
  infinite) vertex type `V`, both the fixed-degree infimum of `costErr` and the global infimum
  `gaugeDistErr` over all degrees `m + 2 ≥ 2` are attained.
* **Uniform `1 / (n + 1)` non-coboundary gap and coboundary characterization**
  (`Cochain.one_div_add_one_le_costErr_of_not_isCoboundary`,
  `Cochain.one_div_add_one_le_gaugeDistErr_of_not_isCoboundary`,
  `Cochain.gaugeDistErr_eq_zero_iff_isCoboundary`, and
  `Cochain.gaugeDistErr_pos_iff_not_isCoboundary`): every non-coboundary cochain of degree `n`
  incurs `gaugeDistErr` at least `1 / (n + 1)`, and for `2 ≤ n` we have `α.gaugeDistErr = 0` if
  and only if `α.IsCoboundary`.

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

section CrossDegree

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

/-- The cross-degree cost of a gauge `β` of degree `m` against a cochain `α` of degree `n`: the
distance with errors between `α` and `β u * (β v)⁻¹`, summed over the unoriented edges
`X.edges`. -/
noncomputable def costErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) : ℝ :=
  ∑ e ∈ X.edges, α.edgeCostErr β e

theorem costErr_def {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β = ∑ e ∈ X.edges, α.edgeCostErr β e := (rfl)

/-- With `[Fintype V]` and `[LinearOrder V]`, `costErr` equals the sum of
`distErr (α u v) (β u * (β v)⁻¹)` over strictly increasing edge pairs `u < v`. -/
theorem costErr_eq_sum_filter_lt [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_def, ← X.sum_filter_lt_mem_edges (α.edgeCostErr β)]
  exact sum_congr rfl fun p hp => α.edgeCostErr_pair β (mem_filter.mp hp).2.2

/-- On the complete complex, `costErr` sums `distErr (α u v) (β u * (β v)⁻¹)` over all strictly
increasing vertex pairs `u < v`. -/
theorem costErr_complete [Fintype V] [LinearOrder V]
    (α : Cochain (complete V) (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β =
      ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
        distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) := by
  rw [costErr_eq_sum_filter_lt]
  refine sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_edges_complete, card_pair_eq_two_iff,
    and_iff_left_iff_imp]
  exact LT.lt.ne

theorem costErr_nonneg {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    0 ≤ α.costErr β :=
  sum_nonneg fun e _ => α.edgeCostErr_nonneg β e

theorem bddBelow_range_costErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    BddBelow (Set.range (α.costErr (m := m))) :=
  ⟨0, Set.forall_mem_range.mpr (α.costErr_nonneg)⟩

theorem ciInf_costErr_nonneg {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    0 ≤ ⨅ β : V → Perm (Fin m), α.costErr β :=
  Real.iInf_nonneg α.costErr_nonneg

theorem bddBelow_range_ciInf_costErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    BddBelow (Set.range fun m : ℕ => ⨅ β : V → Perm (Fin (m + 2)), α.costErr β) :=
  ⟨0, Set.forall_mem_range.mpr fun m => α.ciInf_costErr_nonneg (m + 2)⟩

@[simp] theorem costErr_one_one [NeZero n] {X : TwoComplex V} :
    (1 : Cochain X (Perm (Fin n))).costErr (1 : V → Perm (Fin n)) = 0 := by
  refine sum_eq_zero fun e he => ?_
  rw [edgeCostErr_of_mem_edges _ _ he (X.edgePair_ne ⟨e, he⟩)
    (X.edgePair_fst_mem ⟨e, he⟩) (X.edgePair_snd_mem ⟨e, he⟩)]
  simp

/-- In equal degree `n`, multiplying `costErr` by `n` recovers the unoriented edge sum of
`edgeCost (movedNorm (Fin n))`, for every `n : ℕ`. -/
theorem mul_costErr_eq_sum_edgeCost {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    (n : ℝ) * α.costErr β = ∑ e ∈ X.edges, α.edgeCost (movedNorm (Fin n)) β e := by
  rw [costErr_def, mul_sum]
  exact sum_congr rfl fun e _ => α.mul_edgeCostErr_eq_edgeCost β e

/-- In equal nonzero degree `n`, `costErr` equals the unoriented edge sum of
`edgeCost (movedNorm (Fin n))` divided by `n`. -/
theorem costErr_eq_sum_edgeCost_div [NeZero n] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    α.costErr β = (∑ e ∈ X.edges, α.edgeCost (movedNorm (Fin n)) β e) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, α.mul_costErr_eq_sum_edgeCost β]

/-- In equal degree `n`, multiplying the `costErr` gauge infimum by `n` recovers the infimum of the
`movedNorm (Fin n)` unoriented edge cost sum. -/
theorem mul_ciInf_costErr_eq_ciInf_sum_edgeCost {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    (n : ℝ) * (⨅ β : V → Perm (Fin n), α.costErr β) =
      ⨅ β : V → Perm (Fin n), ∑ e ∈ X.edges, α.edgeCost (movedNorm (Fin n)) β e := by
  rw [Real.mul_iInf_of_nonneg (Nat.cast_nonneg n)]
  exact iInf_congr (α.mul_costErr_eq_sum_edgeCost)

/-- In equal nonzero degree `n`, the `costErr` gauge infimum equals the infimum of the
`movedNorm (Fin n)` unoriented edge cost sum divided by `n`. -/
theorem ciInf_costErr_eq_ciInf_sum_edgeCost_div [NeZero n] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    (⨅ β : V → Perm (Fin n), α.costErr β) =
      (⨅ β : V → Perm (Fin n), ∑ e ∈ X.edges, α.edgeCost (movedNorm (Fin n)) β e) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, α.mul_ciInf_costErr_eq_ciInf_sum_edgeCost]

/-- In equal degree `n`, multiplying `costErr` by `n` recovers `cost` with respect to
`Equiv.Perm.movedNorm (Fin n)`, for every `n : ℕ`. -/
theorem mul_costErr_eq_cost [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    (n : ℝ) * α.costErr β = α.cost (movedNorm (Fin n)) β := by
  rw [α.mul_costErr_eq_sum_edgeCost β, α.cost_eq_sum_edges (movedNorm (Fin n)) β]

/-- In equal nonzero degree `n`, `costErr` equals `cost` with respect to `movedNorm (Fin n)`
divided by `n`. -/
theorem costErr_eq_cost_div [Fintype V] [LinearOrder V] [NeZero n] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin n)) :
    α.costErr β = α.cost (movedNorm (Fin n)) β / n := by
  rw [α.costErr_eq_sum_edgeCost_div β, α.cost_eq_sum_edges (movedNorm (Fin n)) β]

/-- In equal degree `n`, multiplying the `costErr` gauge infimum by `n` recovers
`gaugeDist (movedNorm (Fin n))`. -/
theorem mul_ciInf_costErr_eq_gaugeDist [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    (n : ℝ) * (⨅ β : V → Perm (Fin n), α.costErr β) = α.gaugeDist (movedNorm (Fin n)) := by
  rw [α.mul_ciInf_costErr_eq_ciInf_sum_edgeCost, gaugeDist_def]
  exact iInf_congr fun β => (α.cost_eq_sum_edges (movedNorm (Fin n)) β).symm

/-- In equal nonzero degree `n`, the `costErr` gauge infimum equals `gaugeDist (movedNorm (Fin n))`
divided by `n`. -/
theorem ciInf_costErr_eq_gaugeDist_div [Fintype V] [LinearOrder V] [NeZero n] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    (⨅ β : V → Perm (Fin n), α.costErr β) = α.gaugeDist (movedNorm (Fin n)) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [eq_div_iff hn, mul_comm, α.mul_ciInf_costErr_eq_gaugeDist]

/-- Relabelling a cochain along `e : V ≃ W` pulls the gauge back along `e` in `costErr`. -/
@[simp] theorem costErr_relabel {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabel e).costErr γ = α.costErr (γ ∘ e) := by
  rw [costErr_def, costErr_def, X.sum_edges_relabel e]
  exact sum_congr rfl fun s _ => α.edgeCostErr_relabel_map γ e s

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` pulls the gauge back along `e` in
`costErr`. -/
@[simp] theorem costErr_relabelComplete [Fintype V] [Fintype W]
    (α : Cochain (complete V) (Perm (Fin n))) (γ : W → Perm (Fin m)) (e : V ≃ W) :
    (α.relabelComplete e).costErr γ = α.costErr (γ ∘ e) :=
  (Cochain.congr_complex (fun _ δ => δ.costErr γ) (relabel_complete e).symm
    fun _ _ => by simp).trans (α.costErr_relabel γ e)

/-- Relabelling a cochain along `e : V ≃ W` preserves the degree-`m` `costErr` infimum. -/
theorem ciInf_costErr_relabel {X : TwoComplex V} (α : Cochain X (Perm (Fin n)))
    (e : V ≃ W) (m : ℕ) :
    (⨅ γ : W → Perm (Fin m), (α.relabel e).costErr γ) =
      ⨅ β : V → Perm (Fin m), α.costErr β :=
  (Equiv.arrowCongr e.symm (Equiv.refl (Perm (Fin m)))).iInf_congr fun γ =>
    (α.costErr_relabel γ e).symm

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves the degree-`m` `costErr`
infimum. -/
theorem ciInf_costErr_relabelComplete [Fintype V] [Fintype W]
    (α : Cochain (complete V) (Perm (Fin n))) (e : V ≃ W) (m : ℕ) :
    (⨅ γ : W → Perm (Fin m), (α.relabelComplete e).costErr γ) =
      ⨅ β : V → Perm (Fin m), α.costErr β :=
  (Equiv.arrowCongr e.symm (Equiv.refl (Perm (Fin m)))).iInf_congr fun γ =>
    (α.costErr_relabelComplete γ e).symm

/-- The cross-degree gauge distance of `α`: the infimum of `costErr` over all gauges of all
degrees `m + 2 ≥ 2`. -/
noncomputable def gaugeDistErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) : ℝ :=
  ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β

theorem gaugeDistErr_def {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    α.gaugeDistErr = ⨅ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β := (rfl)

theorem gaugeDistErr_nonneg {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) : 0 ≤ α.gaugeDistErr :=
  Real.iInf_nonneg fun m => α.ciInf_costErr_nonneg (m + 2)

theorem gaugeDistErr_le_costErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) {m : ℕ} (β : V → Perm (Fin (m + 2))) :
    α.gaugeDistErr ≤ α.costErr β :=
  (ciInf_le α.bddBelow_range_ciInf_costErr m).trans
    (ciInf_le (α.bddBelow_range_costErr (m + 2)) β)

theorem gaugeDistErr_le_costErr_of_le {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (hm : 2 ≤ m) (β : V → Perm (Fin m)) :
    α.gaugeDistErr ≤ α.costErr β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact α.gaugeDistErr_le_costErr β

theorem gaugeDistErr_le_ciInf_costErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (hm : 2 ≤ m) :
    α.gaugeDistErr ≤ ⨅ β : V → Perm (Fin m), α.costErr β := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact ciInf_le α.bddBelow_range_ciInf_costErr k

/-- When `2 ≤ n`, the cross-degree gauge distance is at most `1 / n` times the equal-degree
`movedNorm (Fin n)` unoriented edge-sum infimum. -/
theorem gaugeDistErr_le_ciInf_sum_edgeCost_div {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n) :
    α.gaugeDistErr ≤
      (⨅ β : V → Perm (Fin n), ∑ e ∈ X.edges, α.edgeCost (movedNorm (Fin n)) β e) / n := by
  have : NeZero n := ⟨by omega⟩
  exact (α.gaugeDistErr_le_ciInf_costErr hn).trans_eq α.ciInf_costErr_eq_ciInf_sum_edgeCost_div

/-- When `2 ≤ n`, the cross-degree gauge distance is at most `1 / n` times the equal-degree
`movedNorm (Fin n)` gauge distance. -/
theorem gaugeDistErr_le_gaugeDist_div [Fintype V] [LinearOrder V] {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (hn : 2 ≤ n) :
    α.gaugeDistErr ≤ α.gaugeDist (movedNorm (Fin n)) / n := by
  have : NeZero n := ⟨by omega⟩
  exact (α.gaugeDistErr_le_ciInf_costErr hn).trans_eq α.ciInf_costErr_eq_gaugeDist_div

theorem le_gaugeDistErr_iff {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    c ≤ α.gaugeDistErr ↔ ∀ (m : ℕ) (β : V → Perm (Fin (m + 2))), c ≤ α.costErr β := by
  rw [gaugeDistErr_def]
  exact ⟨fun h m β => h.trans (α.gaugeDistErr_le_costErr β),
    fun h => le_ciInf fun m => le_ciInf fun β => h m β⟩

theorem gaugeDistErr_lt_iff {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) {c : ℝ} :
    α.gaugeDistErr < c ↔ ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β < c := by
  rw [← not_le, le_gaugeDistErr_iff]
  push Not
  exact Iff.rfl

private theorem costErr_eq_sum_edgePairs {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (β : V → Perm (Fin m)) :
    α.costErr β = ∑ p ∈ X.edgePairs, distErr (α p.1 p.2) (β p.1 * (β p.2)⁻¹) :=
  X.sum_edges_edgeEval fun u v => distErr (α u v) (β u * (β v)⁻¹)

private theorem exists_eq_mul_inv_edgePairs_iff_isCoboundary {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    (∃ γ : V → Perm (Fin n), ∀ p ∈ X.edgePairs, α p.1 p.2 = γ p.1 * (γ p.2)⁻¹) ↔
      α.IsCoboundary := by
  classical
  constructor
  · rintro ⟨γ, hγ⟩
    rw [isCoboundary_def]
    refine ⟨γ, fun u v huv => ?_⟩
    have he : ({u, v} : Finset V) ∈ X.edges := (X.adj_iff_pair_mem_edges u v).mp huv
    let e : X.edges := ⟨{u, v}, he⟩
    have hp : X.edgePair e ∈ X.edgePairs := X.edgePair_mem_edgePairs e
    have hpair : ({(X.edgePair e).1, (X.edgePair e).2} : Set V) = ({u, v} : Set V) := by
      simpa [e] using congrArg ((↑) : Finset V → Set V) (X.edgePair_pair_eq e)
    rw [Set.pair_eq_pair_iff] at hpair
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa [h₁, h₂] using hγ _ hp
    · have hvu := hγ _ hp
      rw [h₁, h₂] at hvu
      rw [α.apply_swap v u, hvu, mul_inv_rev, inv_inv]
  · intro h
    rw [isCoboundary_def] at h
    obtain ⟨γ, hγ⟩ := h
    refine ⟨γ, fun p hp => ?_⟩
    obtain ⟨e, rfl⟩ := X.mem_edgePairs.mp hp
    exact hγ _ _ (X.adj_edgePair e)

/-- When `n ≤ m`, the degree-`m` `costErr` infimum is invariant under the equal-degree gauge
action on `α`. -/
theorem ciInf_costErr_smul_of_le {X : TwoComplex V}
    (γ : V → Perm (Fin n)) (α : Cochain X (Perm (Fin n))) (hnm : n ≤ m) :
    (⨅ β : V → Perm (Fin m), (γ • α).costErr β) = ⨅ β : V → Perm (Fin m), α.costErr β := by
  classical
  have hL (β : V → Perm (Fin m)) :
      (γ • α).costErr β =
        ∑ p ∈ X.edgePairs, distErr ((γ p.1)⁻¹ * α p.1 p.2 * γ p.2) (β p.1 * (β p.2)⁻¹) := by
    rw [(γ • α).costErr_eq_sum_edgePairs β]
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨e, rfl⟩ := X.mem_edgePairs.mp hp
    rw [smul_apply_of_adj γ α (X.adj_edgePair e)]
  simp_rw [hL, α.costErr_eq_sum_edgePairs]
  exact X.edgePairs.ciInf_sum_distErr_inv_mul_mul_of_le α γ hnm

/-- Transforming a degree-`2` cochain by a degree-`2` gauge preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_smul {X : TwoComplex V}
    (γ : V → Perm (Fin 2)) (α : Cochain X (Perm (Fin 2))) :
    (γ • α).gaugeDistErr = α.gaugeDistErr := by
  simp_rw [gaugeDistErr_def]
  exact iInf_congr fun m => ciInf_costErr_smul_of_le γ α (Nat.le_add_left 2 m)

/-- Relabelling a cochain along `e : V ≃ W` preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_relabel {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (e : V ≃ W) :
    (α.relabel e).gaugeDistErr = α.gaugeDistErr := by
  simp_rw [gaugeDistErr_def]
  exact iInf_congr fun m => α.ciInf_costErr_relabel e (m + 2)

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves `gaugeDistErr`. -/
@[simp] theorem gaugeDistErr_relabelComplete [Fintype V] [Fintype W]
    (α : Cochain (complete V) (Perm (Fin n))) (e : V ≃ W) :
    (α.relabelComplete e).gaugeDistErr = α.gaugeDistErr :=
  (Cochain.congr_complex (fun _ γ => γ.gaugeDistErr) (relabel_complete e).symm
    fun _ _ => by simp).trans (α.gaugeDistErr_relabel e)

/-- For every fixed gauge degree `m : ℕ`, `α.costErr` attains its infimum over `V → Perm (Fin m)`
on any two-complex `X` over an arbitrary vertex type `V`. -/
theorem exists_costErr_eq_ciInf {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) (m : ℕ) :
    ∃ β : V → Perm (Fin m), α.costErr β = ⨅ γ : V → Perm (Fin m), α.costErr γ := by
  simp_rw [α.costErr_eq_sum_edgePairs]
  exact X.edgePairs.exists_eq_ciInf_sum_distErr_mul_inv α m

/-- The cross-degree gauge distance `gaugeDistErr` is always attained by some gauge of some degree
`m + 2 ≥ 2`. -/
theorem exists_costErr_eq_gaugeDistErr {X : TwoComplex V}
    (α : Cochain X (Perm (Fin n))) :
    ∃ (m : ℕ) (β : V → Perm (Fin (m + 2))), α.costErr β = α.gaugeDistErr := by
  simp_rw [gaugeDistErr_def, α.costErr_eq_sum_edgePairs]
  exact X.edgePairs.exists_eq_ciInf₂_sum_distErr_mul_inv α

/-- Every non-coboundary cochain of degree `n` incurs `costErr` at least `1 / (n + 1)` against any
gauge of any degree `m`. -/
theorem one_div_add_one_le_costErr_of_not_isCoboundary {X : TwoComplex V}
    {α : Cochain X (Perm (Fin n))} (hncob : ¬ α.IsCoboundary)
    (β : V → Perm (Fin m)) :
    1 / ((n : ℝ) + 1) ≤ α.costErr β := by
  rw [α.costErr_eq_sum_edgePairs]
  exact X.edgePairs.one_div_add_one_le_sum_distErr_mul_inv_of_not_exists α β
    (mt (exists_eq_mul_inv_edgePairs_iff_isCoboundary α).mp hncob)

/-- Every non-coboundary cochain of degree `n` has `gaugeDistErr` at least `1 / (n + 1)`. -/
theorem one_div_add_one_le_gaugeDistErr_of_not_isCoboundary {X : TwoComplex V}
    {α : Cochain X (Perm (Fin n))} (hncob : ¬ α.IsCoboundary) :
    1 / ((n : ℝ) + 1) ≤ α.gaugeDistErr :=
  (α.le_gaugeDistErr_iff).mpr fun _ β =>
    one_div_add_one_le_costErr_of_not_isCoboundary hncob β

/-- For `2 ≤ n`, `α.gaugeDistErr = 0` if and only if `α` is an equal-degree coboundary. The
hypothesis `2 ≤ n` is sharp: for `n ≤ 1`, `(1 : Cochain X (Perm (Fin n)))` is a coboundary,
whereas on any complex with an edge every gauge of degree `m + 2 ≥ 2` has strictly positive
`costErr`. -/
theorem gaugeDistErr_eq_zero_iff_isCoboundary {X : TwoComplex V}
    {α : Cochain X (Perm (Fin n))} (hn : 2 ≤ n) :
    α.gaugeDistErr = 0 ↔ α.IsCoboundary := by
  simp_rw [gaugeDistErr_def, α.costErr_eq_sum_edgePairs]
  exact (X.edgePairs.ciInf₂_sum_distErr_mul_inv_eq_zero_iff α hn).trans
    (exists_eq_mul_inv_edgePairs_iff_isCoboundary α)

/-- For `2 ≤ n`, `0 < α.gaugeDistErr` if and only if `α` is not an equal-degree coboundary. -/
theorem gaugeDistErr_pos_iff_not_isCoboundary {X : TwoComplex V}
    {α : Cochain X (Perm (Fin n))} (hn : 2 ≤ n) :
    0 < α.gaugeDistErr ↔ ¬ α.IsCoboundary := by
  rw [← gaugeDistErr_eq_zero_iff_isCoboundary hn]
  exact α.gaugeDistErr_nonneg.lt_iff_ne'

@[simp] theorem gaugeDistErr_one {X : TwoComplex V}
    (hn : 2 ≤ n) : (1 : Cochain X (Perm (Fin n))).gaugeDistErr = 0 :=
  (gaugeDistErr_eq_zero_iff_isCoboundary hn).mpr isCoboundary_one

end CrossDegree

end Cochain

end TauCeti

end
