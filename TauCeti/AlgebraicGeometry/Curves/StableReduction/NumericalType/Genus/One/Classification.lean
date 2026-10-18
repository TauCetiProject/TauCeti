/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Classification
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineD
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineE6
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineE7
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineE8
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.FiveComponents
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.FiveFork
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.FourComponents
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.LongFork
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.LongPath
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Star
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.DoubleFork
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Classification of minimal numerical types of genus one

This file assembles the graph-shape and numerical classification of minimal numerical types of
arithmetic genus one ([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)).

Let `T` be a numerical type in which every component has self-intersection `aᵢᵢ = -2wᵢ`. Starting
from a longest chain `c 0 - c 1 - ⋯ - c (t - 1)` of components, there are three possibilities for
the set `A` of components in the chain:

* `A` is the whole component set. Any chord other than `c 0 - c (t - 1)` would bound a proper
  subchain whose ends meet, which `IsSelfIntersectionMinusTwoChain.intersection_eq_zero` excludes.
  If `c 0` and `c (t - 1)` meet and `t ≥ 3`, every vertex has at least two neighbours, so the
  topological genus is positive and the cycle classification applies; otherwise `c` is an
  exhaustive chordless path.
* `A` together with a single component `x` outside `A` is the whole component set. By maximality of
  `c`, `x` only meets the interior subchain `c 1, …, c (t - 2)`, which is at least two components
  shorter than `T`, so `x` meets a unique component `c r` (`0 < r` and `r + 1 < t`). When `r = 1`
  or `r = t - 2`, `(c, x)` is an exhaustive fork. Otherwise, after orienting `c` so that
  `2 ≤ r` and `2r + 1 ≤ t`, `r ≥ 3` gives the affine `E₇` configuration, `r = 2` with `t ≥ 8`
  gives the affine `E₈` configuration, and `r = 2` with `5 ≤ t ≤ 7` is excluded by the fibre
  relations because the proper five-component subfork and the proper chain fix the weights while the
  multiplicities have no positive kernel solution.
* There is a further component `y` outside `insert x A` meeting `insert x A`. If `y` meets `x`,
  maximality of `c` gives at least two chain components on each side of `c r`, producing the
  affine `E₆` configuration. If `y` meets `c r`, `c r` has four neighbours `c (r - 1)`,
  `c (r + 1)`, `x` and `y`, producing the four-leaf star (affine `D₄`). If `y` meets `c s` with
  `r ≠ s`, the subchain between `r - 1` and `s + 1` with leaves `x` and `y` is a double fork,
  which `IsSelfIntersectionMinusTwoFork.not_oppositeFork` forces to exhaust `T`, producing the
  affine `D` configuration.

Combining this structural classification with the per-shape classifications of paths, forks, stars,
cycles, and affine `D` and `E` diagrams yields the full list of minimal numerical types of genus
one, together with uniform divisibility and ratio bounds on their multiplicities and weights.

## Main results

* `TauCeti.NumericalType.exists_chain_or_fork_or_star_or_affine_of_topologicalGenus_eq_zero`:
  structural classification of tree-shaped numerical types whose components have self-intersection
  `-2w`.
* `TauCeti.NumericalType.topologicalGenus_pos_or_exists_chain_or_fork_or_star_or_affine`:
  the same without the tree assumption, including the cycle case `0 < T.topologicalGenus`.
* `TauCeti.NumericalType.IsGenusOneMinimalShape` and
  `TauCeti.NumericalType.IsMinimal.isGenusOneMinimalShape`: the complete classification of minimal
  numerical types of arithmetic genus one ([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)).
* `TauCeti.NumericalType.IsMinimal.exists_multiplicity_dvd_and_le_six_mul` and
  `TauCeti.NumericalType.IsMinimal.exists_weight_dvd_and_le_four_mul`: in a minimal numerical type
  of genus one, the minimum multiplicity divides every multiplicity with quotient at most `6`, and
  the minimum weight divides every weight with quotient at most `4`.
-/

public section

namespace TauCeti.NumericalType

open Finset _root_.Matrix

universe u

variable {T : NumericalType.{u}}

/-! ### Exhaustive chains -/

namespace IsSelfIntersectionMinusTwoChain

variable {t : ℕ} {c : ℕ → T.Component}

/-- If a chain of at least three components exhausts a numerical type and its two endpoints meet,
then every component has at least two neighbours in the intersection graph, so the topological
genus is positive. -/
lemma topologicalGenus_pos_of_card_eq (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : Fintype.card T.Component = t) (ht : 2 < t)
    (hends : 0 < T.intersection (c 0) (c (t - 1))) :
    0 < T.topologicalGenus := by
  classical
  have hu : (range t).image c = (univ : Finset T.Component) :=
    eq_univ_of_card _ (by rw [hc.card_image_range, hcard])
  have htwo (v : T.Component) : 2 ≤ T.intersectionGraph.degree v := by
    have hv : v ∈ (range t).image c := hu ▸ mem_univ v
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
    replace hi := mem_range.mp hi
    suffices ∃ j k, j ≠ k ∧ T.Adj (c i) j ∧ T.Adj (c i) k by
      obtain ⟨j, k, hjk, hj, hk⟩ := this
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      have hsub : ({j, k} : Finset T.Component) ⊆ T.intersectionGraph.neighborFinset (c i) := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rw [SimpleGraph.mem_neighborFinset, T.intersectionGraph_adj_iff]
        rcases hz with rfl | rfl <;> assumption
      exact (card_pair hjk).symm.trans_le (card_le_card hsub)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨c 1, c (t - 1), hc.ne (by omega) (by omega) (by omega),
        T.adj_iff.mpr ⟨hc.ne (by omega) (by omega) (by omega),
          hc.intersection_succ_pos 0 (by omega)⟩,
        T.adj_iff.mpr ⟨hc.ne (by omega) (by omega) (by omega), hends⟩⟩
    by_cases hilast : i = t - 1
    · subst i
      refine ⟨c 0, c (t - 2), hc.ne (by omega) (by omega) (by omega),
        T.adj_iff.mpr ⟨hc.ne (by omega) (by omega) (by omega),
          by rwa [T.intersection_comm]⟩,
        T.adj_iff.mpr ⟨hc.ne (by omega) (by omega) (by omega), ?_⟩⟩
      rw [T.intersection_comm]
      exact hc.intersection_pos (by omega) (by omega)
    · refine ⟨c (i - 1), c (i + 1), hc.ne (by omega) (by omega) (by omega),
        T.adj_iff.mpr ⟨hc.ne (by omega) (by omega) (by omega), ?_⟩,
        T.adj_iff.mpr ⟨hc.ne (by omega) (by omega) (by omega),
          hc.intersection_succ_pos i (by omega)⟩⟩
      rw [T.intersection_comm]
      exact hc.intersection_pos (by omega) (by omega)
  have hdeg : 2 * Fintype.card T.Component ≤ ∑ v, T.intersectionGraph.degree v := by
    simpa [mul_comm 2] using sum_le_sum fun v (_ : v ∈ univ) ↦ htwo v
  have hsum := T.intersectionGraph.sum_degrees_eq_twice_card_edges
  have hedge : #T.intersectionGraph.edgeFinset = T.intersectionGraph.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [topologicalGenus_def, Nat.card_eq_fintype_card]
  omega

/-! ### Exhibiting star and affine `E` configurations -/

/-- A chain component `c r` (`0 < r` and `r + 1 < t`) meeting two distinct components `x` and `y`
outside the chain forms a four-leaf star with leaves `c (r - 1)`, `c (r + 1)`, `x` and `y`. -/
private lemma exists_fourLeafStar (hc : T.IsSelfIntersectionMinusTwoChain t c) {r : ℕ}
    (hr0 : 0 < r) (hrt : r + 1 < t) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx : 0 < T.intersection (c r) x) (hy : 0 < T.intersection (c r) y) :
    ∃ c₀ : T.Component, ∃ l : Fin 4 → T.Component,
      Function.Injective l ∧ ∀ i, T.Adj c₀ (l i) := by
  let l : Fin 4 → T.Component := ![c (r - 1), c (r + 1), x, y]
  refine ⟨c r, l, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [l] at hij ⊢
    all_goals first
      | exact absurd hij (hc.ne (by omega) (by omega) (by omega))
      | exact absurd hij (hx_ne _ (by omega)).symm
      | exact absurd hij (hx_ne _ (by omega))
      | exact absurd hij (hy_ne _ (by omega)).symm
      | exact absurd hij (hy_ne _ (by omega))
      | exact absurd hij hxy
      | exact absurd hij hxy.symm
  · intro i
    fin_cases i <;> simp only [l, T.adj_iff]
    · exact ⟨hc.ne (by omega) (by omega) (by omega),
        by rw [T.intersection_comm]; exact hc.intersection_pos (by omega) (by omega)⟩
    · exact ⟨hc.ne (by omega) (by omega) (by omega), hc.intersection_succ_pos r hrt⟩
    · exact ⟨(hx_ne r (by omega)).symm, hx⟩
    · exact ⟨(hy_ne r (by omega)).symm, hy⟩

/-- A chain component `c r` (`2 ≤ r` and `r + 3 ≤ t`) meeting `x` outside the chain, which in turn
meets `y` outside the chain, produces the seven-component affine `E₆` configuration. -/
private lemma exists_affineE6 (hc : T.IsSelfIntersectionMinusTwoChain t c) {r : ℕ}
    (hr : 2 ≤ r) (hrt : r + 3 ≤ t) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx : 0 < T.intersection (c r) x) (hxy_pos : 0 < T.intersection x y) :
    ∃ l : Fin 7 → T.Component, Function.Injective l ∧
      ∀ i j, AffineDynkinType.E6.graph.Adj i j → T.Adj (l i) (l j) := by
  let l : Fin 7 → T.Component := ![c r, c (r - 1), c (r - 2), c (r + 1), c (r + 2), x, y]
  have hl : Function.Injective l := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [l] at hij ⊢
    all_goals first
      | exact absurd hij (hc.ne (by omega) (by omega) (by omega))
      | exact absurd hij (hx_ne _ (by omega)).symm
      | exact absurd hij (hx_ne _ (by omega))
      | exact absurd hij (hy_ne _ (by omega)).symm
      | exact absurd hij (hy_ne _ (by omega))
      | exact absurd hij hxy
      | exact absurd hij hxy.symm
  refine ⟨l, hl, fun i j hadj ↦ T.adj_iff.mpr ⟨hl.ne hadj.ne, ?_⟩⟩
  have hlt (u v : Fin 7) (huv : u < v) (h : AffineDynkinType.E6.graph.Adj u v) :
      0 < T.intersection (l u) (l v) := by
    have hG := (AffineDynkinType.graph_E6_adj u v).mp h
    rw [min_eq_left (Fin.le_def.mp huv.le), max_eq_right (Fin.le_def.mp huv.le)] at hG
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hG
    rcases hG with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
      [obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 1 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 1 ∧ v = 2 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 3 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 3 ∧ v = 4 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 5 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 5 ∧ v = 6 := ⟨Fin.ext hu, Fin.ext hv⟩]
    all_goals first
      | exact hx
      | exact hxy_pos
      | exact hc.intersection_pos (by omega) (by omega)
      | (rw [T.intersection_comm]; exact hc.intersection_pos (by omega) (by omega))
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hlt i j hij hadj
  · exact (AffineDynkinType.E6.graph.loopless.irrefl i hadj).elim
  · rw [T.intersection_comm]
    exact hlt j i hji hadj.symm

/-- A chain component `c r` (`3 ≤ r` and `r + 4 ≤ t`) meeting `x` outside the chain produces the
eight-component affine `E₇` configuration. -/
private lemma exists_affineE7 (hc : T.IsSelfIntersectionMinusTwoChain t c) {r : ℕ}
    (hr : 3 ≤ r) (hrt : r + 4 ≤ t) {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i)
    (hx : 0 < T.intersection (c r) x) :
    ∃ l : Fin 8 → T.Component, Function.Injective l ∧
      ∀ i j, AffineDynkinType.E7.graph.Adj i j → 0 < T.intersection (l i) (l j) := by
  let l : Fin 8 → T.Component :=
    ![c r, x, c (r - 1), c (r - 2), c (r - 3), c (r + 1), c (r + 2), c (r + 3)]
  have hl : Function.Injective l := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [l] at hij ⊢
    all_goals first
      | exact absurd hij (hc.ne (by omega) (by omega) (by omega))
      | exact absurd hij (hx_ne _ (by omega)).symm
      | exact absurd hij (hx_ne _ (by omega))
  refine ⟨l, hl, fun i j hadj ↦ ?_⟩
  have hlt (u v : Fin 8) (huv : u < v) (h : AffineDynkinType.E7.graph.Adj u v) :
      0 < T.intersection (l u) (l v) := by
    have hG := (AffineDynkinType.graph_E7_adj u v).mp h
    rw [min_eq_left (Fin.le_def.mp huv.le), max_eq_right (Fin.le_def.mp huv.le)] at hG
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hG
    rcases hG with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ |
        ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
      [obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 1 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 2 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 2 ∧ v = 3 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 3 ∧ v = 4 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 5 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 5 ∧ v = 6 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 6 ∧ v = 7 := ⟨Fin.ext hu, Fin.ext hv⟩]
    all_goals first
      | exact hx
      | exact hc.intersection_pos (by omega) (by omega)
      | (rw [T.intersection_comm]; exact hc.intersection_pos (by omega) (by omega))
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hlt i j hij hadj
  · exact (AffineDynkinType.E7.graph.loopless.irrefl i hadj).elim
  · rw [T.intersection_comm]
    exact hlt j i hji hadj.symm

/-- A chain `c 0, …, c (t - 1)` of length `8 ≤ t` with a leaf `x` outside the chain meeting `c 2`
produces the nine-component affine `E₈` configuration. -/
private lemma exists_affineE8 (hc : T.IsSelfIntersectionMinusTwoChain t c) (ht : 8 ≤ t)
    {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i) (hx : 0 < T.intersection (c 2) x) :
    ∃ l : Fin 9 → T.Component, Function.Injective l ∧
      ∀ i j, AffineDynkinType.E8.graph.Adj i j → 0 < T.intersection (l i) (l j) := by
  let l : Fin 9 → T.Component := ![c 2, x, c 1, c 0, c 3, c 4, c 5, c 6, c 7]
  have hl : Function.Injective l := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [l] at hij ⊢
    all_goals first
      | exact absurd hij (hc.ne (by omega) (by omega) (by omega))
      | exact absurd hij (hx_ne _ (by omega)).symm
      | exact absurd hij (hx_ne _ (by omega))
  refine ⟨l, hl, fun i j hadj ↦ ?_⟩
  have hlt (u v : Fin 9) (huv : u < v) (h : AffineDynkinType.E8.graph.Adj u v) :
      0 < T.intersection (l u) (l v) := by
    have hG := (AffineDynkinType.graph_E8_adj u v).mp h
    rw [min_eq_left (Fin.le_def.mp huv.le), max_eq_right (Fin.le_def.mp huv.le)] at hG
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hG
    rcases hG with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ |
        ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
      [obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 1 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 2 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 2 ∧ v = 3 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 0 ∧ v = 4 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 4 ∧ v = 5 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 5 ∧ v = 6 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 6 ∧ v = 7 := ⟨Fin.ext hu, Fin.ext hv⟩;
        obtain ⟨rfl, rfl⟩ : u = 7 ∧ v = 8 := ⟨Fin.ext hu, Fin.ext hv⟩]
    all_goals first
      | exact hx
      | exact hc.intersection_pos (by omega) (by omega)
      | (rw [T.intersection_comm]; exact hc.intersection_pos (by omega) (by omega))
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hlt i j hij hadj
  · exact (AffineDynkinType.E8.graph.loopless.irrefl i hadj).elim
  · rw [T.intersection_comm]
    exact hlt j i hji hadj.symm

/-- Two distinct leaves `x` and `y` outside a chain `c` meeting interior chain components `c r`
and `c s` (`0 < r ≤ s` and `s + 1 < t`) either sit at the same component (forming a four-leaf
star) or sit at `c 1` and `c (t - 2)` of a chain of length `t ≥ 4` with `Fintype.card = t + 2`
(forming an exhaustive double fork). -/
private lemma exists_fourLeafStar_or_doubleFork (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t + 2 ≤ Fintype.card T.Component) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ)))
    (hy_self : T.intersection y y = -(2 * (T.weight y : ℤ))) {r s : ℕ} (hr0 : 0 < r)
    (hrs : r ≤ s) (hst : s + 1 < t) (hx : 0 < T.intersection (c r) x)
    (hy : 0 < T.intersection (c s) y) :
    (∃ c₀ : T.Component, ∃ l : Fin 4 → T.Component,
        Function.Injective l ∧ ∀ i, T.Adj c₀ (l i)) ∨
      ∃ t' c' left right, 4 ≤ t' ∧ Fintype.card T.Component = t' + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t' c' right ∧
        T.IsSelfIntersectionMinusTwoFork t' (fun i ↦ c' (t' - 1 - i)) left := by
  rcases hrs.eq_or_lt with rfl | hrs
  · exact .inl (hc.exists_fourLeafStar hr0 hst hxy hx_ne hy_ne hx hy)
  · have hd := hc.shift (r := r - 1) (s := s - r + 3) (by omega)
    have hrf : T.IsSelfIntersectionMinusTwoFork (s - r + 3) (fun k ↦ c (r - 1 + k)) y :=
      ⟨hd, by omega, fun i hi ↦ hy_ne _ (by omega), hy_self,
        by simpa [show r - 1 + (s - r + 1) = s by omega] using hy⟩
    have hlf : T.IsSelfIntersectionMinusTwoFork (s - r + 3)
        (fun i ↦ c (r - 1 + (s - r + 3 - 1 - i))) x :=
      ⟨hd.reverse, by omega, fun i hi ↦ hx_ne _ (by omega), hx_self,
        by simpa [show r - 1 + 1 = r by omega] using hx⟩
    have hnot : ¬ (s - r + 3 + 2 < Fintype.card T.Component) :=
      hrf.not_oppositeFork hlf (by omega)
    exact .inr ⟨s - r + 3, fun k ↦ c (r - 1 + k), x, y, by omega, by omega, hrf, hlf⟩

/-- An exhaustive configuration consisting of a chain `c` and a single leaf `x` at `c r`
(`2 ≤ r` and `2 * r + 1 ≤ t`) is either an affine `E₇` or an affine `E₈` configuration. -/
private lemma exists_affineE7_or_affineE8_of_card_eq_succ
    (hc : T.IsSelfIntersectionMinusTwoChain t c) (hcard : Fintype.card T.Component = t + 1)
    {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {r : ℕ} (hr : 2 ≤ r)
    (hrt : 2 * r + 1 ≤ t) (hx : 0 < T.intersection (c r) x)
    (hx_zero : ∀ i < t, i ≠ r → T.intersection (c i) x = 0) :
    (∃ l : Fin 8 → T.Component, Function.Injective l ∧
        ∀ i j, AffineDynkinType.E7.graph.Adj i j → 0 < T.intersection (l i) (l j)) ∨
      ∃ l : Fin 9 → T.Component, Function.Injective l ∧
        ∀ i j, AffineDynkinType.E8.graph.Adj i j → 0 < T.intersection (l i) (l j) := by
  by_cases hr3 : 3 ≤ r
  · exact .inl (hc.exists_affineE7 hr3 (by omega) hx_ne hx)
  obtain rfl : r = 2 := by omega
  by_cases ht8 : 8 ≤ t
  · exact .inr (hc.exists_affineE8 ht8 hx_ne hx)
  · exact (hc.not_card_eq_succ_of_branch_two (by omega) (by omega)
      hx_ne hx_self hx hx_zero hcard).elim

end IsSelfIntersectionMinusTwoChain

/-! ### Structural classification of numerical types with self-intersections `-2w` -/

/-- **Structural classification of numerical types with self-intersections `-2w`.**
If every component of a numerical type `T` has self-intersection `aᵢᵢ = -2wᵢ`, then one of the
following holds:

* `0 < T.topologicalGenus` (the intersection graph contains a cycle, so by
  `TauCeti.NumericalType.weight_eq_of_topologicalGenus_pos` and its companions it is a single cycle
  with constant weights and multiplicities);
* `T` is exhausted by a chordless chain of at least two components;
* `T` is exhausted by a fork of chain length at least three;
* `T` contains (and hence, by `TauCeti.NumericalType.exists_equiv_fourLeafStar`, is exhausted by) a
  four-leaf star (affine `D₄`);
* `T` is exhausted by a double fork of chain length at least four (affine `Dₙ`, `n ≥ 5`);
* `T` contains (and hence, by `TauCeti.NumericalType.exists_equiv_affineE6`,
  `exists_equiv_affineE7`, or `exists_equiv_affineE8`, is exhausted by) an affine `E₆`, `E₇`, or
  `E₈` configuration. -/
theorem topologicalGenus_pos_or_exists_chain_or_fork_or_star_or_affine
    (hself : ∀ i, T.intersection i i = -(2 * (T.weight i : ℤ))) :
    0 < T.topologicalGenus ∨
      (∃ t c, 2 ≤ t ∧ Fintype.card T.Component = t ∧ T.IsSelfIntersectionMinusTwoChain t c ∧
        ∀ i < t, ∀ j < t, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∨
      (∃ t c b, Fintype.card T.Component = t + 1 ∧ T.IsSelfIntersectionMinusTwoFork t c b) ∨
      (∃ c₀ : T.Component, ∃ l : Fin 4 → T.Component,
        Function.Injective l ∧ ∀ i, T.Adj c₀ (l i)) ∨
      (∃ t c left right, 4 ≤ t ∧ Fintype.card T.Component = t + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t c right ∧
        T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left) ∨
      (∃ l : Fin 7 → T.Component, Function.Injective l ∧
        ∀ i j, AffineDynkinType.E6.graph.Adj i j → T.Adj (l i) (l j)) ∨
      (∃ l : Fin 8 → T.Component, Function.Injective l ∧
        ∀ i j, AffineDynkinType.E7.graph.Adj i j → 0 < T.intersection (l i) (l j)) ∨
      (∃ l : Fin 9 → T.Component, Function.Injective l ∧
        ∀ i j, AffineDynkinType.E8.graph.Adj i j → 0 < T.intersection (l i) (l j)) := by
  classical
  have hcard_gt_one := T.one_lt_card_of_intersection_self_eq hself
  obtain ⟨t, c, hc, hcU, hmax⟩ := T.exists_chain_forall_le univ
  set A := (range t).image c with hA_def
  have mem_A {x : T.Component} : x ∈ A ↔ ∃ i < t, c i = x := by simp [hA_def]
  have hAcard : #A = t := hc.card_image_range
  have ht : 0 < t := by
    obtain ⟨x⟩ := T.componentNonempty
    have := hmax 1 (fun _ ↦ x) ⟨by omega, fun _ _ ↦ hself x, by omega⟩ fun _ _ ↦ mem_univ x
    omega
  by_cases hAU : A = univ
  · -- The longest chain exhausts `T`.
    have hcard : Fintype.card T.Component = t := by
      rw [← card_univ, ← hAU, hAcard]
    by_cases hends : 2 < t ∧ 0 < T.intersection (c 0) (c (t - 1))
    · exact .inl (hc.topologicalGenus_pos_of_card_eq hcard hends.1 hends.2)
    · refine .inr (.inl ⟨t, c, by omega, hcard, hc, hc.intersection_eq_zero_of_card_eq hcard ?_⟩)
      intro ht2
      have hle : T.intersection (c 0) (c (t - 1)) ≤ 0 := not_lt.mp fun h ↦ hends ⟨ht2, h⟩
      exact le_antisymm hle (T.offDiagonal_nonneg _ _ (hc.ne (by omega) (by omega) (by omega)))
  -- Some component `x` outside `A` meets `c r`.
  obtain ⟨b₀, hmem, x, hxA, hpos⟩ :=
    T.exists_mem_notMem_adj A ⟨c 0, mem_A.mpr ⟨0, ht, rfl⟩⟩ (coe_eq_univ.not.mpr hAU)
  replace hpos := (T.adj_iff.mp hpos).2
  obtain ⟨r, hr, rfl⟩ := mem_A.mp hmem
  have hx_ne : ∀ i < t, x ≠ c i := fun i hi h ↦ hxA (mem_A.mpr ⟨i, hi, h.symm⟩)
  obtain ⟨hr0, hrt⟩ := hc.pos_and_lt_of_intersection_pos hcU hmax (mem_univ x) hx_ne (hself x)
    hr hpos
  have hx_zero : ∀ i < t, i ≠ r → T.intersection (c i) x = 0 :=
    fun i hi hir ↦ hc.intersection_eq_zero_of_ne_of_intersection_pos hcU hmax (mem_univ x)
      hx_ne (hself x) hr hpos hi hir
  by_cases hBU : insert x A = univ
  · -- `c` and `x` exhaust `T`.
    have hcard : Fintype.card T.Component = t + 1 := by
      rw [← card_univ, ← hBU, card_insert_of_notMem hxA, hAcard]
    right; right
    by_cases hfork_right : r = t - 2
    · exact .inl ⟨t, c, x, hcard, hc, by omega, hx_ne, hself x, hfork_right ▸ hpos⟩
    by_cases hfork_left : r = 1
    · refine .inl ⟨t, fun i ↦ c (t - 1 - i), x, hcard, hc.reverse, by omega,
        fun i hi ↦ hx_ne _ (by omega), hself x, ?_⟩
      simpa [show t - 1 - (t - 2) = r by omega] using hpos
    right; right; right; right
    by_cases hdir : 2 * r + 1 ≤ t
    · exact hc.exists_affineE7_or_affineE8_of_card_eq_succ hcard hx_ne (hself x)
        (by omega) hdir hpos hx_zero
    · have hpos' : 0 < T.intersection (c (t - 1 - (t - 1 - r))) x := by
        simpa [show t - 1 - (t - 1 - r) = r by omega] using hpos
      exact hc.reverse.exists_affineE7_or_affineE8_of_card_eq_succ hcard
        (fun i hi ↦ hx_ne _ (by omega)) (hself x) (by omega) (by omega) hpos'
        fun i hi hir ↦ hx_zero _ (by omega) (by omega)
  · -- Some component `y` outside `insert x A` meets `insert x A`.
    obtain ⟨b, hb, y, hyB, hby⟩ :=
      T.exists_mem_notMem_adj ↑(insert x A) (insert_nonempty x A) (coe_eq_univ.not.mpr hBU)
    replace hby := (T.adj_iff.mp hby).2
    have hyx : y ≠ x := fun h ↦ hyB (h ▸ mem_insert_self _ _)
    have hyA : y ∉ A := fun h ↦ hyB (mem_insert_of_mem h)
    have hy_ne : ∀ i < t, y ≠ c i := fun i hi h ↦ hyA (mem_A.mpr ⟨i, hi, h.symm⟩)
    have hcard₂ : t + 2 ≤ Fintype.card T.Component := by
      have := card_le_card (subset_univ (insert y (insert x A)))
      rw [card_univ, card_insert_of_notMem hyB, card_insert_of_notMem hxA, hAcard] at this
      omega
    rcases mem_insert.mp hb with hbx | hbA
    · -- `y` meets `x`, producing the affine `E₆` configuration.
      subst b
      have hr2 := hc.two_le_of_intersection_pos hcU hmax (mem_univ x) hx_ne (hself x)
        (mem_univ y) hy_ne (hself y) hyx hr hpos hby
      have hrt2 := hc.reverse.two_le_of_intersection_pos (fun i hi ↦ hcU _ (by omega)) hmax
        (mem_univ x) (fun i hi ↦ hx_ne _ (by omega)) (hself x) (mem_univ y)
        (fun i hi ↦ hy_ne _ (by omega)) (hself y) hyx (r := t - 1 - r) (by omega)
        (by simpa [show t - 1 - (t - 1 - r) = r by omega] using hpos) hby
      exact .inr (.inr (.inr (.inr (.inr (.inl
        (hc.exists_affineE6 hr2 (by omega) hyx.symm hx_ne hy_ne hpos hby))))))
    · -- `y` meets `c s`, producing either a four-leaf star or an exhaustive double fork.
      obtain ⟨s, hs, rfl⟩ := mem_A.mp hbA
      obtain ⟨hs0, hst⟩ := hc.pos_and_lt_of_intersection_pos hcU hmax (mem_univ y) hy_ne
        (hself y) hs hby
      right; right; right
      rcases le_total r s with hrs | hsr
      · rcases hc.exists_fourLeafStar_or_doubleFork hcard₂ hyx.symm hx_ne hy_ne (hself x)
            (hself y) hr0 hrs hst hpos hby with hstar | hdouble
        · exact .inl hstar
        · exact .inr (.inl hdouble)
      · rcases hc.exists_fourLeafStar_or_doubleFork hcard₂ hyx hy_ne hx_ne (hself y)
            (hself x) hs0 hsr hrt hby hpos with hstar | hdouble
        · exact .inl hstar
        · exact .inr (.inl hdouble)

/-- **Structural classification of tree-shaped numerical types with self-intersections `-2w`.**
If every component of `T` has self-intersection `-2w` and `T.topologicalGenus = 0` (so the
intersection graph is a tree), then `T` is a chordless path, a fork, a four-leaf star, a double
fork, or an affine `E₆`, `E₇`, or `E₈` configuration. -/
theorem exists_chain_or_fork_or_star_or_affine_of_topologicalGenus_eq_zero
    (hself : ∀ i, T.intersection i i = -(2 * (T.weight i : ℤ)))
    (htop : T.topologicalGenus = 0) :
    (∃ t c, 2 ≤ t ∧ Fintype.card T.Component = t ∧ T.IsSelfIntersectionMinusTwoChain t c ∧
        ∀ i < t, ∀ j < t, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∨
      (∃ t c b, Fintype.card T.Component = t + 1 ∧ T.IsSelfIntersectionMinusTwoFork t c b) ∨
      (∃ c₀ : T.Component, ∃ l : Fin 4 → T.Component,
        Function.Injective l ∧ ∀ i, T.Adj c₀ (l i)) ∨
      (∃ t c left right, 4 ≤ t ∧ Fintype.card T.Component = t + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t c right ∧
        T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left) ∨
      (∃ l : Fin 7 → T.Component, Function.Injective l ∧
        ∀ i j, AffineDynkinType.E6.graph.Adj i j → T.Adj (l i) (l j)) ∨
      (∃ l : Fin 8 → T.Component, Function.Injective l ∧
        ∀ i j, AffineDynkinType.E7.graph.Adj i j → 0 < T.intersection (l i) (l j)) ∨
      (∃ l : Fin 9 → T.Component, Function.Injective l ∧
        ∀ i j, AffineDynkinType.E8.graph.Adj i j → 0 < T.intersection (l i) (l j)) :=
  (T.topologicalGenus_pos_or_exists_chain_or_fork_or_star_or_affine hself).resolve_left
    (by omega)

/-! ### Complete classification of minimal numerical types of genus one -/

/-- The twelve shape families into which the 34 minimal numerical types of arithmetic genus one
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)) organize:

* Case (1): a single component of component genus one;
* Cases (2)--(3): two rational components of shape `IsGenusOnePairShape`;
* Cases (4), (10), (16), (25): a cycle of rational components (`0 < T.topologicalGenus`) with
  constant weights and multiplicities, each meeting two others with intersection number equal to
  the common weight;
* Cases (5)--(9): three rational components forming a chain of shape `IsGenusOneChainShape`;
* Cases (11)--(13): four rational components forming a path of shape `IsGenusOneFourPathShape`;
* Cases (14)--(15): four rational components forming a three-leaf star of shape
  `IsGenusOneFourStarShape`;
* Cases (17)--(21): five rational components forming a path of shape `IsGenusOneFivePathShape`;
* Case (22): five rational components forming a four-leaf star (affine `D₄`);
* Cases (23)--(24): five rational components forming a fork;
* Cases (26)--(28): `n ≥ 6` rational components forming a path of shape `IsGenusOneLongPathShape`;
* Cases (29)--(30): `t + 1 ≥ 6` rational components forming a fork of shape
  `IsGenusOneLongForkShape`;
* Case (31): `t + 2 ≥ 6` rational components forming a double fork of shape
  `IsGenusOneAffineDShape`;
* Cases (32)--(34): seven, eight, or nine rational components forming an affine `E₆`, `E₇`, or
  `E₈` configuration. -/
@[expose]
def IsGenusOneMinimalShape (T : NumericalType.{u}) : Prop :=
  (Fintype.card T.Component = 1 ∧ ∀ i, T.genus i = 1 ∧ T.intersection i i = 0) ∨
  ((∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ))) ∧
    ((0 < T.topologicalGenus ∧
        (∀ i j, T.weight i = T.weight j ∧ T.multiplicity i = T.multiplicity j) ∧
        (∀ i, (T.intersectionGraph.neighborSet i).ncard = 2) ∧
        ∀ i j, T.Adj i j → T.intersection i j = T.weight i) ∨
      (Fintype.card T.Component = 2 ∧ ∃ x y, x ≠ y ∧ T.IsGenusOnePairShape x y) ∨
      (Fintype.card T.Component = 3 ∧
        ∃ x j z, x ≠ j ∧ x ≠ z ∧ j ≠ z ∧ T.intersection x z = 0 ∧
          T.IsGenusOneChainShape x j z) ∨
      (Fintype.card T.Component = 4 ∧ ∃ c, T.IsSelfIntersectionMinusTwoChain 4 c ∧
        (∀ i < 4, ∀ j < 4, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneFourPathShape (c 0) (c 1) (c 2) (c 3)) ∨
      (Fintype.card T.Component = 4 ∧ ∃ c₀ x y z,
        ({c₀, x, y, z} : Finset T.Component) = univ ∧
        T.intersection x y = 0 ∧ T.intersection x z = 0 ∧ T.intersection y z = 0 ∧
        T.IsGenusOneFourStarShape c₀ x y z) ∨
      (Fintype.card T.Component = 5 ∧ ∃ c, T.IsSelfIntersectionMinusTwoChain 5 c ∧
        (∀ i < 5, ∀ j < 5, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneFivePathShape (c 0) (c 1) (c 2) (c 3) (c 4)) ∨
      (∃ e : Option (Fin 4) ≃ T.Component,
        (∀ v, T.weight (e v) = T.weight (e none)) ∧
        (∀ v, (T.multiplicity (e v) : ℤ) =
          if v = none then 2 * (T.multiplicity (e (some 0)) : ℤ)
          else T.multiplicity (e (some 0))) ∧
        (∀ v w, T.intersection (e v) (e w) =
          if v = w then -(2 * (T.weight (e none) : ℤ))
          else if v = none ∨ w = none then T.weight (e none) else 0)) ∨
      (∃ e : Fin 5 ≃ T.Component, ∃ w m : ℕ+,
        ((∀ i, (T.weight (e i) : ℤ) = ![2 * (w : ℤ), w, w, w, w] i) ∧
          (∀ i, (T.multiplicity (e i) : ℤ) = ![(m : ℤ), 2 * m, 2 * m, m, m] i) ∧
          (∀ i j, T.intersection (e i) (e j) =
            !![-4 * (w : ℤ), 2 * w, 0, 0, 0;
               2 * w, -2 * w, w, 0, 0;
               0, w, -2 * w, w, w;
               0, 0, w, -2 * w, 0;
               0, 0, w, 0, -2 * w] i j)) ∨
        ((∀ i, (T.weight (e i) : ℤ) = ![(w : ℤ), 2 * w, 2 * w, 2 * w, 2 * w] i) ∧
          (∀ i, (T.multiplicity (e i) : ℤ) = ![2 * (m : ℤ), 2 * m, 2 * m, m, m] i) ∧
          (∀ i j, T.intersection (e i) (e j) =
            !![-2 * (w : ℤ), 2 * w, 0, 0, 0;
               2 * w, -4 * w, 2 * w, 0, 0;
               0, 2 * w, -4 * w, 2 * w, 2 * w;
               0, 0, 2 * w, -4 * w, 0;
               0, 0, 2 * w, 0, -4 * w] i j))) ∨
      (∃ n c, 6 ≤ n ∧ Fintype.card T.Component = n ∧ T.IsSelfIntersectionMinusTwoChain n c ∧
        (∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneLongPathShape n c) ∨
      (∃ t c b, 5 ≤ t ∧ Fintype.card T.Component = t + 1 ∧
        T.IsSelfIntersectionMinusTwoFork t c b ∧ T.IsGenusOneLongForkShape t c b) ∨
      (∃ t c left right, 4 ≤ t ∧ Fintype.card T.Component = t + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t c right ∧
        T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left ∧
        T.IsGenusOneAffineDShape t c left right) ∨
      (∃ e : Fin 7 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          (T.multiplicity (e 2) : ℤ) * AffineDynkinType.E6.marks i) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E6.cartanMatrix i j)) ∨
      (∃ e : Fin 8 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          AffineDynkinType.E7.marks i * T.multiplicity (e 4)) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j)) ∨
      (∃ e : Fin 9 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          AffineDynkinType.E8.marks i * T.multiplicity (e 8)) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j))))

/-- Nonconsecutive vanishing intersections are preserved by reversing a chain. -/
private lemma zero_of_reverse {n : ℕ} {c : ℕ → T.Component}
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) :
    ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c (n - 1 - i)) (c (n - 1 - j)) = 0 := by
  intro i hi j hj hij h1 h2
  exact hzero (n - 1 - i) (by omega) (n - 1 - j) (by omega) (by omega) (by omega) (by omega)

/-- **Classification of minimal numerical types of genus one**
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)). Every minimal numerical type
of arithmetic genus one belongs to one of the shape families of
`TauCeti.NumericalType.IsGenusOneMinimalShape`. -/
theorem IsMinimal.isGenusOneMinimalShape (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) :
    T.IsGenusOneMinimalShape := by
  classical
  by_cases hcard1 : Fintype.card T.Component = 1
  · exact .inl ⟨hcard1, fun i ↦ ⟨(T.arithmeticGenus_eq_one_iff_of_card_eq_one hcard1 i).mp hg,
      T.intersection_eq_zero_of_card_eq_one hcard1 i i⟩⟩
  have h1lt : 1 < Fintype.card T.Component := by
    have := Fintype.card_pos (α := T.Component)
    omega
  have hminusTwo := (T.isMinimal_and_arithmeticGenus_eq_one_iff h1lt).mp ⟨hT, hg⟩
  have hgen (i : T.Component) : T.genus i = 0 := (T.isMinusTwoIndex_iff.mp (hminusTwo i)).1
  have hself (i : T.Component) : T.intersection i i = -(2 * (T.weight i : ℤ)) :=
    (T.isMinusTwoIndex_iff.mp (hminusTwo i)).2
  have hself_ge (i : T.Component) : -(2 * (T.weight i : ℤ)) ≤ T.intersection i i := (hself i).ge
  refine .inr ⟨fun i ↦ ⟨hgen i, hself i⟩, ?_⟩
  rcases T.topologicalGenus_pos_or_exists_chain_or_fork_or_star_or_affine hself with
    htop | ⟨t, c, ht2, hcard, hc, hzero⟩ | ⟨t, c, b, hcard, hf⟩ |
      ⟨c₀, l, hl, hadj⟩ | ⟨t, c, left, right, ht4, hcard, hr, hl⟩ |
      ⟨l, hl, hadj⟩ | ⟨l, hl, hadj⟩ | ⟨l, hl, hadj⟩
  · -- Cycle case.
    exact .inl ⟨htop,
      fun i j ↦ ⟨T.weight_eq_of_topologicalGenus_pos hself_ge htop i j,
        T.multiplicity_eq_of_topologicalGenus_pos hself_ge htop i j⟩,
      T.ncard_neighborSet_eq_two_of_topologicalGenus_pos hself_ge htop,
      fun i j hij ↦ T.intersection_eq_weight_of_topologicalGenus_pos hself_ge htop hij⟩
  · -- Path cases (`t = 2`, `3`, `4`, `5`, or `t ≥ 6`).
    rcases lt_or_ge t 6 with ht6 | ht6
    · interval_cases t
      · obtain ⟨x, y, hxy, hshape⟩ :=
          T.exists_weight_multiplicity_intersection_eq_of_card_eq_two hcard
            (hc.ne (i := 0) (j := 1) (by omega) (by omega) (by omega)) (hself _) (hself _)
        refine .inr (.inl ⟨hcard, x, y, ?_, hshape⟩)
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.ne (by omega) (by omega) (by omega)
        · exact hc.ne (by omega) (by omega) (by omega)
      · obtain ⟨x, z, hxz, hshape⟩ :=
          T.exists_weight_multiplicity_intersection_eq_of_card_eq_three hcard
            (hc.ne (i := 0) (j := 1) (by omega) (by omega) (by omega))
            (hc.ne (i := 0) (j := 2) (by omega) (by omega) (by omega))
            (hc.ne (i := 1) (j := 2) (by omega) (by omega) (by omega))
            (hself _) (hself _) (hself _)
            (hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega))
        refine .inr (.inr (.inl ⟨hcard, x, c 1, z, ?_⟩))
        rcases hxz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hc.ne (by omega) (by omega) (by omega), hc.ne (by omega) (by omega) (by omega),
            hc.ne (by omega) (by omega) (by omega),
            hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega), hshape⟩
        · refine ⟨hc.ne (by omega) (by omega) (by omega), hc.ne (by omega) (by omega) (by omega),
            hc.ne (by omega) (by omega) (by omega), ?_, hshape⟩
          rw [T.intersection_comm]
          exact hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega)
      · rcases T.isGenusOneFourPathShape_or_isGenusOneFourPathShape hcard
            (hself _) (hself _) (hself _) (hself _)
            (hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega))
            (hzero 0 (by omega) 3 (by omega) (by omega) (by omega) (by omega))
            (hzero 1 (by omega) 3 (by omega) (by omega) (by omega) (by omega))
            (hc.intersection_succ_pos 0 (by omega)) (hc.intersection_succ_pos 1 (by omega))
            (hc.intersection_succ_pos 2 (by omega)) with h4 | h4
        · exact .inr (.inr (.inr (.inl ⟨hcard, c, hc, hzero, h4⟩)))
        · exact .inr (.inr (.inr (.inl
            ⟨hcard, fun i ↦ c (4 - 1 - i), hc.reverse, zero_of_reverse hzero, h4⟩)))
      · rcases T.isGenusOneFivePathShape_or_isGenusOneFivePathShape hcard
            (hself _) (hself _) (hself _) (hself _) (hself _)
            (hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega))
            (hzero 0 (by omega) 3 (by omega) (by omega) (by omega) (by omega))
            (hzero 0 (by omega) 4 (by omega) (by omega) (by omega) (by omega))
            (hzero 1 (by omega) 3 (by omega) (by omega) (by omega) (by omega))
            (hzero 1 (by omega) 4 (by omega) (by omega) (by omega) (by omega))
            (hzero 2 (by omega) 4 (by omega) (by omega) (by omega) (by omega))
            (hc.intersection_succ_pos 0 (by omega)) (hc.intersection_succ_pos 1 (by omega))
            (hc.intersection_succ_pos 2 (by omega)) (hc.intersection_succ_pos 3 (by omega))
            with h5 | h5
        · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨hcard, c, hc, hzero, h5⟩)))))
        · exact .inr (.inr (.inr (.inr (.inr (.inl
            ⟨hcard, fun i ↦ c (5 - 1 - i), hc.reverse, zero_of_reverse hzero, h5⟩)))))
    · rcases T.isGenusOneLongPathShape_or_isGenusOneLongPathShape hcard ht6 hc hzero with
        hlong | hlong
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨t, c, ht6, hcard, hc, hzero, hlong⟩))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨t, fun i ↦ c (t - 1 - i), ht6, hcard, hc.reverse, zero_of_reverse hzero, hlong⟩))))))))
  · -- Fork cases (`t = 3`, `4`, or `t ≥ 5`).
    have ht3 := hf.two_lt
    rcases lt_or_ge t 5 with ht5 | ht5
    · interval_cases t
      · -- `t = 3`: three-leaf star on `4` components.
        have hz02 := hf.intersection_eq_zero (by omega) (p := 0) (q := 2)
          (by omega) (by omega) (by omega) (by omega) (by omega)
        have hz0b := hf.branch_intersection_eq_zero (i := 0) (by omega) (by omega)
        have hz2b := hf.branch_intersection_eq_zero (i := 2) (by omega) (by omega)
        obtain ⟨x, y, z, hset, hstar⟩ := T.exists_isGenusOneFourStarShape hcard
          (hself (c 1)) (hself (c 0)) (hself (c 2)) (hself b) hz02 hz0b hz2b
          (by rw [T.intersection_comm]; exact hf.intersection_succ_pos 0 (by omega))
          (hf.intersection_succ_pos 1 (by omega)) hf.branch_intersection_pos
        have h10 : c 1 ∉ ({c 0, c 2, b} : Finset T.Component) := by
          simp [hf.ne (i := 1) (j := 0) (by omega) (by omega) (by omega),
            hf.ne (i := 1) (j := 2) (by omega) (by omega) (by omega),
            (hf.branch_ne 1 (by omega)).symm]
        have h02 : c 0 ∉ ({c 2, b} : Finset T.Component) := by
          simp [hf.ne (i := 0) (j := 2) (by omega) (by omega) (by omega),
            (hf.branch_ne 0 (by omega)).symm]
        have h2b : c 2 ≠ b := (hf.branch_ne 2 (by omega)).symm
        have huniv : ({c 1, x, y, z} : Finset T.Component) = univ := by
          have hsub : ({c 1, c 0, c 2, b} : Finset T.Component) = univ :=
            eq_univ_of_card _ (by
              rw [card_insert_of_notMem h10, card_insert_of_notMem h02, card_pair h2b, hcard])
          simpa [← hset] using hsub
        have hxyz_zero (u v : T.Component) (hu : u ∈ ({x, y, z} : Finset T.Component))
            (hv : v ∈ ({x, y, z} : Finset T.Component)) (huv : u ≠ v) :
            T.intersection u v = 0 := by
          rw [hset] at hu hv; simp only [mem_insert, mem_singleton] at hu hv
          grind [T.intersection_comm]
        have hcard3 : #({x, y, z} : Finset T.Component) = 3 := by
          rw [hset, card_insert_of_notMem h02, card_pair h2b]
        have hyz : y ≠ z := fun h ↦ by
          have := card_le_two (a := x) (b := y)
          rw [← h, insert_eq_of_mem (mem_singleton_self y)] at hcard3; omega
        have hxy : x ≠ y := fun h ↦ by
          have := card_le_two (a := x) (b := z)
          rw [← h, insert_eq_of_mem (mem_insert_self x {z})] at hcard3; omega
        have hxz : x ≠ z := fun h ↦ by
          have := card_le_two (a := y) (b := x)
          rw [← h, insert_eq_of_mem (mem_insert_of_mem (mem_singleton_self x))] at hcard3; omega
        exact .inr (.inr (.inr (.inr (.inl ⟨hcard, c 1, x, y, z, huniv,
          hxyz_zero x y (by simp) (by simp) hxy,
          hxyz_zero x z (by simp) (by simp) hxz,
          hxyz_zero y z (by simp) (by simp) hyz, hstar⟩))))
      · -- `t = 4`: five-component fork.
        let f : Fin 5 → T.Component := fun i ↦ if (i : ℕ) = 4 then b else c i
        have hf_inj : Function.Injective f := fun i j hij ↦ Fin.ext
          (hf.injOn_snoc hf.branch_ne i (by omega) j (by omega) hij)
        have hf_bij : Function.Bijective f :=
          (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by simpa using hcard.symm⟩
        let e : Fin 5 ≃ T.Component := Equiv.ofBijective f hf_bij
        have hz02 : T.intersection (e 0) (e 2) = 0 :=
          hf.intersection_eq_zero (by omega) (p := 0) (q := 2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
        have hz03 : T.intersection (e 0) (e 3) = 0 :=
          hf.intersection_eq_zero (by omega) (p := 0) (q := 3)
            (by omega) (by omega) (by omega) (by omega) (by omega)
        have hz04 : T.intersection (e 0) (e 4) = 0 :=
          hf.branch_intersection_eq_zero (i := 0) (by omega) (by omega)
        obtain ⟨-, w, m, hfive⟩ := hT.exists_weight_multiplicity_intersection_eq_fiveFork hg e
          (hf.intersection_succ_pos 0 (by omega))
          (hf.intersection_succ_pos 1 (by omega))
          (hf.intersection_succ_pos 2 (by omega))
          hf.branch_intersection_pos hz02 hz03 hz04
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e, w, m, hfive⟩)))))))
    · -- `t ≥ 5`: long fork.
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨t, c, b, ht5, hcard, hf, hf.isGenusOneLongForkShape hcard (by omega)⟩)))))))))
  · -- Four-leaf star (affine `D₄`).
    obtain ⟨e, he0, hel, hw, hm, ha⟩ :=
      T.exists_equiv_fourLeafStar c₀ l hl (hself c₀) (fun i ↦ hself (l i)) hadj
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨e, by simpa [he0] using hw, by simpa [hel 0] using hm, by simpa [he0] using ha⟩))))))
  · -- Double fork (affine `Dₙ`, `n ≥ 5`).
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨t, c, left, right, ht4, hcard, hr, hl, hr.isGenusOneAffineDShape hl hcard ht4⟩))))))))))
  · -- Affine `E₆`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE6 l hl (fun i ↦ hself (l i)) hadj
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨e, by simpa [he 0] using hw, by simpa [he 2] using hm, by simpa [he 0] using ha⟩)))))))))))
  · -- Affine `E₇`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE7 l hl (fun i ↦ hself (l i)) hadj
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨e, by simpa [he 0] using hw, by simpa [he 4] using hm, by simpa [he 0] using ha⟩))))))))))))
  · -- Affine `E₈`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE8 l hl (fun i ↦ hself (l i)) hadj
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨e, by simpa [he 0] using hw, by simpa [he 8] using hm, by simpa [he 0] using ha⟩))))))))))))

/-! ### Divisibility and ratio bounds for weights and multiplicities -/

/-- If `(a : ℤ)` is one of `1, 2, 3, 4` times `(b : ℤ)`, then `(b : ℕ)` divides `a` with quotient
at most `4`. -/
private lemma dvd_and_le_four_of_int {a b : ℕ+}
    (h : (a : ℤ) = b ∨ (a : ℤ) = 2 * b ∨ (a : ℤ) = 3 * b ∨ (a : ℤ) = 4 * b) :
    (b : ℕ) ∣ a ∧ (a : ℕ) ≤ 4 * b := by
  rcases h with h | h | h | h <;>
    [exact ⟨⟨1, by omega⟩, by omega⟩; exact ⟨⟨2, by omega⟩, by omega⟩;
      exact ⟨⟨3, by omega⟩, by omega⟩; exact ⟨⟨4, by omega⟩, by omega⟩]

/-- If `(a : ℤ)` is one of `1, …, 6` times `(b : ℤ)`, then `(b : ℕ)` divides `a` with quotient
at most `6`. -/
private lemma dvd_and_le_six_of_int {a b : ℕ+}
    (h : (a : ℤ) = b ∨ (a : ℤ) = 2 * b ∨ (a : ℤ) = 3 * b ∨
      (a : ℤ) = 4 * b ∨ (a : ℤ) = 5 * b ∨ (a : ℤ) = 6 * b) :
    (b : ℕ) ∣ a ∧ (a : ℕ) ≤ 6 * b := by
  rcases h with h | h | h | h | h | h <;>
    [exact ⟨⟨1, by omega⟩, by omega⟩; exact ⟨⟨2, by omega⟩, by omega⟩;
      exact ⟨⟨3, by omega⟩, by omega⟩; exact ⟨⟨4, by omega⟩, by omega⟩;
      exact ⟨⟨5, by omega⟩, by omega⟩; exact ⟨⟨6, by omega⟩, by omega⟩]

/-- Every shape in `IsGenusOneMinimalShape` has a minimum-weight component dividing all weights
with quotient at most `4`, and a minimum-multiplicity component dividing all multiplicities with
quotient at most `6`. -/
private lemma exists_weight_and_multiplicity_dvd_and_le (h : T.IsGenusOneMinimalShape) :
    (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
      (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
        (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) := by
  classical
  have close (jw jm : T.Component)
      (hw : ∀ i, (T.weight i : ℤ) = T.weight jw ∨ (T.weight i : ℤ) = 2 * T.weight jw ∨
        (T.weight i : ℤ) = 3 * T.weight jw ∨ (T.weight i : ℤ) = 4 * T.weight jw)
      (hm : ∀ i, (T.multiplicity i : ℤ) = T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 2 * T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 3 * T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 4 * T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 5 * T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 6 * T.multiplicity jm) :
      (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
        (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
          (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) :=
    ⟨⟨jw, fun i ↦ dvd_and_le_four_of_int (hw i)⟩, ⟨jm, fun i ↦ dvd_and_le_six_of_int (hm i)⟩⟩
  obtain ⟨j₀⟩ := (inferInstance : Nonempty T.Component)
  rcases h with ⟨hcard1, -⟩ | ⟨-,
    ⟨-, hwm, -⟩ |
    ⟨hcard, x, y, hxy, h2⟩ |
    ⟨hcard, x, j, z, hxj, hxz, hjz, -, h3⟩ |
    ⟨hcard, c, hc, -, h4⟩ |
    ⟨-, c₀, x, y, z, huniv, -, -, -, hstar⟩ |
    ⟨hcard, c, hc, -, h5⟩ |
    ⟨e, hw, hm, -⟩ |
    ⟨e, w, m, ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩⟩ |
    ⟨n, c, hn, hcard, hc, -, hlong⟩ |
    ⟨t, c, b, ht, hcard, hf, hfork⟩ |
    ⟨t, c, left, right, ht, hcard, hr, hl, hD⟩ |
    ⟨e, hw, hm, -⟩ | ⟨e, hw, hm, -⟩ | ⟨e, hw, hm, -⟩⟩
  · exact close j₀ j₀
      (fun i ↦ by rw [Fintype.card_le_one_iff.mp hcard1.le i j₀]; omega)
      (fun i ↦ by rw [Fintype.card_le_one_iff.mp hcard1.le i j₀]; omega)
  · exact close j₀ j₀
      (fun i ↦ by rw [(hwm i j₀).1]; omega)
      (fun i ↦ by rw [(hwm i j₀).2]; omega)
  · have mem (i : T.Component) : i = x ∨ i = y := by
      have hu : ({x, y} : Finset T.Component) = univ :=
        eq_univ_of_card _ (by rw [card_pair hxy, hcard])
      simpa using (hu ▸ mem_univ i : i ∈ ({x, y} : Finset T.Component))
    rcases isGenusOnePairShape_iff.mp h2 with ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩ <;>
      [refine close x x ?_ ?_; refine close x y ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl <;> omega)
  · have mem (i : T.Component) : i = x ∨ i = j ∨ i = z := by
      have hu : ({x, j, z} : Finset T.Component) = univ :=
        eq_univ_of_card _ (by
          rw [card_insert_of_notMem (by simp [hxj, hxz]), card_pair hjz, hcard])
      simpa using (hu ▸ mem_univ i : i ∈ ({x, j, z} : Finset T.Component))
    rcases isGenusOneChainShape_iff.mp h3 with ⟨hw1, hw2, hm1, hm2, -⟩ |
      ⟨hw1, hw2, hm1, hm2, -⟩ | ⟨hw1, hw2, hm1, hm2, -⟩ |
      ⟨hw1, hw2, hm1, hm2, -⟩ | ⟨hw1, hw2, hm1, hm2, -⟩ <;>
      [refine close x x ?_ ?_; refine close z x ?_ ?_; refine close x z ?_ ?_;
        refine close x x ?_ ?_; refine close j x ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl | rfl <;> omega)
  · have mem (i : T.Component) : i = c 0 ∨ i = c 1 ∨ i = c 2 ∨ i = c 3 := by
      obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      interval_cases k <;> simp
    rcases isGenusOneFourPathShape_iff.mp h4 with ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ |
      ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ | ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ <;>
      [refine close (c 0) (c 3) ?_ ?_; refine close (c 0) (c 0) ?_ ?_;
        refine close (c 1) (c 0) ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl | rfl | rfl <;> omega)
  · have mem (i : T.Component) : i = c₀ ∨ i = x ∨ i = y ∨ i = z := by
      simpa using (huniv ▸ mem_univ i : i ∈ ({c₀, x, y, z} : Finset T.Component))
    rcases isGenusOneFourStarShape_iff.mp hstar with ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ |
      ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ <;>
      [refine close c₀ x ?_ ?_; refine close z x ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl | rfl | rfl <;> omega)
  · have mem (i : T.Component) : i = c 0 ∨ i = c 1 ∨ i = c 2 ∨ i = c 3 ∨ i = c 4 := by
      obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      interval_cases k <;> simp
    obtain ⟨w, m, _, _, ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩ |
      ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩ |
      ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩ |
      ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩ |
      ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩⟩ :=
        isGenusOneFivePathShape_iff.mp h5 <;>
      [refine close (c 0) (c 0) ?_ ?_; refine close (c 3) (c 0) ?_ ?_;
        refine close (c 0) (c 4) ?_ ?_; refine close (c 0) (c 0) ?_ ?_;
        refine close (c 1) (c 0) ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl | rfl | rfl | rfl <;> omega)
  · refine close (e none) (e (some 0)) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i)]; omega
    · have hv := hm (e.symm i); rw [e.apply_symm_apply] at hv; split_ifs at hv <;> omega
  · refine close (e 1) (e 0) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i), hw 1]
      generalize e.symm i = k; fin_cases k <;> simp
    · rw [← e.apply_symm_apply i, hm (e.symm i), hm 0]
      generalize e.symm i = k; fin_cases k <;> simp
  · refine close (e 0) (e 3) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i), hw 0]
      generalize e.symm i = k; fin_cases k <;> simp
    · rw [← e.apply_symm_apply i, hm (e.symm i), hm 3]
      generalize e.symm i = k; fin_cases k <;> simp
  · obtain ⟨w, m, _, _, ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩⟩ :=
      isGenusOneLongPathShape_iff.mp hlong
    · refine close (c 0) (c (n - 1)) (fun i ↦ ?_) (fun i ↦ ?_)
      · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hwk := hw k hk; have hw0 := hw 0 (by omega); split_ifs at hwk hw0 <;> omega
      · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hmk := hm k hk; have hm0 := hm (n - 1) (by omega); split_ifs at hmk hm0 <;> omega
    · refine close (c 0) (c 0) (fun i ↦ ?_) (fun i ↦ ?_)
      · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hwk := hw k hk; have hw0 := hw 0 (by omega); split_ifs at hwk hw0 <;> omega
      · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hmk := hm k hk; have hm0 := hm 0 (by omega); omega
    · refine close (c 1) (c 0) (fun i ↦ ?_) (fun i ↦ ?_)
      · have hw1 := hw 1 (by omega); rw [ite_eq_right (by omega)] at hw1
        obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hwk := hw k hk; split_ifs at hwk <;> omega
      · have hm0 := hm 0 (by omega); rw [ite_eq_left (by omega)] at hm0
        obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hmk := hm k hk; split_ifs at hmk <;> omega
  · obtain ⟨w, m, _, _, ⟨hw, hwb, hm, hmb, -⟩ | ⟨hw, hwb, hm, hmb, -⟩⟩ :=
      isGenusOneLongForkShape_iff.mp hfork
    · refine close b b (fun i ↦ ?_) (fun i ↦ ?_)
      · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
        · omega
        · have hwk := hw k hk; split_ifs at hwk <;> omega
      · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
        · omega
        · have hmk := hm k hk; split_ifs at hmk <;> omega
    · refine close (c 0) b (fun i ↦ ?_) (fun i ↦ ?_)
      · have hw0 := hw 0 (by omega); simp only [↓reduceIte] at hw0
        rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
        · omega
        · have hwk := hw k hk; split_ifs at hwk <;> omega
      · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
        · omega
        · have hmk := hm k hk; split_ifs at hmk <;> omega
  · obtain ⟨w, m, _, _, hw, hwl, hwr, hm, hml, hmr, -⟩ := isGenusOneAffineDShape_iff.mp hD
    refine close left left (fun i ↦ ?_) (fun i ↦ ?_)
    · rcases hr.eq_or_eq_or_exists_lt_eq_of_card_eq hl ht hcard i with rfl | rfl | ⟨k, hk, rfl⟩ <;>
        [omega; omega; (have hwk := hw k hk; omega)]
    · rcases hr.eq_or_eq_or_exists_lt_eq_of_card_eq hl ht hcard i with rfl | rfl | ⟨k, hk, rfl⟩ <;>
        [omega; omega; (have hmk := hm k hk; split_ifs at hmk <;> omega)]
  · refine close (e 0) (e 2) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i)]; omega
    · rw [← e.apply_symm_apply i, hm (e.symm i)]
      generalize e.symm i = k; fin_cases k <;> simp [mul_comm]
  · refine close (e 0) (e 4) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i)]; omega
    · rw [← e.apply_symm_apply i, hm (e.symm i)]
      generalize e.symm i = k; fin_cases k <;> simp
  · refine close (e 0) (e 8) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i)]; omega
    · rw [← e.apply_symm_apply i, hm (e.symm i)]
      generalize e.symm i = k; fin_cases k <;> simp

/-- In any numerical type satisfying `IsGenusOneMinimalShape`, there is a component whose weight
divides every component's weight with quotient at most `4`. -/
theorem IsGenusOneMinimalShape.exists_weight_dvd_and_le_four_mul
    (h : T.IsGenusOneMinimalShape) :
    ∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j :=
  (exists_weight_and_multiplicity_dvd_and_le h).1

/-- In any numerical type satisfying `IsGenusOneMinimalShape`, there is a component whose
multiplicity divides every component's multiplicity with quotient at most `6`. -/
theorem IsGenusOneMinimalShape.exists_multiplicity_dvd_and_le_six_mul
    (h : T.IsGenusOneMinimalShape) :
    ∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
      (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j :=
  (exists_weight_and_multiplicity_dvd_and_le h).2

/-- In a minimal numerical type of arithmetic genus one, there is a component whose weight divides
every component's weight with quotient at most `4`
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)). -/
theorem IsMinimal.exists_weight_dvd_and_le_four_mul
    (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) :
    ∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j :=
  (hT.isGenusOneMinimalShape hg).exists_weight_dvd_and_le_four_mul

/-- In a minimal numerical type of arithmetic genus one, there is a component whose multiplicity
divides every component's multiplicity with quotient at most `6`
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)). -/
theorem IsMinimal.exists_multiplicity_dvd_and_le_six_mul
    (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) :
    ∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
      (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j :=
  (hT.isGenusOneMinimalShape hg).exists_multiplicity_dvd_and_le_six_mul

end TauCeti.NumericalType
