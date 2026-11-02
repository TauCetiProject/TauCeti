/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.DoubleFork
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Branch
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.E8
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Exceptional
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic.ITauto
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Structural classification of `(-2)`-indices

Let `S` be a set of components of a numerical type, each of self-intersection `aᵢᵢ = -2wᵢ`, which
is connected, in the sense that no nonempty proper subset of `S` is disjoint from the rest of
`S`, and which is a proper subset of the components. This file proves that the configuration
formed by `S` has Dynkin-diagram shape
([Stacks, Proposition 55.5.17](https://stacks.math.columbia.edu/tag/0C8Q)): one of the following
holds.

* `S` is the set of components of a chain `c 0 - c 1 - ⋯ - c (t - 1)`
  (`TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain`), the types `A`, `B`, `C`, `F₄` and
  `G₂`.
* `S` is the set of components of a fork, a chain of at least three components together with a
  leaf meeting its penultimate component (`TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork`),
  the type `D`.
* `S` consists of a chain of five, six or seven components together with a leaf meeting the
  component `c (t - 3)` and no other component of the chain: the types `E₆`, `E₇` and `E₈`.

Since the exceptional sets have at most eight elements, a connected proper set of at least nine
such components is a chain or a fork. The
weights and intersection numbers of each shape are determined by the classifications already
available: `IsSelfIntersectionMinusTwoChain.exists_weight_eq_except_one_end` for chains,
`IsSelfIntersectionMinusTwoFork.exists_weight_intersection_eq` for forks, and
`exists_weight_intersection_branch_six_eq`, `exists_weight_intersection_branch_seven_eq` and
`IsSelfIntersectionMinusTwoChain.exists_weight_intersection_branch_eight_eq` for the exceptional
types. This is the input for the bound on the multiplicities of a minimal numerical type in
[Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W), where a maximal connected set
of `(-2)`-indices is either small or a chain or a fork, the two shapes treated in
`TauCeti/AlgebraicGeometry/Curves/StableReduction/NumericalType/MultiplicityBound.lean`.

## Main results

* `TauCeti.NumericalType.exists_chain_or_fork_or_exceptional`: the classification above.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.card_ne_add_one_of_branch_two`: the
  exceptional configuration of `5 ≤ t ≤ 7` chain components with a leaf at `c 2` cannot exhaust a
  numerical type.
* `TauCeti.NumericalType.topologicalGenus_pos_or_exists_chain_or_fork_or_star_or_affine` and
  `TauCeti.NumericalType.exists_chain_or_fork_or_star_or_affine_of_topologicalGenus_eq_zero`:
  classification when every component has self-intersection `-2w`, without requiring a proper
  subset. These supply the structural part of the minimal genus-one classification
  ([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)).

## Exhaustive configurations

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

-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable {T : NumericalType.{u}}

namespace IsSelfIntersectionMinusTwoChain

variable {t : ℕ} {c : ℕ → T.Component}

/-- Two distinct components outside a chain cannot both meet interior components of the chain,
provided the numerical type has a component besides them and those of the chain: they would form
a four-legged star or a chain with leaves at both ends. -/
private lemma false_of_two_leaves (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t + 2 < Fintype.card T.Component) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ)))
    (hy_self : T.intersection y y = -(2 * (T.weight y : ℤ))) {r s : ℕ} (hr0 : 0 < r)
    (hrs : r ≤ s) (hst : s + 1 < t) (hx : 0 < T.intersection (c r) x)
    (hy : 0 < T.intersection (c s) y) : False := by
  rcases hrs.eq_or_lt with rfl | hrs
  · -- `c r` would meet `c (r - 1)`, `c (r + 1)`, `x` and `y`: a four-legged star.
    have h := T.intersection_eq_zero_of_star_five (by omega) (hc.intersection_self r (by omega))
      (hc.intersection_self (r - 1) (by omega)) (hc.intersection_self (r + 1) (by omega))
      hx_self hy_self (hy_ne r (by omega)).symm (hc.ne (by omega) (by omega) (by omega))
      (hx_ne (r - 1) (by omega)).symm (hy_ne (r - 1) (by omega)).symm
      (hx_ne (r + 1) (by omega)).symm (hy_ne (r + 1) (by omega)).symm hxy
      (by rw [T.intersection_comm]; exact hc.intersection_pos (by omega) (by omega))
      (hc.intersection_succ_pos r (by omega)) hx
    omega
  · -- The block `c (r - 1), …, c (s + 1)` would carry leaves at both its second and its
    -- penultimate component.
    have hd := hc.shift (r := r - 1) (s := s - r + 3) (by omega)
    refine IsSelfIntersectionMinusTwoFork.not_oppositeFork (t := s - r + 3)
      (c := fun k ↦ c (r - 1 + k)) (right := y) (left := x) ?_ ?_ (by omega) (by omega)
    -- Convert the two attachment positions from the shifted block back to `s` and `r`.
    · exact ⟨hd, by omega, fun i hi ↦ hy_ne _ (by omega), hy_self, by
        simpa [show r - 1 + (s - r + 1) = s by omega] using hy⟩
    · exact ⟨hd.reverse, by omega, fun i hi ↦ hx_ne _ (by omega), hx_self, by
        simpa [show r - 1 + 1 = r by omega] using hx⟩

/-- A leaf meeting a chain at the position `r`, with `2 ≤ r` and at least `r` further
components after position `r`, can only sit at position `2` of a chain of at most seven
components: otherwise the chain and the leaf contain an affine `E₇` or `E₈` diagram. -/
private lemma eq_two_and_le_seven (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t + 1 < Fintype.card T.Component) {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {r : ℕ} (hr : 2 ≤ r)
    (hrt : 2 * r + 1 ≤ t) (hx : 0 < T.intersection (c r) x) : r = 2 ∧ t ≤ 7 := by
  by_cases hr3 : 3 ≤ r
  · -- `c (r - 3), …, c (r + 3)` with the leaf `x` at its middle is an affine `E₇` diagram.
    have h := IsSelfIntersectionMinusTwoChain.intersection_branch_eq_zero T
      (hc.shift (r := r - 3) (s := 7) (by omega)) (by omega) (branch := x)
      (fun i hi ↦ hx_ne _ (by omega)) hx_self
    -- Position `3` in this shifted seven-component block is the original position `r`.
    simp only [show r - 3 + 3 = r by omega] at h
    omega
  refine ⟨by omega, not_lt.mp fun ht ↦ ?_⟩
  obtain rfl : r = 2 := by omega
  -- `c 7, c 6, …, c 0` with the leaf `x` at `c 2` is an affine `E₈` diagram.
  exact (hc.mono (s := 8) (by omega)).reverse.not_affineE8 (by omega)
    (fun i hi ↦ hx_ne _ (by omega)) hx_self (by simpa using hx)

/-- A leaf `x` meeting a chain at the position `r`, with at least two components of the chain on
either side, meets no further component `y` outside the chain, provided the numerical type has a
component besides `x`, `y` and those of the chain: `c (r - 2), …, c (r + 2)`, `x`, `y` would be an
affine `E₆` diagram. -/
private lemma intersection_eq_zero_of_leaf (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t + 2 < Fintype.card T.Component) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ)))
    (hy_self : T.intersection y y = -(2 * (T.weight y : ℤ))) {r : ℕ} (hr : 2 ≤ r)
    (hrt : r + 3 ≤ t) (hx : 0 < T.intersection (c r) x) : T.intersection x y = 0 :=
  T.intersection_eq_zero_of_branch_six (by omega)
    (hc.intersection_self (r - 2) (by omega)) (hc.intersection_self (r - 1) (by omega))
    (hc.intersection_self r (by omega)) (hc.intersection_self (r + 1) (by omega))
    (hc.intersection_self (r + 2) (by omega)) hx_self hy_self
    (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
    (hc.ne (by omega) (by omega) (by omega)) (hx_ne _ (by omega)).symm
    (hy_ne _ (by omega)).symm (hc.ne (by omega) (by omega) (by omega))
    (hc.ne (by omega) (by omega) (by omega)) (hx_ne _ (by omega)).symm
    (hy_ne _ (by omega)).symm (hc.ne (by omega) (by omega) (by omega))
    (hy_ne _ (by omega)).symm (hx_ne _ (by omega)).symm (hy_ne _ (by omega)).symm
    (hx_ne _ (by omega)).symm (hy_ne _ (by omega)).symm hxy
    (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
    (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega)) hx

variable {S : Finset T.Component}

/-- A component of `S` outside a longest chain in `S` does not meet the first component of the
chain, since prepending it would give a longer chain. -/
private lemma not_intersection_pos_zero (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcS : ∀ i < t, c i ∈ S)
    (hmax : ∀ t' c', T.IsSelfIntersectionMinusTwoChain t' c' → (∀ i < t', c' i ∈ S) → t' ≤ t)
    {x : T.Component} (hxS : x ∈ S) (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) :
    ¬ 0 < T.intersection (c 0) x := fun hpos ↦ by
  have ht : 0 < t := by
    have hzero : T.IsSelfIntersectionMinusTwoChain 0 fun _ ↦ x := ⟨by omega, by omega, by omega⟩
    have := hmax _ _ (hzero.cons (by omega) hx_self (by omega)) fun _ _ ↦ by
      split_ifs <;> exact hxS
    omega
  have := hmax _ _ (hc.cons hx_ne hx_self (fun _ ↦ by rwa [T.intersection_comm]))
    fun i hi ↦ by split_ifs; exacts [hxS, hcS _ (by omega)]
  omega

/-- A component of `S` outside a longest chain in `S` can only meet interior components of the
chain. -/
lemma pos_and_lt_of_intersection_pos (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcS : ∀ i < t, c i ∈ S)
    (hmax : ∀ t' c', T.IsSelfIntersectionMinusTwoChain t' c' → (∀ i < t', c' i ∈ S) → t' ≤ t)
    {x : T.Component} (hxS : x ∈ S) (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {r : ℕ} (hr : r < t)
    (hx : 0 < T.intersection (c r) x) : 0 < r ∧ r + 1 < t := by
  refine ⟨Nat.pos_of_ne_zero fun h ↦
      hc.not_intersection_pos_zero hcS hmax hxS hx_ne hx_self (h ▸ hx),
    not_le.mp fun h ↦ hc.reverse.not_intersection_pos_zero (fun i hi ↦ hcS _ (by omega)) hmax
      hxS (fun i hi ↦ hx_ne _ (by omega)) hx_self ?_⟩
  -- The first position of the reversed chain is the original last position `r`.
  simpa [show t - 1 = r by omega] using hx

/-- A component of `S` outside a longest chain in `S` meets at most one component of the chain:
it can only meet the interior subchain `c 1, …, c (t - 2)`, which has at least two fewer
components than the numerical type. -/
lemma intersection_eq_zero_of_ne_of_intersection_pos (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcS : ∀ i < t, c i ∈ S)
    (hmax : ∀ t' c', T.IsSelfIntersectionMinusTwoChain t' c' → (∀ i < t', c' i ∈ S) → t' ≤ t)
    {x : T.Component} (hxS : x ∈ S) (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {r i : ℕ} (hr : r < t)
    (hx : 0 < T.intersection (c r) x) (hi : i < t) (hir : i ≠ r) :
    T.intersection (c i) x = 0 := by
  obtain ⟨hr0, hrt⟩ := hc.pos_and_lt_of_intersection_pos hcS hmax hxS hx_ne hx_self hr hx
  refine le_antisymm (not_lt.mp fun hix ↦ hir ?_) (T.offDiagonal_nonneg _ _ (hx_ne i hi).symm)
  obtain ⟨hi0, hit⟩ := hc.pos_and_lt_of_intersection_pos hcS hmax hxS hx_ne hx_self hi hix
  have hcard : (t - 2) + 1 < Fintype.card T.Component := by
    have := hc.le_card_snoc hx_ne
    omega
  have hc' := hc.shift (r := 1) (s := t - 2) (by omega)
  have hx' : 0 < T.intersection (c (1 + (r - 1))) x := by
    have hr_eq : 1 + (r - 1) = r := by omega
    simpa [hr_eq] using hx
  have hix' : 0 < T.intersection (c (1 + (i - 1))) x := by
    have hi_eq : 1 + (i - 1) = i := by omega
    simpa [hi_eq] using hix
  rcases le_total (i - 1) (r - 1) with h | h
  · have := hc'.eq_of_intersection_pos hcard (fun j hj ↦ hx_ne _ (by omega)) hx_self
      (by omega) hix' h hx'
    omega
  · have := hc'.eq_of_intersection_pos hcard (fun j hj ↦ hx_ne _ (by omega)) hx_self
      (by omega) hx' h hix'
    omega

/-- A leaf meeting a chain and a further component of a longest chain set has at least two
components before its point of attachment. -/
lemma two_le_of_intersection_pos (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcS : ∀ i < t, c i ∈ S)
    (hmax : ∀ t' c', T.IsSelfIntersectionMinusTwoChain t' c' → (∀ i < t', c' i ∈ S) → t' ≤ t)
    {x : T.Component} (hxS : x ∈ S) (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {y : T.Component} (hyS : y ∈ S)
    (hy_ne : ∀ i < t, y ≠ c i) (hy_self : T.intersection y y = -(2 * (T.weight y : ℤ)))
    (hyx : y ≠ x) {r : ℕ} (hr : r < t) (hx : 0 < T.intersection (c r) x)
    (hxy : 0 < T.intersection x y) : 2 ≤ r := by
  have hright := hmax _ _
    (((hc.shift (r := r) (s := t - r) (by omega)).cons (fun i hi ↦ hx_ne _ (by omega))
      hx_self (fun _ ↦ by simpa [T.intersection_comm] using hx)).cons
      (fun i hi ↦ by split_ifs; exacts [hyx, hy_ne _ (by omega)])
      hy_self (fun _ ↦ by simpa [T.intersection_comm] using hxy))
    fun i hi ↦ by split_ifs; exacts [hyS, hxS, hcS _ (by omega)]
  omega

/-- A chain `c 0, …, c (t - 1)` of length `5 ≤ t ≤ 7` together with a single leaf `x` at `c 2`
cannot exhaust a numerical type: the five-component subfork on `c 0, c 1, c 2, c 3, x` and the
chain classification fix all weights below `t - 1`, and the resulting fibre relations on the
multiplicities are incompatible at the right end of the chain. -/
lemma card_ne_add_one_of_branch_two (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (ht5 : 5 ≤ t) (ht7 : t ≤ 7) {x : T.Component}
    (hx_ne : ∀ i < t, x ≠ c i) (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ)))
    (hx_pos : 0 < T.intersection (c 2) x)
    (hx_zero : ∀ i < t, i ≠ 2 → T.intersection (c i) x = 0) :
    Fintype.card T.Component ≠ t + 1 := by
  intro hcard
  have hchainCard : t < Fintype.card T.Component := by omega
  have hf4 : T.IsSelfIntersectionMinusTwoFork 4 c x :=
    ⟨hc.mono (by omega), by omega, fun i hi ↦ hx_ne i (by omega), hx_self, hx_pos⟩
  obtain ⟨w, hw4, hwx, -, h2x⟩ := hf4.exists_weight_intersection_eq (by omega)
  obtain ⟨W, -, hWint, -, hright, -⟩ :=
    hc.exists_weight_eq_except_one_end hchainCard (by omega)
  have hWw : W = (w : ℤ) := (hWint 1 (by omega) (by omega)).symm.trans (hw4 1 (by omega))
  subst W
  have hw (i : ℕ) (hi : i < t - 1) : (T.weight (c i) : ℤ) = w := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact hw4 0 (by omega)
    · exact hWint i hi0 (by omega)
  have hedge (i : ℕ) (hi : i + 1 < t - 1) : T.intersection (c i) (c (i + 1)) = w := by
    rw [T.intersection_eq_max_weight (by omega) (hc.intersection_self i (by omega))
      (hc.intersection_self (i + 1) (by omega)) (hc.intersection_succ_pos i (by omega)),
      hw i (by omega), hw (i + 1) (by omega), max_self]
  have hfib (z : T.Component) :
      ∑ j ∈ range t, T.intersection z (c j) * T.multiplicity (c j) +
        T.intersection z x * T.multiplicity x = 0 := by
    simpa using sum_range_add_sum_intersection_mul_multiplicity_eq_zero hc.injOn
      (S := {x}) (fun i hi h ↦ hx_ne i hi (mem_singleton.mp h).symm)
      (by simpa using hcard) z
  have hw_ne : (w : ℤ) ≠ 0 := by positivity
  -- Fibre relation at `x`: `m (c 2) = 2 * m x`.
  have hmx : (T.multiplicity (c 2) : ℤ) = 2 * T.multiplicity x := by
    have h := hfib x
    rw [sum_eq_single_of_mem 2 (mem_range.mpr (by omega)) (fun j hj hj2 ↦ by
        rw [T.intersection_comm, hx_zero j (mem_range.mp hj) hj2, zero_mul]),
      T.intersection_comm x (c 2), h2x, hx_self, hwx] at h
    exact mul_left_cancel₀ hw_ne (by linear_combination h)
  -- Fibre relation at `c 0`: `m (c 1) = 2 * m (c 0)`.
  have hm1 : (T.multiplicity (c 1) : ℤ) = 2 * T.multiplicity (c 0) := by
    have h := hfib (c 0)
    rw [hc.left_sum_eq hchainCard (by omega), hc.intersection_self 0 (by omega),
      hw 0 (by omega), hedge 0 (by omega), hx_zero 0 (by omega) (by omega), zero_mul,
      add_zero] at h
    exact mul_left_cancel₀ hw_ne (by linear_combination h)
  -- At each constant-weight triple, the chain API cancels the common weight.
  have hm2 : (T.multiplicity (c 0) : ℤ) + T.multiplicity (c 2) = 2 * T.multiplicity (c 1) := by
    have h := hc.interior_relation_of_weight_eq hchainCard (i := 1) (by omega) (by omega)
      (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (b := 0) (by
        simpa [hx_zero 1 (by omega) (by omega)] using hfib (c 1))
    simpa using h
  have hm3 : (T.multiplicity (c 1) : ℤ) + T.multiplicity (c 3) + T.multiplicity x =
      2 * T.multiplicity (c 2) :=
    hc.interior_relation_of_weight_eq hchainCard (i := 2) (by omega) (by omega)
      (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (by
        simpa only [h2x] using hfib (c 2))
  have hrec (i : ℕ) (hi2 : 2 < i) (hit : i + 1 < t - 1) :
      (T.multiplicity (c (i - 1)) : ℤ) + T.multiplicity (c (i + 1)) =
        2 * T.multiplicity (c i) := by
    have h := hc.interior_relation_of_weight_eq hchainCard (by omega) (by omega)
      (hw (i - 1) (by omega)) (hw i (by omega)) (hw (i + 1) hit) (b := 0) (by
        simpa [hx_zero i (by omega) (by omega)] using hfib (c i))
    simpa using h
  have hendRel := hc.right_end_relation_of_weight_eq hchainCard (by omega)
    (hw (t - 3) (by omega)) (hw (t - 2) (by omega)) hright
    (by simpa [hx_zero (t - 2) (by omega) (by omega)] using hfib (c (t - 2)))
    (by simpa [hx_zero (t - 1) (by omega) (by omega)] using hfib (c (t - 1)))
  have hm0 : (0 : ℤ) < T.multiplicity (c 0) := by simp
  interval_cases t
  · norm_num only at hendRel
    omega
  · have h4 := hrec 3 (by omega) (by omega)
    norm_num only at h4 hendRel
    omega
  · have h4 := hrec 3 (by omega) (by omega)
    have h5 := hrec 4 (by omega) (by omega)
    norm_num only at h4 h5 hendRel
    omega

end IsSelfIntersectionMinusTwoChain

-- The Stacks Project leaves the proof of Proposition 55.5.17 to the discussion at the start of
-- [Section 55.5](https://stacks.math.columbia.edu/tag/0C7L). The argument here starts from a
-- longest chain `c` inside `S`. A component of `S` outside the chain that meets it meets exactly
-- one of its components, an interior one: otherwise the chain could be lengthened or would close
-- up into a cycle, which `IsSelfIntersectionMinusTwoChain.intersection_eq_zero` excludes. Two
-- such components would form either a four-legged star (Stacks, Lemma 55.5.6) or a chain with
-- leaves at both ends (Stacks, Lemma 55.5.11), and such a component meeting a further component
-- of `S` would, by maximality of `c`, form an affine `E₆` diagram (Stacks, Lemma 55.5.12). So
-- `S` is the chain together with at most one leaf. A leaf at the second or penultimate component
-- gives a fork, and the affine `E₇` and `E₈` diagrams (Stacks, Lemmas 55.5.15 and 55.5.16)
-- confine every other position of the leaf to the exceptional types.
/-- **Classification of connected proper sets of `(-2)`-indices.** Let `S` be a proper subset of
the components of a numerical type, each of self-intersection `-2w`, which is connected: every
nonempty proper subset of `S` meets a component of `S` outside it. Then `S` is the set of
components of a chain, or of a fork, or of a chain of five, six or seven components together with
a leaf meeting `c (t - 3)` and no other component of the chain. These are the Dynkin diagrams of
types `A` (with `B`, `C`, `F₄` and `G₂`), `D` and `E₆`, `E₇`, `E₈`
([Stacks, Proposition 55.5.17](https://stacks.math.columbia.edu/tag/0C8Q)). -/
theorem exists_chain_or_fork_or_exceptional {S : Finset T.Component}
    (hS : ∀ i ∈ S, T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hcard : #S < Fintype.card T.Component)
    (hconn : ∀ A ⊆ S, A.Nonempty → A ≠ S → ∃ i ∈ A, ∃ j ∈ S, j ∉ A ∧ 0 < T.intersection i j) :
    (∃ t c, T.IsSelfIntersectionMinusTwoChain t c ∧ (range t).image c = S) ∨
    (∃ t c b, T.IsSelfIntersectionMinusTwoFork t c b ∧ insert b ((range t).image c) = S) ∨
    ∃ t c b, T.IsSelfIntersectionMinusTwoChain t c ∧ 5 ≤ t ∧ t ≤ 7 ∧ (∀ i < t, b ≠ c i) ∧
      T.intersection b b = -(2 * (T.weight b : ℤ)) ∧ 0 < T.intersection (c (t - 3)) b ∧
      (∀ i < t, i ≠ t - 3 → T.intersection (c i) b = 0) ∧ insert b ((range t).image c) = S := by
  obtain ⟨t, c, hc, hcS, hmax⟩ := exists_chain_forall_le S
  set A := (range t).image c with hA_def
  by_cases hAS : A = S
  · exact .inl ⟨t, c, hc, hAS⟩
  have hAsub : A ⊆ S := fun x hx ↦ by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact hcS i (mem_range.mp hi)
  have mem_A {x : T.Component} : x ∈ A ↔ ∃ i < t, c i = x := by simp [hA_def]
  have ht : 0 < t := by
    by_contra ht
    obtain ⟨x, hx⟩ : S.Nonempty := by
      rw [nonempty_iff_ne_empty]
      rintro rfl
      exact hAS (subset_empty.mp hAsub)
    have := hmax 1 (fun _ ↦ x) ⟨by omega, fun _ _ ↦ hS x hx, by omega⟩ fun _ _ ↦ hx
    omega
  -- Some component `x` of `S` outside the chain meets the chain, at a position `r`.
  obtain ⟨b₀, hmem, x, hxS, hxA, hpos⟩ :=
    hconn A hAsub ⟨c 0, mem_A.mpr ⟨0, ht, rfl⟩⟩ hAS
  obtain ⟨r, hr, rfl⟩ := mem_A.mp hmem
  have hx_ne : ∀ i < t, x ≠ c i := fun i hi h ↦ hxA (mem_A.mpr ⟨i, hi, h.symm⟩)
  have hx_self := hS x hxS
  obtain ⟨hr0, hrt⟩ := hc.pos_and_lt_of_intersection_pos hcS hmax hxS hx_ne hx_self hr hpos
  have hAcard : #A = t := hc.card_image_range
  have hcard₁ : t + 1 < Fintype.card T.Component := by
    have := card_le_card (insert_subset hxS hAsub)
    rw [card_insert_of_notMem hxA, hAcard] at this
    omega
  -- `x` meets no other component of the chain.
  have hx_zero : ∀ i < t, i ≠ r → T.intersection (c i) x = 0 :=
    fun i hi hir ↦ hc.intersection_eq_zero_of_ne_of_intersection_pos hcS hmax hxS hx_ne hx_self
      hr hpos hi hir
  -- The chain and `x` exhaust `S`.
  have hS_eq : insert x A = S := by
    by_contra hne
    obtain ⟨b, hb, y, hyS, hyB, hby⟩ :=
      hconn (insert x A) (insert_subset hxS hAsub) (insert_nonempty _ _) hne
    have hyx : y ≠ x := fun h ↦ hyB (h ▸ mem_insert_self _ _)
    have hyA : y ∉ A := fun h ↦ hyB (mem_insert_of_mem h)
    have hy_ne : ∀ i < t, y ≠ c i := fun i hi h ↦ hyA (mem_A.mpr ⟨i, hi, h.symm⟩)
    have hy_self := hS y hyS
    have hcard₂ : t + 2 < Fintype.card T.Component := by
      have := card_le_card (insert_subset hyS (insert_subset hxS hAsub))
      rw [card_insert_of_notMem hyB, card_insert_of_notMem hxA, hAcard] at this
      omega
    rcases mem_insert.mp hb with hbx | hbA
    · -- `x` has a second neighbour `y` in `S`. By maximality, `x` has at least two chain
      -- components on either side, so it is a leaf of an affine `E₆` diagram.
      rw [hbx] at hby
      have hr2 := hc.two_le_of_intersection_pos hcS hmax hxS hx_ne hx_self hyS hy_ne hy_self
        hyx hr hpos hby
      have hrev : t - 1 - (t - 1 - r) = r := by omega
      have hrt2 := hc.reverse.two_le_of_intersection_pos (fun i hi ↦ hcS _ (by omega)) hmax
        hxS (fun i hi ↦ hx_ne _ (by omega)) hx_self hyS (fun i hi ↦ hy_ne _ (by omega)) hy_self
        hyx (r := t - 1 - r) (by omega) (by simpa [T.intersection_comm, hrev] using hpos) hby
      have h := hc.intersection_eq_zero_of_leaf hcard₂ hyx.symm hx_ne hy_ne hx_self hy_self
        (by omega) (by omega) hpos
      omega
    · -- `y` meets the chain at a position `s`; together with `x` this gives two leaves.
      obtain ⟨s, hs, rfl⟩ := mem_A.mp hbA
      obtain ⟨hs0, hst⟩ := hc.pos_and_lt_of_intersection_pos hcS hmax hyS hy_ne hy_self hs hby
      rcases le_total r s with hrs | hsr
      · exact hc.false_of_two_leaves hcard₂ hyx.symm hx_ne hy_ne hx_self hy_self hr0 hrs hst
          hpos hby
      · exact hc.false_of_two_leaves hcard₂ hyx hy_ne hx_ne hy_self hx_self hs0 hsr hrt hby hpos
  -- Reversing a chain preserves its component set, by Mathlib's reversal of `range`.
  have hS_eq_rev : insert x ((range t).image fun i ↦ c (t - 1 - i)) = S := by
    have himage : (range t).image (fun i ↦ c (t - 1 - i)) = A := by
      rw [hA_def]
      simpa only [image_image, Function.comp_def] using
        congrArg (fun s : Finset ℕ ↦ s.image c) (range_image_pred_top_sub t)
    rwa [himage]
  -- Read in the appropriate direction, the leaf `x` sits at a fork or an exceptional position.
  right
  by_cases hfork_right : r = t - 2
  · exact .inl ⟨t, c, x, ⟨hc, by omega, hx_ne, hx_self, hfork_right ▸ hpos⟩, hS_eq⟩
  by_cases hfork_left : r = 1
  · refine .inl ⟨t, fun i ↦ c (t - 1 - i), x, ⟨hc.reverse, by omega,
      fun i hi ↦ hx_ne _ (by omega), hx_self, ?_⟩, ?_⟩
    · have hrev : t - 1 - (t - 2) = r := by omega
      simpa [hrev] using hpos
    · exact hS_eq_rev
  right
  by_cases hdir : 2 * r + 1 ≤ t
  · obtain ⟨rfl, ht7⟩ := hc.eq_two_and_le_seven hcard₁ hx_ne hx_self (by omega) hdir hpos
    refine ⟨t, fun i ↦ c (t - 1 - i), x, hc.reverse, by omega, ht7,
      fun i hi ↦ hx_ne _ (by omega), hx_self, ?_, ?_, ?_⟩
    · have hrev : t - 1 - (t - 3) = 2 := by omega
      simpa [hrev] using hpos
    · intro i hi hi3
      exact hx_zero _ (by omega) (by omega)
    · exact hS_eq_rev
  · have hpos' : 0 < T.intersection (c (t - 1 - (t - 1 - r))) x := by
      have hrev : t - 1 - (t - 1 - r) = r := by omega
      rwa [hrev]
    obtain ⟨h2, ht7⟩ := hc.reverse.eq_two_and_le_seven hcard₁ (fun i hi ↦ hx_ne _ (by omega))
      hx_self (by omega) (by omega) hpos'
    have hr : r = t - 3 := by omega
    exact ⟨t, c, x, hc, by omega, ht7, hx_ne, hx_self, by simpa [hr] using hpos,
      fun i hi hi3 ↦ hx_zero i hi (by omega), hS_eq⟩

open _root_.Matrix

namespace IsSelfIntersectionMinusTwoChain

variable {t : ℕ} {c : ℕ → T.Component}

/-! ### Exhibiting star and affine `E` configurations -/

/-- A chain and an injective family outside it give an injective map from their disjoint sum. -/
private lemma injective_sumElim (hc : T.IsSelfIntersectionMinusTwoChain t c)
    {ι : Type*} {b : ι → T.Component} (hb : Function.Injective b)
    (hb_ne : ∀ j i, i < t → b j ≠ c i) :
    Function.Injective (Sum.elim (fun i : Fin t ↦ c i) b) := by
  apply Function.Injective.sumElim
  · intro i j hij
    exact Fin.ext (hc.injOn i i.isLt j j.isLt hij)
  · exact hb
  · exact fun i j ↦ (hb_ne j i i.isLt).symm

/-- Intersections for a chain with extra vertices reduce to consecutive chain positions and
intersections involving the extra vertices. -/
private lemma intersection_pos_sumElim (hc : T.IsSelfIntersectionMinusTwoChain t c)
    {ι : Type*} (b : ι → T.Component) (i j : Fin t ⊕ ι)
    (h : match i, j with
      | .inl i, .inl j => (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
      | .inl i, .inr j => 0 < T.intersection (c i) (b j)
      | .inr i, .inl j => 0 < T.intersection (c j) (b i)
      | .inr i, .inr j => 0 < T.intersection (b i) (b j)) :
    0 < T.intersection (Sum.elim (fun i : Fin t ↦ c i) b i)
      (Sum.elim (fun i : Fin t ↦ c i) b j) := by
  rcases i with i | i <;> rcases j with j | j
  · rcases h with h | h
    · exact hc.intersection_pos h.symm j.isLt
    · rw [T.intersection_comm]
      exact hc.intersection_pos h.symm i.isLt
  · exact h
  · simpa only [Sum.elim_inr, Sum.elim_inl, T.intersection_comm] using h
  · exact h

/-- Embed a finite graph by selecting chain positions and extra vertices. Only increasing
adjacent pairs need to be checked; injectivity and symmetry are handled uniformly. -/
private lemma exists_graph_map_sumElim (hc : T.IsSelfIntersectionMinusTwoChain t c)
    {ι : Type*} (b : ι → T.Component) (hb : Function.Injective b)
    (hb_ne : ∀ j i, i < t → b j ≠ c i) {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : Fin n → Fin t ⊕ ι) (hp : Function.Injective p)
    (h : ∀ u v, u < v → G.Adj u v →
      match p u, p v with
      | .inl i, .inl j => (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
      | .inl i, .inr j => 0 < T.intersection (c i) (b j)
      | .inr i, .inl j => 0 < T.intersection (c j) (b i)
      | .inr i, .inr j => 0 < T.intersection (b i) (b j)) :
    ∃ l : Fin n → T.Component, Function.Injective l ∧
      ∀ i j, G.Adj i j → T.Adj (l i) (l j) := by
  let l := Sum.elim (fun i : Fin t ↦ c i) b ∘ p
  have hl : Function.Injective l := (hc.injective_sumElim hb hb_ne).comp hp
  refine ⟨l, hl, fun i j hij ↦ T.adj_iff.mpr ⟨hl.ne hij.ne, ?_⟩⟩
  exact T.intersection_pos_of_adj_of_forall_lt
    (fun u v huv huv_adj ↦ hc.intersection_pos_sumElim b (p u) (p v) (h u v huv huv_adj)) hij

/-- A chain component `c r` (`0 < r` and `r + 1 < t`) meeting two distinct components `x` and `y`
outside the chain forms a four-leaf star with leaves `c (r - 1)`, `c (r + 1)`, `x` and `y`. -/
private lemma exists_fourLeafStar (hc : T.IsSelfIntersectionMinusTwoChain t c) {r : ℕ}
    (hr0 : 0 < r) (hrt : r + 1 < t) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx : 0 < T.intersection (c r) x) (hy : 0 < T.intersection (c r) y) :
    ∃ c₀ : T.Component, ∃ l : Fin 4 → T.Component,
      Function.Injective l ∧ ∀ i, T.Adj c₀ (l i) := by
  let p : Fin 5 → Fin t ⊕ Fin 2 :=
    ![.inl ⟨r, by omega⟩, .inl ⟨r - 1, by omega⟩, .inl ⟨r + 1, by omega⟩,
      .inr 0, .inr 1]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢ <;> omega
  obtain ⟨l, hl, hadj⟩ := hc.exists_graph_map_sumElim (![x, y])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro j i hi; fin_cases j; exacts [hx_ne i hi, hy_ne i hi])
    (G := SimpleGraph.starGraph (0 : Fin 5)) p hp (by
      intro u v huv h
      fin_cases u <;> fin_cases v
      all_goals norm_num [Fin.lt_def] at huv
      all_goals norm_num [SimpleGraph.starGraph_adj] at h
      all_goals simp [p]
      all_goals omega)
  exact ⟨l 0, fun i ↦ l i.succ, hl.comp (Fin.succ_injective 4),
    fun i ↦ hadj 0 i.succ (SimpleGraph.starGraph_center_adj (Fin.succ_ne_zero i).symm)⟩

/-- A chain component `c r` (`2 ≤ r` and `r + 3 ≤ t`) meeting `x` outside the chain, which in turn
meets `y` outside the chain, produces the seven-component affine `E₆` configuration. -/
private lemma exists_affineE6 (hc : T.IsSelfIntersectionMinusTwoChain t c) {r : ℕ}
    (hr : 2 ≤ r) (hrt : r + 3 ≤ t) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx : 0 < T.intersection (c r) x) (hxy_pos : 0 < T.intersection x y) :
    ∃ l : Fin 7 → T.Component, Function.Injective l ∧
      ∀ i j, AffineDynkinType.E6.graph.Adj i j → T.Adj (l i) (l j) := by
  let p : Fin 7 → Fin t ⊕ Fin 2 :=
    ![.inl ⟨r, by omega⟩, .inl ⟨r - 1, by omega⟩,
      .inl ⟨r - 2, by omega⟩, .inl ⟨r + 1, by omega⟩,
      .inl ⟨r + 2, by omega⟩, .inr 0,
      .inr 1]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢ <;> omega
  apply hc.exists_graph_map_sumElim (![x, y])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro j i hi; fin_cases j; exacts [hx_ne i hi, hy_ne i hi])
    (G := AffineDynkinType.E6.graph) p hp
  intro u v huv h
  fin_cases u <;> fin_cases v
  all_goals norm_num [Fin.lt_def] at huv
  all_goals norm_num [AffineDynkinType.graph_E6_adj] at h
  all_goals simp [p]
  all_goals omega

/-- A chain component `c r` (`3 ≤ r` and `r + 4 ≤ t`) meeting `x` outside the chain produces the
eight-component affine `E₇` configuration. -/
private lemma exists_affineE7 (hc : T.IsSelfIntersectionMinusTwoChain t c) {r : ℕ}
    (hr : 3 ≤ r) (hrt : r + 4 ≤ t) {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i)
    (hx : 0 < T.intersection (c r) x) :
    ∃ l : Fin 8 → T.Component, Function.Injective l ∧
      ∀ i j, AffineDynkinType.E7.graph.Adj i j → 0 < T.intersection (l i) (l j) := by
  let p : Fin 8 → Fin t ⊕ Fin 1 :=
    ![.inl ⟨r, by omega⟩, .inr 0,
      .inl ⟨r - 1, by omega⟩, .inl ⟨r - 2, by omega⟩,
      .inl ⟨r - 3, by omega⟩, .inl ⟨r + 1, by omega⟩,
      .inl ⟨r + 2, by omega⟩, .inl ⟨r + 3, by omega⟩]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢ <;> omega
  suffices h : ∃ l : Fin 8 → T.Component, Function.Injective l ∧
      ∀ i j, AffineDynkinType.E7.graph.Adj i j → T.Adj (l i) (l j) by
    obtain ⟨l, hl, hadj⟩ := h
    exact ⟨l, hl, fun i j hij ↦ (T.adj_iff.mp (hadj i j hij)).2⟩
  apply hc.exists_graph_map_sumElim (fun _ : Fin 1 ↦ x)
    (Function.injective_of_subsingleton _)
    (fun _ i hi ↦ hx_ne i hi) (G := AffineDynkinType.E7.graph) p hp
  intro u v huv h
  fin_cases u <;> fin_cases v
  all_goals norm_num [Fin.lt_def] at huv
  all_goals norm_num [AffineDynkinType.graph_E7_adj] at h
  all_goals simp [p]
  all_goals omega

/-- A chain `c 0, …, c (t - 1)` of length `8 ≤ t` with a leaf `x` outside the chain meeting `c 2`
produces the nine-component affine `E₈` configuration. -/
private lemma exists_affineE8 (hc : T.IsSelfIntersectionMinusTwoChain t c) (ht : 8 ≤ t)
    {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i) (hx : 0 < T.intersection (c 2) x) :
    ∃ l : Fin 9 → T.Component, Function.Injective l ∧
      ∀ i j, AffineDynkinType.E8.graph.Adj i j → 0 < T.intersection (l i) (l j) := by
  let p : Fin 9 → Fin t ⊕ Fin 1 :=
    ![.inl ⟨2, by omega⟩, .inr 0,
      .inl ⟨1, by omega⟩, .inl ⟨0, by omega⟩,
      .inl ⟨3, by omega⟩, .inl ⟨4, by omega⟩,
      .inl ⟨5, by omega⟩, .inl ⟨6, by omega⟩,
      .inl ⟨7, by omega⟩]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢
  suffices h : ∃ l : Fin 9 → T.Component, Function.Injective l ∧
      ∀ i j, AffineDynkinType.E8.graph.Adj i j → T.Adj (l i) (l j) by
    obtain ⟨l, hl, hadj⟩ := h
    exact ⟨l, hl, fun i j hij ↦ (T.adj_iff.mp (hadj i j hij)).2⟩
  apply hc.exists_graph_map_sumElim (fun _ : Fin 1 ↦ x)
    (Function.injective_of_subsingleton _)
    (fun _ i hi ↦ hx_ne i hi) (G := AffineDynkinType.E8.graph) p hp
  intro u v huv h
  fin_cases u <;> fin_cases v
  all_goals norm_num [Fin.lt_def] at huv
  all_goals norm_num [AffineDynkinType.graph_E8_adj] at h
  all_goals simp [p]
  all_goals omega

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
    have hr_s : r - 1 + (s - r + 1) = s := by omega
    have hr_one : r - 1 + 1 = r := by omega
    have hrf : T.IsSelfIntersectionMinusTwoFork (s - r + 3) (fun k ↦ c (r - 1 + k)) y :=
      ⟨hd, by omega, fun i hi ↦ hy_ne _ (by omega), hy_self,
        by simpa [hr_s] using hy⟩
    have hlf : T.IsSelfIntersectionMinusTwoFork (s - r + 3)
        (fun i ↦ c (r - 1 + (s - r + 3 - 1 - i))) x :=
      ⟨hd.reverse, by omega, fun i hi ↦ hx_ne _ (by omega), hx_self,
        by simpa [hr_one] using hx⟩
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
  · exact (hc.card_ne_add_one_of_branch_two (by omega) (by omega)
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
    · exact .inl (hc.topologicalGenus_pos_of_card_eq_of_intersection_pos hcard hends.1 hends.2)
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
    by_cases hfork_right : r = t - 2
    · have hfork : ∃ t c b, Fintype.card T.Component = t + 1 ∧
          T.IsSelfIntersectionMinusTwoFork t c b :=
        ⟨t, c, x, hcard, hc, by omega, hx_ne, hself x, hfork_right ▸ hpos⟩
      itauto
    by_cases hfork_left : r = 1
    · have hfork : ∃ t c b, Fintype.card T.Component = t + 1 ∧
          T.IsSelfIntersectionMinusTwoFork t c b := by
        refine ⟨t, fun i ↦ c (t - 1 - i), x, hcard, hc.reverse, by omega,
          fun i hi ↦ hx_ne _ (by omega), hself x, ?_⟩
        have hreverse : t - 1 - (t - 2) = r := by omega
        simpa [hreverse] using hpos
      itauto
    by_cases hdir : 2 * r + 1 ≤ t
    · have hE := hc.exists_affineE7_or_affineE8_of_card_eq_succ hcard hx_ne (hself x)
        (by omega) hdir hpos hx_zero
      itauto
    · have hreverse : t - 1 - (t - 1 - r) = r := by omega
      have hpos' : 0 < T.intersection (c (t - 1 - (t - 1 - r))) x := by
        simpa [hreverse] using hpos
      have hE := hc.reverse.exists_affineE7_or_affineE8_of_card_eq_succ hcard
        (fun i hi ↦ hx_ne _ (by omega)) (hself x) (by omega) (by omega) hpos'
        fun i hi hir ↦ hx_zero _ (by omega) (by omega)
      itauto
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
      have hreverse : t - 1 - (t - 1 - r) = r := by omega
      have hrt2 := hc.reverse.two_le_of_intersection_pos (fun i hi ↦ hcU _ (by omega)) hmax
        (mem_univ x) (fun i hi ↦ hx_ne _ (by omega)) (hself x) (mem_univ y)
        (fun i hi ↦ hy_ne _ (by omega)) (hself y) hyx (r := t - 1 - r) (by omega)
        (by simpa [hreverse] using hpos) hby
      have hE := hc.exists_affineE6 hr2 (by omega) hyx.symm hx_ne hy_ne hpos hby
      itauto
    · -- `y` meets `c s`, producing either a four-leaf star or an exhaustive double fork.
      obtain ⟨s, hs, rfl⟩ := mem_A.mp hbA
      obtain ⟨hs0, hst⟩ := hc.pos_and_lt_of_intersection_pos hcU hmax (mem_univ y) hy_ne
        (hself y) hs hby
      rcases le_total r s with hrs | hsr
      · rcases hc.exists_fourLeafStar_or_doubleFork hcard₂ hyx.symm hx_ne hy_ne (hself x)
            (hself y) hr0 hrs hst hpos hby with hstar | hdouble
        · itauto
        · itauto
      · rcases hc.exists_fourLeafStar_or_doubleFork hcard₂ hyx hy_ne hx_ne (hself y)
            (hself x) hs0 hsr hrt hby hpos with hstar | hdouble
        · itauto
        · itauto

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

end NumericalType

end TauCeti
