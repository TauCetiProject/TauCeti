/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Branch
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.DoubleFork
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.E8
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Exceptional
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Connected proper sets of `(-2)`-indices

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
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.intersection_eq_zero_of_card_eq`: in an
  exhaustive chain whose endpoints do not meet when `2 < t`, nonconsecutive components do not meet.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.not_card_eq_succ_of_branch_two`: the
  exceptional configuration of `5 ≤ t ≤ 7` chain components with a leaf at `c 2` cannot exhaust a
  numerical type.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.exists_lt_eq_of_card_eq`,
  `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.eq_or_exists_lt_eq_of_card_eq` and
  `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.eq_or_eq_or_exists_lt_eq_of_card_eq`:
  decomposition of any component in a numerical type exhausted by a chain, a fork, or a double
  fork.

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
    simpa [show 1 + (r - 1) = r by omega] using hx
  have hix' : 0 < T.intersection (c (1 + (i - 1))) x := by
    simpa [show 1 + (i - 1) = i by omega] using hix
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

/-- In a chain exhausting all components of a numerical type, any two nonconsecutive components
other than the pair of endpoints do not meet, because the subchain between them is proper. If the
endpoints do not meet when `2 < t`, then no two nonconsecutive components meet. -/
lemma intersection_eq_zero_of_card_eq (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : Fintype.card T.Component = t)
    (hends : 2 < t → T.intersection (c 0) (c (t - 1)) = 0) (i : ℕ) (hi : i < t) (j : ℕ)
    (hj : j < t) (hij : i ≠ j) (hij₁ : i + 1 ≠ j) (hji₁ : j + 1 ≠ i) :
    T.intersection (c i) (c j) = 0 := by
  have hlt : ∀ u v : ℕ, u + 1 < v → v < t → T.intersection (c u) (c v) = 0 := by
    intro u v huv hv
    by_cases he : u = 0 ∧ v = t - 1
    · rcases he with ⟨rfl, rfl⟩
      exact hends (by omega)
    · have hsub := (hc.shift (r := u) (s := v - u + 1) (by omega)).intersection_eq_zero
        (by omega) (p := 0) (q := v - u) (by omega) (by omega) (by omega) (by omega) (by omega)
      simpa [show u + (v - u) = v by omega] using hsub
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j (by omega) hj
  · rw [T.intersection_comm]
    exact hlt j i (by omega) hi

/-- A chain `c 0, …, c (t - 1)` of length `5 ≤ t ≤ 7` together with a single leaf `x` at `c 2`
cannot exhaust a numerical type: the five-component subfork on `c 0, c 1, c 2, c 3, x` and the
chain classification fix all weights below `t - 1`, and the resulting fibre relations on the
multiplicities are incompatible at the right end of the chain. -/
lemma not_card_eq_succ_of_branch_two (hc : T.IsSelfIntersectionMinusTwoChain t c)
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
  have hedge_prev (i : ℕ) (hi0 : 0 < i) (hi : i < t - 1) :
      T.intersection (c (i - 1)) (c i) = w := by
    simpa [Nat.sub_add_cancel hi0] using hedge (i - 1) (by omega)
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
  -- Interior fibre relation at `c i` (`0 < i` and `i + 1 < t - 1`).
  have hint (i : ℕ) (hi0 : 0 < i) (hit : i + 1 < t - 1) :
      (w : ℤ) * T.multiplicity (c (i - 1)) - 2 * w * T.multiplicity (c i) +
        w * T.multiplicity (c (i + 1)) + T.intersection (c i) x * T.multiplicity x = 0 := by
    have h := hfib (c i)
    rw [hc.interior_sum_eq hchainCard _ hi0 (by omega),
      T.intersection_comm (c i) (c (i - 1)), hedge_prev i hi0 (by omega),
      hc.intersection_self i (by omega), hw i (by omega), hedge i hit] at h
    linear_combination h
  have hm2 : (T.multiplicity (c 0) : ℤ) + T.multiplicity (c 2) = 2 * T.multiplicity (c 1) := by
    have h := hint 1 (by omega) (by omega)
    rw [hx_zero 1 (by omega) (by omega), zero_mul, add_zero] at h
    exact mul_left_cancel₀ hw_ne (by linear_combination h)
  have hm3 : (T.multiplicity (c 1) : ℤ) + T.multiplicity (c 3) + T.multiplicity x =
      2 * T.multiplicity (c 2) := by
    have h := hint 2 (by omega) (by omega)
    rw [h2x] at h
    exact mul_left_cancel₀ hw_ne (by linear_combination h)
  have hrec (i : ℕ) (hi2 : 2 < i) (hit : i + 1 < t - 1) :
      (T.multiplicity (c (i - 1)) : ℤ) + T.multiplicity (c (i + 1)) =
        2 * T.multiplicity (c i) := by
    have h := hint i (by omega) hit
    rw [hx_zero i (by omega) (by omega), zero_mul, add_zero] at h
    exact mul_left_cancel₀ hw_ne (by linear_combination h)
  -- Fibre relations at `c (t - 2)` and `c (t - 1)`.
  have hpen := hfib (c (t - 2))
  rw [hc.interior_sum_eq hchainCard _ (by omega) (by omega),
    T.intersection_comm (c (t - 2)) (c (t - 2 - 1)), hedge_prev (t - 2) (by omega) (by omega),
    show t - 2 - 1 = t - 3 by omega, show t - 2 + 1 = t - 1 by omega,
    hc.intersection_self (t - 2) (by omega), hw (t - 2) (by omega),
    hx_zero (t - 2) (by omega) (by omega), zero_mul, add_zero] at hpen
  have hlast := hfib (c (t - 1))
  rw [hc.right_sum_eq hchainCard (by omega), T.intersection_comm (c (t - 1)) (c (t - 2)),
    hc.intersection_self (t - 1) (by omega), hx_zero (t - 1) (by omega) (by omega),
    zero_mul, add_zero] at hlast
  have ha_last : T.intersection (c (t - 2)) (c (t - 1)) =
      max (w : ℤ) (T.weight (c (t - 1)) : ℤ) := by
    have h := T.intersection_eq_max_weight (by omega)
      (hc.intersection_self (t - 2) (by omega)) (hc.intersection_self (t - 1) (by omega))
      (hc.intersection_pos (by omega) (by omega))
    rwa [hw (t - 2) (by omega)] at h
  have hendRel : 2 * (T.multiplicity (c (t - 3)) : ℤ) = 3 * T.multiplicity (c (t - 2)) ∨
      (T.multiplicity (c (t - 3)) : ℤ) = T.multiplicity (c (t - 2)) := by
    have hwpos : (0 : ℤ) < w := by positivity
    have h2w_ne : (2 * (w : ℤ)) ≠ 0 := by positivity
    rcases hright with hright | hright | hright
    · left
      rw [ha_last, hright, max_self] at hpen hlast
      exact mul_left_cancel₀ hw_ne (by linear_combination 2 * hpen + hlast)
    · right
      rw [ha_last, hright, max_eq_right (by omega)] at hpen hlast
      exact mul_left_cancel₀ h2w_ne (by linear_combination 2 * hpen + hlast)
    · right
      rw [ha_last, max_eq_left (by omega)] at hpen hlast
      exact mul_left_cancel₀ hw_ne
        (by linear_combination hpen + hlast + (T.multiplicity (c (t - 1)) : ℤ) * hright)
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

/-- Every component of a numerical type exhausted by a chain `c` of length `t` has the form `c i`
for some `i < t`. -/
lemma IsSelfIntersectionMinusTwoChain.exists_lt_eq_of_card_eq {t : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain t c) (hcard : Fintype.card T.Component = t)
    (v : T.Component) : ∃ i < t, c i = v := by
  classical
  have hu : (range t).image c = univ := eq_univ_of_card _ (by rw [hc.card_image_range, hcard])
  simpa [← hu] using mem_univ v

/-- Every component of a numerical type exhausted by a fork `(c, b)` of chain length `t` is either
`b` or `c i` for some `i < t`. -/
lemma IsSelfIntersectionMinusTwoFork.eq_or_exists_lt_eq_of_card_eq {t : ℕ} {c : ℕ → T.Component}
    {b : T.Component} (hf : T.IsSelfIntersectionMinusTwoFork t c b)
    (hcard : Fintype.card T.Component = t + 1) (v : T.Component) :
    v = b ∨ ∃ i < t, c i = v := by
  classical
  have hb_notMem : b ∉ (range t).image c := by
    simp only [mem_image, mem_range, not_exists, not_and]
    exact fun i hi h ↦ hf.branch_ne i hi h.symm
  have hu : insert b ((range t).image c) = univ :=
    eq_univ_of_card _ (by rw [card_insert_of_notMem hb_notMem, hf.card_image_range, hcard])
  simpa [← hu] using mem_univ v

/-- Every component of a numerical type exhausted by a double fork `(c, left, right)` of chain
length `t ≥ 4` is `left`, `right`, or `c i` for some `i < t`. -/
lemma IsSelfIntersectionMinusTwoFork.eq_or_eq_or_exists_lt_eq_of_card_eq {t : ℕ}
    {c : ℕ → T.Component} {left right : T.Component}
    (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left) (ht : 4 ≤ t)
    (hcard : Fintype.card T.Component = t + 2) (v : T.Component) :
    v = left ∨ v = right ∨ ∃ i < t, c i = v := by
  classical
  have hleft_ne (i : ℕ) (hi : i < t) : left ≠ c i := by
    simpa only [show t - 1 - (t - 1 - i) = i by omega] using hl.branch_ne (t - 1 - i) (by omega)
  have hlr : left ≠ right := by
    rintro rfl
    have hpos : 0 < T.intersection (c 1) left := by
      simpa only [show t - 1 - (t - 2) = 1 by omega] using hl.branch_intersection_pos
    rw [hr.branch_intersection_eq_zero (by omega) (by omega)] at hpos
    exact lt_irrefl 0 hpos
  have hr_notMem : right ∉ (range t).image c := by
    simp only [mem_image, mem_range, not_exists, not_and]
    exact fun i hi h ↦ hr.branch_ne i hi h.symm
  have hl_notMem : left ∉ insert right ((range t).image c) := by
    simp only [mem_insert, mem_image, mem_range, not_or, not_exists, not_and]
    exact ⟨hlr, fun i hi h ↦ hleft_ne i hi h.symm⟩
  have hu : insert left (insert right ((range t).image c)) = univ :=
    eq_univ_of_card _ (by
      rw [card_insert_of_notMem hl_notMem, card_insert_of_notMem hr_notMem,
        hr.card_image_range, hcard])
  simpa [← hu] using mem_univ v

/-- Any numerical type in which every component has self-intersection `-2w` has at least two
components. -/
lemma one_lt_card_of_intersection_self_eq
    (hself : ∀ i, T.intersection i i = -(2 * (T.weight i : ℤ))) :
    1 < Fintype.card T.Component := by
  have hpos : 0 < Fintype.card T.Component := Fintype.card_pos
  by_contra! hle
  have hcard : Fintype.card T.Component = 1 := by omega
  obtain ⟨i⟩ := T.componentNonempty
  have h0 := T.intersection_eq_zero_of_card_eq_one hcard i i
  have hw := (T.weight i).pos
  have := hself i
  omega

end NumericalType

end TauCeti
