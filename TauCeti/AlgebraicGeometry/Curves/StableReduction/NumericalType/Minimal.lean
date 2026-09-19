/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Minimal numerical types and their genus contributions

The signed genus of a numerical type `T` is a sum of contributions of its components,

`g(T) = 1 + ∑ᵢ Φᵢ`, where `Φᵢ = mᵢ (wᵢ (gᵢ - 1) - aᵢᵢ / 2)`.

As soon as `T` has more than one component, the sign of a single contribution is controlled by
the component alone: `Φᵢ < 0` exactly when `gᵢ = 0` and `aᵢᵢ = -wᵢ`, a *`(-1)`-index*, and
`Φᵢ = 0` exactly when `gᵢ = 0` and `aᵢᵢ = -2wᵢ`, a *`(-2)`-index*. On a proper regular model
these are the numerical shadows of exceptional curves of the first kind and of `(-2)`-curves.
A numerical type is *minimal* when it has no `(-1)`-index, so that every contribution is
nonnegative.

This file develops that analysis and the resulting bounds on minimal numerical types: in a
minimal type of genus `g` with more than one component, there are at most `2g - 2` components
that are not `(-2)`-indices, every component genus is below `g`, and the multiplicity-weighted
self-intersection and pairwise intersection numbers at a component that is not a `(-2)`-index
are at most `6g - 6`. These are the first steps of the bound on the multiplicities of a minimal
numerical type which, in the Artin–Winters argument, bounds the `ℓ`-torsion of its Picard group.

## Main definitions

* `TauCeti.NumericalType.IsMinusOneIndex`: `gᵢ = 0` and `aᵢᵢ = -wᵢ`.
* `TauCeti.NumericalType.IsMinusTwoIndex`: `gᵢ = 0` and `aᵢᵢ = -2wᵢ`.
* `TauCeti.NumericalType.IsMinimal`: there is no `(-1)`-index.
* `TauCeti.NumericalType.genusContribution`: the contribution `Φᵢ` of a component to the signed
  genus, a rational number which need not be an integer.

## Main results

* `TauCeti.NumericalType.arithmeticGenus_eq_one_add_sum_genusContribution`: `g = 1 + ∑ᵢ Φᵢ`.
* `TauCeti.NumericalType.genusContribution_neg_iff` and
  `TauCeti.NumericalType.genusContribution_eq_zero_iff`: with more than one component, the
  negative contributions are those of the `(-1)`-indices and the zero contributions those of the
  `(-2)`-indices ([Stacks, Tag 0C75](https://stacks.math.columbia.edu/tag/0C75) and
  [Stacks, Tag 0C7D](https://stacks.math.columbia.edu/tag/0C7D)).
* `TauCeti.NumericalType.IsMinimal.one_le_arithmeticGenus`: a minimal numerical type with more
  than one component has genus at least one
  ([Stacks, Tag 0C7B](https://stacks.math.columbia.edu/tag/0C7B)).
* `TauCeti.NumericalType.IsMinimal.card_filter_not_isMinusTwoIndex_le`,
  `TauCeti.NumericalType.IsMinimal.genus_lt_arithmeticGenus`,
  `TauCeti.NumericalType.IsMinimal.multiplicity_mul_abs_intersection_self_le` and
  `TauCeti.NumericalType.IsMinimal.multiplicity_mul_intersection_le`: the four bounds on a minimal
  numerical type listed above ([Stacks, Tag 0C9V](https://stacks.math.columbia.edu/tag/0C9V)).

## References

The statements follow the sections [*Numerical types*](https://stacks.math.columbia.edu/tag/0C6Y)
and [*Bounding invariants of numerical types*](https://stacks.math.columbia.edu/tag/0C9T) of the
Stacks Project chapter on semistable reduction. The bounds of
[Stacks, Tag 0C9V](https://stacks.math.columbia.edu/tag/0C9V) are stated there for genus at least
two; the arguments do not use that hypothesis, and the second bound is stated there only for
components that are not `(-2)`-indices, which is not needed either.
-/

public section

namespace TauCeti

namespace NumericalType

open Finset

universe u v

variable (T : NumericalType.{u})

/-! ### Special indices and minimality -/

/-- A component of a numerical type is a `(-1)`-index when its genus is zero and its
self-intersection is minus its weight
([Stacks, Tag 0C76](https://stacks.math.columbia.edu/tag/0C76)). -/
def IsMinusOneIndex (i : T.Component) : Prop :=
  T.genus i = 0 ∧ T.intersection i i = -(T.weight i : ℤ)

/-- A component of a numerical type is a `(-2)`-index when its genus is zero and its
self-intersection is minus twice its weight
([Stacks, Tag 0C7E](https://stacks.math.columbia.edu/tag/0C7E)). -/
def IsMinusTwoIndex (i : T.Component) : Prop :=
  T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ))

/-- A numerical type is minimal when it has no `(-1)`-index
([Stacks, Tag 0C7A](https://stacks.math.columbia.edu/tag/0C7A)). -/
def IsMinimal : Prop := ∀ i, ¬ T.IsMinusOneIndex i

/-- Unfolding of `TauCeti.NumericalType.IsMinusOneIndex`. -/
lemma isMinusOneIndex_iff {i : T.Component} :
    T.IsMinusOneIndex i ↔ T.genus i = 0 ∧ T.intersection i i = -(T.weight i : ℤ) := Iff.rfl

/-- Unfolding of `TauCeti.NumericalType.IsMinusTwoIndex`. -/
lemma isMinusTwoIndex_iff {i : T.Component} :
    T.IsMinusTwoIndex i ↔ T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)) :=
  Iff.rfl

instance : DecidablePred T.IsMinusOneIndex := fun _ ↦ decidable_of_iff _ T.isMinusOneIndex_iff.symm

instance : DecidablePred T.IsMinusTwoIndex := fun _ ↦ decidable_of_iff _ T.isMinusTwoIndex_iff.symm

/-- Unfolding of `TauCeti.NumericalType.IsMinimal`. -/
lemma isMinimal_iff : T.IsMinimal ↔ ∀ i, ¬ T.IsMinusOneIndex i := Iff.rfl

variable {C : Type v} (e : T.Component ≃ C)

/-- Reindexing preserves and reflects `(-1)`-indices. -/
@[simp]
lemma isMinusOneIndex_reindex (i : C) :
    (T.reindex e).IsMinusOneIndex i ↔ T.IsMinusOneIndex (e.symm i) := Iff.rfl

/-- Reindexing preserves and reflects `(-2)`-indices. -/
@[simp]
lemma isMinusTwoIndex_reindex (i : C) :
    (T.reindex e).IsMinusTwoIndex i ↔ T.IsMinusTwoIndex (e.symm i) := Iff.rfl

/-- Minimality is invariant under reindexing. -/
@[simp]
lemma isMinimal_reindex : (T.reindex e).IsMinimal ↔ T.IsMinimal := by
  constructor
  · intro h i hi
    exact h (e i) ((T.isMinusOneIndex_reindex e (e i)).mpr (by simpa using hi))
  · intro h i hi
    exact h (e.symm i) ((T.isMinusOneIndex_reindex e i).mp hi)

/-- A `(-2)`-index is not a `(-1)`-index. -/
lemma IsMinusTwoIndex.not_isMinusOneIndex {i : T.Component} (h : T.IsMinusTwoIndex i) :
    ¬ T.IsMinusOneIndex i := fun h' ↦ by
  have hw : (0 : ℤ) < T.weight i := Int.natCast_pos.mpr (T.weight i).pos
  have := h.2.symm.trans h'.2
  linarith

/-! ### Numerical types with one component -/

/-- A numerical type with a single component is minimal. -/
lemma isMinimal_of_card_eq_one (h : Fintype.card T.Component = 1) : T.IsMinimal := fun i hi ↦ by
  have hw : (0 : ℤ) < T.weight i := Int.natCast_pos.mpr (T.weight i).pos
  have := hi.2.symm.trans (T.intersection_eq_zero_of_card_eq_one h i i)
  linarith

/-- A numerical type with a component of nonzero self-intersection has more than one component. -/
lemma one_lt_card_of_intersection_self_ne_zero {i : T.Component}
    (h : T.intersection i i ≠ 0) : 1 < Fintype.card T.Component :=
  lt_of_le_of_ne Fintype.card_pos fun h1 ↦
    h (T.intersection_eq_zero_of_card_eq_one h1.symm i i)

/-- A numerical type with a `(-1)`-index has more than one component. -/
lemma IsMinusOneIndex.one_lt_card {i : T.Component} (h : T.IsMinusOneIndex i) :
    1 < Fintype.card T.Component :=
  T.one_lt_card_of_intersection_self_ne_zero <| by
    rw [(T.isMinusOneIndex_iff.mp h).2]
    have hw : (0 : ℤ) < T.weight i := Int.natCast_pos.mpr (T.weight i).pos
    omega

/-! ### Genus contributions -/

/-- The contribution `mᵢ (wᵢ (gᵢ - 1) - aᵢᵢ / 2)` of a component to the signed genus of a numerical
type. It is a half-integer, which need not be an integer. -/
def genusContribution (i : T.Component) : ℚ :=
  (T.multiplicity i : ℚ) * ((T.weight i : ℚ) * ((T.genus i : ℚ) - 1) - (T.intersection i i : ℚ) / 2)

/-- The defining formula of the contribution of a component to the signed genus. -/
lemma genusContribution_def (i : T.Component) :
    T.genusContribution i = (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.genus i : ℚ) - 1) - (T.intersection i i : ℚ) / 2) := by
  rw [genusContribution]

/-- Genus contributions are invariant under reindexing. -/
@[simp]
lemma genusContribution_reindex (i : C) :
    (T.reindex e).genusContribution i = T.genusContribution (e.symm i) := by
  simp only [genusContribution, reindex_multiplicity, reindex_weight, reindex_genus,
    reindex_intersection]

/-- The signed genus is one plus the sum of the contributions of the components. -/
lemma arithmeticGenus_eq_one_add_sum_genusContribution :
    (T.arithmeticGenus : ℚ) = 1 + ∑ i, T.genusContribution i := by
  have h := congrArg (Int.cast : ℤ → ℚ) T.two_mul_arithmeticGenus
  push_cast at h
  have hsum : ∑ i, T.genusContribution i =
      ∑ i, (T.multiplicity i : ℚ) * (T.weight i : ℚ) * ((T.genus i : ℚ) - 1) -
        (∑ i, (T.multiplicity i : ℚ) * (T.intersection i i : ℚ)) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [genusContribution]; ring
  rw [hsum]
  linarith

/-- Twice the contribution of a component whose self-intersection is `-k` times its weight. -/
private lemma two_mul_genusContribution_eq {i : T.Component} {k : ℕ}
    (hk : T.intersection i i = -((k : ℤ) * (T.weight i : ℤ))) :
    2 * T.genusContribution i =
      (T.multiplicity i : ℚ) * (T.weight i : ℚ) * (2 * (T.genus i : ℚ) + k - 2) := by
  rw [genusContribution, hk]
  push_cast
  ring

/-- With more than one component, the contribution of a component to the signed genus is negative
exactly when it is a `(-1)`-index ([Stacks, Tag 0C75](https://stacks.math.columbia.edu/tag/0C75)).
-/
theorem genusContribution_neg_iff (h : 1 < Fintype.card T.Component) (i : T.Component) :
    T.genusContribution i < 0 ↔ T.IsMinusOneIndex i := by
  obtain ⟨k, hk1, hk⟩ := T.exists_intersection_self_eq h i
  have he := T.two_mul_genusContribution_eq hk
  have hmw : (0 : ℚ) < (T.multiplicity i : ℚ) * (T.weight i : ℚ) := by positivity
  rw [isMinusOneIndex_iff, hk]
  constructor
  · intro hneg
    have hlt : 2 * (T.genus i : ℚ) + k - 2 < 0 := by
      by_contra hge
      nlinarith [mul_nonneg hmw.le (not_lt.mp hge)]
    have hlt' : 2 * T.genus i + k < 2 := by
      exact_mod_cast (by linarith : 2 * (T.genus i : ℚ) + k < 2)
    have hg : T.genus i = 0 := by omega
    have hk' : k = 1 := by omega
    subst hk'
    simp [hg]
  · rintro ⟨hg, hkw⟩
    have hk' : (k : ℤ) = 1 := by
      have hw : (0 : ℤ) < T.weight i := Int.natCast_pos.mpr (T.weight i).pos
      nlinarith
    have hk'' : k = 1 := by exact_mod_cast hk'
    subst hk''
    rw [hg] at he
    push_cast at he
    nlinarith

/-- With more than one component, the contribution of a component to the signed genus is zero
exactly when it is a `(-2)`-index ([Stacks, Tag 0C7D](https://stacks.math.columbia.edu/tag/0C7D)).
-/
theorem genusContribution_eq_zero_iff (h : 1 < Fintype.card T.Component) (i : T.Component) :
    T.genusContribution i = 0 ↔ T.IsMinusTwoIndex i := by
  obtain ⟨k, hk1, hk⟩ := T.exists_intersection_self_eq h i
  have he := T.two_mul_genusContribution_eq hk
  have hmw : (0 : ℚ) < (T.multiplicity i : ℚ) * (T.weight i : ℚ) := by positivity
  have hw : (0 : ℤ) < T.weight i := Int.natCast_pos.mpr (T.weight i).pos
  rw [isMinusTwoIndex_iff, hk]
  constructor
  · intro hzero
    rw [hzero, mul_zero] at he
    have hsum : 2 * (T.genus i : ℚ) + k - 2 = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left hmw.ne'
    have hsum' : 2 * T.genus i + k = 2 := by
      exact_mod_cast (by linarith : 2 * (T.genus i : ℚ) + k = 2)
    have hg : T.genus i = 0 := by omega
    have hk' : k = 2 := by omega
    subst hk'
    simp [hg]
  · rintro ⟨hg, hkw⟩
    have hk' : (k : ℤ) = 2 := by nlinarith
    have hk'' : k = 2 := by exact_mod_cast hk'
    subst hk''
    rw [hg] at he
    push_cast at he
    linarith

/-- With more than one component, the contribution of a component to the signed genus is
nonnegative exactly when it is not a `(-1)`-index. -/
lemma genusContribution_nonneg_iff (h : 1 < Fintype.card T.Component) (i : T.Component) :
    0 ≤ T.genusContribution i ↔ ¬ T.IsMinusOneIndex i := by
  rw [← T.genusContribution_neg_iff h, not_lt]

/-- With more than one component, a component that is neither a `(-1)`-index nor a `(-2)`-index
contributes at least `1 / 2` to the signed genus. -/
lemma one_half_le_genusContribution (h : 1 < Fintype.card T.Component) {i : T.Component}
    (h₁ : ¬ T.IsMinusOneIndex i) (h₂ : ¬ T.IsMinusTwoIndex i) :
    1 / 2 ≤ T.genusContribution i := by
  obtain ⟨k, hk1, hk⟩ := T.exists_intersection_self_eq h i
  have he := T.two_mul_genusContribution_eq hk
  have hm : (1 : ℚ) ≤ T.multiplicity i := by exact_mod_cast (T.multiplicity i).pos
  have hw : (1 : ℚ) ≤ T.weight i := by exact_mod_cast (T.weight i).pos
  have hnat : 3 ≤ 2 * T.genus i + k := by
    by_contra hlt
    rcases Nat.eq_zero_or_pos (T.genus i) with hg | hg
    · have hk3 : k < 3 := by omega
      interval_cases k
      · exact h₁ ⟨hg, by rw [hk]; ring⟩
      · exact h₂ ⟨hg, by rw [hk]; push_cast; ring⟩
    · omega
  have hq : (1 : ℚ) ≤ 2 * (T.genus i : ℚ) + k - 2 := by
    have : ((3 : ℕ) : ℚ) ≤ ((2 * T.genus i + k : ℕ) : ℚ) := by exact_mod_cast hnat
    push_cast at this
    linarith
  nlinarith [mul_le_mul hm hw zero_le_one (by linarith : (0 : ℚ) ≤ T.multiplicity i)]

/-! ### Minimal numerical types -/

namespace IsMinimal

variable {T}

/-- In a minimal numerical type with more than one component, every contribution to the signed
genus is nonnegative. -/
lemma genusContribution_nonneg (hT : T.IsMinimal) (h : 1 < Fintype.card T.Component)
    (i : T.Component) : 0 ≤ T.genusContribution i :=
  (T.genusContribution_nonneg_iff h i).mpr (hT i)

/-- In a minimal numerical type with more than one component, every contribution to the signed
genus is at most `g - 1`. -/
lemma genusContribution_le (hT : T.IsMinimal) (h : 1 < Fintype.card T.Component)
    (i : T.Component) : T.genusContribution i ≤ T.arithmeticGenus - 1 := by
  rw [T.arithmeticGenus_eq_one_add_sum_genusContribution, add_sub_cancel_left]
  exact Finset.single_le_sum (fun j _ ↦ hT.genusContribution_nonneg h j) (Finset.mem_univ i)

/-- A minimal numerical type with more than one component has signed genus at least one
([Stacks, Tag 0C7B](https://stacks.math.columbia.edu/tag/0C7B)). -/
theorem one_le_arithmeticGenus (hT : T.IsMinimal) (h : 1 < Fintype.card T.Component) :
    1 ≤ T.arithmeticGenus := by
  have hq : (1 : ℚ) ≤ T.arithmeticGenus := by
    rw [T.arithmeticGenus_eq_one_add_sum_genusContribution]
    linarith [Finset.sum_nonneg fun i (_ : i ∈ univ) ↦ hT.genusContribution_nonneg h i]
  exact_mod_cast hq

/-- A minimal numerical type of genus `g` with more than one component has at most `2g - 2`
components that are not `(-2)`-indices. -/
theorem card_filter_not_isMinusTwoIndex_le (hT : T.IsMinimal) (h : 1 < Fintype.card T.Component) :
    (#{i | ¬ T.IsMinusTwoIndex i} : ℤ) ≤ 2 * T.arithmeticGenus - 2 := by
  have hq : ((#{i | ¬ T.IsMinusTwoIndex i} : ℕ) : ℚ) ≤ 2 * T.arithmeticGenus - 2 := by
    have hsub : ∑ i ∈ {i | ¬ T.IsMinusTwoIndex i}, T.genusContribution i ≤
        ∑ i, T.genusContribution i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun i _ _ ↦ hT.genusContribution_nonneg h i
    have hlow : ∑ i ∈ {i | ¬ T.IsMinusTwoIndex i}, (1 / 2 : ℚ) ≤
        ∑ i ∈ {i | ¬ T.IsMinusTwoIndex i}, T.genusContribution i :=
      Finset.sum_le_sum fun i hi ↦
        T.one_half_le_genusContribution h (hT i) (Finset.mem_filter.mp hi).2
    rw [Finset.sum_const, nsmul_eq_mul] at hlow
    have hg := T.arithmeticGenus_eq_one_add_sum_genusContribution
    linarith
  exact_mod_cast hq

/-- In a minimal numerical type with more than one component, every component genus is smaller
than the signed genus. -/
theorem genus_lt_arithmeticGenus (hT : T.IsMinimal) (h : 1 < Fintype.card T.Component)
    (i : T.Component) : (T.genus i : ℤ) < T.arithmeticGenus := by
  rcases Nat.eq_zero_or_pos (T.genus i) with hg | hg
  · rw [hg, Nat.cast_zero]
    linarith [hT.one_le_arithmeticGenus h]
  · have hle := hT.genusContribution_le h i
    have hneg : (T.intersection i i : ℚ) < 0 := by exact_mod_cast T.intersection_self_neg h i
    have hm : (1 : ℚ) ≤ T.multiplicity i := by exact_mod_cast (T.multiplicity i).pos
    have hw : (1 : ℚ) ≤ T.weight i := by exact_mod_cast (T.weight i).pos
    have hg1 : (0 : ℚ) ≤ (T.genus i : ℚ) - 1 := by
      have : (1 : ℚ) ≤ T.genus i := by exact_mod_cast hg
      linarith
    have hmw : (1 : ℚ) ≤ (T.multiplicity i : ℚ) * (T.weight i : ℚ) := by nlinarith
    have hcontr : (T.genus i : ℚ) - 1 < T.genusContribution i := by
      rw [genusContribution]
      nlinarith [mul_le_mul_of_nonneg_right hmw hg1]
    have hq : (T.genus i : ℚ) < T.arithmeticGenus := by linarith
    exact_mod_cast hq

/-- In a minimal numerical type of genus `g` with more than one component, the weighted
self-intersection `mⱼ|aⱼⱼ|` of a component that is not a `(-2)`-index is at most `6g - 6`. -/
theorem multiplicity_mul_abs_intersection_self_le (hT : T.IsMinimal)
    (h : 1 < Fintype.card T.Component) {j : T.Component} (hj : ¬ T.IsMinusTwoIndex j) :
    (T.multiplicity j : ℤ) * |T.intersection j j| ≤ 6 * T.arithmeticGenus - 6 := by
  obtain ⟨k, hk1, hk⟩ := T.exists_intersection_self_eq h j
  have he := T.two_mul_genusContribution_eq hk
  have hle := hT.genusContribution_le h j
  set x : ℤ := (T.multiplicity j : ℤ) * (T.weight j : ℤ) with hx
  have hx1 : 1 ≤ x := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast (T.multiplicity j).pos) (by exact_mod_cast (T.weight j).pos)
  -- the contribution bound `Φⱼ ≤ g - 1`, cleared of denominators
  have hint : x * (2 * (T.genus j : ℤ) + k - 2) ≤ 2 * T.arithmeticGenus - 2 := by
    have hq : ((x * (2 * (T.genus j : ℤ) + k - 2) : ℤ) : ℚ) ≤
        ((2 * T.arithmeticGenus - 2 : ℤ) : ℚ) := by
      push_cast
      rw [hx]
      push_cast
      linarith
    exact_mod_cast hq
  have habs : (T.multiplicity j : ℤ) * |T.intersection j j| = x * k := by
    rw [hk, abs_neg, abs_of_nonneg (by positivity), hx]
    ring
  rw [habs]
  rcases Nat.eq_zero_or_pos (T.genus j) with hg | hg
  · -- a genus-zero component of a minimal type that is not a `(-2)`-index has `k ≥ 3`
    have hk3 : 3 ≤ k := by
      by_contra hlt
      interval_cases k
      · exact hT j ⟨hg, by rw [hk]; ring⟩
      · exact hj ⟨hg, by rw [hk]; push_cast; ring⟩
    rw [hg, Nat.cast_zero] at hint
    have hk3' : (3 : ℤ) ≤ k := by exact_mod_cast hk3
    nlinarith
  · have hg1 : (1 : ℤ) ≤ T.genus j := by exact_mod_cast hg
    have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    nlinarith

/-- In a minimal numerical type of genus `g` with more than one component, every
multiplicity-weighted intersection number `mᵢaᵢⱼ` with a component `j` that is not a
`(-2)`-index is at most `6g - 6`. -/
theorem multiplicity_mul_intersection_le (hT : T.IsMinimal) (h : 1 < Fintype.card T.Component)
    {j : T.Component} (hj : ¬ T.IsMinusTwoIndex j) (i : T.Component) :
    (T.multiplicity i : ℤ) * T.intersection i j ≤ 6 * T.arithmeticGenus - 6 :=
  (T.multiplicity_mul_intersection_le i j).trans
    (hT.multiplicity_mul_abs_intersection_self_le h hj)

end IsMinimal

end NumericalType

end TauCeti
