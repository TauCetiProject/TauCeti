/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Minimal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Contracting a `(-1)`-index of a numerical type

Let `e` be a `(-1)`-index of a numerical type `T`, so that `gₑ = 0` and `aₑₑ = -wₑ`. On a proper
regular model this is the numerical shadow of an exceptional curve of the first kind, and
contracting that curve produces a new regular model. This file constructs the numerical type
`T'` of the contracted model ([Stacks, Tag 0C77](https://stacks.math.columbia.edu/tag/0C77)).
Its components are those of `T` other than `e`, and for such components `i`, `j`:

* `m'ᵢ = mᵢ`;
* `a'ᵢⱼ = aᵢⱼ - aᵢₑaⱼₑ / aₑₑ = aᵢⱼ + aᵢₑaⱼₑ / wₑ`;
* `w'ᵢ = wᵢ / 2` if `aᵢₑ / wₑ` is even and `aᵢₑ / wᵢ` is odd, and `w'ᵢ = wᵢ` otherwise;
* `g'ᵢ = (wᵢ / w'ᵢ) (gᵢ - 1) + 1 + (aᵢₑ² - wₑaᵢₑ) / (2w'ᵢwₑ)`.

All divisions are exact, and the choice of `w'ᵢ` is exactly what makes `g'ᵢ` a nonnegative
integer. The contraction has the same signed genus as `T`.

## Main definitions

* `TauCeti.NumericalType.contract`: the numerical type obtained by contracting a `(-1)`-index.

## Main results

* `TauCeti.NumericalType.contractGenus_eq`: the formula for `g'ᵢ` above.
* `TauCeti.NumericalType.genusContribution_contract`: the genus contribution of a remaining
  component drops by `mᵢaᵢₑ / 2`.
* `TauCeti.NumericalType.arithmeticGenus_contract`: contracting a `(-1)`-index does not change
  the signed genus.

## References

[Stacks, Lemma 55.3.9](https://stacks.math.columbia.edu/tag/0C77). The weight condition is
stated here without divisions: `aᵢₑ / wₑ` is even exactly when `2wₑ ∣ aᵢₑ`, and `aᵢₑ / wᵢ` is odd
exactly when `2wᵢ ∤ aᵢₑ`.
-/

public section

namespace TauCeti

namespace NumericalType

open Finset

universe u

variable {T : NumericalType.{u}} {e : T.Component}

/-! ### Arithmetic of the contracted data -/

private lemma weight_pos (i : T.Component) : (0 : ℤ) < T.weight i :=
  Int.natCast_pos.mpr (T.weight i).pos

private lemma intersection_nonneg_of_ne {i : T.Component} (hi : i ≠ e) :
    0 ≤ T.intersection i e :=
  T.offDiagonal_nonneg i e hi

private lemma weight_dvd_intersection_left (i : T.Component) :
    (T.weight e : ℤ) ∣ T.intersection i e :=
  T.intersection_comm e i ▸ T.weight_dvd e i

/-- The condition under which contracting the `(-1)`-index `e` halves the weight of the
component `i`: `aᵢₑ / wₑ` is even and `aᵢₑ / wᵢ` is odd. -/
def ContractHalvesWeight (e i : T.Component) : Prop :=
  2 * (T.weight e : ℤ) ∣ T.intersection i e ∧ ¬ 2 * (T.weight i : ℤ) ∣ T.intersection i e

instance (e i : T.Component) : Decidable (T.ContractHalvesWeight e i) :=
  inferInstanceAs (Decidable (2 * (T.weight e : ℤ) ∣ T.intersection i e ∧
    ¬ 2 * (T.weight i : ℤ) ∣ T.intersection i e))

/-- The weight of a component whose weight is halved by the contraction is even. -/
lemma ContractHalvesWeight.two_dvd_weight {i : T.Component} (h : T.ContractHalvesWeight e i) :
    2 ∣ (T.weight i : ℕ) := by
  obtain ⟨d, hd⟩ := T.weight_dvd i e
  have hodd : ¬ 2 ∣ d := fun ⟨k, hk⟩ ↦ h.2 ⟨k, by rw [hd, hk]; ring⟩
  have h2 : (2 : ℤ) ∣ (T.weight i : ℤ) * d := hd ▸ (dvd_mul_right 2 _).trans h.1
  refine Int.natCast_dvd_natCast.mp (even_iff_two_dvd.mp ?_)
  exact (Int.even_mul.mp (even_iff_two_dvd.mpr h2)).resolve_right
    fun h ↦ hodd (even_iff_two_dvd.mp h)

/-- The weight `w'ᵢ` of a component `i` after contracting the `(-1)`-index `e`. -/
def contractWeight (e i : T.Component) : ℕ+ :=
  if h : T.ContractHalvesWeight e i then
    (⟨(T.weight i : ℕ) / 2, Nat.div_pos (Nat.le_of_dvd (T.weight i).pos h.two_dvd_weight)
      two_pos⟩ : ℕ+)
  else T.weight i

/-- A halved weight is half of the original weight. -/
lemma two_mul_contractWeight {i : T.Component} (h : T.ContractHalvesWeight e i) :
    2 * (T.contractWeight e i : ℤ) = T.weight i := by
  simp only [contractWeight, h, ↓reduceDIte, PNat.mk_coe]
  exact_mod_cast Nat.mul_div_cancel' h.two_dvd_weight

/-- A weight that is not halved is unchanged. -/
lemma contractWeight_of_not {i : T.Component} (h : ¬ T.ContractHalvesWeight e i) :
    T.contractWeight e i = T.weight i := by
  simp only [contractWeight, h, ↓reduceDIte]

/-- The contracted weight divides the original weight. -/
lemma contractWeight_dvd_weight (i : T.Component) :
    (T.contractWeight e i : ℤ) ∣ T.weight i := by
  by_cases h : T.ContractHalvesWeight e i
  · exact ⟨2, by rw [← two_mul_contractWeight h, mul_comm]⟩
  · rw [contractWeight_of_not h]

/-- The numerator `2wᵢ(gᵢ - 1) + aᵢₑ(aᵢₑ / wₑ - 1)` of `g'ᵢ - 1`, whose denominator is `2w'ᵢ`. -/
private def contractGenusNumerator (e i : T.Component) : ℤ :=
  2 * T.weight i * ((T.genus i : ℤ) - 1) +
    T.intersection i e * (T.intersection i e / T.weight e - 1)

/-- The genus numerator is divisible by `2w'ᵢ`, with quotient at least `-1`. This is the choice
of `w'ᵢ` at work. -/
private lemma contractGenusNumerator_spec {i : T.Component} (hi : i ≠ e) :
    2 * (T.contractWeight e i : ℤ) ∣ T.contractGenusNumerator e i ∧
      -(2 * (T.contractWeight e i : ℤ)) ≤ T.contractGenusNumerator e i := by
  -- Write `aᵢₑ = wₑc = wᵢd`, so that the numerator is `2wᵢ(gᵢ - 1) + wᵢd(c - 1)`. In both
  -- cases below it is `2w'ᵢ` times an integer that is at least `-1`.
  have hb := intersection_nonneg_of_ne hi
  obtain ⟨c, hc⟩ := weight_dvd_intersection_left (e := e) i
  obtain ⟨d, hd⟩ := T.weight_dvd i e
  have hwe := weight_pos e
  have hwi := weight_pos i
  have hcb : T.intersection i e / T.weight e = c := by
    rw [hc, Int.mul_ediv_cancel_left _ hwe.ne']
  have hc0 : 0 ≤ c := by nlinarith
  have hd0 : 0 ≤ d := by nlinarith
  -- If `aᵢₑ = 0` then `d = 0`, and otherwise `c ≥ 1`.
  have hcd : c = 0 → d = 0 := fun h0 ↦ by
    have : (T.weight i : ℤ) * d = 0 := by rw [← hd, hc, h0, mul_zero]
    exact (mul_eq_zero.mp this).resolve_left hwi.ne'
  have hcd' : 0 ≤ d * (c - 1) := by
    rcases eq_or_lt_of_le hc0 with h0 | h0
    · rw [hcd h0.symm, zero_mul]
    · exact mul_nonneg hd0 (by omega)
  unfold contractGenusNumerator
  rw [hcb]
  by_cases h : T.ContractHalvesWeight e i
  · -- Halved weight, `wᵢ = 2w'ᵢ`: here `c` is even and `d` odd, so `c ≥ 2`, `d ≥ 1`, and the
    -- quotient `2(gᵢ - 1) + d(c - 1)` is at least `-1`.
    have hw := two_mul_contractWeight h
    set w' := (T.contractWeight e i : ℤ)
    have hdodd : ¬ 2 ∣ d := fun ⟨k, hk⟩ ↦ h.2 ⟨k, by rw [hd, hk]; ring⟩
    have hceven : 2 ∣ c := by
      obtain ⟨k, hk⟩ := h.1
      exact ⟨k, by nlinarith⟩
    have hc2 : 2 ≤ c := by
      rcases eq_or_lt_of_le hc0 with h0 | h0
      · exact absurd (by rw [hcd h0.symm]; exact dvd_zero 2) hdodd
      · obtain ⟨k, hk⟩ := hceven
        omega
    have hd1 : 1 ≤ d := by
      rcases eq_or_lt_of_le hd0 with h0 | h0
      · exact absurd (by rw [← h0]; exact dvd_zero 2) hdodd
      · exact h0
    have hnum : 2 * T.weight i * ((T.genus i : ℤ) - 1) + T.intersection i e * (c - 1) =
        2 * w' * (2 * ((T.genus i : ℤ) - 1) + d * (c - 1)) := by
      rw [hd, ← hw]
      ring
    rw [hnum]
    refine ⟨dvd_mul_right _ _, ?_⟩
    have : 1 ≤ d * (c - 1) := by nlinarith
    have hw' : 0 < w' := by positivity
    nlinarith [T.genus i]
  · -- Unchanged weight: `c` is odd or `d` is even, so `d(c - 1) = 2k` with `k ≥ 0`, and the
    -- quotient is `gᵢ - 1 + k`.
    rw [contractWeight_of_not h]
    have heven : 2 ∣ d * (c - 1) := by
      by_cases h2 : 2 ∣ d
      · exact h2.mul_right _
      · have hcodd : ¬ 2 ∣ c := fun ⟨k, hk⟩ ↦
          h ⟨⟨k, by rw [hc, hk]; ring⟩, fun ⟨k, hk⟩ ↦ h2 ⟨k, by nlinarith⟩⟩
        exact Dvd.dvd.mul_left (by omega) _
    obtain ⟨k, hk⟩ := heven
    have hnum : 2 * T.weight i * ((T.genus i : ℤ) - 1) + T.intersection i e * (c - 1) =
        2 * T.weight i * (((T.genus i : ℤ) - 1) + k) := by
      rw [hd, mul_assoc (T.weight i : ℤ), hk]
      ring
    rw [hnum]
    refine ⟨dvd_mul_right _ _, ?_⟩
    have : 0 ≤ k := by omega
    nlinarith [T.genus i]

/-- The genus `g'ᵢ` of a component `i` after contracting the `(-1)`-index `e`. -/
def contractGenus (e i : T.Component) : ℕ :=
  (T.contractGenusNumerator e i / (2 * T.contractWeight e i) + 1).toNat

/-- The genus formula for the contraction with its denominator cleared:
`2w'ᵢ(g'ᵢ - 1) = 2wᵢ(gᵢ - 1) + aᵢₑ(aᵢₑ / wₑ - 1)`. -/
private lemma two_mul_contractWeight_mul_contractGenus_sub_one {i : T.Component} (hi : i ≠ e) :
    2 * (T.contractWeight e i : ℤ) * ((T.contractGenus e i : ℤ) - 1) =
      T.contractGenusNumerator e i := by
  obtain ⟨hdvd, hle⟩ := contractGenusNumerator_spec hi
  have hpos : (0 : ℤ) < 2 * T.contractWeight e i := by positivity
  have hq : -1 ≤ T.contractGenusNumerator e i / (2 * T.contractWeight e i) := by
    rw [Int.le_ediv_iff_mul_le hpos]
    linarith
  rw [contractGenus, Int.toNat_of_nonneg (by omega), add_sub_cancel_right,
    Int.mul_ediv_cancel' hdvd]

/-- The genus of a component other than `e` after contracting `e`, in the form of
[Stacks, Lemma 55.3.9](https://stacks.math.columbia.edu/tag/0C77):
`g'ᵢ = (wᵢ / w'ᵢ) (gᵢ - 1) + 1 + (aᵢₑ² - wₑaᵢₑ) / (2w'ᵢwₑ)`. -/
lemma contractGenus_eq {i : T.Component} (hi : i ≠ e) :
    (T.contractGenus e i : ℚ) =
      (T.weight i / T.contractWeight e i : ℚ) * ((T.genus i : ℚ) - 1) + 1 +
        ((T.intersection i e : ℚ) ^ 2 - T.weight e * T.intersection i e) /
          (2 * T.contractWeight e i * T.weight e) := by
  have h := two_mul_contractWeight_mul_contractGenus_sub_one hi
  obtain ⟨c, hc⟩ := weight_dvd_intersection_left (e := e) i
  rw [contractGenusNumerator, hc, Int.mul_ediv_cancel_left _ (weight_pos e).ne'] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  rw [hc]
  have hw' : (T.contractWeight e i : ℚ) ≠ 0 := by positivity
  have hwe : (T.weight e : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  linear_combination (T.weight e : ℚ) * h'

/-! ### Intersection numbers -/

/-- The intersection matrix `a'ᵢⱼ = aᵢⱼ - aᵢₑaⱼₑ / aₑₑ` on the components other than `e`, after
contracting the `(-1)`-index `e`. Since `aₑₑ = -wₑ` it is written `aᵢⱼ + aᵢₑaⱼₑ / wₑ`. -/
def contractIntersection (e : T.Component) : Matrix {i // i ≠ e} {i // i ≠ e} ℤ :=
  fun i j ↦ T.intersection i j + T.intersection i e * T.intersection j e / T.weight e

/-- Unfolding of `TauCeti.NumericalType.contractIntersection`. -/
lemma contractIntersection_apply (i j : {i // i ≠ e}) :
    T.contractIntersection e i j =
      T.intersection i j + T.intersection i e * T.intersection j e / T.weight e :=
  (rfl)

/-- The contracted intersection numbers with the exact division by `wₑ` cleared. -/
lemma weight_mul_contractIntersection (i j : {i // i ≠ e}) :
    (T.weight e : ℤ) * T.contractIntersection e i j =
      T.weight e * T.intersection i j + T.intersection i e * T.intersection j e := by
  rw [contractIntersection_apply, mul_add,
    Int.mul_ediv_cancel' ((weight_dvd_intersection_left j.1).mul_left _)]

/-- The contracted intersection matrix is symmetric. -/
lemma contractIntersection_isSymm : (T.contractIntersection e).IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ by
    rw [contractIntersection_apply, contractIntersection_apply, T.intersection_comm, mul_comm]

/-- Contracting `e` does not decrease the intersection number of two components other than `e`. -/
lemma intersection_le_contractIntersection (i j : {i // i ≠ e}) :
    T.intersection i j ≤ T.contractIntersection e i j :=
  le_add_of_nonneg_right (Int.ediv_nonneg (mul_nonneg (intersection_nonneg_of_ne i.2)
    (intersection_nonneg_of_ne j.2)) (weight_pos e).le)

/-- Two distinct components both meeting `e` meet after contracting `e`. -/
lemma contractIntersection_pos {i j : {i // i ≠ e}} (hij : i ≠ j) (hi : 0 < T.intersection i e)
    (hj : 0 < T.intersection j e) : 0 < T.contractIntersection e i j := by
  have := Int.ediv_pos_of_pos_of_dvd (mul_pos hi hj) (weight_pos e).le
    ((weight_dvd_intersection_left j.1).mul_left _)
  have := T.offDiagonal_nonneg i j fun h ↦ hij (Subtype.ext h)
  rw [contractIntersection_apply]
  omega

/-- The no-disconnected-cut condition for the contracted intersection numbers: every nonempty
proper set of components other than `e` meets its complement after contracting `e`. -/
lemma exists_contractIntersection_pos (s : Set {i // i ≠ e}) (hne : s.Nonempty)
    (hs : s ≠ Set.univ) : ∃ i ∈ s, ∃ j ∉ s, i ≠ j ∧ 0 < T.contractIntersection e i j := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, j ∉ s := by
    by_contra! h
    exact hs (Set.eq_univ_of_forall h)
  have hmem {x : {i // i ≠ e}} : x.1 ∈ Subtype.val '' s ↔ x ∈ s :=
    Subtype.val_injective.mem_set_image
  -- A crossing edge of `T` between two components other than `e` survives the contraction.
  have hsurvive {x y : T.Component} (hx : x ∈ Subtype.val '' s) (hy : y ∉ Subtype.val '' s)
      (hye : y ≠ e) (hxy : T.Adj x y) :
      ∃ i ∈ s, ∃ j ∉ s, i ≠ j ∧ 0 < T.contractIntersection e i j := by
    obtain ⟨x, hxs, rfl⟩ := hx
    rw [adj_iff] at hxy
    exact ⟨x, hxs, ⟨y, hye⟩, fun h ↦ hy ⟨_, h, rfl⟩, fun h ↦ hxy.1 (congrArg Subtype.val h),
      hxy.2.trans_le (intersection_le_contractIntersection x ⟨y, hye⟩)⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := T.exists_mem_notMem_adj (Subtype.val '' s) (hne.image _)
    fun h ↦ hj₀ (hmem.mp (h ▸ Set.mem_univ j₀.1))
  by_cases hye : y ≠ e
  · exact hsurvive hx hy hye hxy
  rw [not_not] at hye
  subst hye
  rw [adj_iff] at hxy
  -- `x` meets `e`; cut again along the set obtained by adding `e`.
  obtain ⟨x', hx', y', hy', hxy'⟩ := T.exists_mem_notMem_adj (insert y (Subtype.val '' s))
    (Set.insert_nonempty _ _) fun h ↦ by
      rcases h ▸ Set.mem_univ j₀.1 with h' | h'
      · exact j₀.2 h'
      · exact hj₀ (hmem.mp h')
  have hy'e : y' ≠ y := fun h ↦ hy' (Or.inl h)
  have hy's : y' ∉ Subtype.val '' s := fun h ↦ hy' (Or.inr h)
  rcases hx' with rfl | hx's
  · rw [adj_iff] at hxy'
    obtain ⟨x, hxs, rfl⟩ := hx
    refine ⟨x, hxs, ⟨y', hy'e⟩, fun h ↦ hy's ⟨_, h, rfl⟩, fun h ↦ hy's ⟨x, hxs, ?_⟩,
      contractIntersection_pos (fun h ↦ hy's ⟨x, hxs, congrArg Subtype.val h⟩) hxy.2 ?_⟩
    · exact congrArg Subtype.val h
    · exact T.intersection_comm _ x' ▸ hxy'.2
  · exact hsurvive hx's hy's hy'e hxy'

/-- The contracted intersection matrix kills the multiplicity vector: the fibre relation. -/
lemma sum_multiplicity_mul_contractIntersection (he : T.IsMinusOneIndex e) (i : {i // i ≠ e}) :
    ∑ j : {i // i ≠ e}, (T.multiplicity j : ℤ) * T.contractIntersection e i j = 0 := by
  refine mul_left_cancel₀ (weight_pos e).ne' ?_
  rw [mul_zero, Finset.mul_sum]
  have hterm (j : {i // i ≠ e}) :
      (T.weight e : ℤ) * ((T.multiplicity j : ℤ) * T.contractIntersection e i j) =
        T.weight e * ((T.multiplicity j : ℤ) * T.intersection i j) +
          T.intersection i e * ((T.multiplicity j : ℤ) * T.intersection j e) := by
    linear_combination (T.multiplicity j : ℤ) * T.weight_mul_contractIntersection i j
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Finset.sum_subtype (univ.erase e) (by simp)
      (fun j ↦ (T.multiplicity j : ℤ) * T.intersection i j),
    ← Finset.sum_subtype (univ.erase e) (by simp)
      (fun j ↦ (T.multiplicity j : ℤ) * T.intersection j e)]
  have hi := T.fiber_relation i
  have he' := T.fiber_relation e
  rw [← Finset.add_sum_erase _ _ (mem_univ e)] at hi he'
  simp_rw [T.intersection_comm e, (T.isMinusOneIndex_iff.mp he).2] at he'
  linear_combination (T.weight e : ℤ) * hi + T.intersection i e * he'

/-! ### The contracted numerical type -/

/-- The numerical type obtained by contracting a `(-1)`-index `e` of a numerical type `T`
([Stacks, Lemma 55.3.9](https://stacks.math.columbia.edu/tag/0C77)).

Its components are those of `T` other than `e`, with the same multiplicities, intersection
matrix `TauCeti.NumericalType.contractIntersection`, weights
`TauCeti.NumericalType.contractWeight` and genera `TauCeti.NumericalType.contractGenus`. On a
proper regular model, it is the numerical type of the model obtained by contracting the
exceptional curve corresponding to `e`. -/
@[expose]
def contract (T : NumericalType.{u}) {e : T.Component} (he : T.IsMinusOneIndex e) :
    NumericalType.{u} where
  Component := {i // i ≠ e}
  componentNonempty := by
    obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card he.one_lt_card e
    exact ⟨⟨i, hi⟩⟩
  multiplicity i := T.multiplicity i
  weight i := T.contractWeight e i
  intersection := T.contractIntersection e
  intersection_isSymm := contractIntersection_isSymm
  offDiagonal_nonneg i j hij :=
    (T.offDiagonal_nonneg i j fun h ↦ hij (Subtype.ext h)).trans
      (intersection_le_contractIntersection i j)
  connected := (Relation.forall_reflTransGen_iff _).2 exists_contractIntersection_pos
  fiber_relation := sum_multiplicity_mul_contractIntersection he
  weight_dvd i j := by
    refine (contractWeight_dvd_weight (e := e) i).trans ?_
    rw [contractIntersection_apply,
      Int.mul_ediv_assoc _ (weight_dvd_intersection_left (e := e) j)]
    exact dvd_add (T.weight_dvd i j) ((T.weight_dvd i e).mul_right _)
  genus i := T.contractGenus e i

variable (he : T.IsMinusOneIndex e)

@[simp]
lemma contract_multiplicity (i : {i // i ≠ e}) :
    (T.contract he).multiplicity i = T.multiplicity i :=
  (rfl)

@[simp]
lemma contract_weight (i : {i // i ≠ e}) : (T.contract he).weight i = T.contractWeight e i :=
  (rfl)

@[simp]
lemma contract_intersection (i j : {i // i ≠ e}) :
    (T.contract he).intersection i j = T.contractIntersection e i j :=
  (rfl)

@[simp]
lemma contract_genus (i : {i // i ≠ e}) : (T.contract he).genus i = T.contractGenus e i :=
  (rfl)

/-- Contracting `e` lowers the genus contribution of every remaining component `i` by
`mᵢaᵢₑ / 2`. -/
lemma genusContribution_contract (i : {i // i ≠ e}) :
    (T.contract he).genusContribution i =
      T.genusContribution i - T.multiplicity i * T.intersection i e / 2 := by
  have h := two_mul_contractWeight_mul_contractGenus_sub_one i.2
  obtain ⟨c, hc⟩ := weight_dvd_intersection_left (e := e) i.1
  have hwe := (weight_pos e).ne'
  rw [contractGenusNumerator, hc, Int.mul_ediv_cancel_left _ hwe] at h
  have hself : T.contractIntersection e i i = T.intersection i i + T.weight e * c * c := by
    rw [contractIntersection_apply, hc, mul_assoc, Int.mul_ediv_cancel_left _ hwe]
    ring
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  rw [genusContribution_def (T.contract he) i, genusContribution_def, contract_multiplicity,
    contract_weight, contract_genus, contract_intersection, hself, hc]
  push_cast
  linear_combination (T.multiplicity i : ℚ) / 2 * h'

/-- Contracting a `(-1)`-index does not change the signed genus
([Stacks, Lemma 55.3.9](https://stacks.math.columbia.edu/tag/0C77)). -/
theorem arithmeticGenus_contract : (T.contract he).arithmeticGenus = T.arithmeticGenus := by
  refine Int.cast_injective (α := ℚ) ?_
  rw [arithmeticGenus_eq_one_add_sum_genusContribution,
    arithmeticGenus_eq_one_add_sum_genusContribution, ← Finset.add_sum_erase _ _ (mem_univ e)]
  have hsum : ∑ i : (T.contract he).Component, (T.contract he).genusContribution i =
      ∑ i ∈ univ.erase e,
        (T.genusContribution i - T.multiplicity i * T.intersection i e / 2) := by
    rw [Finset.sum_subtype (p := (· ≠ e)) (univ.erase e) (by simp)
      (fun i ↦ T.genusContribution i - T.multiplicity i * T.intersection i e / 2)]
    exact Finset.sum_congr rfl fun i _ ↦ genusContribution_contract he i
  -- The fibre relation at `e` gives `∑_{i ≠ e} mᵢaᵢₑ = mₑwₑ`.
  have hfib := T.fiber_relation e
  rw [← Finset.add_sum_erase _ _ (mem_univ e), (T.isMinusOneIndex_iff.mp he).2] at hfib
  simp_rw [T.intersection_comm e] at hfib
  have hfib' := congrArg (Int.cast : ℤ → ℚ) hfib
  push_cast at hfib'
  rw [hsum, Finset.sum_sub_distrib, ← Finset.sum_div, genusContribution_def,
    (T.isMinusOneIndex_iff.mp he).1, (T.isMinusOneIndex_iff.mp he).2]
  push_cast
  linear_combination (-1 / 2 : ℚ) * hfib'

/-! ### A worked example -/

/-- A `(-1)`-index `0` of weight one and multiplicity two meeting, with intersection number two,
a component `1` of weight two, multiplicity one and genus one. Contracting `0` halves the weight
of `1`, since `a₁₀ / w₀ = 2` is even and `a₁₀ / w₁ = 1` is odd. -/
private noncomputable abbrev halvingExample : NumericalType.{0} where
  Component := Fin 2
  multiplicity := ![2, 1]
  weight := ![1, 2]
  intersection := !![-1, 2; 2, -4]
  intersection_isSymm := Matrix.IsSymm.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl
  offDiagonal_nonneg i j h := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide
  connected := by
    have key : ∀ i j : Fin 2, i ≠ j → (0 : ℤ) < !![(-1 : ℤ), 2; 2, -4] i j := by
      intro i j h
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide
    intro i j
    rcases eq_or_ne i j with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨h, key i j h⟩
  fiber_relation i := by fin_cases i <;> decide
  weight_dvd i j := by fin_cases i <;> fin_cases j <;> decide
  genus := ![0, 1]

private lemma halvingExample_isMinusOneIndex : halvingExample.IsMinusOneIndex 0 := by
  rw [isMinusOneIndex_iff]
  decide

example : halvingExample.arithmeticGenus = 2 := by
  rw [arithmeticGenus_def]
  decide

example : halvingExample.contractWeight 0 1 = 1 := by decide

example : halvingExample.contractIntersection 0 ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by decide

example : halvingExample.contractGenus 0 1 = 2 := by decide

/-- The contraction of `halvingExample` is a single component of multiplicity one, weight one and
genus two, so its signed genus `1 + 1 · 1 · (2 - 1) = 2` is that of `halvingExample`. -/
example : (halvingExample.contract halvingExample_isMinusOneIndex).arithmeticGenus = 2 := by
  rw [arithmeticGenus_def]
  decide

end NumericalType

end TauCeti
