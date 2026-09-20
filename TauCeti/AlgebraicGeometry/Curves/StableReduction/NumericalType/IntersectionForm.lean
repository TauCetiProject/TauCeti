/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Basic
public import TauCeti.LinearAlgebra.Matrix.NegSemidef
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The intersection form of a numerical type

The intersection matrix `A = (aᵢⱼ)` of a numerical type is symmetric, has nonnegative
off-diagonal entries and a connected graph, and kills the positive multiplicity vector `m`. Its
quadratic form `x ↦ xᵀ A x` is therefore negative semidefinite, and it vanishes exactly on the
rational multiples of `m` ([Stacks, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)).
Since `m` has no zero entry, the form is negative definite on the vectors that vanish at some
component, that is, on the vectors supported on a proper subset of the components. In
particular every proper principal submatrix of `A` is negative definite. Written out, this gives
`aᵢⱼ² < aᵢᵢ aⱼⱼ` for two distinct components `i` and `j` of a numerical type with more than two
components, and a negative determinant for the `3 × 3` submatrix on three distinct components of a
numerical type with more than three components.

These are the inputs of the classification of configurations of `(-2)`-indices in
[Stacks, Section 0C7L](https://stacks.math.columbia.edu/tag/0C7L), which in turn bounds the
multiplicities of a minimal numerical type.

## Main results

* `TauCeti.NumericalType.dotProduct_intersection_mulVec_nonpos`: `xᵀ A x ≤ 0`.
* `TauCeti.NumericalType.dotProduct_intersection_mulVec_eq_zero_iff`: `xᵀ A x = 0` exactly when
  the cross-products `mⱼ xᵢ = mᵢ xⱼ` agree, i.e. when `x` is proportional to `m`.
* `TauCeti.NumericalType.dotProduct_intersection_mulVec_neg`: `xᵀ A x < 0` for a nonzero `x`
  vanishing at some component.
* `TauCeti.NumericalType.intersection_sq_lt_intersection_mul_intersection`: `aᵢⱼ² < aᵢᵢ aⱼⱼ` for
  distinct components when there are more than two components.
* `TauCeti.NumericalType.intersection_det_triple_neg`: the determinant of the principal `3 × 3`
  submatrix on three distinct components is negative when there are more than three components.
-/

public section

namespace TauCeti

open Finset Matrix

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-! ### The intersection matrix over `ℚ` -/

private lemma isSymm_map_intersection :
    (T.intersection.map ((↑) : ℤ → ℚ)).IsSymm :=
  T.intersection_isSymm.map _

private lemma map_intersection_nonneg (i j : T.Component) (hij : i ≠ j) :
    0 ≤ T.intersection.map ((↑) : ℤ → ℚ) i j := by
  simpa using T.offDiagonal_nonneg i j hij

private lemma map_intersection_connected (i j : T.Component) :
    Relation.ReflTransGen (fun i j ↦ i ≠ j ∧ 0 < T.intersection.map ((↑) : ℤ → ℚ) i j) i j :=
  (T.connected i j).lift id fun _ _ h ↦ ⟨h.1, by simpa using h.2⟩

private lemma map_intersection_mulVec_multiplicity :
    T.intersection.map ((↑) : ℤ → ℚ) *ᵥ (fun i ↦ ((T.multiplicity i : ℕ) : ℚ)) = 0 := by
  funext i
  have h := congrArg ((↑) : ℤ → ℚ) (T.fiber_relation i)
  push_cast at h
  simpa [mulVec, dotProduct, mul_comm] using h

private lemma cast_dotProduct_intersection_mulVec (x : T.Component → ℤ) :
    ((x ⬝ᵥ T.intersection *ᵥ x : ℤ) : ℚ) =
      (fun i ↦ (x i : ℚ)) ⬝ᵥ T.intersection.map ((↑) : ℤ → ℚ) *ᵥ fun i ↦ (x i : ℚ) := by
  simp [dotProduct, mulVec]

/-! ### Semidefiniteness -/

/-- The intersection form of a numerical type is negative semidefinite
([Stacks, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)). -/
theorem dotProduct_intersection_mulVec_nonpos (x : T.Component → ℤ) :
    x ⬝ᵥ T.intersection *ᵥ x ≤ 0 := by
  have h := dotProduct_mulVec_nonpos_of_mulVec_eq_zero T.isSymm_map_intersection
    T.map_intersection_nonneg (fun i ↦ by simp) T.map_intersection_mulVec_multiplicity
    (fun i ↦ (x i : ℚ))
  exact_mod_cast (T.cast_dotProduct_intersection_mulVec x).trans_le h

/-- The intersection form of a numerical type vanishes at an integral vector exactly when the
vector is proportional to the multiplicity vector, that is, when its cross-products with the
multiplicity vector agree ([Stacks, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)). -/
theorem dotProduct_intersection_mulVec_eq_zero_iff (x : T.Component → ℤ) :
    x ⬝ᵥ T.intersection *ᵥ x = 0 ↔
      ∀ i j, (T.multiplicity j : ℤ) * x i = (T.multiplicity i : ℤ) * x j := by
  have hm (i : T.Component) : (0 : ℚ) < ((T.multiplicity i : ℕ) : ℚ) := by simp
  rw [← Int.cast_inj (α := ℚ), T.cast_dotProduct_intersection_mulVec, Int.cast_zero,
    dotProduct_mulVec_eq_zero_iff_of_mulVec_eq_zero T.isSymm_map_intersection
      T.map_intersection_nonneg T.map_intersection_connected hm
      T.map_intersection_mulVec_multiplicity]
  constructor
  · rintro ⟨c, hc⟩ i j
    have hi := congrFun hc i
    have hj := congrFun hc j
    simp only [Pi.smul_apply, smul_eq_mul] at hi hj
    have : ((T.multiplicity j : ℕ) : ℚ) * x i = ((T.multiplicity i : ℕ) : ℚ) * x j := by
      rw [hi, hj]
      ring
    exact_mod_cast this
  · intro h
    let i₀ : T.Component := Classical.arbitrary _
    refine ⟨(x i₀ : ℚ) / ((T.multiplicity i₀ : ℕ) : ℚ), funext fun j ↦ ?_⟩
    have hj : ((T.multiplicity j : ℕ) : ℚ) * x i₀ = ((T.multiplicity i₀ : ℕ) : ℚ) * x j := by
      exact_mod_cast h i₀ j
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff (hm i₀).ne']
    linear_combination -hj

/-- The intersection form of a numerical type is negative definite on the vectors vanishing at
some component, that is, on the vectors supported on a proper subset of the components. -/
theorem dotProduct_intersection_mulVec_neg {x : T.Component → ℤ} (hx : x ≠ 0) {i : T.Component}
    (hi : x i = 0) : x ⬝ᵥ T.intersection *ᵥ x < 0 := by
  refine (T.dotProduct_intersection_mulVec_nonpos x).lt_of_ne fun h ↦ hx (funext fun j ↦ ?_)
  have hij := (T.dotProduct_intersection_mulVec_eq_zero_iff x).mp h j i
  rw [hi, mul_zero, mul_eq_zero] at hij
  exact hij.resolve_left (Int.natCast_ne_zero.mpr (T.multiplicity i).ne_zero)

/-! ### Two components -/

/-- The intersection form evaluated at a vector supported on two distinct components. -/
private lemma dotProduct_intersection_mulVec_of_support_pair {i j : T.Component} (hij : i ≠ j)
    (x : T.Component → ℤ) (hx : ∀ k, k ≠ i ∧ k ≠ j → x k = 0) :
    x ⬝ᵥ T.intersection *ᵥ x = T.intersection i i * x i ^ 2 +
      2 * T.intersection i j * x i * x j + T.intersection j j * x j ^ 2 := by
  have hrow (k : T.Component) : (T.intersection *ᵥ x) k =
      T.intersection k i * x i + T.intersection k j * x j := by
    rw [mulVec, dotProduct, Fintype.sum_eq_add i j hij fun l hl ↦ by rw [hx l hl, mul_zero]]
  rw [dotProduct, Fintype.sum_eq_add i j hij fun l hl ↦ by rw [hx l hl, zero_mul], hrow, hrow,
    T.intersection_comm j i]
  ring

/-- In a numerical type with more than two components, the intersection numbers of two
distinct components satisfy `aᵢⱼ² < aᵢᵢ aⱼⱼ`: the principal `2 × 2` submatrix on `{i, j}` is
negative definite. -/
theorem intersection_sq_lt_intersection_mul_intersection (hcard : 2 < Fintype.card T.Component)
    {i j : T.Component} (hij : i ≠ j) :
    T.intersection i j ^ 2 < T.intersection i i * T.intersection j j := by
  have hii := T.intersection_self_neg (by omega) i
  obtain ⟨k, hk⟩ : ((univ.erase i).erase j).Nonempty := by
    rw [← card_pos, card_erase_of_mem (by simp [hij.symm]), card_erase_of_mem (mem_univ i),
      card_univ]
    omega
  obtain ⟨hkj, hki⟩ : k ≠ j ∧ k ≠ i := by simpa using hk
  classical
  -- Evaluate the form at `aᵢⱼ eᵢ - aᵢᵢ eⱼ`, which vanishes at `k` but not at `j`.
  let x : T.Component → ℤ := fun l ↦
    if l = i then T.intersection i j else if l = j then -T.intersection i i else 0
  have hxi : x i = T.intersection i j := by simp [x]
  have hxj : x j = -T.intersection i i := by simp [x, hij.symm]
  have hneg := T.dotProduct_intersection_mulVec_neg (x := x)
    (fun h ↦ hii.ne (neg_eq_zero.mp (hxj.symm.trans (congrFun h j)))) (i := k)
    (by simp [x, hki, hkj])
  rw [T.dotProduct_intersection_mulVec_of_support_pair hij x
    (fun l hl ↦ by simp [x, hl.1, hl.2]), hxi, hxj] at hneg
  nlinarith

/-! ### Three components -/

/-- A sum over the components of a function vanishing outside three distinct components. -/
private lemma sum_eq_of_support_triple {i j k : T.Component} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (y : T.Component → ℤ) (hy : ∀ l, l ≠ i → l ≠ j → l ≠ k → y l = 0) :
    ∑ l, y l = y i + y j + y k := by
  have hsub : ∑ l ∈ ({i, j, k} : Finset T.Component), y l = ∑ l, y l := by
    refine sum_subset (subset_univ _) fun l _ hl ↦ ?_
    simp only [mem_insert, mem_singleton, not_or] at hl
    exact hy l hl.1 hl.2.1 hl.2.2
  rw [← hsub, sum_insert (by simp [hij, hik]), sum_insert (by simp [hjk]), sum_singleton]
  ring

/-- The intersection form evaluated at a vector supported on three distinct components. -/
private lemma dotProduct_intersection_mulVec_of_support_triple {i j k : T.Component} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (x : T.Component → ℤ)
    (hx : ∀ l, l ≠ i → l ≠ j → l ≠ k → x l = 0) :
    x ⬝ᵥ T.intersection *ᵥ x =
      T.intersection i i * x i ^ 2 + T.intersection j j * x j ^ 2 +
        T.intersection k k * x k ^ 2 + 2 * T.intersection i j * x i * x j +
        2 * T.intersection i k * x i * x k + 2 * T.intersection j k * x j * x k := by
  have hrow (l : T.Component) : (T.intersection *ᵥ x) l =
      T.intersection l i * x i + T.intersection l j * x j + T.intersection l k * x k := by
    rw [mulVec, dotProduct]
    exact T.sum_eq_of_support_triple hij hik hjk _ fun m h₁ h₂ h₃ ↦ by
      rw [hx m h₁ h₂ h₃, mul_zero]
  rw [dotProduct, T.sum_eq_of_support_triple hij hik hjk _
    (fun l h₁ h₂ h₃ ↦ by rw [hx l h₁ h₂ h₃, zero_mul]), hrow i, hrow j, hrow k,
    T.intersection_comm j i, T.intersection_comm k i, T.intersection_comm k j]
  ring

/-- In a numerical type with more than three components, the principal `3 × 3` submatrix of the
intersection matrix on three distinct components `i`, `j`, `k` is negative definite, so its
determinant `aᵢᵢaⱼⱼaₖₖ - aᵢᵢaⱼₖ² - aⱼⱼaᵢₖ² - aₖₖaᵢⱼ² + 2aᵢⱼaᵢₖaⱼₖ`, written out on the left below,
is negative. -/
theorem intersection_det_triple_neg (hcard : 3 < Fintype.card T.Component)
    {i j k : T.Component} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    T.intersection i i * T.intersection j j * T.intersection k k -
          T.intersection i i * T.intersection j k ^ 2 -
        T.intersection j j * T.intersection i k ^ 2 -
      T.intersection k k * T.intersection i j ^ 2 +
        2 * T.intersection i j * T.intersection i k * T.intersection j k < 0 := by
  -- Write `M` for the principal submatrix on `{i, j, k}`. The vector `x` below is the last column
  -- of the adjugate of `M`, so that `M x = det M • eₖ` and hence the intersection form at `x` is
  -- `(det M) xₖ`. Its last entry `xₖ` is positive by the two-component case, and the form at `x`
  -- is negative because `x` vanishes at a fourth component.
  have hxk : 0 < T.intersection i i * T.intersection j j - T.intersection i j ^ 2 :=
    sub_pos.mpr (T.intersection_sq_lt_intersection_mul_intersection (by omega) hij)
  obtain ⟨l, hl⟩ : (((univ.erase i).erase j).erase k).Nonempty := by
    rw [← card_pos, card_erase_of_mem (by simp [hik.symm, hjk.symm]),
      card_erase_of_mem (by simp [hij.symm]), card_erase_of_mem (mem_univ i), card_univ]
    omega
  simp only [mem_erase, mem_univ, and_true] at hl
  obtain ⟨hlk, hlj, hli⟩ := hl
  let x : T.Component → ℤ := fun m ↦
    if m = i then T.intersection i j * T.intersection j k - T.intersection i k * T.intersection j j
    else if m = j then
      T.intersection i j * T.intersection i k - T.intersection i i * T.intersection j k
    else if m = k then T.intersection i i * T.intersection j j - T.intersection i j ^ 2
    else 0
  have hvi : x i =
      T.intersection i j * T.intersection j k - T.intersection i k * T.intersection j j := by
    simp [x]
  have hvj : x j =
      T.intersection i j * T.intersection i k - T.intersection i i * T.intersection j k := by
    simp [x, hij.symm]
  have hvk : x k = T.intersection i i * T.intersection j j - T.intersection i j ^ 2 := by
    simp [x, hik.symm, hjk.symm]
  have hneg := T.dotProduct_intersection_mulVec_neg
    (x := x) (fun h ↦ hxk.ne' (hvk.symm.trans (congrFun h k))) (i := l)
    (by simp [x, hli, hlj, hlk])
  rw [T.dotProduct_intersection_mulVec_of_support_triple hij hik hjk x
    (fun m h₁ h₂ h₃ ↦ by simp [x, h₁, h₂, h₃]), hvi, hvj, hvk] at hneg
  by_contra hdet
  rw [not_lt] at hdet
  linarith [mul_nonneg hdet hxk.le]

end NumericalType

end TauCeti
