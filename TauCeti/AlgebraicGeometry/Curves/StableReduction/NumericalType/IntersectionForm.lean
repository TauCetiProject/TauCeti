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
components, a negative determinant for the `3 × 3` submatrix on three distinct components of a
numerical type with more than three components, and a positive determinant for the `4 × 4`
submatrix on four distinct components of a numerical type with more than four components. On five
components the determinant is not the convenient form: what the classification uses there is the
value of the form itself at an explicit vector.

These are the inputs of the classification of configurations of `(-2)`-indices in
[Stacks, Section 0C7L](https://stacks.math.columbia.edu/tag/0C7L), which in turn bounds the
multiplicities of a minimal numerical type.

## Main results

* `TauCeti.NumericalType.dotProduct_intersection_mulVec_nonpos`: `xᵀ A x ≤ 0`.
* `TauCeti.NumericalType.dotProduct_intersection_mulVec_eq_zero_iff`: `xᵀ A x = 0` exactly when
  the cross-products `mⱼ xᵢ = mᵢ xⱼ` agree, i.e. when `x` is proportional to `m`.
* `TauCeti.NumericalType.dotProduct_intersection_mulVec_neg`: `xᵀ A x < 0` for a nonzero `x`
  vanishing at some component.
* `TauCeti.NumericalType.dotProduct_intersection_mulVec_of_support_subset`: `xᵀ A x` is the sum
  over the principal submatrix carrying the support of `x`.
* `TauCeti.NumericalType.sum_sum_intersection_mul_neg`: the same sum is negative for a nonzero
  vector on a proper finite set of components.
* `TauCeti.NumericalType.intersection_sq_lt_intersection_mul_intersection`: `aᵢⱼ² < aᵢᵢ aⱼⱼ` for
  distinct components when there are more than two components.
* `TauCeti.NumericalType.intersection_det_triple_neg`: the determinant of the principal `3 × 3`
  submatrix on three distinct components is negative when there are more than three components.
* `TauCeti.NumericalType.intersection_det_four_pos`: the determinant of the principal `4 × 4`
  submatrix on four distinct components is positive when there are more than four components.
* `TauCeti.NumericalType.intersection_five_neg`: the intersection form at a vector supported on
  five distinct components, written out, is negative when there are more than five components.
* `TauCeti.NumericalType.intersection_six_neg`: the analogous formula for six components.
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

/-- The intersection form evaluated at a vector supported on a finite set of components is the
corresponding sum over the principal submatrix on that set. -/
theorem dotProduct_intersection_mulVec_of_support_subset {s : Finset T.Component}
    {x : T.Component → ℤ} (hx : ∀ i ∉ s, x i = 0) :
    x ⬝ᵥ T.intersection *ᵥ x = ∑ i ∈ s, ∑ j ∈ s, T.intersection i j * x i * x j := by
  rw [dotProduct, ← sum_subset (subset_univ s) fun i _ hi ↦ by rw [hx i hi, zero_mul]]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mulVec, dotProduct, mul_sum,
    ← sum_subset (subset_univ s) fun j _ hj ↦ by rw [hx j hj, mul_zero, mul_zero]]
  exact sum_congr rfl fun j _ ↦ by ring

/-- The intersection form of a numerical type is negative definite on the vectors supported on a
proper subset of the components: if `s` is a finite set of components which is not all of them
and `y` does not vanish identically on `s`, then `∑_{i, j ∈ s} aᵢⱼ yᵢ yⱼ < 0`. -/
theorem sum_sum_intersection_mul_neg {s : Finset T.Component} (hs : s ≠ univ)
    {y : T.Component → ℤ} (hy : ∃ i ∈ s, y i ≠ 0) :
    ∑ i ∈ s, ∑ j ∈ s, T.intersection i j * y i * y j < 0 := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, m ∉ s := by
    by_contra h
    exact hs (eq_univ_of_forall (by simpa using h))
  set x : T.Component → ℤ := fun i ↦ if i ∈ s then y i else 0 with hxdef
  have hx : ∀ i ∉ s, x i = 0 := fun i hi ↦ by simp [hxdef, hi]
  have hxne : x ≠ 0 := by
    obtain ⟨i, hi, hyi⟩ := hy
    exact fun h ↦ hyi (by simpa [hxdef, hi] using congrFun h i)
  have heq : ∑ i ∈ s, ∑ j ∈ s, T.intersection i j * x i * x j =
      ∑ i ∈ s, ∑ j ∈ s, T.intersection i j * y i * y j :=
    sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ by simp [hxdef, hi, hj]
  have hneg := T.dotProduct_intersection_mulVec_neg hxne (hx m hm)
  rwa [T.dotProduct_intersection_mulVec_of_support_subset hx, heq] at hneg

/-! ### Two components -/

/-- The intersection form evaluated at a vector supported on two distinct components. -/
private lemma dotProduct_intersection_mulVec_of_support_pair {i j : T.Component} (hij : i ≠ j)
    (x : T.Component → ℤ) (hx : ∀ k, k ≠ i ∧ k ≠ j → x k = 0) :
    x ⬝ᵥ T.intersection *ᵥ x = T.intersection i i * x i ^ 2 +
      2 * T.intersection i j * x i * x j + T.intersection j j * x j ^ 2 := by
  rw [T.dotProduct_intersection_mulVec_of_support_subset (s := {i, j})
    fun k hk ↦ hx k (by simpa [not_or] using hk)]
  simp only [sum_pair hij, T.intersection_comm j i]
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

/-- The intersection form evaluated at a vector supported on three distinct components. -/
private lemma dotProduct_intersection_mulVec_of_support_triple {i j k : T.Component} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (x : T.Component → ℤ)
    (hx : ∀ l, l ≠ i → l ≠ j → l ≠ k → x l = 0) :
    x ⬝ᵥ T.intersection *ᵥ x =
      T.intersection i i * x i ^ 2 + T.intersection j j * x j ^ 2 +
        T.intersection k k * x k ^ 2 + 2 * T.intersection i j * x i * x j +
        2 * T.intersection i k * x i * x k + 2 * T.intersection j k * x j * x k := by
  rw [T.dotProduct_intersection_mulVec_of_support_subset (s := {i, j, k}) fun l hl ↦ by
    simp only [mem_insert, mem_singleton, not_or] at hl
    exact hx l hl.1 hl.2.1 hl.2.2]
  simp only [sum_insert (by simp [hij, hik] : i ∉ ({j, k} : Finset T.Component)), sum_pair hjk,
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

/-! ### Four components -/

/-- A sum over the components of a function vanishing outside four distinct components. -/
private lemma sum_eq_of_support_four {i j k l : T.Component} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (y : T.Component → ℤ) (hy : ∀ m, m ≠ i → m ≠ j → m ≠ k → m ≠ l → y m = 0) :
    ∑ m, y m = y i + y j + y k + y l := by
  have hsub : ∑ m ∈ ({i, j, k, l} : Finset T.Component), y m = ∑ m, y m := by
    refine sum_subset (subset_univ _) fun m _ hm ↦ ?_
    simp only [mem_insert, mem_singleton, not_or] at hm
    exact hy m hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  rw [← hsub, sum_insert (by simp [hij, hik, hil]), sum_insert (by simp [hjk, hjl]),
    sum_insert (by simp [hkl]), sum_singleton]
  ring

/-- In a numerical type with more than four components, the principal `4 × 4` submatrix of the
intersection matrix on four distinct components `i`, `j`, `k`, `l` is negative definite, so its
determinant is positive. The displayed expression is the determinant written in terms of the ten
entries on and above the diagonal. -/
theorem intersection_det_four_pos (hcard : 4 < Fintype.card T.Component)
    {i j k l : T.Component} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) :
    0 < T.intersection i i * T.intersection j j * T.intersection k k * T.intersection l l -
          T.intersection i i * T.intersection j j * T.intersection k l ^ 2 -
        T.intersection i i * T.intersection k k * T.intersection j l ^ 2 -
      T.intersection i i * T.intersection l l * T.intersection j k ^ 2 +
        2 * T.intersection i i * T.intersection j k * T.intersection j l *
          T.intersection k l -
      T.intersection j j * T.intersection k k * T.intersection i l ^ 2 -
        T.intersection j j * T.intersection l l * T.intersection i k ^ 2 +
      2 * T.intersection j j * T.intersection i k * T.intersection i l *
        T.intersection k l -
      T.intersection k k * T.intersection l l * T.intersection i j ^ 2 +
        2 * T.intersection k k * T.intersection i j * T.intersection i l *
          T.intersection j l +
      2 * T.intersection l l * T.intersection i j * T.intersection i k *
        T.intersection j k +
      T.intersection i j ^ 2 * T.intersection k l ^ 2 -
        2 * T.intersection i j * T.intersection i k * T.intersection j l *
          T.intersection k l -
      2 * T.intersection i j * T.intersection i l * T.intersection j k *
        T.intersection k l +
      T.intersection i k ^ 2 * T.intersection j l ^ 2 -
        2 * T.intersection i k * T.intersection i l * T.intersection j k *
          T.intersection j l +
      T.intersection i l ^ 2 * T.intersection j k ^ 2 := by
  -- Use the last column of the adjugate of the principal submatrix. Its last entry is the
  -- negative `3 × 3` determinant, and the intersection form evaluates to their product.
  have hxl := T.intersection_det_triple_neg (by omega : 3 < Fintype.card T.Component)
    hij hik hjk
  obtain ⟨m, hm⟩ : ((((univ.erase i).erase j).erase k).erase l).Nonempty := by
    rw [← card_pos, card_erase_of_mem (by simp [hil.symm, hjl.symm, hkl.symm]),
      card_erase_of_mem (by simp [hik.symm, hjk.symm]),
      card_erase_of_mem (by simp [hij.symm]), card_erase_of_mem (mem_univ i), card_univ]
    omega
  simp only [mem_erase, mem_univ, and_true] at hm
  obtain ⟨hml, hmk, hmj, hmi⟩ := hm
  let x : T.Component → ℤ := fun n ↦
    if n = i then
      -T.intersection j j * T.intersection k k * T.intersection i l +
        T.intersection j j * T.intersection i k * T.intersection k l +
        T.intersection k k * T.intersection i j * T.intersection j l -
        T.intersection i j * T.intersection j k * T.intersection k l -
        T.intersection i k * T.intersection j k * T.intersection j l +
        T.intersection i l * T.intersection j k ^ 2
    else if n = j then
      -T.intersection i i * T.intersection k k * T.intersection j l +
        T.intersection i i * T.intersection j k * T.intersection k l +
        T.intersection k k * T.intersection i j * T.intersection i l -
        T.intersection i j * T.intersection i k * T.intersection k l +
        T.intersection i k ^ 2 * T.intersection j l -
        T.intersection i k * T.intersection i l * T.intersection j k
    else if n = k then
      -T.intersection i i * T.intersection j j * T.intersection k l +
        T.intersection i i * T.intersection j k * T.intersection j l +
        T.intersection j j * T.intersection i k * T.intersection i l +
        T.intersection i j ^ 2 * T.intersection k l -
        T.intersection i j * T.intersection i k * T.intersection j l -
        T.intersection i j * T.intersection i l * T.intersection j k
    else if n = l then
      T.intersection i i * T.intersection j j * T.intersection k k -
        T.intersection i i * T.intersection j k ^ 2 -
        T.intersection j j * T.intersection i k ^ 2 -
        T.intersection k k * T.intersection i j ^ 2 +
        2 * T.intersection i j * T.intersection i k * T.intersection j k
    else 0
  have hxi : x i =
      -T.intersection j j * T.intersection k k * T.intersection i l +
        T.intersection j j * T.intersection i k * T.intersection k l +
        T.intersection k k * T.intersection i j * T.intersection j l -
        T.intersection i j * T.intersection j k * T.intersection k l -
        T.intersection i k * T.intersection j k * T.intersection j l +
        T.intersection i l * T.intersection j k ^ 2 := by simp [x]
  have hxj : x j =
      -T.intersection i i * T.intersection k k * T.intersection j l +
        T.intersection i i * T.intersection j k * T.intersection k l +
        T.intersection k k * T.intersection i j * T.intersection i l -
        T.intersection i j * T.intersection i k * T.intersection k l +
        T.intersection i k ^ 2 * T.intersection j l -
        T.intersection i k * T.intersection i l * T.intersection j k := by
    simp [x, hij.symm]
  have hxk : x k =
      -T.intersection i i * T.intersection j j * T.intersection k l +
        T.intersection i i * T.intersection j k * T.intersection j l +
        T.intersection j j * T.intersection i k * T.intersection i l +
        T.intersection i j ^ 2 * T.intersection k l -
        T.intersection i j * T.intersection i k * T.intersection j l -
        T.intersection i j * T.intersection i l * T.intersection j k := by
    simp [x, hik.symm, hjk.symm]
  have hxl' : x l =
      T.intersection i i * T.intersection j j * T.intersection k k -
        T.intersection i i * T.intersection j k ^ 2 -
        T.intersection j j * T.intersection i k ^ 2 -
        T.intersection k k * T.intersection i j ^ 2 +
        2 * T.intersection i j * T.intersection i k * T.intersection j k := by
    simp [x, hil.symm, hjl.symm, hkl.symm]
  let d :=
    T.intersection i i * T.intersection j j * T.intersection k k * T.intersection l l -
          T.intersection i i * T.intersection j j * T.intersection k l ^ 2 -
        T.intersection i i * T.intersection k k * T.intersection j l ^ 2 -
      T.intersection i i * T.intersection l l * T.intersection j k ^ 2 +
        2 * T.intersection i i * T.intersection j k * T.intersection j l *
          T.intersection k l -
      T.intersection j j * T.intersection k k * T.intersection i l ^ 2 -
        T.intersection j j * T.intersection l l * T.intersection i k ^ 2 +
      2 * T.intersection j j * T.intersection i k * T.intersection i l *
        T.intersection k l -
      T.intersection k k * T.intersection l l * T.intersection i j ^ 2 +
        2 * T.intersection k k * T.intersection i j * T.intersection i l *
          T.intersection j l +
      2 * T.intersection l l * T.intersection i j * T.intersection i k *
        T.intersection j k +
      T.intersection i j ^ 2 * T.intersection k l ^ 2 -
        2 * T.intersection i j * T.intersection i k * T.intersection j l *
          T.intersection k l -
      2 * T.intersection i j * T.intersection i l * T.intersection j k *
        T.intersection k l +
      T.intersection i k ^ 2 * T.intersection j l ^ 2 -
        2 * T.intersection i k * T.intersection i l * T.intersection j k *
          T.intersection j l +
      T.intersection i l ^ 2 * T.intersection j k ^ 2
  have hsupp (n : T.Component) (hni : n ≠ i) (hnj : n ≠ j) (hnk : n ≠ k) (hnl : n ≠ l) :
      x n = 0 := by simp [x, hni, hnj, hnk, hnl]
  have hrow_i : (T.intersection *ᵥ x) i = 0 := by
    rw [mulVec, dotProduct, T.sum_eq_of_support_four hij hik hil hjk hjl hkl _
      (fun n hni hnj hnk hnl ↦ by rw [hsupp n hni hnj hnk hnl, mul_zero]),
      hxi, hxj, hxk, hxl']
    ring
  have hrow_j : (T.intersection *ᵥ x) j = 0 := by
    rw [mulVec, dotProduct, T.sum_eq_of_support_four hij hik hil hjk hjl hkl _
      (fun n hni hnj hnk hnl ↦ by rw [hsupp n hni hnj hnk hnl, mul_zero]),
      hxi, hxj, hxk, hxl', T.intersection_comm j i]
    ring
  have hrow_k : (T.intersection *ᵥ x) k = 0 := by
    rw [mulVec, dotProduct, T.sum_eq_of_support_four hij hik hil hjk hjl hkl _
      (fun n hni hnj hnk hnl ↦ by rw [hsupp n hni hnj hnk hnl, mul_zero]),
      hxi, hxj, hxk, hxl', T.intersection_comm k i, T.intersection_comm k j]
    ring
  have hrow_l : (T.intersection *ᵥ x) l = d := by
    rw [mulVec, dotProduct, T.sum_eq_of_support_four hij hik hil hjk hjl hkl _
      (fun n hni hnj hnk hnl ↦ by rw [hsupp n hni hnj hnk hnl, mul_zero]),
      hxi, hxj, hxk, hxl', T.intersection_comm l i, T.intersection_comm l j,
      T.intersection_comm l k]
    simp only [d]
    ring
  have hform : x ⬝ᵥ T.intersection *ᵥ x = x l * d := by
    rw [dotProduct, T.sum_eq_of_support_four hij hik hil hjk hjl hkl _
      (fun n hni hnj hnk hnl ↦ by rw [hsupp n hni hnj hnk hnl, zero_mul]),
      hrow_i, hrow_j, hrow_k, hrow_l]
    ring
  have hneg := T.dotProduct_intersection_mulVec_neg (x := x)
    (fun hx ↦ hxl.ne (hxl'.symm.trans (congrFun hx l))) (i := m)
    (by simp [x, hmi, hmj, hmk, hml])
  rw [hform] at hneg
  have hd : 0 < d := by nlinarith
  simpa only [d] using hd

/-! ### Five components -/

/-- In a numerical type with more than five components, the intersection form is negative definite
on the vectors supported on five distinct components `c₁, …, c₅`: its value at the vector taking
the values `y₁, …, y₅` there and vanishing elsewhere, written out below, is negative unless all
five values vanish. -/
theorem intersection_five_neg (hcard : 5 < Fintype.card T.Component)
    {c₁ c₂ c₃ c₄ c₅ : T.Component}
    (h₁₂ : c₁ ≠ c₂) (h₁₃ : c₁ ≠ c₃) (h₁₄ : c₁ ≠ c₄) (h₁₅ : c₁ ≠ c₅)
    (h₂₃ : c₂ ≠ c₃) (h₂₄ : c₂ ≠ c₄) (h₂₅ : c₂ ≠ c₅)
    (h₃₄ : c₃ ≠ c₄) (h₃₅ : c₃ ≠ c₅) (h₄₅ : c₄ ≠ c₅)
    {y₁ y₂ y₃ y₄ y₅ : ℤ} (hy : ¬(y₁ = 0 ∧ y₂ = 0 ∧ y₃ = 0 ∧ y₄ = 0 ∧ y₅ = 0)) :
    T.intersection c₁ c₁ * y₁ ^ 2 + T.intersection c₂ c₂ * y₂ ^ 2 +
          T.intersection c₃ c₃ * y₃ ^ 2 + T.intersection c₄ c₄ * y₄ ^ 2 +
        T.intersection c₅ c₅ * y₅ ^ 2 +
      2 * (T.intersection c₁ c₂ * y₁ * y₂ + T.intersection c₁ c₃ * y₁ * y₃ +
        T.intersection c₁ c₄ * y₁ * y₄ + T.intersection c₁ c₅ * y₁ * y₅ +
        T.intersection c₂ c₃ * y₂ * y₃ + T.intersection c₂ c₄ * y₂ * y₄ +
        T.intersection c₂ c₅ * y₂ * y₅ + T.intersection c₃ c₄ * y₃ * y₄ +
        T.intersection c₃ c₅ * y₃ * y₅ + T.intersection c₄ c₅ * y₄ * y₅) < 0 := by
  classical
  let y : T.Component → ℤ := fun m ↦
    if m = c₁ then y₁ else if m = c₂ then y₂ else if m = c₃ then y₃
      else if m = c₄ then y₄ else if m = c₅ then y₅ else 0
  have e₁ : y c₁ = y₁ := by simp [y]
  have e₂ : y c₂ = y₂ := by simp [y, h₁₂.symm]
  have e₃ : y c₃ = y₃ := by simp [y, h₁₃.symm, h₂₃.symm]
  have e₄ : y c₄ = y₄ := by simp [y, h₁₄.symm, h₂₄.symm, h₃₄.symm]
  have e₅ : y c₅ = y₅ := by simp [y, h₁₅.symm, h₂₅.symm, h₃₅.symm, h₄₅.symm]
  have hmem : ∃ i ∈ ({c₁, c₂, c₃, c₄, c₅} : Finset T.Component), y i ≠ 0 := by
    rcases (by omega : y₁ ≠ 0 ∨ y₂ ≠ 0 ∨ y₃ ≠ 0 ∨ y₄ ≠ 0 ∨ y₅ ≠ 0) with h | h | h | h | h
    · exact ⟨c₁, by simp, by rw [e₁]; exact h⟩
    · exact ⟨c₂, by simp, by rw [e₂]; exact h⟩
    · exact ⟨c₃, by simp, by rw [e₃]; exact h⟩
    · exact ⟨c₄, by simp, by rw [e₄]; exact h⟩
    · exact ⟨c₅, by simp, by rw [e₅]; exact h⟩
  have hsu : ({c₁, c₂, c₃, c₄, c₅} : Finset T.Component) ≠ univ := by
    exact (card_lt_iff_ne_univ _).mp (card_le_five.trans_lt hcard)
  have hval : ∑ i ∈ ({c₁, c₂, c₃, c₄, c₅} : Finset T.Component),
      ∑ j ∈ ({c₁, c₂, c₃, c₄, c₅} : Finset T.Component), T.intersection i j * y i * y j =
      T.intersection c₁ c₁ * y₁ ^ 2 + T.intersection c₂ c₂ * y₂ ^ 2 +
            T.intersection c₃ c₃ * y₃ ^ 2 + T.intersection c₄ c₄ * y₄ ^ 2 +
          T.intersection c₅ c₅ * y₅ ^ 2 +
        2 * (T.intersection c₁ c₂ * y₁ * y₂ + T.intersection c₁ c₃ * y₁ * y₃ +
          T.intersection c₁ c₄ * y₁ * y₄ + T.intersection c₁ c₅ * y₁ * y₅ +
          T.intersection c₂ c₃ * y₂ * y₃ + T.intersection c₂ c₄ * y₂ * y₄ +
          T.intersection c₂ c₅ * y₂ * y₅ + T.intersection c₃ c₄ * y₃ * y₄ +
          T.intersection c₃ c₅ * y₃ * y₅ + T.intersection c₄ c₅ * y₄ * y₅) := by
    have n₁ : c₁ ∉ ({c₂, c₃, c₄, c₅} : Finset T.Component) := by simp [h₁₂, h₁₃, h₁₄, h₁₅]
    have n₂ : c₂ ∉ ({c₃, c₄, c₅} : Finset T.Component) := by simp [h₂₃, h₂₄, h₂₅]
    have n₃ : c₃ ∉ ({c₄, c₅} : Finset T.Component) := by simp [h₃₄, h₃₅]
    have n₄ : c₄ ∉ ({c₅} : Finset T.Component) := by simp [h₄₅]
    simp only [sum_insert n₁, sum_insert n₂, sum_insert n₃, sum_insert n₄, sum_singleton,
      e₁, e₂, e₃, e₄, e₅, T.intersection_comm c₂ c₁, T.intersection_comm c₃ c₁,
      T.intersection_comm c₃ c₂, T.intersection_comm c₄ c₁, T.intersection_comm c₄ c₂,
      T.intersection_comm c₄ c₃, T.intersection_comm c₅ c₁, T.intersection_comm c₅ c₂,
      T.intersection_comm c₅ c₃, T.intersection_comm c₅ c₄]
    ring
  rw [← hval]
  exact T.sum_sum_intersection_mul_neg hsu hmem

/-! ### Six components -/

/-- In a numerical type with more than six components, the intersection form is negative definite
on vectors supported on six distinct components. -/
theorem intersection_six_neg (hcard : 6 < Fintype.card T.Component)
    {c₁ c₂ c₃ c₄ c₅ c₆ : T.Component}
    (h₁₂ : c₁ ≠ c₂) (h₁₃ : c₁ ≠ c₃) (h₁₄ : c₁ ≠ c₄) (h₁₅ : c₁ ≠ c₅) (h₁₆ : c₁ ≠ c₆)
    (h₂₃ : c₂ ≠ c₃) (h₂₄ : c₂ ≠ c₄) (h₂₅ : c₂ ≠ c₅) (h₂₆ : c₂ ≠ c₆)
    (h₃₄ : c₃ ≠ c₄) (h₃₅ : c₃ ≠ c₅) (h₃₆ : c₃ ≠ c₆)
    (h₄₅ : c₄ ≠ c₅) (h₄₆ : c₄ ≠ c₆) (h₅₆ : c₅ ≠ c₆)
    {y₁ y₂ y₃ y₄ y₅ y₆ : ℤ}
    (hy : ¬(y₁ = 0 ∧ y₂ = 0 ∧ y₃ = 0 ∧ y₄ = 0 ∧ y₅ = 0 ∧ y₆ = 0)) :
    T.intersection c₁ c₁ * y₁ ^ 2 + T.intersection c₂ c₂ * y₂ ^ 2 +
          T.intersection c₃ c₃ * y₃ ^ 2 + T.intersection c₄ c₄ * y₄ ^ 2 +
        T.intersection c₅ c₅ * y₅ ^ 2 + T.intersection c₆ c₆ * y₆ ^ 2 +
      2 * (T.intersection c₁ c₂ * y₁ * y₂ + T.intersection c₁ c₃ * y₁ * y₃ +
        T.intersection c₁ c₄ * y₁ * y₄ + T.intersection c₁ c₅ * y₁ * y₅ +
        T.intersection c₁ c₆ * y₁ * y₆ + T.intersection c₂ c₃ * y₂ * y₃ +
        T.intersection c₂ c₄ * y₂ * y₄ + T.intersection c₂ c₅ * y₂ * y₅ +
        T.intersection c₂ c₆ * y₂ * y₆ + T.intersection c₃ c₄ * y₃ * y₄ +
        T.intersection c₃ c₅ * y₃ * y₅ + T.intersection c₃ c₆ * y₃ * y₆ +
        T.intersection c₄ c₅ * y₄ * y₅ + T.intersection c₄ c₆ * y₄ * y₆ +
        T.intersection c₅ c₆ * y₅ * y₆) < 0 := by
  classical
  let y : T.Component → ℤ := fun m ↦
    if m = c₁ then y₁ else if m = c₂ then y₂ else if m = c₃ then y₃
      else if m = c₄ then y₄ else if m = c₅ then y₅ else if m = c₆ then y₆ else 0
  have e₁ : y c₁ = y₁ := by simp [y]
  have e₂ : y c₂ = y₂ := by simp [y, h₁₂.symm]
  have e₃ : y c₃ = y₃ := by simp [y, h₁₃.symm, h₂₃.symm]
  have e₄ : y c₄ = y₄ := by simp [y, h₁₄.symm, h₂₄.symm, h₃₄.symm]
  have e₅ : y c₅ = y₅ := by
    simp [y, h₁₅.symm, h₂₅.symm, h₃₅.symm, h₄₅.symm]
  have e₆ : y c₆ = y₆ := by
    simp [y, h₁₆.symm, h₂₆.symm, h₃₆.symm, h₄₆.symm, h₅₆.symm]
  have hmem : ∃ i ∈ ({c₁, c₂, c₃, c₄, c₅, c₆} : Finset T.Component), y i ≠ 0 := by
    rcases (by omega : y₁ ≠ 0 ∨ y₂ ≠ 0 ∨ y₃ ≠ 0 ∨ y₄ ≠ 0 ∨ y₅ ≠ 0 ∨ y₆ ≠ 0) with
      h | h | h | h | h | h
    · exact ⟨c₁, by simp, by rw [e₁]; exact h⟩
    · exact ⟨c₂, by simp, by rw [e₂]; exact h⟩
    · exact ⟨c₃, by simp, by rw [e₃]; exact h⟩
    · exact ⟨c₄, by simp, by rw [e₄]; exact h⟩
    · exact ⟨c₅, by simp, by rw [e₅]; exact h⟩
    · exact ⟨c₆, by simp, by rw [e₆]; exact h⟩
  have hsu : ({c₁, c₂, c₃, c₄, c₅, c₆} : Finset T.Component) ≠ univ := by
    exact (card_lt_iff_ne_univ _).mp (card_le_six.trans_lt hcard)
  have hval : ∑ i ∈ ({c₁, c₂, c₃, c₄, c₅, c₆} : Finset T.Component),
      ∑ j ∈ ({c₁, c₂, c₃, c₄, c₅, c₆} : Finset T.Component),
        T.intersection i j * y i * y j =
      T.intersection c₁ c₁ * y₁ ^ 2 + T.intersection c₂ c₂ * y₂ ^ 2 +
            T.intersection c₃ c₃ * y₃ ^ 2 + T.intersection c₄ c₄ * y₄ ^ 2 +
          T.intersection c₅ c₅ * y₅ ^ 2 + T.intersection c₆ c₆ * y₆ ^ 2 +
        2 * (T.intersection c₁ c₂ * y₁ * y₂ + T.intersection c₁ c₃ * y₁ * y₃ +
          T.intersection c₁ c₄ * y₁ * y₄ + T.intersection c₁ c₅ * y₁ * y₅ +
          T.intersection c₁ c₆ * y₁ * y₆ + T.intersection c₂ c₃ * y₂ * y₃ +
          T.intersection c₂ c₄ * y₂ * y₄ + T.intersection c₂ c₅ * y₂ * y₅ +
          T.intersection c₂ c₆ * y₂ * y₆ + T.intersection c₃ c₄ * y₃ * y₄ +
          T.intersection c₃ c₅ * y₃ * y₅ + T.intersection c₃ c₆ * y₃ * y₆ +
          T.intersection c₄ c₅ * y₄ * y₅ + T.intersection c₄ c₆ * y₄ * y₆ +
          T.intersection c₅ c₆ * y₅ * y₆) := by
    have n₁ : c₁ ∉ ({c₂, c₃, c₄, c₅, c₆} : Finset T.Component) := by
      simp [h₁₂, h₁₃, h₁₄, h₁₅, h₁₆]
    have n₂ : c₂ ∉ ({c₃, c₄, c₅, c₆} : Finset T.Component) := by
      simp [h₂₃, h₂₄, h₂₅, h₂₆]
    have n₃ : c₃ ∉ ({c₄, c₅, c₆} : Finset T.Component) := by
      simp [h₃₄, h₃₅, h₃₆]
    have n₄ : c₄ ∉ ({c₅, c₆} : Finset T.Component) := by simp [h₄₅, h₄₆]
    have n₅ : c₅ ∉ ({c₆} : Finset T.Component) := by simp [h₅₆]
    simp only [sum_insert n₁, sum_insert n₂, sum_insert n₃, sum_insert n₄,
      sum_insert n₅, sum_singleton, e₁, e₂, e₃, e₄, e₅, e₆,
      T.intersection_comm c₂ c₁, T.intersection_comm c₃ c₁,
      T.intersection_comm c₃ c₂, T.intersection_comm c₄ c₁,
      T.intersection_comm c₄ c₂, T.intersection_comm c₄ c₃,
      T.intersection_comm c₅ c₁, T.intersection_comm c₅ c₂,
      T.intersection_comm c₅ c₃, T.intersection_comm c₅ c₄,
      T.intersection_comm c₆ c₁, T.intersection_comm c₆ c₂,
      T.intersection_comm c₆ c₃, T.intersection_comm c₆ c₄,
      T.intersection_comm c₆ c₅]
    ring
  rw [← hval]
  exact T.sum_sum_intersection_mul_neg hsu hmem

end NumericalType

end TauCeti
