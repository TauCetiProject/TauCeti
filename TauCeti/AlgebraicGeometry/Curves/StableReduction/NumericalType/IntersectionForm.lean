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
particular every proper principal submatrix of `A` is negative definite, and for two distinct
components `i` and `j` of a numerical type with more than two components,
`aᵢⱼ² < aᵢᵢ aⱼⱼ`.

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

end NumericalType

end TauCeti
