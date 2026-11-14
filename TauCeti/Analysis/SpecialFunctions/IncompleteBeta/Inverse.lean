/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Basic

/-!
# Reflection and boundary-shape formulas for the inverse regularized incomplete beta function

The regularized incomplete beta function satisfies the reflection identity
`I_x(a, b) = 1 - I_{1 - x}(b, a)` (`TauCeti.regularizedIncompleteBeta_symm`) and collapses to the
elementary powers `x ^ a` at `b = 1` and `1 - (1 - x) ^ b` at `a = 1`. On the interior domain
`0 < a`, `0 < b`, and `u ∈ (0, 1)`, inverting these identities yields the corresponding reflection
formula for `TauCeti.inverseRegularizedIncompleteBeta` and its closed forms when either shape
parameter is `1`.

Positivity of the shape parameters and strict interiority `0 < u` and `u < 1` are genuinely
required: outside that domain `TauCeti.inverseRegularizedIncompleteBeta` takes the junk value `0`,
which breaks reflection (`0 ≠ 1 - 0`) and disagrees with `u ^ a⁻¹` at `u = 1`.

## Main results

* `TauCeti.inverseRegularizedIncompleteBeta_symm` — the reflection identity
  `I⁻¹_u(a, b) = 1 - I⁻¹_{1 - u}(b, a)` for positive shape parameters and `u ∈ (0, 1)`;
* `TauCeti.inverseRegularizedIncompleteBeta_one_right` — `I⁻¹_u(a, 1) = u ^ a⁻¹`;
* `TauCeti.inverseRegularizedIncompleteBeta_one_left` — `I⁻¹_u(1, b) = 1 - (1 - u) ^ b⁻¹`;
* `TauCeti.inverseRegularizedIncompleteBeta_one_one` — `I⁻¹_u(1, 1) = u`.

## References

* [NIST Digital Library of Mathematical Functions, §8.17](https://dlmf.nist.gov/8.17)
-/

public section

noncomputable section

open Set

namespace TauCeti

variable {a b u : ℝ}

/-- **Reflection of the inverse regularized incomplete beta function.** On the interior domain
`0 < a`, `0 < b`, and `0 < u < 1`, swapping the shape parameters reflects both the probability
level and the output across `1 / 2`. Outside `(0, 1)` the zero junk value breaks the outer
`1 - ·` reflection. -/
theorem inverseRegularizedIncompleteBeta_symm (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 < u) (hu1 : u < 1) :
    inverseRegularizedIncompleteBeta a b u =
      1 - inverseRegularizedIncompleteBeta b a (1 - u) := by
  have hu'0 : 0 < 1 - u := sub_pos.mpr hu1
  have hu'1 : 1 - u < 1 := sub_lt_self 1 hu0
  have hmem := inverseRegularizedIncompleteBeta_mem_Ioo hb ha hu'0 hu'1
  set y : ℝ := 1 - inverseRegularizedIncompleteBeta b a (1 - u)
  have hy0 : 0 < y := sub_pos.mpr hmem.2
  have hy1 : y < 1 := sub_lt_self 1 hmem.1
  have hval : regularizedIncompleteBeta a b y = u := by
    rw [regularizedIncompleteBeta_symm ha hb y, sub_sub_cancel,
      regularizedIncompleteBeta_inverse hb ha hu'0 hu'1, sub_sub_cancel]
  conv_lhs => rw [← hval]
  exact inverseRegularizedIncompleteBeta_regularizedIncompleteBeta ha hb hy0 hy1

/-- At second shape parameter `1`, the inverse regularized incomplete beta function on `(0, 1)` is
the power `u ^ a⁻¹`. -/
@[simp]
theorem inverseRegularizedIncompleteBeta_one_right (ha : 0 < a) (hu0 : 0 < u) (hu1 : u < 1) :
    inverseRegularizedIncompleteBeta a 1 u = u ^ a⁻¹ := by
  have hq : u ^ a⁻¹ ∈ Ioo 0 1 :=
    ⟨Real.rpow_pos_of_pos hu0 _, Real.rpow_lt_one hu0.le hu1 (inv_pos.2 ha)⟩
  have hval : regularizedIncompleteBeta a 1 (u ^ a⁻¹) = u := by
    rw [regularizedIncompleteBeta_one_right ha hq.1.le hq.2.le, ← Real.rpow_mul hu0.le,
      inv_mul_cancel₀ ha.ne', Real.rpow_one]
  conv_lhs => rw [← hval]
  exact inverseRegularizedIncompleteBeta_regularizedIncompleteBeta ha one_pos hq.1 hq.2

/-- At first shape parameter `1`, the inverse regularized incomplete beta function on `(0, 1)` is
the complementary power `1 - (1 - u) ^ b⁻¹`. -/
@[simp]
theorem inverseRegularizedIncompleteBeta_one_left (hb : 0 < b) (hu0 : 0 < u) (hu1 : u < 1) :
    inverseRegularizedIncompleteBeta 1 b u = 1 - (1 - u) ^ b⁻¹ := by
  rw [inverseRegularizedIncompleteBeta_symm one_pos hb hu0 hu1,
    inverseRegularizedIncompleteBeta_one_right hb (sub_pos.mpr hu1) (sub_lt_self 1 hu0)]

/-- At unit shape parameters `(1, 1)`, the inverse regularized incomplete beta function is the
identity on `(0, 1)`. -/
theorem inverseRegularizedIncompleteBeta_one_one (hu0 : 0 < u) (hu1 : u < 1) :
    inverseRegularizedIncompleteBeta 1 1 u = u := by
  simp [hu0, hu1]

end TauCeti
