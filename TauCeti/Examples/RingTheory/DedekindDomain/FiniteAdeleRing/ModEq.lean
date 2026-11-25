/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ModEq

/-!
# Checks for congruence of finite adeles

The Checks of AdelicAlgebraicGroups §5.2, *Integral adelic congruence*, over `ℤ ⊆ ℚ`: modulo
zero congruence is equality; `1 ≡ 0` modulo `1`; `1` is not congruent to `0` modulo `2`; and the
inverse-based expression `(x - y) / N` at `N = 0` is `0`, hence integral, even for the pair
`(1, 0)`, which is not congruent modulo zero.
-/

public section

namespace TauCeti.FiniteAdeleModEqChecks

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing

/-- Modulo zero, congruence is equality. -/
example (x y : FiniteAdeleRing ℤ ℚ) : ModEq 0 x y ↔ x = y :=
  modEq_zero_iff

/-- `1 ≡ 0` modulo `1`. -/
example : ModEq (1 : ℤ) (1 : FiniteAdeleRing ℤ ℚ) 0 :=
  modEq_iff.mpr ⟨1, one_mem _, by simp⟩

/-- `1` is not congruent to `0` modulo `2`: `1 / 2` is not integral. -/
example : ¬ ModEq (2 : ℤ) (1 : FiniteAdeleRing ℤ ℚ) 0 := by
  rw [modEq_iff_mul_inv_mem two_ne_zero, sub_zero, mul_one, algebraMap_mem_integralAdeles_iff]
  rintro ⟨n, hn⟩
  have h : (2 : ℚ) * n = 1 := by
    rw [show ((n : ℤ) : ℚ) = algebraMap ℤ ℚ n from rfl, hn]
    norm_num
  have h' : (2 * n : ℤ) = 1 := by exact_mod_cast h
  omega

/-- At `N = 0` the inverse-based expression `(1 - 0) / 0` is `0`, which is integral, although `1`
and `0` are not congruent modulo zero: it cannot define congruence modulo zero. -/
example : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (algebraMap ℤ ℚ 0)⁻¹ * (1 - 0) ∈
      integralAdeles ℤ ℚ ∧ ¬ ModEq (0 : ℤ) (1 : FiniteAdeleRing ℤ ℚ) 0 := by
  refine ⟨by simp, fun h ↦ one_ne_zero (α := ℚ) (algebraMap_injective ℚ Int.not_isField ?_)⟩
  rw [map_one, map_zero]
  exact modEq_zero_iff.mp h

end TauCeti.FiniteAdeleModEqChecks
