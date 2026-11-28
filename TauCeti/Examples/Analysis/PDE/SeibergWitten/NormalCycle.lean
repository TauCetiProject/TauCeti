/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.RingTheory.Polynomial.PrescribedPowerSums
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import TauCeti.Analysis.Complex.PowSubstitution

/-!
# Examples: the Newton coefficients and exponents of the normal cycle

Near a pseudoholomorphic curve `C`, Taubes reads a large-parameter Seiberg–Witten solution
through the moments `M_k = ∫ Wᵏ dμ_z` of its normalized curvature slices `μ_z` on the normal
fibres. Newton's recursion `b₀ = 1`, `j b_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} M_k`
(`TauCeti.newtonCoeff`) turns them into the coefficients of the monic polynomial
`P_z(W) = Wᵐ - b₁ W^(m-1) + ⋯ + (-1)ᵐ b_m` (`TauCeti.newtonPolynomial`), and the coefficients are
estimated in `L^(p_m)` with `p_m = 2 + 2 / m`. This file checks both normalizations on explicit
examples, and shows how the competing conventions would fail.

**Newton's recursion.** For the counting measure of two points `V₁, V₂`, the moments are the power
sums `M_k = V₁ᵏ + V₂ᵏ`. Then `b₁ = V₁ + V₂` (`newtonCoeff_one_pair`), the recursion at `j = 2` reads
`2 b₂ = b₁ M₁ - M₂` (`TauCeti.two_mul_newtonCoeff_two`), and `2 b₂ = 2 V₁ V₂`
(`newtonCoeff_two_pair`), so `P_z(W) = (W - V₁) (W - V₂)` (`newtonPolynomial_pair`). The
recursion without the factor `j` would set `b₂ = b₁ M₁ - M₂ = 2 V₁ V₂`
(`newtonCoeff_one_mul_sub_eq_two_mul`), which is not `V₁ V₂` once `V₁ V₂ ≠ 0`
(`newtonCoeff_one_mul_sub_ne_mul`).

**The exponent `p_m = 2 + 2 / m`.** Its Morrey exponent is `1 - 2 / p_m = 1 / (m + 1)`
(`TauCeti.one_sub_two_div_two_add_two_div`). For `0 < k ≤ m`, the exponent of a power substitution
of degree `k` satisfies `p_m (1 - 2 / k) ≤ p_m (1 - 2 / m) = 2 - 2 / m - 4 / m²`
(`TauCeti.two_add_two_div_mul_one_sub_two_div_le`,
`TauCeti.two_add_two_div_mul_one_sub_two_div`), so it stays below `2`
(`TauCeti.two_add_two_div_mul_one_sub_two_div_lt_two`). The examples below instantiate these for a
natural number of sheets, and for `m = 3`. The margin `p_m (1 - 1 / m) < 2` of the individual
branches is `TauCeti.two_add_two_div_mul_one_sub_inv_lt_two`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti.Examples.NormalCycle

/-! ### Newton's recursion for two points -/

section Newton

variable {K : Type*} [Field K] [CharZero K] (V₁ V₂ : K)

omit [CharZero K] in
/-- **The first Newton coefficient of two points** is their sum: `b₁ = V₁ + V₂`. -/
theorem newtonCoeff_one_pair :
    newtonCoeff (fun j => V₁ ^ j + V₂ ^ j) 1 = V₁ + V₂ := by
  simp

/-- **The second Newton coefficient of two points** is their product: `b₂ = V₁ V₂`. -/
theorem newtonCoeff_two_pair :
    newtonCoeff (fun j => V₁ ^ j + V₂ ^ j) 2 = V₁ * V₂ := by
  simpa using newtonCoeff_sum_map_pow {V₁, V₂} 2

/-- **The Newton polynomial of two points** is `(X - V₁) (X - V₂)`: its roots are the points. -/
theorem newtonPolynomial_pair :
    newtonPolynomial (fun j => V₁ ^ j + V₂ ^ j) 2 = (X - C V₁) * (X - C V₂) := by
  simpa using newtonPolynomial_sum_map_pow {V₁, V₂}

/-- **The recursion without the factor `j`** would set `b₂ = b₁ M₁ - M₂`, which for two points is
`2 V₁ V₂`. -/
theorem newtonCoeff_one_mul_sub_eq_two_mul :
    newtonCoeff (fun j => V₁ ^ j + V₂ ^ j) 1 * (V₁ ^ 1 + V₂ ^ 1) - (V₁ ^ 2 + V₂ ^ 2) =
      2 * (V₁ * V₂) := by
  rw [← newtonCoeff_two_pair V₁ V₂, two_mul_newtonCoeff_two]

/-- **The recursion without the factor `j` is wrong**: for two points with `V₁ V₂ ≠ 0`, the value
`b₁ M₁ - M₂` is not the second elementary symmetric function `V₁ V₂`. -/
theorem newtonCoeff_one_mul_sub_ne_mul (h : V₁ * V₂ ≠ 0) :
    newtonCoeff (fun j => V₁ ^ j + V₂ ^ j) 1 * (V₁ ^ 1 + V₂ ^ 1) - (V₁ ^ 2 + V₂ ^ 2) ≠
      V₁ * V₂ := by
  rw [newtonCoeff_one_mul_sub_eq_two_mul]
  intro h2
  exact h (by linear_combination h2)

end Newton

/-! ### The exponent `p_m = 2 + 2 / m` -/

section Exponent

/-- **The Morrey exponent of `p_m` for `m` sheets**: for a positive number of sheets `m`,
`1 - 2 / p_m = 1 / (m + 1)`. -/
example {m : ℕ} (hm : m ≠ 0) : 1 - 2 / (2 + 2 / (m : ℝ)) = 1 / (m + 1) :=
  one_sub_two_div_two_add_two_div (Nat.cast_ne_zero.2 hm) (Nat.cast_add_one_ne_zero m)

/-- For three sheets, `p₃ = 8 / 3` has Morrey exponent `1 / 4`. -/
example : 1 - 2 / (2 + 2 / (3 : ℝ)) = 1 / 4 := by
  rw [one_sub_two_div_two_add_two_div three_ne_zero (by norm_num)]
  norm_num

/-- **Monotonicity in the degree**: for `0 < k ≤ m` sheets, `p_m (1 - 2 / k) ≤ p_m (1 - 2 / m)`. -/
example {m k : ℕ} (hk : 0 < k) (hkm : k ≤ m) :
    (2 + 2 / (m : ℝ)) * (1 - 2 / k) ≤ (2 + 2 / (m : ℝ)) * (1 - 2 / m) :=
  two_add_two_div_mul_one_sub_two_div_le (Nat.cast_pos.2 hk) (Nat.cast_le.2 hkm)

/-- **The margin in degree `k`**: for `0 < k ≤ m` sheets, `p_m (1 - 2 / k) < 2`. -/
example {m k : ℕ} (hk : 0 < k) (hkm : k ≤ m) : (2 + 2 / (m : ℝ)) * (1 - 2 / k) < 2 :=
  two_add_two_div_mul_one_sub_two_div_lt_two (Nat.cast_pos.2 hk) (Nat.cast_le.2 hkm)

end Exponent

end TauCeti.Examples.NormalCycle
