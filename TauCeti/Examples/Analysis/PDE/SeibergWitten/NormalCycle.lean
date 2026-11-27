/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.RingTheory.Polynomial.PrescribedPowerSums
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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
`2 b₂ = b₁ M₁ - M₂` (`two_mul_newtonCoeff_two_eq`), and `2 b₂ = 2 V₁ V₂`
(`newtonCoeff_two_pair`), so `P_z(W) = (W - V₁) (W - V₂)` (`newtonPolynomial_pair`). The
recursion without the factor `j` would set `b₂ = b₁ M₁ - M₂ = 2 V₁ V₂`
(`newtonCoeff_one_mul_sub_eq_two_mul`), which is not `V₁ V₂` once `V₁ V₂ ≠ 0`
(`newtonCoeff_one_mul_sub_ne_mul`).

**The exponent `p_m = 2 + 2 / m`.** Its Morrey exponent is `1 - 2 / p_m = 1 / (m + 1)`
(`one_sub_two_div_two_add_two_div`). For `0 < k ≤ m`, the exponent of a power substitution of
degree `k` satisfies `p_m (1 - 2 / k) ≤ p_m (1 - 2 / m) = 2 - 2 / m - 4 / m²`
(`two_add_two_div_mul_one_sub_two_div_le`, `two_add_two_div_mul_one_sub_two_div`), so it stays
below `2` (`two_add_two_div_mul_one_sub_two_div_lt_two`). The margin `p_m (1 - 1 / m) < 2` of the
individual branches is `TauCeti.two_add_two_div_mul_one_sub_inv_lt_two`.

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

/-- **The first Newton coefficient of two points** is their sum: `b₁ = V₁ + V₂`. -/
theorem newtonCoeff_one_pair :
    newtonCoeff (fun j => V₁ ^ j + V₂ ^ j) 1 = V₁ + V₂ := by
  simpa using newtonCoeff_sum_map_pow {V₁, V₂} 1

/-- **The second Newton coefficient of two points** is their product: `b₂ = V₁ V₂`. -/
theorem newtonCoeff_two_pair :
    newtonCoeff (fun j => V₁ ^ j + V₂ ^ j) 2 = V₁ * V₂ := by
  simpa using newtonCoeff_sum_map_pow {V₁, V₂} 2

/-- **Newton's recursion at `j = 2`**: `2 b₂ = b₁ M₁ - M₂`, for every sequence of moments. -/
theorem two_mul_newtonCoeff_two_eq (M : ℕ → K) :
    2 * newtonCoeff M 2 = newtonCoeff M 1 * M 1 - M 2 := by
  have h := mul_newtonCoeff_eq_sum M 2
  rw [show ({a ∈ Finset.antidiagonal 2 | a.1 < 2} : Finset (ℕ × ℕ)) = {(0, 2), (1, 1)} by
    decide] at h
  norm_num at h
  rw [h]
  ring

/-- **The Newton polynomial of two points** is `(X - V₁) (X - V₂)`: its roots are the points. -/
theorem newtonPolynomial_pair :
    newtonPolynomial (fun j => V₁ ^ j + V₂ ^ j) 2 = (X - C V₁) * (X - C V₂) := by
  simpa using newtonPolynomial_sum_map_pow {V₁, V₂}

/-- **The recursion without the factor `j`** would set `b₂ = b₁ M₁ - M₂`, which for two points is
`2 V₁ V₂`. -/
theorem newtonCoeff_one_mul_sub_eq_two_mul :
    newtonCoeff (fun j => V₁ ^ j + V₂ ^ j) 1 * (V₁ ^ 1 + V₂ ^ 1) - (V₁ ^ 2 + V₂ ^ 2) =
      2 * (V₁ * V₂) := by
  rw [← newtonCoeff_two_pair V₁ V₂, two_mul_newtonCoeff_two_eq]

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

variable {m : ℝ}

/-- **The Morrey exponent of `p_m = 2 + 2 / m`** is `1 - 2 / p_m = 1 / (m + 1)`. -/
theorem one_sub_two_div_two_add_two_div (hm : m ≠ 0) (hm₁ : m + 1 ≠ 0) :
    1 - 2 / (2 + 2 / m) = 1 / (m + 1) := by
  field_simp
  ring

/-- `p_m (1 - 2 / m) = 2 - 2 / m - 4 / m²` for `p_m = 2 + 2 / m`. -/
theorem two_add_two_div_mul_one_sub_two_div (hm : m ≠ 0) :
    (2 + 2 / m) * (1 - 2 / m) = 2 - 2 / m - 4 / m ^ 2 := by
  field_simp
  ring

/-- **Monotonicity of the exponent in the degree**: for `0 < k ≤ m`,
`p_m (1 - 2 / k) ≤ p_m (1 - 2 / m)`. -/
theorem two_add_two_div_mul_one_sub_two_div_le {k : ℝ} (hk : 0 < k) (hkm : k ≤ m) :
    (2 + 2 / m) * (1 - 2 / k) ≤ (2 + 2 / m) * (1 - 2 / m) := by
  have hm : 0 < m := hk.trans_le hkm
  gcongr

/-- **The margin of the exponent `p_m = 2 + 2 / m`**: for `0 < k ≤ m`, `p_m (1 - 2 / k) < 2`. -/
theorem two_add_two_div_mul_one_sub_two_div_lt_two {k : ℝ} (hk : 0 < k) (hkm : k ≤ m) :
    (2 + 2 / m) * (1 - 2 / k) < 2 := by
  have hm : 0 < m := hk.trans_le hkm
  refine (two_add_two_div_mul_one_sub_two_div_le hk hkm).trans_lt ?_
  rw [two_add_two_div_mul_one_sub_two_div hm.ne']
  have : 0 < 2 / m + 4 / m ^ 2 := by positivity
  linarith

end Exponent

end TauCeti.Examples.NormalCycle
