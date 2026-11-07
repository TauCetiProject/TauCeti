/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Gauss
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Relation
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.AGM.SecondKind

/-!
# The Gauss–Brent–Salamin formula for `π`

Gauss's theorem expresses `K(k)` by the AGM `M(1, k′)`, the AGM evaluation of the second kind
expresses `E(k) / K(k)` by the squared AGM corrections, and Legendre's relation ties the
complete integrals at complementary moduli `k` and `k′ = √(1 - k²)` to `π / 2`. Combined, they
express `π` by two AGM iterations alone:

* `TauCeti.Real.pi_eq_four_mul_agm_mul_agm_div_one_sub_tsum`: for `x, y > 0` with
  `x² + y² = 1`, Salamin's formula
  `π = 4 M(1, x) M(1, y) / (1 - ∑ 2ʲ (cⱼ(x)² + cⱼ(y)²))`;
* `TauCeti.Real.pi_eq_four_mul_agm_sq_div_one_sub_tsum`: the self-complementary case
  `x = y = 1 / √2`, the **Gauss–Brent–Salamin formula**
  `π = 4 M(1, 1/√2)² / (1 - ∑_{j ≥ 1} 2^(j+1) cⱼ²)`.

Here `cⱼ² = aⱼ² - gⱼ²` for the AGM iteration `a₀ = 1`, `g₀ = x`, with `j ≥ 1`. Mathlib's
`NNReal.agmSequences 1 x n` is the pair `(gₙ₊₁, aₙ₊₁)`, so its index `n` corresponds to the
classical index `j = n + 1`. Truncating the series and the AGM after finitely many steps gives
the Brent–Salamin algorithm for computing `π`.

## References

* E. Salamin, Computation of π using arithmetic-geometric mean, *Math. Comp.* 30 (1976),
  565–570.
* R. P. Brent, Fast multiple-precision evaluation of elementary functions, *J. ACM* 23 (1976),
  242–251.
* J. M. Borwein and P. B. Borwein, *Pi and the AGM*, Wiley, 1987, §2.4.
-/

public section

namespace TauCeti.Real

open _root_.Real
open NNReal (agm agmSequences)
open scoped NNReal

/-- **Salamin's formula** for complementary moduli: if `x, y > 0` and `x² + y² = 1`, then
`π = 4 M(1, x) M(1, y) / (1 - ∑ₙ 2ⁿ⁺¹ (cₙ₊₁(x)² + cₙ₊₁(y)²))`, where `M` is the AGM and
`cₙ₊₁(x)² = aₙ₊₁² - gₙ₊₁²` is the squared correction of the AGM iteration started at `(1, x)`.
Mathlib's `agmSequences 1 x n` is the pair `(gₙ₊₁, aₙ₊₁)`. -/
theorem pi_eq_four_mul_agm_mul_agm_div_one_sub_tsum {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ^ 2 + y ^ 2 = 1) :
    π = 4 * agm 1 x * agm 1 y / (1 - ∑' n, (2 : ℝ) ^ (n + 1) *
      (((agmSequences 1 x n).2 : ℝ) ^ 2 - ((agmSequences 1 x n).1 : ℝ) ^ 2 +
        (((agmSequences 1 y n).2 : ℝ) ^ 2 - ((agmSequences 1 y n).1 : ℝ) ^ 2))) := by
  have hxy' : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 = 1 := by exact_mod_cast hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  -- The complementary modulus of `x` is `y`, and vice versa, in each spelling used upstream.
  have hcomp {u v : ℝ≥0} (huv : (u : ℝ) ^ 2 + (v : ℝ) ^ 2 = 1) :
      √(1 - (u : ℝ) ^ 2) = v ∧ NNReal.sqrt (Real.toNNReal (1 - (u : ℝ) ^ 2)) = v ∧
        (√(1 - (u : ℝ) ^ 2)).toNNReal = v := by
    have hv : √(1 - (u : ℝ) ^ 2) = v := by
      rw [show 1 - (u : ℝ) ^ 2 = (v : ℝ) ^ 2 by linarith, sqrt_sq v.coe_nonneg]
    refine ⟨hv, ?_, by rw [hv, toNNReal_coe]⟩
    ext
    rw [coe_sqrt, coe_toNNReal _ (by nlinarith [sq_nonneg (v : ℝ)]), hv]
  obtain ⟨hyx, hyx', hyx''⟩ := hcomp (u := y) (v := x) (by linarith)
  obtain ⟨-, hxy₁', hxy₁''⟩ := hcomp (u := x) (v := y) hxy'
  have hy₁ : (y : ℝ) ^ 2 < 1 := by nlinarith
  have hx₁ : (x : ℝ) ^ 2 < 1 := by nlinarith
  have hy₂ : (y : ℝ) < 1 := by nlinarith
  -- Gauss's theorem, the AGM evaluation of `E`, and Legendre's relation at modulus `y`.
  have hKy := legendreK_eq_pi_div_two_mul_agm hy₁
  have hKx := legendreK_eq_pi_div_two_mul_agm hx₁
  rw [hyx''] at hKy
  rw [hxy₁''] at hKx
  have hEy := hasSum_legendreEc_agm hy₁
  have hEx := hasSum_legendreEc_agm hx₁
  rw [hyx'] at hEy
  rw [hxy₁'] at hEx
  have hL := legendre_relation hy' hy₂
  rw [hyx] at hL
  have hKy₀ := legendreK_pos hy₁
  have hKx₀ := legendreK_pos hx₁
  have hA : (0 : ℝ) < agm 1 x := NNReal.coe_pos.2 (NNReal.agm_pos one_pos hx)
  have hB : (0 : ℝ) < agm 1 y := NNReal.coe_pos.2 (NNReal.agm_pos one_pos hy)
  -- Legendre's relation evaluates the denominator as `π / (K(y) K(x)) = 4 M(1, x) M(1, y) / π`.
  have hD : 1 - 2 * (1 - (y : ℝ) ^ 2 / 2 - legendreEc y / legendreK y +
      (1 - (x : ℝ) ^ 2 / 2 - legendreEc x / legendreK x)) =
      π / (legendreK y * legendreK x) := by
    field_simp
    linear_combination 2 * hL + legendreK y * legendreK x * hxy'
  have hπ : π = 4 * agm 1 x * agm 1 y / (1 - 2 * (1 - (y : ℝ) ^ 2 / 2 -
      legendreEc y / legendreK y + (1 - (x : ℝ) ^ 2 / 2 - legendreEc x / legendreK x))) := by
    rw [hD, hKy, hKx]
    field_simp
    norm_num
  refine hπ.trans ?_
  congr 2
  exact ((hEy.add hEx).mul_left 2).tsum_eq.symm.trans (tsum_congr fun n ↦ by ring)

/-- **The Gauss–Brent–Salamin formula**: with the AGM iteration `a₀ = 1`, `g₀ = 1 / √2` and
`cⱼ² = aⱼ² - gⱼ²`, `π = 4 M(1, 1/√2)² / (1 - ∑_{j ≥ 1} 2^(j+1) cⱼ²)`. Mathlib's
`agmSequences 1 (√2)⁻¹ n` is the pair `(gₙ₊₁, aₙ₊₁)`, so the series index is `n = j - 1`. -/
theorem pi_eq_four_mul_agm_sq_div_one_sub_tsum :
    π = 4 * agm 1 (NNReal.sqrt 2)⁻¹ ^ 2 / (1 - ∑' n, (2 : ℝ) ^ (n + 2) *
      (((agmSequences 1 (NNReal.sqrt 2)⁻¹ n).2 : ℝ) ^ 2 -
        ((agmSequences 1 (NNReal.sqrt 2)⁻¹ n).1 : ℝ) ^ 2)) := by
  have hs : 0 < (NNReal.sqrt 2)⁻¹ := by positivity
  have hsq : ((NNReal.sqrt 2)⁻¹) ^ 2 + ((NNReal.sqrt 2)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, NNReal.sq_sqrt, ← two_mul, mul_inv_cancel₀ two_ne_zero]
  rw [pi_eq_four_mul_agm_mul_agm_div_one_sub_tsum hs hs hsq]
  rw [mul_assoc, ← sq]
  congr 3
  exact funext fun n ↦ by ring

end TauCeti.Real
