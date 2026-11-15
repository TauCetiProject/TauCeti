/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination

/-!
# A scale-invariant root bound for monic polynomials

Let `p = Xᵈ + a_{d-1} X^{d-1} + ⋯ + a₀` be a monic polynomial over a normed field whose
coefficients satisfy `‖aᵢ‖ ≤ c^(d - i)`. Then every root `z` of `p` satisfies `‖z‖ ≤ 2 c`
(`Polynomial.IsRoot.norm_le_two_mul`). Unlike Cauchy's bound `‖z‖ < 1 + maxᵢ ‖aᵢ‖`
(`Polynomial.IsRoot.norm_lt_cauchyBound`), this bound is homogeneous: replacing the roots `z` by
`t z` multiplies `aᵢ` by `t^(d - i)`, and the bound by `‖t‖`. It is a form of Fujiwara's bound
`‖z‖ ≤ 2 maxᵢ ‖aᵢ‖^(1 / (d - i))`, stated without fractional powers.

If `‖z‖ > 2 c`, then `‖aᵢ zⁱ‖ ≤ 2^-(d - i) ‖z‖ᵈ`, and these weights sum to less than one, which
contradicts `zᵈ = -∑_{i < d} aᵢ zⁱ`.

## References

* M. Fujiwara, *Über die obere Schranke des absoluten Betrages der Wurzeln einer algebraischen
  Gleichung*, Tôhoku Math. J. 10 (1916), 167–171.
-/

public section

namespace Polynomial

variable {K : Type*} [NormedField K]

/-- **A Fujiwara-type root bound.** If the coefficients of a monic polynomial `p` of degree `d`
satisfy `‖p.coeff i‖ ≤ c ^ (d - i)` for every `i < d`, then every root `z` of `p` satisfies
`‖z‖ ≤ 2 * c`. -/
theorem IsRoot.norm_le_two_mul {p : K[X]} (hp : p.Monic) {c : ℝ}
    (hc : ∀ i < p.natDegree, ‖p.coeff i‖ ≤ c ^ (p.natDegree - i)) {z : K} (hz : p.IsRoot z) :
    ‖z‖ ≤ 2 * c := by
  set d := p.natDegree
  by_contra! hlt
  -- `c ≥ 0` because the coefficient of `X^(d - 1)` has norm at most `c` (a root forces `d > 0`).
  have hd : 0 < d := by
    by_contra! h
    have hp1 : p = 1 := hp.natDegree_eq_zero.1 (Nat.le_zero.1 h)
    simp [hp1] at hz
  have hc₀ : 0 ≤ c := by
    simpa [Nat.sub_sub_self hd] using (norm_nonneg _).trans (hc (d - 1) (by omega))
  have hz₀ : 0 < ‖z‖ := by linarith
  -- From `zᵈ = -∑_{i < d} aᵢ zⁱ` and `c < ‖z‖ / 2`, `‖z‖ᵈ ≤ ‖z‖ᵈ ∑_{i < d} 2^-(d - i)`.
  have heq : z ^ d = -∑ i ∈ Finset.range d, p.coeff i * z ^ i := by
    have h := hz
    rw [IsRoot.def, eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at h
    linear_combination h
  have hle : ‖z‖ ^ d ≤ ‖z‖ ^ d * ∑ i ∈ Finset.range d, (2 : ℝ)⁻¹ ^ (d - i) := by
    calc ‖z‖ ^ d = ‖∑ i ∈ Finset.range d, p.coeff i * z ^ i‖ := by rw [← norm_pow, heq, norm_neg]
      _ ≤ ∑ i ∈ Finset.range d, ‖z‖ ^ d * 2⁻¹ ^ (d - i) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [Finset.mem_range] at hi
        rw [norm_mul, norm_pow]
        calc ‖p.coeff i‖ * ‖z‖ ^ i ≤ c ^ (d - i) * ‖z‖ ^ i := by gcongr; exact hc i hi
          _ ≤ (2⁻¹ * ‖z‖) ^ (d - i) * ‖z‖ ^ i := by gcongr; linarith
          _ = ‖z‖ ^ d * 2⁻¹ ^ (d - i) := by
            rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hi.le, mul_comm]
      _ = _ := (Finset.mul_sum _ _ _).symm
  -- The weights `2^-(d - i)` sum to `1 - 2^-d < 1`.
  have hw : ∑ i ∈ Finset.range d, (2 : ℝ)⁻¹ ^ (d - i) < 1 := by
    rw [← Finset.sum_range_reflect]
    have h : ∀ j ∈ Finset.range d, (2 : ℝ)⁻¹ ^ (d - (d - 1 - j)) = 2⁻¹ * 2⁻¹ ^ j := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show d - (d - 1 - j) = j + 1 by omega, pow_succ, mul_comm]
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, geom_sum_eq (by norm_num)]
    have : (0 : ℝ) < 2⁻¹ ^ d := by positivity
    linarith [show (2 : ℝ)⁻¹ * ((2⁻¹ ^ d - 1) / (2⁻¹ - 1)) = 1 - 2⁻¹ ^ d by field_simp; ring]
  have := mul_lt_mul_of_pos_left hw (pow_pos hz₀ d)
  linarith

end Polynomial
