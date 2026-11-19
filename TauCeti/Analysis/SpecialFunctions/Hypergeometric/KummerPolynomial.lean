/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Polynomial cases of the regularized hypergeometric function

If an upper parameter of the regularized hypergeometric function `Complex.regularizedHGFun a b`
is a nonpositive integer `-n`, then every coefficient of index greater than `n` vanishes, so the
series terminates and the function is a polynomial of degree at most `n`. No condition on the
lower parameters is needed.

For Olver's regularized Kummer function `𝐌(a, b, z)` this gives, for every natural `n` and every
complex `b`, including the nonpositive integers,
`𝐌(-n, b, z) = ∑_{k ≤ n} (-n)_k z^k / (k! Γ(b + k))`
([DLMF 13.2.3](https://dlmf.nist.gov/13.2#E3) and the paragraph following 13.2.5). In particular
`𝐌(-1, b, z) = Γ(b)⁻¹ - z Γ(b + 1)⁻¹`, which is `-z` at `b = 0`.

## Main results

* `Complex.regularizedHGFun_eq_sum_range_of_neg_natCast_mem` — the terminating series.
* `Complex.regularizedHGFun_singleton_neg_natCast` — the Kummer case DLMF 13.2.3 with `a = -n`.
* `Complex.exists_natDegree_le_regularizedHGFun_singleton_neg_natCast` — `𝐌(-n, b, ·)` is a
  polynomial of degree at most `n`.
* `Complex.regularizedHGFun_singleton_neg_one` — `𝐌(-1, b, z) = Γ(b)⁻¹ - z Γ(b + 1)⁻¹`.
-/

public section

noncomputable section

open Finset Polynomial
open scoped Nat

namespace Complex

/-- If `-n` is an upper parameter, the regularized hypergeometric series terminates at
degree `n`: `regularizedHGFun a b z` is the sum of its first `n + 1` terms. -/
theorem regularizedHGFun_eq_sum_range_of_neg_natCast_mem {a b : Multiset ℂ} {n : ℕ}
    (ha : -(n : ℂ) ∈ a) (z : ℂ) :
    regularizedHGFun a b z =
      ∑ k ∈ range (n + 1), regularizedHGFunCoeff a b k * z ^ k := by
  have hs := (regularizedHGFunSeries a b).hasSum (x := z)
    (by simp [radius_regularizedHGFunSeries_eq_top_of_finite ha rfl])
  simp only [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] at hs
  refine hs.unique (hasSum_sum_of_ne_finset_zero fun k hk => ?_)
  rw [regularizedHGFunCoeff_eq_zero_left a b k n ha (by simpa using hk), zero_mul]

/-- **DLMF 13.2.3** for `a = -n`: for every natural `n` and every complex `b`,
`𝐌(-n, b, z) = ∑_{k ≤ n} (-n)_k z^k / (k! Γ(b + k))`. -/
theorem regularizedHGFun_singleton_neg_natCast (b z : ℂ) (n : ℕ) :
    regularizedHGFun {-(n : ℂ)} {b} z =
      ∑ k ∈ range (n + 1), (ascPochhammer ℂ k).eval (-(n : ℂ)) * z ^ k /
        (k ! * Gamma (b + k)) := by
  rw [regularizedHGFun_eq_sum_range_of_neg_natCast_mem (Multiset.mem_singleton_self _) z]
  refine sum_congr rfl fun k _ => ?_
  simp only [regularizedHGFunCoeff, Multiset.map_singleton, Multiset.prod_singleton]
  ring

/-- For every natural `n` and every complex `b`, the Kummer function `𝐌(-n, b, ·)` is a
polynomial of degree at most `n`. -/
theorem exists_natDegree_le_regularizedHGFun_singleton_neg_natCast (b : ℂ) (n : ℕ) :
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ ∀ z, regularizedHGFun {-(n : ℂ)} {b} z = p.eval z := by
  refine ⟨∑ k ∈ range (n + 1), C (regularizedHGFunCoeff {-(n : ℂ)} {b} k) * X ^ k,
    natDegree_sum_le_of_forall_le _ _ fun k hk => ?_, fun z => ?_⟩
  · exact (natDegree_C_mul_X_pow_le _ k).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))
  · simp [regularizedHGFun_eq_sum_range_of_neg_natCast_mem (Multiset.mem_singleton_self _) z,
      eval_finsetSum]

/-- `𝐌(-1, b, z) = Γ(b)⁻¹ - z Γ(b + 1)⁻¹` for every complex `b`. -/
@[simp]
theorem regularizedHGFun_singleton_neg_one (b z : ℂ) :
    regularizedHGFun {-1} {b} z = (Gamma b)⁻¹ - z * (Gamma (b + 1))⁻¹ := by
  simpa [sum_range_succ, sub_eq_add_neg, div_eq_mul_inv] using
    regularizedHGFun_singleton_neg_natCast b z 1

/-- `𝐌(-1, 0, z) = -z`. -/
theorem regularizedHGFun_singleton_neg_one_zero (z : ℂ) :
    regularizedHGFun {-1} {0} z = -z := by
  simp

end Complex
