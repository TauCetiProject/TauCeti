/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Polynomial cases of the regularized Kummer function

If an upper parameter of the regularized hypergeometric function `Complex.regularizedHGFun a b`
is a nonpositive integer `-n`, the series terminates and the function is a polynomial of degree
at most `n` (`Complex.regularizedHGFun_eq_sum_range_of_neg_natCast_mem`). For Olver's regularized
Kummer function `𝐌(a, b, z)` this gives, for every natural `n` and every
complex `b`, including the nonpositive integers,
`𝐌(-n, b, z) = ∑_{k ≤ n} (-n)_k z^k / (k! Γ(b + k))`
([DLMF 13.2.3](https://dlmf.nist.gov/13.2#E3) and the paragraph following 13.2.5). In particular
`𝐌(-1, b, z) = Γ(b)⁻¹ - z Γ(b + 1)⁻¹`, which `simp` reduces to `-z` at `b = 0`.

## Main results

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
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ ∀ z, regularizedHGFun {-(n : ℂ)} {b} z = p.eval z :=
  exists_natDegree_le_regularizedHGFun_of_neg_natCast_mem (Multiset.mem_singleton_self _)

/-- `𝐌(-1, b, z) = Γ(b)⁻¹ - z Γ(b + 1)⁻¹` for every complex `b`. -/
@[simp]
theorem regularizedHGFun_singleton_neg_one (b z : ℂ) :
    regularizedHGFun {-1} {b} z = (Gamma b)⁻¹ - z * (Gamma (b + 1))⁻¹ := by
  simpa [sum_range_succ, sub_eq_add_neg, div_eq_mul_inv] using
    regularizedHGFun_singleton_neg_natCast b z 1

end Complex
