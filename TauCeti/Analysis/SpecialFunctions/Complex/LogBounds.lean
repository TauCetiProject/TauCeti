/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# The Taylor series of `-log (1 - ·)` summed over a family

Mathlib's `Complex.hasSum_taylorSeries_neg_log'` expands `-log (1 - z)` as `∑' e, z ^ (e+1)/(e+1)`
for a single `z` of modulus less than one.  This file sums that over a family `r : ι → ℂ`: the
double family indexed by `ι × ℕ` is summable, so the sum may be regrouped fibrewise and the
prime-power-style sum over pairs equals the sum of local logarithms.

Both hypotheses are needed.  `∀ i, ‖r i‖ < 1` alone does not suffice: the fibre at `i` sums to
`‖r i‖ / (1 - ‖r i‖)`, which is dominated by `‖r i‖` only when `‖r i‖` is bounded away from `1`,
and summability of `r` is what supplies that uniformity.  That fibrewise argument is not carried out
here: it is `TauCeti.summable_mul_norm_pow_succ`, stated for a seminormed additive group and an
arbitrary real weight, and this file uses it at weight `1`.

## Main results

* `Complex.summable_taylorSeries_neg_log`: for a summable `r : ι → ℂ` with every `‖r i‖ < 1`, the
  family `(i, e) ↦ r i ^ (e + 1) / (e + 1)` is summable over `ι × ℕ`.
* `Complex.tsum_taylorSeries_neg_log`: its sum over `ι × ℕ` is `∑' i, -log (1 - r i)`.
-/

public section

namespace Complex

/-- **The Taylor family of `-log (1 - rᵢ)` is summable over index and exponent together.**  For a
summable family `r` of complex numbers, all of modulus less than one, the double family
`(i, e) ↦ rᵢ ^ (e + 1) / (e + 1)` is absolutely summable, so its sum may be taken fibrewise.

Both hypotheses are needed, and neither is arithmetic: see the module docstring for why
`∀ i, ‖r i‖ < 1` alone does not suffice. -/
theorem summable_taylorSeries_neg_log {ι : Type*} {r : ι → ℂ} (hr : Summable r)
    (h1 : ∀ i, ‖r i‖ < 1) :
    Summable fun ie : ι × ℕ ↦ r ie.1 ^ (ie.2 + 1) / ((ie.2 : ℂ) + 1) := by
  -- The majorant is the weighted geometric bound at weight `1`; summability of `r` supplies its
  -- eventual bound with `ε = 1 / 2`.
  have hhalf : ∀ᶠ i in Filter.cofinite, ‖r i‖ ≤ 1 / 2 :=
    hr.tendsto_cofinite_zero.norm.eventually_le_const (by norm_num)
  have hbd : ∃ ε > 0, ∀ᶠ i in Filter.cofinite, (1 : ℝ) ≠ 0 → ‖r i‖ ≤ 1 - ε :=
    ⟨1 / 2, by norm_num, by filter_upwards [hhalf] with i hi _; linarith⟩
  have hmaj : Summable fun ie : ι × ℕ ↦ ‖r ie.1‖ ^ (ie.2 + 1) := by
    simpa using TauCeti.summable_mul_norm_pow_succ (w := fun _ ↦ (1 : ℝ)) hbd
      (by simpa using hr.norm) (fun i _ ↦ h1 i)
  refine hmaj.of_norm_bounded ?_
  rintro ⟨i, e⟩
  rw [norm_div, norm_pow]
  refine div_le_self (by positivity) ?_
  have hcast : ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_natCast]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le e)


/-- **The double sum is the sum of the local logarithms.**  For a summable `r : ι → ℂ` with every
`‖r i‖ < 1`, summing the Taylor series of `-log (1 - r i)` over `ι × ℕ` gives `∑' i, -log (1 - r i)`
— the fibrewise regrouping that `summable_taylorSeries_neg_log` licenses. -/
theorem tsum_taylorSeries_neg_log {ι : Type*} {r : ι → ℂ} (hr : Summable r)
    (h1 : ∀ i, ‖r i‖ < 1) :
    ∑' ie : ι × ℕ, r ie.1 ^ (ie.2 + 1) / ((ie.2 : ℂ) + 1) = ∑' i, -Complex.log (1 - r i) := by
  have hfib : ∀ i, HasSum (fun e : ℕ ↦ r i ^ (e + 1) / ((e : ℂ) + 1))
      (-Complex.log (1 - r i)) := fun i ↦ hasSum_taylorSeries_neg_log' (h1 i)
  exact ((summable_taylorSeries_neg_log hr h1).hasSum.prod_fiberwise hfib).tsum_eq.symm

end Complex
