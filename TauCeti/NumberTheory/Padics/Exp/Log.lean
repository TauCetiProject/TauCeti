/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import TauCeti.NumberTheory.LocalField.DeepUnits.Basic

/-!
# The `p`-adic logarithm on deep discs in terms of the norm

Mathlib's `NormedSpace.log` on `ℚ_[p]` turns products into sums on the closed disc
`‖u - 1‖ ≤ p ^ (-i)` about `1`, whenever the depth `i` satisfies `1 < (p - 1) * i`, that is,
`i ≥ 1` for odd `p` and `i ≥ 2` for `p = 2`.

This is the homomorphism property of `TauCeti.NumberTheory.LocalField.DeepUnits.Basic` for the
local field `ℚ_[p]`, whose absolute ramification index is one, restated with Mathlib's `p`-adic
norm instead of the unit filtration. Together with the results of
`TauCeti.NumberTheory.Padics.Exp.Disc`, it is the analytic input for the logarithm on the
principal units `1 + qℤ_p`, with `q = p` for odd `p` and `q = 4` for `p = 2`, in
`TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm`. The norm and inverse identities of
the exponential and logarithm on these discs are the cases of
`TauCeti.norm_exp_sub_one_of_norm_lt`, `TauCeti.norm_log_of_norm_sub_one_lt`,
`TauCeti.log_exp_of_norm_lt` and `TauCeti.exp_log_of_norm_sub_one_lt` given by
`TauCeti.zpow_neg_lt_amiceRadius_zero`.

## Main results

* `Padic.mem_unitFiltration_iff_norm_sub_one_le`: the unit filtration `U(ℚ_p,i)` is the disc
  `‖x - 1‖ ≤ p ^ (-i)`.
* `Padic.log_mul`: `log (u * w) = log u + log w`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (5.5).
-/

public section

open ValuativeRel NormedSpace

namespace Padic

variable {p : ℕ} [hp : Fact p.Prime]

private theorem absoluteRamificationIndex_lt {i : ℕ} (hi : 1 < (p - 1) * i) :
    TauCeti.absoluteRamificationIndex ℚ_[p] p < (p - 1) * i := by
  rwa [TauCeti.absoluteRamificationIndex_padic]

omit hp in
private theorem ne_zero_of_one_lt_mul {i : ℕ} (hi : 1 < (p - 1) * i) : i ≠ 0 := by
  rintro rfl
  simp at hi

/-- A unit of `ℚ_[p]` lies in the unit filtration `U(ℚ_p,i)`, `i ≥ 1`, exactly when
`‖x - 1‖ ≤ p ^ (-i)`. -/
theorem mem_unitFiltration_iff_norm_sub_one_le {i : ℕ} (hi : i ≠ 0) {x : ℚ_[p]ˣ} :
    x ∈ TauCeti.unitFiltration ℚ_[p] i ↔ ‖(x : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
  rw [TauCeti.mem_unitFiltration_iff_valuation_sub_one_le hi
    (TauCeti.Padic.irreducible_natCast_self p), valuation_le_valuation_natCast_pow_iff]

private theorem ne_zero_of_norm_sub_one_le {i : ℕ} (hi : i ≠ 0) {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) : x ≠ 0 := by
  rintro rfl
  have h1 : (p : ℝ) ^ (-(i : ℤ)) < 1 :=
    zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt) (by simpa using Nat.pos_of_ne_zero hi)
  rw [zero_sub, norm_neg, norm_one] at hx
  linarith

/-- An element `x` with `‖x - 1‖ ≤ p ^ (-i)` is a unit lying in the unit filtration `U(ℚ_p,i)`. -/
private theorem mk0_mem_unitFiltration {i : ℕ} (hi : 1 < (p - 1) * i) {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) :
    Units.mk0 x (ne_zero_of_norm_sub_one_le (ne_zero_of_one_lt_mul hi) hx) ∈
      TauCeti.unitFiltration ℚ_[p] i :=
  (mem_unitFiltration_iff_norm_sub_one_le (ne_zero_of_one_lt_mul hi)).mpr hx

/-- **The logarithm is a homomorphism on deep discs.** For `1 < (p - 1) * i`,
`‖u - 1‖ ≤ p ^ (-i)` and `‖w - 1‖ ≤ p ^ (-i)`, `log (u * w) = log u + log w`. -/
theorem log_mul {i : ℕ} (hi : 1 < (p - 1) * i) {u w : ℚ_[p]}
    (hu : ‖u - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) (hw : ‖w - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) :
    log (u * w) = log u + log w :=
  TauCeti.log_mul_of_mem_unitFiltration (absoluteRamificationIndex_lt hi)
    (mk0_mem_unitFiltration hi hu) (mk0_mem_unitFiltration hi hw)

end Padic
