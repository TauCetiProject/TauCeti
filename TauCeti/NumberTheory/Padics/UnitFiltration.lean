/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic

/-!
# The `p`-adic unit filtration in terms of the norm

For `i ≥ 1`, the unit filtration `U(ℚ_p,i)` of the local field `ℚ_[p]`, whose absolute
ramification index is one, is the closed disc `‖x - 1‖ ≤ p ^ (-i)` about `1` for Mathlib's
`p`-adic norm. Together with the results of `TauCeti.NumberTheory.Padics.Exp.Disc`, this is
the input for the logarithm on the principal units `1 + qℤ_p`, with `q = p` for odd `p` and
`q = 4` for `p = 2`, in `TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm`.

When the depth `i` satisfies `1 < (p - 1) * i`, that is, `i ≥ 1` for odd `p` and `i ≥ 2` for
`p = 2`, this disc lies inside the open disc of radius `p ^ (-1 / (p - 1))`
(`TauCeti.zpow_neg_lt_amiceRadius_zero`). The norm, inverse and homomorphism identities of the
exponential and logarithm on these discs are therefore the cases of
`TauCeti.norm_exp_sub_one_of_norm_lt`, `TauCeti.norm_log_of_norm_sub_one_lt`,
`TauCeti.log_exp_of_norm_lt`, `TauCeti.exp_log_of_norm_sub_one_lt` and
`TauCeti.log_mul_of_norm_sub_one_lt` given by that inequality.

## Main results

* `Padic.mem_unitFiltration_iff_norm_sub_one_le`: the unit filtration `U(ℚ_p,i)` is the disc
  `‖x - 1‖ ≤ p ^ (-i)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (5.5).
-/

public section

open ValuativeRel

namespace Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- A unit of `ℚ_[p]` lies in the unit filtration `U(ℚ_p,i)`, `i ≥ 1`, exactly when
`‖x - 1‖ ≤ p ^ (-i)`. -/
theorem mem_unitFiltration_iff_norm_sub_one_le {i : ℕ} (hi : i ≠ 0) {x : ℚ_[p]ˣ} :
    x ∈ TauCeti.unitFiltration ℚ_[p] i ↔ ‖(x : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
  rw [TauCeti.mem_unitFiltration_iff_valuation_sub_one_le hi
    (TauCeti.Padic.irreducible_natCast_self p), valuation_le_valuation_natCast_pow_iff]

end Padic
