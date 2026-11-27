/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Counting.Basic
public import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannSiegelTheta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannSiegelTheta.Asymptotics

/-!
# Recorded bounds for the argument of the Riemann zeta function

`TauCeti.ZetaArgumentBoundUpTo H C` records a uniform bound on the discrepancy between
the one-sided zero count of `riemannZetaData` and `riemannSiegelTheta / π + 1`.
The count includes zeros at the upper endpoint with full multiplicity, so this uses the
right-hand convention at zero ordinates.

`TauCeti.ZetaArgumentBoundUpTo.abs_zeroCountingFunction_sub_log_sub_le` uses
`abs_riemannSiegelTheta_sub_le` to convert the record to an explicit error for the logarithmic
main term of the Riemann–von Mangoldt formula, with an arbitrary constant shift.

## References

* C. Bellotti and P.-J. Wong, *Improved estimates for the argument and zero-counting function
  of the Riemann zeta-function*, (1.2), arXiv:2412.15470.
* T. S. Trudgian, *An improved upper bound for the argument of the Riemann zeta-function on
  the critical line II*, (1.2), J. Number Theory 134 (2014), 280–292.
-/

public section

open Real Set TauCeti.LFunctions

namespace TauCeti

/-- A bound `C` for `|N(T) - ϑ(T)/π - 1|` for `0 ≤ T ≤ H`, with `N(T)` counting
zeros with `0 < Im ρ ≤ T` with multiplicity. The recorded bounds of Bellotti–Wong and
Trudgian supply the parameters `(30610046000, 2.5167)` and `(6800000, 2)`, respectively. -/
def ZetaArgumentBoundUpTo (H C : ℝ) : Prop :=
  ∀ T ∈ Icc 0 H,
    |(riemannZetaData.zeroCountingFunction T : ℝ) - riemannSiegelTheta T / π - 1| ≤ C

/-- The height record gives an absolute discrepancy bound at every height in `[0, H]`.
This is not a simp lemma so that simp does not expand record hypotheses into quantified formulas. -/
theorem zetaArgumentBoundUpTo_iff {H C : ℝ} :
    ZetaArgumentBoundUpTo H C ↔ ∀ T ∈ Icc 0 H,
      |(riemannZetaData.zeroCountingFunction T : ℝ) - riemannSiegelTheta T / π - 1| ≤ C :=
  Iff.rfl

/-- At height zero the zero count and theta both vanish, so the discrepancy has modulus one. -/
@[simp] theorem zetaArgumentBoundUpTo_zero_iff {C : ℝ} : ZetaArgumentBoundUpTo 0 C ↔ 1 ≤ C := by
  rw [zetaArgumentBoundUpTo_iff, Icc_self]
  simp

/-- On the positive heights covered by the record, the zero count differs from the logarithmic
main term with constant shift `κ` by at most `C + 1/(π*T) + |7/8 - κ|`. In particular,
`κ = 7/8` keeps just the Stirling error in addition to the recorded error. -/
theorem ZetaArgumentBoundUpTo.abs_zeroCountingFunction_sub_log_sub_le {H C T : ℝ}
    (h : ZetaArgumentBoundUpTo H C) (hT : T ∈ Ioc 0 H) (κ : ℝ) :
    |(riemannZetaData.zeroCountingFunction T : ℝ) -
        T / (2 * π) * log (T / (2 * π * exp 1)) - κ| ≤ C + 1 / (π * T) + |7 / 8 - κ| := by
  have hrecord := zetaArgumentBoundUpTo_iff.mp h T ⟨hT.1.le, hT.2⟩
  have htheta :
      |riemannSiegelTheta T / π + 1 - T / (2 * π) * log (T / (2 * π * exp 1)) - 7 / 8| ≤
        1 / (π * T) := by
    have heq :
        riemannSiegelTheta T / π + 1 - T / (2 * π) * log (T / (2 * π * exp 1)) - 7 / 8 =
          (riemannSiegelTheta T - (T / 2 * log (T / (2 * π * exp 1)) - π / 8)) / π := by
      field [pi_ne_zero]
    rw [heq, abs_div, abs_of_pos pi_pos]
    calc
      _ ≤ 1 / T / π := div_le_div_of_nonneg_right (abs_riemannSiegelTheta_sub_le hT.1) pi_pos.le
      _ = _ := by rw [div_div, mul_comm T π]
  grind

end TauCeti
