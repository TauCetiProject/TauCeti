/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Liouville.Basic
public import TauCeti.NumberTheory.Height.Absolute
import TauCeti.NumberTheory.Height.Rat

/-!
# Liouville's inequality in terms of the denominator

For an algebraic number `α` of degree `d`, the distance to a distinct rational `p / q` is at
least `1 / (C * q ^ d)` with `C = 2 ^ (d - 1) * M(α) * (‖α‖ + 1) ^ d`. Here `M(α)` is the
Mahler measure, equivalently the relative multiplicative height in `ℚ(α)`.

`IsAlgebraic.inv_le_norm_ratCast_sub` bounds the distance in terms of the height of the rational
approximant. Within distance one of `α`, that height is at most `(‖α‖ + 1) * q`. Outside this
ball the distance itself is already at least one. For real `α` we give the result for any
positive denominator, expressing `M(α)` as the `d`-th power of the absolute Weil height.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Theorem 1.5.21.
* J.-H. Evertse, *Diophantine Approximation* (2019), Chapter 6, Theorem 6.1.
-/

public section

open Height NumberField TauCeti

namespace IsAlgebraic

/-- Liouville's lower bound for the distance from a complex algebraic number to a rational,
with an explicit constant and the reduced denominator of the rational. -/
theorem one_le_mahlerMeasure_mul_pow_mul_norm_sub_ratCast {α : ℂ} (hα : IsAlgebraic ℚ α)
    {r : ℚ} (hne : α ≠ r) :
    let d := (minpoly ℚ α).natDegree
    1 ≤ 2 ^ (d - 1) * mahlerMeasure α * ((‖α‖ + 1) * r.den) ^ d * ‖α - r‖ := by
  dsimp only
  have hM := one_le_mahlerMeasure α
  have hA : 1 ≤ ‖α‖ + 1 := by linarith [norm_nonneg α]
  have hq : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  rcases le_total 1 ‖α - r‖ with hfar | hnear
  · bound
  have hr : |(r : ℝ)| ≤ ‖α‖ + 1 := by
    rw [← Complex.norm_ratCast]
    exact (norm_le_norm_add_norm_sub α (r : ℂ)).trans (by gcongr)
  have hH := (Rat.mulHeight₁_le_max_one_abs_mul_den r).trans
    (mul_le_mul_of_nonneg_right (max_le hA hr) (Nat.cast_nonneg _))
  have h := hα.inv_le_norm_ratCast_sub hne.symm
  rw [← mahlerMeasure_def, norm_sub_rev, inv_le_iff_one_le_mul₀' (by positivity)] at h
  exact h.trans (by gcongr)

/-- For a real algebraic number `α` of degree `d`, the error in approximating `α` by `p / q`
is at least `1 / (2 ^ (d - 1) * (H(α) * (|α| + 1) * q) ^ d)`, where `H` is the absolute
multiplicative Weil height. The fraction may be unreduced. -/
theorem one_le_pow_mul_abs_sub_div {α : ℝ} (hα : IsAlgebraic ℚ α) (p : ℤ) {q : ℕ}
    (hq : 0 < q) (hne : α ≠ p / q) :
    let d := (minpoly ℚ α).natDegree
    1 ≤ 2 ^ (d - 1) * absMulHeight₁ α ^ d * ((|α| + 1) * q) ^ d * |α - p / q| := by
  let r : ℚ := p / q
  have hr : (r : ℝ) = p / q := by simp [r]
  have hden : r.den ≤ q := Nat.le_of_dvd hq <| Int.natCast_dvd_natCast.mp <| by
    simpa [r, Rat.divInt_eq_div] using Rat.den_dvd p q
  have halg : IsAlgebraic ℚ (α : ℂ) :=
    (isAlgebraic_algebraMap_iff (A := ℂ) Complex.ofReal_injective).2 hα
  have hne' : (α : ℂ) ≠ (r : ℂ) := by
    exact_mod_cast (hr ▸ hne : α ≠ (r : ℝ))
  have h := halg.one_le_mahlerMeasure_mul_pow_mul_norm_sub_ratCast hne'
  have hdeg : minpoly ℚ (α : ℂ) = minpoly ℚ α :=
    minpoly.algebraMap_eq Complex.ofReal_injective α
  have hM : mahlerMeasure (α : ℂ) = mahlerMeasure α := mahlerMeasure_map Complex.ofRealHom α
  have hdist : ‖(α : ℂ) - r‖ = |α - p / q| := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hr]
  dsimp only at h ⊢
  rw [hdeg, hM, mahlerMeasure_eq_absMulHeight₁_pow, Complex.norm_real, Real.norm_eq_abs, hdist] at h
  have hH := one_le_absMulHeight₁ α
  exact h.trans (by gcongr)

end IsAlgebraic
