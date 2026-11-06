/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod.Basic
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Cubic

/-!
# The real period of a Weierstrass curve with three real `2`-torsion roots

Let `W` be a Weierstrass curve over `ℝ` whose `2`-torsion polynomial factors as
`Ψ₂Sq(x) = 4 (x - e₁)(x - e₂)(x - e₃)` with `e₃ < e₂ < e₁`, the case of a curve whose real points
have two components. Then `Ψ₂Sq` is positive exactly on `(e₃, e₂) ∪ (e₁, ∞)`
(`TauCeti.Real.setOf_cubic_pos`), and the evaluation of the cubic integral over each of these
intervals gives the real period `WeierstrassCurve.realPeriod` in closed form:

  `Ω(W) = 4 K(k) / √(e₁ - e₃) = 2π / M(√(e₁ - e₃), √(e₁ - e₂))`,

where `k = √((e₂ - e₃) / (e₁ - e₃))` and `M` is the arithmetic-geometric mean. The AGM form is
how the real period in the Birch–Swinnerton-Dyer quotient is computed in practice, the AGM
converging quadratically.

## Main results

* `WeierstrassCurve.realPeriod_eq_four_mul_agmIntegral_of_three_real_roots`:
  `Ω(W) = 4 · agmIntegral √(e₁ - e₂) √(e₁ - e₃)`.
* `WeierstrassCurve.realPeriod_eq_of_three_real_roots`: `Ω(W) = 4 K(k) / √(e₁ - e₃)`.
* `WeierstrassCurve.realPeriod_eq_two_mul_pi_div_agm_of_three_real_roots`:
  `Ω(W) = 2π / M(√(e₁ - e₃), √(e₁ - e₂))`.

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge, 1997, §3.7.
-/

public section

open MeasureTheory Set
open NNReal (agm)
open Real TauCeti TauCeti.Real
open scoped Real

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ) {e₁ e₂ e₃ : ℝ}

/-- With three real roots `e₃ < e₂ < e₁`, the real period integral splits as the cubic integrals
over `(e₃, e₂)` and over `(e₁, ∞)`. -/
private theorem realPeriodLIntegral_eq_add_of_three_real_roots (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * (x - e₂) * (x - e₃)) :
    W.realPeriodLIntegral =
      (∫⁻ x in Ioo e₃ e₂, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹) +
        ∫⁻ x in Ioi e₁, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ := by
  simp only [realPeriodLIntegral_def, hW]
  rw [setOf_cubic_pos h₃₂ h₂₁, lintegral_union measurableSet_Ioi
    (disjoint_left.2 fun x hx hx' ↦ by linarith [hx.2, mem_Ioi.1 hx'])]

/-- **The real period with three real roots, by the AGM integral.** If
`Ψ₂Sq(x) = 4 (x - e₁)(x - e₂)(x - e₃)` with `e₃ < e₂ < e₁`, then `Ω(W)` is four times the AGM
integral of the axes `√(e₁ - e₂)` and `√(e₁ - e₃)`. -/
theorem realPeriod_eq_four_mul_agmIntegral_of_three_real_roots (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * (x - e₂) * (x - e₃)) :
    W.realPeriod = 4 * agmIntegral √(e₁ - e₂) √(e₁ - e₃) := by
  rw [realPeriod_def, W.realPeriodLIntegral_eq_add_of_three_real_roots h₃₂ h₂₁ hW,
    lintegral_Ioo_inv_sqrt_cubic_eq_agmIntegral h₃₂ h₂₁,
    lintegral_Ioi_inv_sqrt_cubic_eq_agmIntegral h₂₁ (h₃₂.trans h₂₁), ← two_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (agmIntegral_pos (sqrt_pos.2 (by linarith)) (sqrt_pos.2 (by linarith))).le,
    ENNReal.toReal_ofNat]
  ring

/-- **The real period with three real roots, by the complete elliptic integral.** If
`Ψ₂Sq(x) = 4 (x - e₁)(x - e₂)(x - e₃)` with `e₃ < e₂ < e₁`, then
`Ω(W) = 4 K(k) / √(e₁ - e₃)` with modulus `k = √((e₂ - e₃) / (e₁ - e₃))`. -/
theorem realPeriod_eq_of_three_real_roots (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * (x - e₂) * (x - e₃)) :
    W.realPeriod = 4 * legendreK √((e₂ - e₃) / (e₁ - e₃)) / √(e₁ - e₃) := by
  rw [W.realPeriod_eq_four_mul_agmIntegral_of_three_real_roots h₃₂ h₂₁ hW,
    agmIntegral_sqrt_sub_eq_legendreK h₃₂.le h₂₁, mul_div_assoc]

/-- **The real period with three real roots, by the AGM.** If
`Ψ₂Sq(x) = 4 (x - e₁)(x - e₂)(x - e₃)` with `e₃ < e₂ < e₁`, then
`Ω(W) = 2π / M(√(e₁ - e₃), √(e₁ - e₂))`, where `M` is the arithmetic-geometric mean. -/
theorem realPeriod_eq_two_mul_pi_div_agm_of_three_real_roots (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * (x - e₂) * (x - e₃)) :
    W.realPeriod = 2 * π / agm (√(e₁ - e₃)).toNNReal (√(e₁ - e₂)).toNNReal := by
  have hagm := agmIntegral_eq_pi_div_two_div_agm
    (a := (√(e₁ - e₃)).toNNReal) (b := (√(e₁ - e₂)).toNNReal)
  rw [Real.coe_toNNReal _ (sqrt_nonneg _), Real.coe_toNNReal _ (sqrt_nonneg _),
    agmIntegral_comm] at hagm
  rw [W.realPeriod_eq_four_mul_agmIntegral_of_three_real_roots h₃₂ h₂₁ hW, hagm]
  ring

end WeierstrassCurve
