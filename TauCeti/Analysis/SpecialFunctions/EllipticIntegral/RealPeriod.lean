/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Cubic

/-!
# The real period of a Weierstrass curve with three real `2`-torsion roots

Let `W` be a Weierstrass curve over `ℝ` whose `2`-torsion polynomial factors as
`Ψ₂Sq(x) = 4 (x - e₁)(x - e₂)(x - e₃)` with `e₃ < e₂ < e₁`, the case of a curve whose real points
have two components. Then `Ψ₂Sq` is positive exactly on `(e₃, e₂) ∪ (e₁, ∞)`, and the evaluation
of the cubic integral over each of these intervals gives the real period
`WeierstrassCurve.realPeriod` in closed form:

  `Ω(W) = 4 K(k) / √(e₁ - e₃) = 2π / M(√(e₁ - e₃), √(e₁ - e₂))`,

where `k = √((e₂ - e₃) / (e₁ - e₃))` and `M` is the arithmetic-geometric mean. The AGM form is
how the real period in the Birch–Swinnerton-Dyer quotient is computed in practice, the AGM
converging quadratically.

## Main results

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

/-- For `e₃ < e₂ < e₁`, the cubic `4 (x - e₁)(x - e₂)(x - e₃)` is positive exactly on
`(e₃, e₂) ∪ (e₁, ∞)`. -/
private theorem setOf_cubic_pos (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) :
    {x : ℝ | 0 < 4 * (x - e₁) * (x - e₂) * (x - e₃)} = Ioo e₃ e₂ ∪ Ioi e₁ := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
  constructor
  · intro h
    by_contra hc
    rcases le_or_gt x e₃ with h3 | h3
    · have : 0 < (x - e₁) * (x - e₂) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith
    · have h2 : e₂ ≤ x := le_of_not_gt fun h2 ↦ hc (Or.inl ⟨h3, h2⟩)
      have h1 : x ≤ e₁ := le_of_not_gt fun h1 ↦ hc (Or.inr h1)
      have : 0 ≤ (x - e₂) * (x - e₃) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  · rintro (⟨h3, h2⟩ | h1)
    · have : 0 < (x - e₁) * (x - e₂) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith
    · have : 0 < (x - e₁) * (x - e₂) := mul_pos (by linarith) (by linarith)
      nlinarith

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

/-- **The real period with three real roots, by the complete elliptic integral.** If
`Ψ₂Sq(x) = 4 (x - e₁)(x - e₂)(x - e₃)` with `e₃ < e₂ < e₁`, then
`Ω(W) = 4 K(k) / √(e₁ - e₃)` with modulus `k = √((e₂ - e₃) / (e₁ - e₃))`. -/
theorem realPeriod_eq_of_three_real_roots (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * (x - e₂) * (x - e₃)) :
    W.realPeriod = 4 * legendreK √((e₂ - e₃) / (e₁ - e₃)) / √(e₁ - e₃) := by
  have hk : (√((e₂ - e₃) / (e₁ - e₃))) ^ 2 < 1 := by
    rw [sq_sqrt (div_nonneg (by linarith) (by linarith)), div_lt_one (by linarith)]
    linarith
  rw [realPeriod_def, W.realPeriodLIntegral_eq_add_of_three_real_roots h₃₂ h₂₁ hW,
    lintegral_Ioo_inv_sqrt_cubic_eq_legendreK h₃₂ h₂₁,
    lintegral_Ioi_inv_sqrt_cubic_eq_legendreK h₃₂.le h₂₁, ← two_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg (legendreK_pos hk).le (sqrt_nonneg _))]
  norm_num
  ring

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
  rw [realPeriod_def, W.realPeriodLIntegral_eq_add_of_three_real_roots h₃₂ h₂₁ hW,
    lintegral_Ioo_inv_sqrt_cubic_eq_agmIntegral h₃₂ h₂₁,
    lintegral_Ioi_inv_sqrt_cubic_eq_agmIntegral h₂₁ (h₃₂.trans h₂₁), ← two_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (agmIntegral_pos (sqrt_pos.2 (by linarith)) (sqrt_pos.2 (by linarith))).le, hagm]
  norm_num
  ring

end WeierstrassCurve
