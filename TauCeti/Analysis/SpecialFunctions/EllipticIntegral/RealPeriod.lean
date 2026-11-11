/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod.OneRealRoot
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Cubic

/-!
# The real period of a Weierstrass curve in closed form

This file evaluates the real period `WeierstrassCurve.realPeriod` of a Weierstrass curve `W` over
`ℝ` by the complete elliptic integral of the first kind and by the arithmetic-geometric mean, in
both cases of the factorization of its `2`-torsion polynomial `Ψ₂Sq` over `ℝ`. The AGM forms are
how the real period in the Birch–Swinnerton-Dyer quotient is computed in practice, the AGM
converging quadratically.

**Three real roots.** If `Ψ₂Sq(x) = 4 (x - e₁)(x - e₂)(x - e₃)` with `e₃ < e₂ < e₁`, the case of
a curve whose real points have two components, then `Ψ₂Sq` is positive exactly on
`(e₃, e₂) ∪ (e₁, ∞)` (`TauCeti.Real.setOf_cubic_pos`), and the evaluation of the cubic integral
over each of these intervals gives

  `Ω(W) = 4 K(k) / √(e₁ - e₃) = 2π / M(√(e₁ - e₃), √(e₁ - e₂))`,

where `k = √((e₂ - e₃) / (e₁ - e₃))` and `M` is the arithmetic-geometric mean.

**One real root.** If `Ψ₂Sq(x) = 4 (x - e₁)((x - a)² + b²)` with `b ≠ 0`, the case of a curve
whose real points are connected, then `Ω(W)` is twice the cubic integral over `(e₁, ∞)`
(`WeierstrassCurve.realPeriod_eq_integral_of_one_real_root`), and its evaluation gives

  `Ω(W) = 2 K(k) / √A = 2π / M(2√A, √(2A + 2(e₁ - a)))`,

where `A = √((e₁ - a)² + b²)` and `k = √((A + a - e₁) / (2A))`.

## Main results

* `WeierstrassCurve.realPeriod_eq_four_mul_agmIntegral_of_three_real_roots`:
  `Ω(W) = 4 · agmIntegral √(e₁ - e₂) √(e₁ - e₃)`.
* `WeierstrassCurve.realPeriod_eq_of_three_real_roots`: `Ω(W) = 4 K(k) / √(e₁ - e₃)`.
* `WeierstrassCurve.realPeriod_eq_two_mul_pi_div_agm_of_three_real_roots`:
  `Ω(W) = 2π / M(√(e₁ - e₃), √(e₁ - e₂))`.
* `WeierstrassCurve.realPeriod_eq_of_one_real_root`: `Ω(W) = 2 K(k) / √A`.
* `WeierstrassCurve.realPeriod_eq_two_mul_pi_div_agm_of_one_real_root`:
  `Ω(W) = 2π / M(2√A, √(2A + 2(e₁ - a)))`.

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge, 1997, §3.7.
-/

public section

open MeasureTheory Set
open NNReal (agm)
open Real TauCeti TauCeti.Real
open scoped Real

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ) {e₁ e₂ e₃ a b : ℝ}

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

/-- **The real period with one real root, by the complete elliptic integral.** If
`Ψ₂Sq(x) = 4 (x - e₁)((x - a)² + b²)` with `b ≠ 0`, then `Ω(W) = 2 K(k) / √A`, where
`A = √((e₁ - a)² + b²)` is the distance from `e₁` to the nonreal roots `a ± b i` and the modulus
is `k = √((A + a - e₁) / (2A))`. -/
theorem realPeriod_eq_of_one_real_root (hb : b ≠ 0)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * ((x - a) ^ 2 + b ^ 2)) :
    W.realPeriod = 2 * legendreK √((√((e₁ - a) ^ 2 + b ^ 2) + a - e₁) /
      (2 * √((e₁ - a) ^ 2 + b ^ 2))) / √(√((e₁ - a) ^ 2 + b ^ 2)) := by
  have hq := sqrt_add_sub_div_two_mul_sqrt_mem_Ico (e₁ := e₁) (a := a) (Or.inl hb)
  have hK := legendreK_pos (by rw [sq_sqrt hq.1]; exact hq.2)
  rw [realPeriod_def, W.realPeriodLIntegral_eq_of_one_real_root hb hW,
    lintegral_Ioi_inv_sqrt_mul_sq_add_sq_eq_legendreK (Or.inl hb),
    ENNReal.toReal_ofReal (div_nonneg hK.le (sqrt_nonneg _)), mul_div_assoc]

/-- **The real period with one real root, by the AGM.** If
`Ψ₂Sq(x) = 4 (x - e₁)((x - a)² + b²)` with `b ≠ 0`, then
`Ω(W) = 2π / M(2√A, √(2A + 2(e₁ - a)))`, where `A = √((e₁ - a)² + b²)` and `M` is the
arithmetic-geometric mean. -/
theorem realPeriod_eq_two_mul_pi_div_agm_of_one_real_root (hb : b ≠ 0)
    (hW : ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * ((x - a) ^ 2 + b ^ 2)) :
    W.realPeriod = 2 * π / agm (2 * √(√((e₁ - a) ^ 2 + b ^ 2))).toNNReal
      (√(2 * √((e₁ - a) ^ 2 + b ^ 2) + 2 * (e₁ - a))).toNNReal := by
  have hq := sqrt_add_sub_div_two_mul_sqrt_mem_Ico (e₁ := e₁) (a := a) (Or.inl hb)
  rw [W.realPeriod_eq_of_one_real_root hb hW]
  have hA : 0 < √((e₁ - a) ^ 2 + b ^ 2) := sqrt_pos.2 (by positivity)
  set A := √((e₁ - a) ^ 2 + b ^ 2)
  clear_value A
  set q := (A + a - e₁) / (2 * A)
  have hk : √q ^ 2 < 1 := by rw [sq_sqrt hq.1]; exact hq.2
  -- Scaled by `2√A`, the complementary modulus `√(1 - q)` is `√(2A + 2(e₁ - a))`.
  have hk' : √(2 * A + 2 * (e₁ - a)) = 2 * √A * √(1 - √q ^ 2) := by
    rw [eq_comm, ← sqrt_sq (by positivity : 0 ≤ 2 * √A * √(1 - √q ^ 2)), mul_pow, mul_pow,
      sq_sqrt hA.le, sq_sqrt hq.1, sq_sqrt (by linarith [hq.2])]
    congr 1
    simp only [q]
    field_simp
    ring
  have hagm : agm (2 * √A).toNNReal (2 * √A * √(1 - √q ^ 2)).toNNReal =
      (2 * √A).toNNReal * agm 1 (√(1 - √q ^ 2)).toNNReal := by
    rw [toNNReal_mul (p := 2 * √A) (q := √(1 - √q ^ 2)) (by positivity),
      ← NNReal.agm_mul_distrib, mul_one]
  have hM : (0 : ℝ) < agm 1 (√(1 - √q ^ 2)).toNNReal :=
    NNReal.agm_pos one_pos (toNNReal_pos.2 (sqrt_pos.2 (by linarith)))
  have hsA : 0 < √A := sqrt_pos.2 hA
  rw [legendreK_eq_pi_div_two_mul_agm hk, hk', hagm, NNReal.coe_mul,
    coe_toNNReal _ (by positivity)]
  field_simp

end WeierstrassCurve
