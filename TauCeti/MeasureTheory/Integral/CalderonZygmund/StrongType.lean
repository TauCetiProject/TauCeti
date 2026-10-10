/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.WeakType
public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.General

/-!
# Singular integral operators of strong type `(p, p)` for `1 < p < 2`

Let `T` be a bounded linear operator on `L²(ℝⁿ)` satisfying the Calderón–Zygmund cancellation
condition, for instance one given by a kernel satisfying Hörmander's condition. The weak type
`(1, 1)` half of the **Calderón–Zygmund theorem** is
`ContinuousLinearMap.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`. Marcinkiewicz
interpolation between that bound and the `L²` bound
(`ContinuousLinearMap.eLpNorm_le_of_rpow_mul_meas_lt_le`) gives the strong type `(p, p)` bound

`‖T f‖_p ≤ (p / (p - 1) · 2 C + p / (2 - p) · 4 ‖T‖²) ^ (1 / p) ‖f‖_p`

for every `1 < p < 2` and every `f ∈ L²`, where `C = 2ⁿ (4 ‖T‖² + 1) + 4 B` is the weak type
`(1, 1)` constant. This constant blows up as `p → 1`, and also as `p → 2` when `‖T‖ > 0`. That
is a limitation of the interpolation argument, not of every operator satisfying the hypotheses
(the zero operator satisfies them), although classical singular integrals such as the Hilbert
transform are indeed not bounded on `L¹`.

Since `T` is only given on `L²`, the estimate is stated for `f ∈ L²`, and it is informative for
`f ∈ L² ∩ Lᵖ`. The range `2 < p < ∞` is not treated here. Classically it follows by duality, in
the scalar or Hilbert space valued setting, from the same theorem applied to the adjoint of `T`,
provided the adjoint also satisfies the cancellation condition (for instance when the kernel of
`T` also satisfies Hörmander's condition in the other variable).

Points of `ℝⁿ` are functions `ι → ℝ`, so distances and balls are taken in the sup norm.

## Main declarations

* `ContinuousLinearMap.eLpNorm_le_of_setLIntegral_compl_closedBall_le`: an `L²`-bounded operator
  satisfying the cancellation condition is of strong type `(p, p)` for `1 < p < 2`.
* `ContinuousLinearMap.eLpNorm_le_of_hormander`: an `L²`-bounded operator with a kernel satisfying
  Hörmander's condition is of strong type `(p, p)` for `1 < p < 2`.

## References

* A. P. Calderón and A. Zygmund, *On the existence of certain singular integrals*, Acta Math.
  **88** (1952), 85–139.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.
-/

public section

namespace ContinuousLinearMap

open MeasureTheory Metric Set TauCeti
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}

/-- **The Calderón–Zygmund theorem**, strong type `(p, p)` for `1 < p < 2`. Let `T` be a bounded
linear operator on `L²(ℝⁿ)` satisfying the cancellation condition: for every `b ∈ L²` vanishing off
a closed ball `closedBall y r` with integral zero, `∫_{ℝⁿ \ closedBall y (2r)} ‖T b‖ ≤ B ‖b‖₁`.
Then for every `1 < p < 2` and every `f ∈ L²`,

`‖T f‖_p ≤ (p / (p - 1) · 2 C + p / (2 - p) · 4 ‖T‖²) ^ (1 / p) ‖f‖_p`,

where `C = 2ⁿ (4 ‖T‖² + 1) + 4 B` is the weak type `(1, 1)` constant of
`ContinuousLinearMap.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`. The bound is
vacuous unless `f` also lies in `Lᵖ`. -/
theorem eLpNorm_le_of_setLIntegral_compl_closedBall_le
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ))) {B : ℝ≥0∞}
    (hT : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖T b x‖ₑ ≤ B * ∫⁻ x, ‖b x‖ₑ)
    (hp : 1 < p) (hp₂ : p < 2) (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    eLpNorm (T f) p volume ≤
      (ENNReal.ofReal (p.toReal / (p.toReal - 1)) *
          (2 * (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B)) +
        ENNReal.ofReal (p.toReal / (2 - p.toReal)) * (4 * ‖T‖ₑ ^ 2)) ^ (1 / p.toReal) *
        eLpNorm f p volume := by
  have h := eLpNorm_le_of_rpow_mul_meas_lt_le T zero_lt_one hp hp₂ ENNReal.ofNat_ne_top
    (fun g s => by
      simpa using mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le T hT g s) f
  convert h using 6 <;> norm_num

/-- **The Calderón–Zygmund theorem** for an operator given by a kernel, strong type `(p, p)` for
`1 < p < 2`. Let `T` be a bounded linear operator on `L²(ℝⁿ)` such that `T b x = ∫ K x y (b y) dy`
for almost every `x` off any closed ball outside which `b` vanishes, where the kernel `K` satisfies
Hörmander's condition `∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`.
Then for every `1 < p < 2` and every `f ∈ L²`,

`‖T f‖_p ≤ (p / (p - 1) · 2 (2ⁿ (4 ‖T‖² + 1) + 4 B) + p / (2 - p) · 4 ‖T‖²) ^ (1 / p) ‖f‖_p`. -/
theorem eLpNorm_le_of_hormander [CompleteSpace F]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} (hK : StronglyMeasurable (Function.uncurry K))
    {B : ℝ≥0∞} (hB : ∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ≤ B)
    (hrep : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) →
        ∀ᵐ x, x ∉ closedBall y r → T b x = ∫ z, K x z (b z))
    (hp : 1 < p) (hp₂ : p < 2) (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    eLpNorm (T f) p volume ≤
      (ENNReal.ofReal (p.toReal / (p.toReal - 1)) *
          (2 * (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B)) +
        ENNReal.ofReal (p.toReal / (2 - p.toReal)) * (4 * ‖T‖ₑ ^ 2)) ^ (1 / p.toReal) *
        eLpNorm f p volume := by
  have h := eLpNorm_le_of_rpow_mul_meas_lt_le T zero_lt_one hp hp₂ ENNReal.ofNat_ne_top
    (fun g s => by simpa using mul_volume_lt_enorm_le_of_hormander T hK hB hrep g s) f
  convert h using 6 <;> norm_num

end ContinuousLinearMap
