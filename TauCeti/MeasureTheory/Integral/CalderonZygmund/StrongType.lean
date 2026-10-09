/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.WeakType
public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.LpBounded

/-!
# Singular integral operators of strong type `(p, p)` for `1 < p < 2`

Let `T` be a bounded linear operator on `L²(ℝⁿ)` satisfying the Calderón–Zygmund cancellation
condition: for every `b ∈ L²` vanishing off a closed ball `closedBall y r` with integral zero,
`∫_{ℝⁿ \ closedBall y (2r)} ‖T b‖ ≤ B ‖b‖₁`. Such an operator is of weak type `(1, 1)`
(`ContinuousLinearMap.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`), and
Marcinkiewicz interpolation between this endpoint and the `L²` bound
(`ContinuousLinearMap.lintegral_rpow_enorm_le_of_rpow_mul_meas_lt_le`) shows that it is of strong
type `(p, p)` for every `1 < p < 2`: for every `f ∈ L²`,

`∫ ‖T f‖ ^ p ≤ (p / (p - 1) · 2 A + p / (2 - p) · 4 ‖T‖²) ∫ ‖f‖ ^ p`,

where `A = 2ⁿ (4 ‖T‖² + 1) + 4 B` is the weak-type constant of
`ContinuousLinearMap.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`. This is
`ContinuousLinearMap.lintegral_rpow_enorm_le_of_setLIntegral_compl_closedBall_le`. The same
holds for an operator given off the support of `b` by a kernel satisfying Hörmander's condition
(`ContinuousLinearMap.lintegral_rpow_enorm_le_of_hormander`).

The factor `p / (p - 1)` must blow up as `p → 1`, since a Calderón–Zygmund operator need not be
bounded on `L¹`. The blow-up of `p / (2 - p)` as `p → 2` is an artifact of the interpolation
method only, as `T` is bounded on `L²` by hypothesis. The range `2 < p < ∞` follows from this one
by duality, applied to the adjoint of `T`, and is not treated here.

## References

* A. P. Calderón and A. Zygmund, *On the existence of certain singular integrals*, Acta Math.
  **88** (1952), 85–139.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.
* L. Grafakos, *Classical Fourier Analysis*, Theorem 5.3.3.
-/

public section

namespace ContinuousLinearMap

open MeasureTheory Metric Set TauCeti
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Calderón–Zygmund theorem**, strong type `(p, p)` for `1 < p < 2`. Let `T` be a bounded
linear operator on `L²(ℝⁿ)` satisfying the cancellation condition: for every `b ∈ L²` vanishing
off a closed ball `closedBall y r` with integral zero,
`∫_{ℝⁿ \ closedBall y (2r)} ‖T b‖ ≤ B ‖b‖₁`. Then for every `1 < p < 2` and every `f ∈ L²`,

`∫ ‖T f‖ ^ p ≤ (p / (p - 1) · 2 (2ⁿ (4 ‖T‖² + 1) + 4 B) + p / (2 - p) · 4 ‖T‖²) ∫ ‖f‖ ^ p`. -/
theorem lintegral_rpow_enorm_le_of_setLIntegral_compl_closedBall_le
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ))) {B : ℝ≥0∞}
    (hT : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖T b x‖ₑ ≤ B * ∫⁻ x, ‖b x‖ₑ)
    {p : ℝ} (hp : 1 < p) (hp' : p < 2) (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    ∫⁻ x, ‖T f x‖ₑ ^ p ≤
      (ENNReal.ofReal (p / (p - 1)) *
          (2 * (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B)) +
        ENNReal.ofReal (p / (2 - p)) * (4 * ‖T‖ₑ ^ 2)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have h := T.lintegral_rpow_enorm_le_of_rpow_mul_meas_lt_le
    (fun f t => by simpa using mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le T hT f t)
    one_pos hp (by simpa using hp') f
  convert h using 4 <;> norm_num

/-- **The Calderón–Zygmund theorem** for an operator given by a kernel, strong type `(p, p)` for
`1 < p < 2`. Let `T` be a bounded linear operator on `L²(ℝⁿ)` such that `T b x = ∫ K x y (b y) dy`
for almost every `x` off any closed ball outside which `b` vanishes, where the kernel `K` satisfies
Hörmander's condition `∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`. Then
for every `1 < p < 2` and every `f ∈ L²`,

`∫ ‖T f‖ ^ p ≤ (p / (p - 1) · 2 (2ⁿ (4 ‖T‖² + 1) + 4 B) + p / (2 - p) · 4 ‖T‖²) ∫ ‖f‖ ^ p`. -/
theorem lintegral_rpow_enorm_le_of_hormander [CompleteSpace F]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} (hK : StronglyMeasurable (Function.uncurry K))
    {B : ℝ≥0∞} (hB : ∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ≤ B)
    (hrep : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) →
        ∀ᵐ x, x ∉ closedBall y r → T b x = ∫ z, K x z (b z))
    {p : ℝ} (hp : 1 < p) (hp' : p < 2) (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    ∫⁻ x, ‖T f x‖ₑ ^ p ≤
      (ENNReal.ofReal (p / (p - 1)) *
          (2 * (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B)) +
        ENNReal.ofReal (p / (2 - p)) * (4 * ‖T‖ₑ ^ 2)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have h := T.lintegral_rpow_enorm_le_of_rpow_mul_meas_lt_le
    (fun f t => by simpa using mul_volume_lt_enorm_le_of_hormander T hK hB hrep f t)
    one_pos hp (by simpa using hp') f
  convert h using 4 <;> norm_num

end ContinuousLinearMap
