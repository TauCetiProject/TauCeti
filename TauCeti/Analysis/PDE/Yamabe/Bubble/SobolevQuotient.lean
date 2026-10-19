/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Energy
public import TauCeti.Analysis.PDE.Yamabe.SphereConstant

/-!
# The Sobolev quotient of the Yamabe bubbles

Let `E` be a real inner product space of dimension `n`, with Lebesgue measure, and let
`U = U_{t,b}` be the bubble of scale `t > 0` centred at `b` (`TauCeti.Yamabe.bubble`). With
`aₙ = 4 (n - 1) / (n - 2)`, `pₙ = 2 n / (n - 2)` and `|Sⁿ|` the area of the unit round sphere
(`TauCeti.roundSphereVolume`), this file identifies the critical norm and the energy of a
bubble with the round sphere:

* `∫ U ^ pₙ = |Sⁿ|` for `n ≠ 2`, `n > 0`;
* `aₙ ∫ ‖dU‖² = n (n - 1) |Sⁿ|` for `n > 2`.

Consequently, for `n > 2`, the bubbles attain the constant `Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)`
(`TauCeti.Yamabe.sphereYamabeConstant`) in the Sobolev quotient:

`aₙ ∫ ‖dU‖² = Y(Sⁿ) (∫ U ^ pₙ) ^ (2 / pₙ)`.

This is the equality case of the sharp Euclidean Sobolev inequality
`aₙ ∫ ‖du‖² ≥ Y(Sⁿ) (∫ |u| ^ pₙ) ^ (2 / pₙ)`; the inequality itself is not proved here. All three
identities are independent of the scale `t` and the centre `b`.

## Main declarations

* `TauCeti.Yamabe.integral_bubble_rpow_criticalExponent_eq_roundSphereVolume`: `∫ U ^ pₙ = |Sⁿ|`.
* `TauCeti.Yamabe.conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_roundSphereVolume`:
  `aₙ ∫ ‖dU‖² = n (n - 1) |Sⁿ|`.
* `TauCeti.Yamabe.conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_sphereYamabeConstant`:
  `aₙ ∫ ‖dU‖² = Y(Sⁿ) (∫ U ^ pₙ) ^ (2 / pₙ)`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976).
* G. Talenti, *Best constant in Sobolev inequality*, Ann. Mat. Pura Appl. 110 (1976).
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open MeasureTheory Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The critical norm of a bubble is the area of the round sphere**: in every positive dimension
`n ≠ 2`, for Lebesgue measure, `∫ U_{t,b} ^ pₙ = |Sⁿ|`. -/
theorem integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (hn₀ : 0 < finrank ℝ E)
    (hn : finrank ℝ E ≠ 2) {t : ℝ} (ht : 0 < t) (b : E) :
    ∫ x, bubble t b x ^ criticalExponent (finrank ℝ E) = roundSphereVolume (finrank ℝ E) := by
  rw [integral_bubble_rpow_criticalExponent hn₀ hn ht b,
    roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma]

/-- **The energy of a bubble**: in dimension `n > 2`, for Lebesgue measure,
`aₙ ∫ ‖dU_{t,b}‖² = n (n - 1) |Sⁿ|`. -/
theorem conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_roundSphereVolume
    (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2 =
      (finrank ℝ E : ℝ) * (finrank ℝ E - 1) * roundSphereVolume (finrank ℝ E) := by
  rw [conformalCoefficient_mul_integral_norm_fderiv_bubble_sq volume hn ht b,
    integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' ht b]

/-- **The bubbles attain the Yamabe constant of the sphere**: in dimension `n > 2`, for Lebesgue
measure, `aₙ ∫ ‖dU_{t,b}‖² = Y(Sⁿ) (∫ U_{t,b} ^ pₙ) ^ (2 / pₙ)`. This is the equality case of the
sharp Euclidean Sobolev inequality. -/
theorem conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_sphereYamabeConstant
    (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2 =
      sphereYamabeConstant (finrank ℝ E) *
        (∫ x, bubble t b x ^ criticalExponent (finrank ℝ E)) ^
          (2 / criticalExponent (finrank ℝ E)) := by
  have hp : 2 / criticalExponent (finrank ℝ E) = ((finrank ℝ E : ℝ) - 2) / finrank ℝ E := by
    have hn₀ : finrank ℝ E ≠ 0 := by omega
    have h₀ : (finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hn₀
    have h₂ : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    rw [criticalExponent_def]
    field_simp
  rw [conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_roundSphereVolume hn ht b,
    integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' ht b, hp,
    sphereYamabeConstant_mul_roundSphereVolume_rpow (by omega)]

end TauCeti.Yamabe
