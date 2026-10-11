/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.WeakType
public import TauCeti.MeasureTheory.Integral.DistRpow

/-!
# Standard Calderón–Zygmund kernels satisfy Hörmander's condition

The Calderón–Zygmund theorem (`ContinuousLinearMap.mul_volume_lt_enorm_le_of_hormander`) asks of
the kernel `K` of a singular integral operator only **Hörmander's condition**

`∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`.

The kernels met in practice (the Hilbert and Riesz transforms, the second derivatives of the
Newtonian kernel) are instead known to satisfy the pointwise **standard smoothness estimate**

`‖K x y - K x y'‖ ≤ C dist y y' ^ δ / dist x y' ^ (n + δ)` whenever `dist x y' > 2 dist y y'`,

for some `δ > 0`. This file shows that the pointwise estimate implies Hörmander's condition with
`B = C A 2ⁿ / (2^δ - 1)`, in any metric measure space whose balls satisfy the growth bound
`μ (closedBall y r) ≤ A rⁿ` (`TauCeti.setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow`). The
exponent `n` need not be an integer. On `ℝⁿ = ι → ℝ` with Lebesgue measure, where closed balls
are cubes of volume `(2r)ⁿ`, this gives `B = 4ⁿ C / (2^δ - 1)`
(`TauCeti.setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi`), and so the Calderón–Zygmund
theorem for operators with a standard kernel: they are of weak type `(1, 1)` as soon as they are
bounded on `L²` (`ContinuousLinearMap.mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow`). The same
bound is the hypothesis of the strong type `(p, p)` theorem for `1 < p < 2`
(`ContinuousLinearMap.eLpNorm_le_of_hormander`).

The proof integrates the pointwise estimate against the tail bound
`∫_{dist x y' > R} dist x y' ^ (-s) dx ≤ A 2ⁿ R ^ (n - s) / (1 - 2 ^ (n - s))` for `s > n`
(`TauCeti.setLIntegral_ofReal_dist_rpow_neg_le`). Taking `R = 2 dist y y'` and `s = n + δ` gives
Hörmander's condition, with a bound independent of `y` and `y'`.

## Main declarations

* `TauCeti.setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow`: the standard smoothness estimate
  implies Hörmander's condition.
* `TauCeti.setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi`: the same on `ℝⁿ`.
* `ContinuousLinearMap.mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow`: an operator bounded on
  `L²(ℝⁿ)` with a kernel satisfying the standard smoothness estimate is of weak type `(1, 1)`.

## References

* E. Stein, *Harmonic Analysis*, Chapter I, §6.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal NNReal

section Metric

variable {X G : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [SeminormedAddCommGroup G]

/-- **The standard smoothness estimate implies Hörmander's condition.** Let the closed balls
about `y'` satisfy the growth bound `μ (closedBall y' r) ≤ A rⁿ` with `0 ≤ n`, and let `K` satisfy
the standard smoothness estimate with exponent `δ > 0`,

`‖K x y - K x y'‖ ≤ C dist y y' ^ δ dist x y' ^ (-(n + δ))` whenever `dist x y' > 2 dist y y'`.

Then `∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ C A 2ⁿ / (2^δ - 1)`. -/
theorem setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow {K : X → X → G} {y y' : X}
    {A : ℝ≥0∞} {n : ℝ} (hμ : ∀ r, 0 < r → μ (closedBall y' r) ≤ A * ENNReal.ofReal (r ^ n))
    (hn : 0 ≤ n) {C : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x, 2 * dist y y' < dist x y' →
      ‖K x y - K x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(n + δ)))) :
    ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ∂μ ≤
      C * A * ENNReal.ofReal (2 ^ n / (2 ^ δ - 1)) := by
  set t := dist y y'
  have hmeas : MeasurableSet {x | 2 * t < dist x y'} :=
    measurableSet_lt measurable_const (continuous_id.dist continuous_const).measurable
  have hpt : ∀ x ∈ {x | 2 * t < dist x y'}, ‖K x y - K x y'‖ₑ ≤
      ENNReal.ofReal (C * t ^ δ) * ENNReal.ofReal (dist x y' ^ (-(n + δ))) := fun x hx => by
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, mul_assoc]
    exact ENNReal.ofReal_le_ofReal (hK x hx)
  calc ∫⁻ x in {x | 2 * t < dist x y'}, ‖K x y - K x y'‖ₑ ∂μ
      ≤ ∫⁻ x in {x | 2 * t < dist x y'},
          ENNReal.ofReal (C * t ^ δ) * ENNReal.ofReal (dist x y' ^ (-(n + δ))) ∂μ :=
        setLIntegral_mono' hmeas hpt
    _ = ENNReal.ofReal (C * t ^ δ) *
          ∫⁻ x in {x | 2 * t < dist x y'}, ENNReal.ofReal (dist x y' ^ (-(n + δ))) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ C * A * ENNReal.ofReal (2 ^ n / (2 ^ δ - 1)) := by
        rcases eq_or_lt_of_le (show 0 ≤ t from dist_nonneg) with ht | ht
        · rw [← ht, Real.zero_rpow hδ.ne', mul_zero, ENNReal.ofReal_zero, zero_mul]
          exact bot_le
        -- The scalar identity `C tᵟ · 2ⁿ (2t)^(-δ) / (1 - 2^(-δ)) = C 2ⁿ / (2^δ - 1)`.
        have hr : (C : ℝ) * t ^ δ *
            (2 ^ n / (1 - 2 ^ (n - (n + δ))) * (2 * t) ^ (n - (n + δ))) =
              C * (2 ^ n / (2 ^ δ - 1)) := by
          have h2 : (1 : ℝ) < 2 ^ δ := Real.one_lt_rpow one_lt_two hδ
          have : (2 : ℝ) ^ δ - 1 ≠ 0 := by linarith
          have : t ^ δ ≠ 0 := (Real.rpow_pos_of_pos ht δ).ne'
          simp only [show n - (n + δ) = -δ by ring, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2),
            Real.rpow_neg (by positivity : 0 ≤ 2 * t), Real.mul_rpow zero_le_two ht.le]
          field_simp
        calc ENNReal.ofReal (C * t ^ δ) *
              ∫⁻ x in {x | 2 * t < dist x y'}, ENNReal.ofReal (dist x y' ^ (-(n + δ))) ∂μ
            ≤ ENNReal.ofReal (C * t ^ δ) *
                (A * ENNReal.ofReal
                  (2 ^ n / (1 - 2 ^ (n - (n + δ))) * (2 * t) ^ (n - (n + δ)))) := by
              gcongr
              exact setLIntegral_ofReal_dist_rpow_neg_le hμ (by positivity) (by linarith)
                (by positivity)
          _ = A * ENNReal.ofReal (C * (2 ^ n / (2 ^ δ - 1))) := by
              rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), hr]
          _ = C * A * ENNReal.ofReal (2 ^ n / (2 ^ δ - 1)) := by
              rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
              ring

end Metric

section Pi

variable {ι G : Type*} [Fintype ι] [SeminormedAddCommGroup G]

/-- **The standard smoothness estimate implies Hörmander's condition** on `ℝⁿ = ι → ℝ`, with the
sup norm and Lebesgue measure. If `δ > 0` and

`‖K x y - K x y'‖ ≤ C dist y y' ^ δ dist x y' ^ (-(n + δ))` whenever `dist x y' > 2 dist y y'`,

then `∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ 4ⁿ C / (2^δ - 1)`. -/
theorem setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi {K : (ι → ℝ) → (ι → ℝ) → G}
    {y y' : ι → ℝ} {C : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x, 2 * dist y y' < dist x y' →
      ‖K x y - K x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Fintype.card ι + δ)))) :
    ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ≤
      C * ENNReal.ofReal (4 ^ Fintype.card ι / (2 ^ δ - 1)) := by
  -- Closed balls in the sup norm are cubes, of volume `(2r)ⁿ = 2ⁿ rⁿ`.
  have hμ (r : ℝ) (hr : 0 < r) : volume (closedBall y' r) ≤
      ENNReal.ofReal (2 ^ Fintype.card ι) * ENNReal.ofReal (r ^ (Fintype.card ι : ℝ)) := by
    rw [Real.volume_pi_closedBall y' hr.le, ← ENNReal.ofReal_mul (by positivity),
      Real.rpow_natCast, mul_pow]
  have h4 : (2 : ℝ) ^ Fintype.card ι * (2 ^ (Fintype.card ι : ℝ) / (2 ^ δ - 1)) =
      4 ^ Fintype.card ι / (2 ^ δ - 1) := by
    rw [Real.rpow_natCast, ← mul_div_assoc, ← mul_pow]
    norm_num
  refine (setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow hμ (Nat.cast_nonneg _) hδ hK).trans
    (le_of_eq ?_)
  rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity), h4]

end Pi

end TauCeti

namespace ContinuousLinearMap

open MeasureTheory Metric Set TauCeti
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Calderón–Zygmund theorem** for an operator with a standard kernel. Let `T` be a bounded
linear operator on `L²(ℝⁿ)` such that `T b x = ∫ K x y (b y) dy` for almost every `x` off any
closed ball outside which `b` vanishes, where for some `δ > 0` the kernel `K` satisfies the
standard smoothness estimate

`‖K x y - K x y'‖ ≤ C dist y y' ^ δ dist x y' ^ (-(n + δ))` whenever `dist x y' > 2 dist y y'`.

Then for every `f ∈ L²` and every `t`,

`t · |{‖T f‖ > t}| ≤ (2ⁿ (4 ‖T‖² + 1) + 4 · 4ⁿ C / (2^δ - 1)) ‖f‖₁`. -/
theorem mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow [Nonempty ι]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} (hKm : StronglyMeasurable (Function.uncurry K))
    {C : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖K x y - K x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Fintype.card ι + δ))))
    (hrep : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) →
        ∀ᵐ x, x ∉ closedBall y r → T b x = ∫ z, K x z (b z))
    (f : Lp E 2 (volume : Measure (ι → ℝ))) (t : ℝ≥0∞) :
    t * volume {x | t < ‖T f x‖ₑ} ≤
      (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) +
        4 * (C * ENNReal.ofReal (4 ^ Fintype.card ι / (2 ^ δ - 1)))) * ∫⁻ x, ‖f x‖ₑ :=
  mul_volume_lt_enorm_le_of_hormander T hKm
    (fun _ _ => setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi hδ fun x => hK x _ _) hrep f t

end ContinuousLinearMap
