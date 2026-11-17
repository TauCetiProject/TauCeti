/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.SchurTest
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# Hardy's inequality against `dt / t`

For `θ > 0`, `1 ≤ q ≤ ∞` and `g : ℝ → ℝ≥0∞`, **Hardy's inequality** in the weighted
form used by real interpolation reads

`‖t ↦ t ^ (-θ) ∫₀ᵗ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 - θ) g t‖_{L^q(dt / t)}`

(`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_le`). It is the step that bounds the norm of the real
interpolation space `(L¹, L^∞)_{θ,q}`, which integrates `t ^ (-θ) ∫₀ᵗ f*`, by the Lorentz gauge
`‖t ↦ t ^ (1 - θ) f* t‖_{L^q(dt / t)}`, which integrates the decreasing rearrangement `f*` itself.
The constant `θ⁻¹` is independent of `q`. With `q = p` and `θ = 1 - 1 / p` it is the classical
inequality `‖t ↦ t⁻¹ ∫₀ᵗ g‖_{L^p} ≤ p / (p - 1) ‖g‖_{L^p}` on `(0, ∞)`.

The average is an integral operator against `dt / t`: with `G s = s ^ (1 - θ) g s`,

`t ^ (-θ) ∫₀ᵗ g = ∫ k(t, s) G s ds / s`, where `k(t, s) = (s / t) ^ θ` for `s ≤ t` and `0`
otherwise.

Both the row integrals `∫ k(t, s) ds / s` and the column integrals `∫ k(t, s) dt / t` of the
kernel are `θ⁻¹`, by the dilation and inversion invariance of `dt / t` and the integral
`∫₀¹ u ^ θ du / u = θ⁻¹` (`TauCeti.lintegral_multHaar_indicator_Iic_one_rpow`), so Schur's test
(`TauCeti.eLpNorm_lintegral_mul_le`) gives the bound.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge University Press,
  1952, Theorems 327 and 330.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.3.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {θ : ℝ}

/-- The kernel of Hardy's averaging operator against `dt / t`: `(s / t) ^ θ` for `s ≤ t`, and `0`
otherwise. -/
private noncomputable def hardyKernel (θ : ℝ) (t s : ℝ) : ℝ≥0∞ :=
  if s ≤ t then ENNReal.ofReal ((s / t) ^ θ) else 0

private theorem measurable_uncurry_hardyKernel (θ : ℝ) :
    Measurable (Function.uncurry (hardyKernel θ)) :=
  Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    (Measurable.ennreal_ofReal (by fun_prop)) measurable_const

/-- The row integrals of the Hardy kernel: `∫ k(t, s) ds / s = θ⁻¹` for `t > 0`. -/
private theorem lintegral_hardyKernel_right (hθ : 0 < θ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ s, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have hmp : MeasurePreserving (t * ·) multHaar multHaar :=
    ⟨measurable_const_mul t, map_multHaar_mul_left ht⟩
  rw [← hmp.lintegral_comp (measurable_uncurry_hardyKernel θ).of_uncurry_left,
    ← lintegral_multHaar_indicator_Iic_one_rpow hθ]
  refine lintegral_congr fun u ↦ ?_
  simp only [hardyKernel, indicator_apply, mem_Iic, mul_le_iff_le_one_right ht,
    mul_div_cancel_left₀ _ ht.ne']

/-- The column integrals of the Hardy kernel: `∫ k(t, s) dt / t = θ⁻¹` for `s > 0`. -/
private theorem lintegral_hardyKernel_left (hθ : 0 < θ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have hmp : MeasurePreserving (s * ·) multHaar multHaar :=
    ⟨measurable_const_mul s, map_multHaar_mul_left hs⟩
  have hinv : MeasurePreserving Inv.inv multHaar multHaar := ⟨measurable_inv, map_multHaar_inv⟩
  have hmeas : Measurable fun t ↦ hardyKernel θ (s * t) s :=
    (measurable_uncurry_hardyKernel θ).of_uncurry_right.comp (measurable_const_mul s)
  -- substitute `t = s / v`, which turns the kernel into `v ^ θ` for `v ≤ 1`
  rw [← hmp.lintegral_comp (measurable_uncurry_hardyKernel θ).of_uncurry_right,
    ← hinv.lintegral_comp hmeas, ← lintegral_multHaar_indicator_Iic_one_rpow hθ]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with v hv
  simp only [hardyKernel, indicator_apply, mem_Iic, le_mul_iff_one_le_right hs,
    one_le_inv₀ hv, div_mul_cancel_left₀ hs.ne', inv_inv]

/-- Hardy's average as an integral operator against `dt / t`: for `t > 0`,
`t ^ (-θ) ∫₀ᵗ g = ∫ k(t, s) s ^ (1 - θ) g s ds / s`. -/
private theorem ofReal_rpow_neg_mul_setLIntegral_eq (g : ℝ → ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s =
      ∫⁻ s, hardyKernel θ t s * (ENNReal.ofReal (s ^ (1 - θ)) * g s) ∂multHaar := by
  rw [lintegral_multHaar_eq_setLIntegral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← Iic_inter_Ioi, ← Measure.restrict_restrict measurableSet_Iic,
    ← lintegral_indicator measurableSet_Iic]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
  simp only [hardyKernel, indicator_apply, mem_Iic]
  split_ifs
  · rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.div_rpow hs.le ht.le, Real.rpow_sub hs, Real.rpow_one, Real.rpow_neg ht.le]
    field_simp
  · simp

/-- **Hardy's inequality** against `dt / t`. For `θ > 0`, `1 ≤ q ≤ ∞` and `g : ℝ → ℝ≥0∞`,
`‖t ↦ t ^ (-θ) ∫₀ᵗ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 - θ) g t‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_neg_mul_setLIntegral_le (hθ : 0 < θ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) q multHaar := by
  have hA0 : ENNReal.ofReal θ⁻¹ ≠ 0 := by simpa using hθ
  by_cases hG : AEMeasurable (fun s ↦ ENNReal.ofReal (s ^ (1 - θ)) * g s) multHaar
  swap
  · -- otherwise the right-hand side is infinite
    rw [eLpNorm_of_not_aestronglyMeasurable fun h ↦ hG h.aemeasurable, ENNReal.mul_top hA0]
    exact le_top
  rw [eLpNorm_congr_ae (ae_pos_multHaar.mono fun t ht ↦
    ofReal_rpow_neg_mul_setLIntegral_eq (θ := θ) g ht)]
  refine (eLpNorm_lintegral_mul_le (measurable_uncurry_hardyKernel θ).aemeasurable hG hq
    (ae_pos_multHaar.mono fun t ht ↦ (lintegral_hardyKernel_right hθ ht).le)
    (ae_pos_multHaar.mono fun s hs ↦ (lintegral_hardyKernel_left hθ hs).le)).trans_eq ?_
  rw [← ENNReal.rpow_add _ _ hA0 ENNReal.ofReal_ne_top, sub_add_cancel, ENNReal.rpow_one]

end TauCeti
