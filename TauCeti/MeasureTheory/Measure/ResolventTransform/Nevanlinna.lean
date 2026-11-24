/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Nevanlinna
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Complex.Pick.Herglotz.Finite
import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Analytic characterization of resolvent transforms on the real line

A holomorphic function `F` on the upper half-plane `{z : ℂ | 0 < z.im}` is the resolvent transform
`m_μ(z) = ∫ (x - z)⁻¹ dμ(x)` of a finite Borel measure `μ` on `ℝ` if and only if `0 ≤ Im F(z)` on
the upper half-plane and `y ‖F(iy)‖` is bounded at infinity along the imaginary axis. It is the
resolvent transform of a probability measure if and only if `0 ≤ Im F(z)` on the upper half-plane
and `iy F(iy) → -1` as `y → ∞`.

The proof passes through the Herglotz representation in resolvent convention
(`TauCeti.exists_eq_subtractedResolventKernel_add`) together with the decaying imaginary-axis bound
criteria (`TauCeti.isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound` and
`TauCeti.eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound`), and reads off the
total mass from the imaginary-axis asymptotic `MeasureTheory.tendsto_mul_I_mul_resolventTransform`.

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not `(z - x)⁻¹`.

## Main results

* `TauCeti.nevanlinnaKernel_eq_one_add_sq_mul_resolvent_sub`: away from its pole, the Nevanlinna
  kernel `(1 + x z) / (x - z)` equals `(1 + x²) (x - z)⁻¹ - x`.
* `MeasureTheory.exists_isFiniteMeasure_resolventTransform_eq`: existence of a representing finite
  measure from `0 ≤ Im F` and an eventual bound on `y ‖F(iy)‖`.
* `MeasureTheory.exists_isFiniteMeasure_resolventTransform_eq_iff`: analytic characterization of
  resolvent transforms of finite measures on `ℝ`.
* `MeasureTheory.exists_isFiniteMeasure_measureReal_univ_eq_and_resolventTransform_eq`: existence
  with prescribed total mass `c` when `iy F(iy) → -c`.
* `MeasureTheory.exists_isFiniteMeasure_measureReal_univ_eq_and_resolventTransform_eq_iff`:
  analytic characterization of resolvent transforms of finite measures on `ℝ` with prescribed total
  mass `c`.
* `MeasureTheory.exists_isProbabilityMeasure_resolventTransform_eq_iff`: analytic characterization
  of resolvent transforms of probability measures on `ℝ`.

## References

* N. I. Akhiezer, *The Classical Moment Problem*, Oliver & Boyd (1965), Theorem 3.1.1.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.4.1.
* G. Teschl, *Mathematical Methods in Quantum Mechanics*, §3.4, Theorems 3.20 and 3.21.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- Away from its pole, the Nevanlinna kernel `(1 + x z) / (x - z)` decomposes into the weighted
resolvent `(1 + x²) (x - z)⁻¹` minus `x`. -/
theorem nevanlinnaKernel_eq_one_add_sq_mul_resolvent_sub {z : ℂ} {x : ℝ}
    (h : (x : ℂ) - z ≠ 0) :
    nevanlinnaKernel z x = ((1 + x ^ 2 : ℝ) : ℂ) * resolvent z x - x := by
  rw [nevanlinnaKernel_def, resolvent_real_eq_inv]
  push_cast
  field_simp [h]
  ring

end TauCeti

namespace MeasureTheory

/-- **Existence of a representing measure from the Pick–Nevanlinna conditions.** If `F` is
holomorphic on the upper half-plane with nonnegative imaginary part and `y ‖F(iy)‖` is eventually
bounded as `y → ∞`, then `F` agrees on the upper half-plane with the resolvent transform of a
finite measure on `ℝ`. -/
theorem exists_isFiniteMeasure_resolventTransform_eq {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im)
    (hbdd : ∃ C : ℝ, ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z := by
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨_, μ, -, hμw, hrep⟩ := TauCeti.exists_eq_subtractedResolventKernel_add hF him
  exact ⟨μ, TauCeti.isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound hμw hrep
      (TauCeti.eventually_mul_abs_im_le_of_mul_norm_le hC),
    TauCeti.eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound hrep hC⟩

/-- **Analytic characterization of resolvent transforms of finite measures.** A function on `ℂ`
agrees on the upper half-plane with the resolvent transform of a finite Borel measure on `ℝ` if and
only if it is holomorphic there, has nonnegative imaginary part there, and satisfies an eventual
`O(y⁻¹)` bound along the positive imaginary axis. -/
theorem exists_isFiniteMeasure_resolventTransform_eq_iff {F : ℂ → ℂ} :
    (∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z) ↔
      DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
        (∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im) ∧
        ∃ C : ℝ, ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C := by
  refine ⟨?_, fun ⟨hF, him, hbdd⟩ ↦ exists_isFiniteMeasure_resolventTransform_eq hF him hbdd⟩
  rintro ⟨μ, hμ, hF⟩
  refine ⟨analyticOnNhd_resolventTransform_setOf_im_pos.differentiableOn.congr fun z hz ↦ hF z hz,
    fun z hz ↦ hF z hz ▸ im_resolventTransform_nonneg hz.le, μ.real univ, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [hF (y * I) (by simpa using hy)]
  exact mul_norm_resolventTransform_ofReal_mul_I_le hy

/-- **Existence of a representing finite measure with prescribed total mass.** If `F` is
holomorphic on the upper half-plane with nonnegative imaginary part and `iy F(iy) → -c` as
`y → ∞`, then `F` agrees on the upper half-plane with the resolvent transform of a finite measure
on `ℝ` of total mass `c`. -/
theorem exists_isFiniteMeasure_measureReal_univ_eq_and_resolventTransform_eq {F : ℂ → ℂ} {c : ℝ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im)
    (hlim : Tendsto (fun y : ℝ ↦ (y : ℂ) * I * F (y * I)) atTop (𝓝 (-(c : ℂ)))) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ.real univ = c ∧
      ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z := by
  have hbdd : ∃ C : ℝ, ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C := by
    refine ⟨|c| + 1, ?_⟩
    have hnorm : Tendsto (fun y : ℝ ↦ ‖(y : ℂ) * I * F (y * I)‖) atTop (𝓝 |c|) := by
      simpa using hlim.norm
    filter_upwards [hnorm.eventually (gt_mem_nhds (by linarith : |c| < |c| + 1)),
      eventually_gt_atTop 0] with y hy hypos
    simpa [abs_of_pos hypos] using hy.le
  obtain ⟨μ, hμ, hFμ⟩ := exists_isFiniteMeasure_resolventTransform_eq hF him hbdd
  have hμlim : Tendsto (fun y : ℝ ↦ (y : ℂ) * I * F (y * I)) atTop (𝓝 (-(μ.real univ : ℂ))) :=
    (tendsto_mul_I_mul_resolventTransform (μ := μ)).congr' <|
      (eventually_gt_atTop 0).mono fun y hy ↦ by
        dsimp only
        rw [hFμ (y * I) (by simpa using hy)]
  have hmass : μ.real univ = c := by
    have := neg_inj.1 (tendsto_nhds_unique hμlim hlim)
    exact_mod_cast this
  exact ⟨μ, hμ, hmass, hFμ⟩

/-- **Analytic characterization of resolvent transforms of finite measures with prescribed total
mass.** A function on `ℂ` agrees on the upper half-plane with the resolvent transform of a finite
Borel measure on `ℝ` of total mass `c` if and only if it is holomorphic there, has nonnegative
imaginary part there, and satisfies `iy F(iy) → -c` as `y → ∞`. -/
theorem exists_isFiniteMeasure_measureReal_univ_eq_and_resolventTransform_eq_iff {F : ℂ → ℂ}
    {c : ℝ} :
    (∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ.real univ = c ∧
        ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z) ↔
      DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
        (∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im) ∧
        Tendsto (fun y : ℝ ↦ (y : ℂ) * I * F (y * I)) atTop (𝓝 (-(c : ℂ))) := by
  refine ⟨?_, fun ⟨hF, him, hlim⟩ ↦
    exists_isFiniteMeasure_measureReal_univ_eq_and_resolventTransform_eq hF him hlim⟩
  rintro ⟨μ, hμ, rfl, hF⟩
  obtain ⟨hdiff, him, -⟩ := exists_isFiniteMeasure_resolventTransform_eq_iff.1 ⟨μ, hμ, hF⟩
  refine ⟨hdiff, him, (tendsto_mul_I_mul_resolventTransform (μ := μ)).congr' ?_⟩
  filter_upwards [eventually_gt_atTop 0] with y hy
  exact congrArg ((y : ℂ) * I * ·) (hF (y * I) (by simpa using hy)).symm

/-- **Analytic characterization of resolvent transforms of probability measures.** A function on
`ℂ` agrees on the upper half-plane with the resolvent transform of a probability measure on `ℝ` if
and only if it is holomorphic there, has nonnegative imaginary part there, and satisfies
`iy F(iy) → -1` as `y → ∞`. -/
theorem exists_isProbabilityMeasure_resolventTransform_eq_iff {F : ℂ → ℂ} :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z) ↔
      DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
        (∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im) ∧
        Tendsto (fun y : ℝ ↦ (y : ℂ) * I * F (y * I)) atTop (𝓝 (-1)) := by
  rw [← ofReal_one, ← exists_isFiniteMeasure_measureReal_univ_eq_and_resolventTransform_eq_iff]
  exact exists_congr fun μ ↦
    ⟨fun ⟨hμ, hF⟩ ↦ ⟨inferInstance, probReal_univ, hF⟩,
      fun ⟨_, hm, hF⟩ ↦ ⟨isProbabilityMeasure_iff_real.2 hm, hF⟩⟩

end MeasureTheory

end
