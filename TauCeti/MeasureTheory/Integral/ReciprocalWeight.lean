/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Perspective
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import TauCeti.Analysis.Convex.Deriv
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.Probability.Density

/-!
# A reciprocal-weighted convex integral comparison

For a finite measure `ν` and an almost everywhere positive function `g`, Jensen's inequality
with weight `1 / g` compares `∫ Φ(g) / g` with
`m * Φ (ν.real univ / m)`, where `m = ∫ 1 / g`. Monotonicity of `Φ` and of its perspective
then allow a lower bound on `ν.real univ` and an upper bound on `m` to be substituted.
The resulting inequality applies to a level surface with `g` the gradient norm. Empty
measures and zero denominators are included using the real division convention.

`ConvexOn.setLIntegral_ofReal_mul_inv_le` is a version for extended integrals over two sets that
needs no integrability or monotonicity: Jensen's inequality for a supporting line compares the
integrals of `Φ(‖v‖) ‖v‖⁻¹` and `Φ(‖u‖) ‖u‖⁻¹` when `‖v‖` is constant on its set, that set has
at most the measure of the other, and the integrals of the reciprocal weights compare the other
way.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen,
  *The Pólya–Szegő inequality for smoothing rearrangements*, Theorem 5.8.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace ConvexOn

/-- A reciprocal-weighted Jensen comparison. A lower bound `P` on the measure of a level
surface and an upper bound `M` on its reciprocal-gradient integral yield a lower bound on
the convex gradient integral. Positivity of the reciprocal integral is derived when the
measure is nonzero, so the statement also includes empty levels and `M = 0`. -/
theorem mul_map_div_le_integral_div {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) {g : α → ℝ}
    (hg : ∀ᵐ x ∂ν, 0 < g x) (hi : Integrable (fun x ↦ (g x)⁻¹) ν)
    (hΦi : Integrable (fun x ↦ Φ (g x) / g x) ν) {P M : ℝ}
    (hP : 0 ≤ P) (hPν : P ≤ ν.real univ) (hM : (∫ x, (g x)⁻¹ ∂ν) ≤ M) :
    M * Φ (P / M) ≤ ∫ x, Φ (g x) / g x ∂ν := by
  by_cases hν : ν = 0
  · have hP0 : P = 0 := le_antisymm (by simpa [hν] using hPν) hP
    simp [hν, hP0, hΦ0]
  have : NeZero ν := ⟨hν⟩
  have hgn : ∀ᵐ x ∂ν, 0 ≤ (g x)⁻¹ := hg.mono fun x hx ↦ (inv_pos.mpr hx).le
  let m := ∫ x, (g x)⁻¹ ∂ν
  have hm : 0 < m := by
    refine lt_of_le_of_ne (integral_nonneg_of_ae hgn) ?_
    intro hm0
    have hz := (integral_eq_zero_iff_of_nonneg_ae hgn hi).mp hm0.symm
    obtain ⟨x, hx, hx0⟩ := (hg.and hz).exists
    exact (inv_pos.mpr hx).ne' hx0
  have hiae : AEMeasurable (fun x ↦ (g x)⁻¹) ν := hi.aestronglyMeasurable.aemeasurable
  let μ := ν.withDensity (fun x ↦ ENNReal.ofReal (g x)⁻¹)
  have : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hgn).mpr hi)
  have hμm : μ.real univ = m := by
    simpa using TauCeti.Probability.integral_withDensity_ofReal hiae hgn (fun _ ↦ (1 : ℝ))
  have : NeZero μ := ⟨fun h ↦ by simpa [h] using hμm.trans_ne hm.ne'⟩
  have hweight : (fun x ↦ g x / g x) =ᵐ[ν] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hg] with x hx using div_self hx.ne'
  have hdiv (f : α → ℝ) : (fun x ↦ (g x)⁻¹ • f x) = fun x ↦ f x / g x := by
    ext x
    rw [smul_eq_mul, inv_mul_eq_div]
  have hμg : Integrable g μ := by
    rw [TauCeti.Probability.integrable_withDensity_ofReal_iff hiae hgn, hdiv]
    exact (integrable_const (1 : ℝ)).congr hweight.symm
  have hμΦ : Integrable (fun x ↦ Φ (g x)) μ := by
    rw [TauCeti.Probability.integrable_withDensity_ofReal_iff hiae hgn, hdiv]
    exact hΦi
  have hμint : ∫ x, g x ∂μ = ν.real univ := by
    rw [TauCeti.Probability.integral_withDensity_ofReal hiae hgn, hdiv]
    simpa only [integral_const, smul_eq_mul, mul_one] using integral_congr_ae hweight
  have hμΦint : ∫ x, Φ (g x) ∂μ = ∫ x, Φ (g x) / g x ∂ν := by
    rw [TauCeti.Probability.integral_withDensity_ofReal hiae hgn, hdiv]
  have hgμ : ∀ᵐ x ∂μ, 0 ≤ g x :=
    (withDensity_absolutelyContinuous ν _).ae_le (hg.mono fun _ hx ↦ hx.le)
  have hJ := hΦ.map_average_le_of_monotoneOn_Ici hΦm hgμ hμg hμΦ
  rw [average_eq, average_eq, hμm, hμint, hμΦint] at hJ
  have hJ' : m * Φ (ν.real univ / m) ≤ ∫ x, Φ (g x) / g x ∂ν := by
    rw [mul_comm m, div_eq_inv_mul]
    exact (le_div_iff₀ hm).mp (by simpa only [smul_eq_mul, div_eq_inv_mul] using hJ)
  calc
    M * Φ (P / M) ≤ m * Φ (P / m) := hΦ.antitoneOn_mul_map_div hΦ0 hP hm
      (hm.trans_le hM) hM
    _ ≤ m * Φ (ν.real univ / m) := mul_le_mul_of_nonneg_left
      (hΦm (div_nonneg hP hm.le) (div_nonneg measureReal_nonneg hm.le)
        (div_le_div_of_nonneg_right hPν hm.le)) hm.le
    _ ≤ ∫ x, Φ (g x) / g x ∂ν := hJ'

/-- **Jensen's inequality for a supporting line, with reciprocal weights.** This is the levelwise
comparison behind the Pólya–Szegő inequality. Let `Φ` be convex on `[0, ∞)` with `Φ 0 ≤ 0`, and
let `u` and `v` be nonvanishing on measurable sets `A` and `B`, with `‖v‖` constant on `B`. If `B`
has at most the measure of `A`, and the integral of `‖v‖⁻¹` over `B` is finite and at least that
of `‖u‖⁻¹` over `A`, then the integral of `Φ(‖v‖) ‖v‖⁻¹` over `B` is at most that of
`Φ(‖u‖) ‖u‖⁻¹` over `A`. -/
theorem setLIntegral_ofReal_mul_inv_le {X F G : Type*} [MeasurableSpace X]
    {ν : Measure X} [NormedAddCommGroup F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [NormedAddCommGroup G] {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) {u : X → F} {v : X → G}
    (hu : Measurable u) (huA : ∀ x ∈ A, u x ≠ 0) (hvB : ∀ x ∈ B, v x ≠ 0)
    (hvc : ∀ x ∈ B, ∀ y ∈ B, ‖v x‖ = ‖v y‖) (hP : ν B ≤ ν A)
    (hm : ∫⁻ x in A, ‖u x‖ₑ⁻¹ ∂ν ≤ ∫⁻ x in B, ‖v x‖ₑ⁻¹ ∂ν)
    (hm' : ∫⁻ x in B, ‖v x‖ₑ⁻¹ ∂ν ≠ ∞) :
    ∫⁻ x in B, ENNReal.ofReal (Φ ‖v x‖) * ‖v x‖ₑ⁻¹ ∂ν ≤
      ∫⁻ x in A, ENNReal.ofReal (Φ ‖u x‖) * ‖u x‖ₑ⁻¹ ∂ν := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
  · simp
  obtain ⟨k', d', hk', hd', hle', heq'⟩ :=
    hΦ.exists_mul_sub_le_max_zero hΦ0 (norm_pos_iff.2 (hvB b hb))
  -- The supporting line to the positive part of `Φ` at `‖v b‖`, written in `ℝ≥0∞`.
  set k := ENNReal.ofReal k'
  set d := ENNReal.ofReal d'
  have hd : d ≠ ∞ := ENNReal.ofReal_ne_top
  have hofReal (s : ℝ) : ENNReal.ofReal (max (Φ s) 0 + d') = ENNReal.ofReal (Φ s) + d := by
    simp [d, ENNReal.ofReal_add (le_max_right _ _) hd', ENNReal.ofReal_max]
  have hle (s : ℝ) (hs : 0 ≤ s) : k * ENNReal.ofReal s ≤ ENNReal.ofReal (Φ s) + d := by
    rw [← hofReal, ← ENNReal.ofReal_mul hk']
    exact ENNReal.ofReal_le_ofReal (hle' s hs)
  have heq : ENNReal.ofReal (Φ ‖v b‖) + d = k * ENNReal.ofReal ‖v b‖ := by
    rw [← hofReal, heq', ENNReal.ofReal_mul hk']
  -- On `B` the tangent line touches: the weight `(Φ(‖v‖) + d) ‖v‖⁻¹` is the slope `k`.
  have hBk : ∫⁻ x in B, ENNReal.ofReal (Φ ‖v x‖) * ‖v x‖ₑ⁻¹ ∂ν +
      d * ∫⁻ x in B, ‖v x‖ₑ⁻¹ ∂ν ≤ k * ν B := by
    rw [← lintegral_const_mul' d _ hd, ← setLIntegral_const]
    refine (le_lintegral_add _ _).trans (setLIntegral_mono' hB fun x hx ↦ ?_)
    rw [← add_mul, ← ofReal_norm, hvc x hx b hb, heq, mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (norm_pos_iff.2 (hvB b hb))).ne'
        ENNReal.ofReal_ne_top, mul_one]
  -- On `A` the tangent line lies below: the weight `(Φ(‖u‖) + d) ‖u‖⁻¹` is at least `k`.
  have hAk : k * ν A ≤ ∫⁻ x in A, ENNReal.ofReal (Φ ‖u x‖) * ‖u x‖ₑ⁻¹ ∂ν +
      d * ∫⁻ x in A, ‖u x‖ₑ⁻¹ ∂ν := by
    have hmeas : Measurable fun x ↦ d * ‖u x‖ₑ⁻¹ := hu.eNorm.inv.const_mul d
    rw [← lintegral_const_mul' d _ hd, ← setLIntegral_const, ← lintegral_add_right _ hmeas]
    refine setLIntegral_mono' hA fun x hx ↦ ?_
    have hx0 : ‖u x‖ₑ ≠ 0 := ENNReal.coe_ne_zero.2 (nnNorm_ne_zero_iff.2 (huA x hx))
    calc k = k * ‖u x‖ₑ * ‖u x‖ₑ⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hx0 eNorm_ne_top, mul_one]
      _ ≤ (ENNReal.ofReal (Φ ‖u x‖) + d) * ‖u x‖ₑ⁻¹ := by
          rw [← ofReal_norm]
          gcongr
          exact hle _ (norm_nonneg _)
      _ = _ := by rw [add_mul, mul_comm d]
  refine ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top hd hm') ?_
  calc _ ≤ k * ν B := hBk
    _ ≤ k * ν A := by gcongr
    _ ≤ _ := hAk
    _ ≤ _ := by gcongr

end ConvexOn
