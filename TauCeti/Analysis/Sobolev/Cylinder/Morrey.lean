/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Sobolev.Morrey.Basic
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip
import TauCeti.MeasureTheory.Measure.Haar.Prod

/-!
# Morrey's estimate on the cylinder

Let `V` be a real Banach space. Sections of the trivial bundle with fibre `V` over the cylinder
`ℝ × S¹` are maps `ξ : ℝ × ℝ → V` of period one in the second variable `t`, and the fundamental
domain of the cylinder is the strip `ℝ × [0, 1]` with its Lebesgue measure
`TauCeti.StripSobolev.stripMeasure`. The `W^{1,p}` norm of a `C¹` section is, up to a factor
between `1` and `3 ^ (1 / p)`, the `Lᵖ` norm on the strip of its jet
`TauCeti.StripSobolev.jet ξ = (ξ, ∂s ξ, ∂t ξ)`.

The cylinder has dimension two, so for `p > 2` Morrey's inequality bounds a section pointwise by
its `W^{1,p}` norm: there is a constant `C`, depending on `p`, with

`‖ξ z‖ ≤ C ‖jet ξ‖_{Lᵖ(ℝ × [0, 1])}`

for every `C¹` section `ξ` of period one in `t` and every point `z`
(`TauCeti.CylinderSobolev.exists_enorm_le_mul_eLpNorm_jet`). No decay of `ξ` at the ends is
assumed: if the right-hand side is finite, the bound holds anyway. Applied to differences, the
same constant bounds `‖ξ z - η z‖` by the `Lᵖ` norm of `jet (ξ - η)`, so sections whose jets
converge in `Lᵖ` converge uniformly.

The proof applies the Morrey potential estimate on the unit ball `B` about `z`
(`TauCeti.enorm_sub_setAverage_le_of_starConvex_of_finrank_lt`), which bounds `ξ z` minus the
mean of `ξ` over `B` by the `Lᵖ(B)` norm of the derivative of `ξ`. The mean itself is bounded by
the `Lᵖ(B)` norm of `ξ` (Hölder's inequality, `TauCeti.enorm_setAverage_le`). In the sup norm
of `ℝ × ℝ` the ball `B` is a square of side two, which lies in two consecutive strips
`ℝ × [τ, τ + 1]`. For a function of period one in `t` the integral over each of them equals the
integral over `ℝ × [0, 1]` (`TauCeti.setLIntegral_univ_prod_Icc_add_eq_of_periodic`), so the
`Lᵖ(B)` norm of a periodic section is at most twice its `Lᵖ` norm on the strip
(`TauCeti.CylinderSobolev.eLpNorm_restrict_ball_le_two_mul_of_periodic`).

This is the Sobolev embedding that turns the `Lᵖ` form of the quadratic estimate for the Floer
operator, stated with sup norms of the increments, into a `W^{1,p}` estimate
(`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_jet` in
`TauCeti.Geometry.Symplectic.Floer.QuadraticEstimate`).

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.1,
  on the Sobolev embedding `W^{1,p} ⊂ C⁰` for `p > 2` on surfaces.
-/

public section

namespace TauCeti.CylinderSobolev

open MeasureTheory Metric Set Module
open StripSobolev (jet stripMeasure norm_le_norm_jet eLpNorm_fderiv_le_two_mul_eLpNorm_jet
  continuous_jet)
open scoped ENNReal NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Unit balls of the cylinder.** The integral over a ball of radius one of a measurable function
of period one in `t` is at most twice its integral over the strip `ℝ × [0, 1]`. -/
theorem setLIntegral_ball_le_two_mul_of_periodic {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g)
    (hper : ∀ s t, g (s, t + 1) = g (s, t)) (z : ℝ × ℝ) :
    ∫⁻ y in ball z 1, g y ≤ 2 * ∫⁻ y, g y ∂stripMeasure := by
  have hsub : ball z 1 ⊆
      (univ : Set ℝ) ×ˢ Icc (z.2 - 1) (z.2 - 1 + 1) ∪ (univ : Set ℝ) ×ˢ Icc z.2 (z.2 + 1) := by
    intro y hy
    simp only [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hy
    obtain ⟨-, h₁, h₂⟩ := hy
    rcases le_total y.2 z.2 with h | h
    · exact Or.inl ⟨mem_univ _, by linarith, by linarith⟩
    · exact Or.inr ⟨mem_univ _, h, by linarith⟩
  have hstrip (τ : ℝ) :
      ∫⁻ y in (univ : Set ℝ) ×ˢ Icc τ (τ + 1), g y = ∫⁻ y, g y ∂stripMeasure := by
    rw [Measure.volume_eq_prod]
    exact setLIntegral_univ_prod_Icc_add_eq_of_periodic one_pos hg hper τ
  calc ∫⁻ y in ball z 1, g y
      ≤ ∫⁻ y in (univ : Set ℝ) ×ˢ Icc (z.2 - 1) (z.2 - 1 + 1) ∪
          (univ : Set ℝ) ×ˢ Icc z.2 (z.2 + 1), g y := lintegral_mono_set hsub
    _ ≤ _ := lintegral_union_le _ _ _
    _ = 2 * ∫⁻ y, g y ∂stripMeasure := by rw [hstrip, hstrip, two_mul]

/-- **`Lᵖ` norms over unit balls of the cylinder.** The `Lᵖ` norm over a ball of radius one of a
strongly measurable function of period one in `t` is at most twice its `Lᵖ` norm on the strip, for
`1 ≤ p < ∞`. -/
theorem eLpNorm_restrict_ball_le_two_mul_of_periodic {f : ℝ × ℝ → E} (hf : StronglyMeasurable f)
    (hper : ∀ s t, f (s, t + 1) = f (s, t)) {p : ℝ≥0} (hp : 1 ≤ p) (z : ℝ × ℝ) :
    eLpNorm f p (volume.restrict (ball z 1)) ≤ 2 * eLpNorm f p stripMeasure := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp1 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hp
  rw [eLpNorm_nnreal_eq_lintegral hp0 hf.aestronglyMeasurable,
    eLpNorm_nnreal_eq_lintegral hp0 hf.aestronglyMeasurable]
  calc (∫⁻ y in ball z 1, ‖f y‖ₑ ^ (p : ℝ)) ^ (1 / (p : ℝ))
      ≤ (2 * ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂stripMeasure) ^ (1 / (p : ℝ)) := by
        gcongr
        exact setLIntegral_ball_le_two_mul_of_periodic
          (hf.eNorm.pow_const _) (fun s t ↦ by rw [hper]) z
    _ = 2 ^ (1 / (p : ℝ)) * (∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂stripMeasure) ^ (1 / (p : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ 2 * (∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂stripMeasure) ^ (1 / (p : ℝ)) := by
        gcongr
        calc (2 : ℝ≥0∞) ^ (1 / (p : ℝ)) ≤ 2 ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le one_le_two hp1
          _ = 2 := ENNReal.rpow_one 2

/-- **Morrey's estimate on the cylinder.** For `p > 2` there is a constant `C` such that every
`C¹` section `ξ` of period one in `t` satisfies `‖ξ z‖ ≤ C ‖jet ξ‖_{Lᵖ(ℝ × [0, 1])}` at every
point `z`. -/
theorem exists_enorm_le_mul_eLpNorm_jet [CompleteSpace V] {p : ℝ≥0} (hp : 2 < p) :
    ∃ C : ℝ≥0, ∀ {ξ : ℝ × ℝ → V}, ContDiff ℝ 1 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ z, ‖ξ z‖ₑ ≤ C * eLpNorm (jet ξ) p stripMeasure := by
  have hn : finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hp' : (finrank ℝ (ℝ × ℝ) : ℝ≥0) < p := by rw [hn]; exact_mod_cast hp
  have hp1 : 1 ≤ p := le_of_lt (lt_of_le_of_lt (by norm_num) hp)
  set m := volume (ball (0 : ℝ × ℝ) 1)
  have hm (z : ℝ × ℝ) : volume (ball z 1) = m := Measure.addHaar_ball_center volume z 1
  have hm0 : m ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hmtop : m ≠ ∞ := measure_ball_lt_top.ne
  -- The Morrey potential estimate on the unit ball about `z`, with a constant independent of `z`
  -- since all unit balls have the same measure.
  obtain ⟨c₀, hmor, hc₀⟩ : ∃ c₀ : ℝ≥0∞, (∀ {ξ : ℝ × ℝ → V}, ContDiff ℝ 1 ξ → ∀ z,
      ‖ξ z - ⨍ y in ball z 1, ξ y‖ₑ ≤ c₀ * eLpNorm (fderiv ℝ ξ) p (volume.restrict (ball z 1))) ∧
      c₀ ≠ ∞ :=
    ⟨_, fun {ξ} hξ z ↦ (enorm_sub_setAverage_le_of_starConvex_of_finrank_lt (μ := volume)
      (u := ξ) (S := ball z 1) isOpen_ball hξ.contDiffOn
      ((convex_ball z 1).starConvex (mem_ball_self one_pos)) ball_subset_closedBall Subset.rfl
      (by rw [hm]; exact hm0) hp').trans_eq (by rw [hm]), by finiteness⟩
  -- Hölder's inequality for the mean over the unit ball about `z`.
  obtain ⟨c₁, hmean, hc₁⟩ : ∃ c₁ : ℝ≥0∞, (∀ (ξ : ℝ × ℝ → V) z,
      ‖⨍ y in ball z 1, ξ y‖ₑ ≤ c₁ * eLpNorm ξ p (volume.restrict (ball z 1))) ∧ c₁ ≠ ∞ :=
    ⟨_, fun ξ z ↦ (TauCeti.enorm_setAverage_le (mu := volume) (s := ball z 1) (f := ξ) (p := p)
      (by exact_mod_cast hp1) ENNReal.coe_ne_top).trans_eq (by rw [hm, ENNReal.coe_toReal]),
      ENNReal.rpow_ne_top_of_ne_zero hm0 hmtop⟩
  refine ⟨((2 * c₀ + c₁) * 2).toNNReal, fun {ξ} hξ hper z ↦ ?_⟩
  rw [ENNReal.coe_toNNReal (by finiteness)]
  -- The jet on the unit ball is controlled by the jet on the strip.
  have hball := eLpNorm_restrict_ball_le_two_mul_of_periodic (continuous_jet hξ).stronglyMeasurable
    (jet_add_one_of_periodic hper) hp1 z
  -- The derivative and the section are controlled by the jet.
  have hder := eLpNorm_fderiv_le_two_mul_eLpNorm_jet (μ := volume.restrict (ball z 1))
    (hξ.continuous_fderiv one_ne_zero).aestronglyMeasurable p
  have hval : eLpNorm ξ p (volume.restrict (ball z 1)) ≤
      eLpNorm (jet ξ) p (volume.restrict (ball z 1)) :=
    eLpNorm_mono hξ.continuous.aestronglyMeasurable (norm_le_norm_jet ξ)
  set N := eLpNorm (jet ξ) p (volume.restrict (ball z 1))
  calc ‖ξ z‖ₑ = ‖(ξ z - ⨍ y in ball z 1, ξ y) + ⨍ y in ball z 1, ξ y‖ₑ := by
        rw [sub_add_cancel]
    _ ≤ ‖ξ z - ⨍ y in ball z 1, ξ y‖ₑ + ‖⨍ y in ball z 1, ξ y‖ₑ := eNorm_add_le _ _
    _ ≤ c₀ * (2 * N) + c₁ * N := by
        gcongr
        · exact (hmor hξ z).trans (by gcongr)
        · exact (hmean ξ z).trans (by gcongr)
    _ = (2 * c₀ + c₁) * N := by ring
    _ ≤ (2 * c₀ + c₁) * (2 * eLpNorm (jet ξ) p stripMeasure) := by gcongr
    _ = (2 * c₀ + c₁) * 2 * eLpNorm (jet ξ) p stripMeasure := by ring

end TauCeti.CylinderSobolev
