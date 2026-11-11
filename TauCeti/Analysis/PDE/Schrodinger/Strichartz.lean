/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Dispersive
public import TauCeti.Analysis.PDE.Strichartz.TTStar

/-!
# The Strichartz estimate for the Schrödinger equation on the line at `(4, ∞)`

On a one-dimensional real inner product space, the dispersive estimate
`‖S(t) g‖_∞ ≤ (4π|t|)^(-1/2) ‖g‖₁` for the Schrödinger propagator `S(t) = exp(itΔ)`
(`TauCeti.eLpNorm_schrodingerPropagator_le`) is already an `L¹ → L^∞` bound for the time pairings
`S(s) S(t)* = S(s - t)` with decay `|s - t| ^ (-1/2) = |s - t| ^ (-2 / 4)`. So the `TT*` argument of
`TauCeti.Analysis.PDE.Strichartz.TTStar` applies with `(q, r) = (4, ∞)`, the admissible pair of
dimension one with `r = ∞`, without any interpolation. It gives the dual Strichartz estimate

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^{4/3}_t L¹_x}`

and the Strichartz estimate `‖S(t) f‖_{L⁴_t L^∞_x} ≤ C ‖f‖₂` tested against
`G ∈ L^{4/3}_t L¹_x`.

## Main declarations

* `TauCeti.exists_enorm_integral_schrodingerPropagator_neg_le`: the dual estimate.
* `TauCeti.exists_enorm_integral_inner_schrodingerPropagator_le`: the homogeneous estimate in
  weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- On the line, the time pairings of the Schrödinger propagator decay from `L¹` to `L^∞` like
`|s - t| ^ (-1/2)`. -/
private theorem eLpNorm_schrodingerPropagator_adjoint_le (hE : Module.finrank ℝ E = 1)
    {s t : ℝ} (hst : s ≠ t) (g : Lp V 2 (volume : Measure E)) :
    eLpNorm (schrodingerPropagator V s (((schrodingerPropagator V t)†) g)) ∞ volume ≤
      ENNReal.ofReal ((4 * Real.pi) ^ (-(2⁻¹ : ℝ))) *
        ‖s - t‖ₑ ^ (-(2 / (4 : ℝ≥0) : ℝ)) * eLpNorm g 1 volume := by
  have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
  have hk : ENNReal.ofReal ((4 * Real.pi) ^ (-(2⁻¹ : ℝ))) * ‖s - t‖ₑ ^ (-(2 / (4 : ℝ≥0) : ℝ)) =
      ENNReal.ofReal ((4 * Real.pi * |s - t|) ^ (-(Module.finrank ℝ E : ℝ) / 2)) := by
    rw [hE, ← ofReal_norm, Real.norm_eq_abs,
      ENNReal.ofReal_rpow_of_pos (abs_pos.2 hst'), ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow (by positivity) (abs_nonneg _)]
    norm_num
  rw [schrodingerPropagator_def, schrodingerPropagator_def, adjoint_phasePropagator,
    ← phasePropagator_add_apply, ← sub_eq_add_neg, ← schrodingerPropagator_def, hk]
  by_cases hg : Integrable g
  · exact eLpNorm_schrodingerPropagator_le hst' g hg
  · have hg' : eLpNorm g 1 volume = ∞ := by
      by_contra h
      exact hg (memLp_one_iff_integrable.1 (lt_top_iff_ne_top.2 h))
    rw [hg', ENNReal.mul_top (by positivity)]
    exact le_top

private theorem holderConjugate_four_div_three_four : (4 / 3 : ℝ≥0).HolderConjugate 4 := by
  rw [← NNReal.holderConjugate_coe_iff, Real.holderConjugate_iff]
  norm_num

/-- **The dual Strichartz estimate for the Schrödinger equation on the line**, at the admissible
pair `(4, ∞)`. There is `C` such that for every almost everywhere strongly measurable
`F : ℝ → L²(E, V)` on a one-dimensional space `E` for which `s ↦ S(-s) F(s)` is integrable,

`‖∫ S(-s) F(s) ds‖₂ ≤ C ‖F‖_{L^{4/3}_t L¹_x}`. -/
theorem exists_enorm_integral_schrodingerPropagator_neg_le (hE : Module.finrank ℝ E = 1) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp V 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ schrodingerPropagator V (-s) (F s)) →
      ‖∫ s, schrodingerPropagator V (-s) (F s)‖ₑ ≤
        C * eLpNorm (fun s : ℝ ↦ eLpNorm (F s) 1 (volume : Measure E)) ((4 / 3 : ℝ≥0) : ℝ≥0∞)
          volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ) (H := Lp V 2 (volume : Measure E))
    (E := V) (X := E) (μ := volume) (r := ∞) (r' := 1) (by norm_num : (2 : ℝ≥0) < 4)
    holderConjugate_four_div_three_four
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2⁻¹ : ℝ))) ^ (2⁻¹ : ℝ)).toNNReal,
    fun F hF hSF => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  simpa only [adjoint_phasePropagator] using hC (schrodingerPropagator V) _
    (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le hE hst g) F hF
    (by simpa only [adjoint_phasePropagator] using hSF)

/-- **The Strichartz estimate for the Schrödinger equation on the line**, at the admissible pair
`(4, ∞)`, in weak form. There is `C` such that for every `f ∈ L²(E, V)` on a one-dimensional space
`E` and every almost everywhere strongly measurable `G : ℝ → L²(E, V)` for which
`t ↦ S(-t) G(t)` is integrable,

`|∫ ⟪S(t) f, G(t)⟫ dt| ≤ C ‖f‖₂ ‖G‖_{L^{4/3}_t L¹_x}`.

This is `‖S(t) f‖_{L⁴_t L^∞_x} ≤ C ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_schrodingerPropagator_le (hE : Module.finrank ℝ E = 1) :
    ∃ C : ℝ≥0, ∀ (f : Lp V 2 (volume : Measure E)) (G : ℝ → Lp V 2 (volume : Measure E)),
      AEStronglyMeasurable G → Integrable (fun t ↦ schrodingerPropagator V (-t) (G t)) →
      ‖∫ t, ⟪schrodingerPropagator V t f, G t⟫_ℂ‖ₑ ≤
        C * ‖f‖ₑ * eLpNorm (fun t : ℝ ↦ eLpNorm (G t) 1 (volume : Measure E))
          ((4 / 3 : ℝ≥0) : ℝ≥0∞) volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp V 2 (volume : Measure E)) (E := V) (X := E) (μ := volume) (r := ∞) (r' := 1)
    (by norm_num : (2 : ℝ≥0) < 4) holderConjugate_four_div_three_four
  refine ⟨C * (ENNReal.ofReal ((4 * Real.pi) ^ (-(2⁻¹ : ℝ))) ^ (2⁻¹ : ℝ)).toNNReal,
    fun f G hG hSG => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (by finiteness)]
  exact hC (schrodingerPropagator V) _
    (fun s t hst g => eLpNorm_schrodingerPropagator_adjoint_le hE hst g) f G hG
    (by simpa only [adjoint_phasePropagator] using hSG)

end TauCeti
