/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Integral

/-!
# Compact parameter integration and quantization

At each fixed position, Kohn–Nirenberg quantization on Schwartz inputs commutes with
integration over a compact parameter space carrying a finite measure. The coefficient
needs joint continuity in the parameter and frequency and a parameter-uniform growth
bound at that position. The Fourier normalization remains `a(x, 2πζ)`.

`TauCeti.quantizeSchwartzValue_integral_of_uniform_bound` proves this for coefficient
maps, and `TauCeti.Symbol.quantizeSchwartzValue_integral` applies it to the native symbol
integral using its jointly continuous jets and uniform symbol estimates. No common
compact spatial support is needed for these pointwise identities.

The proof follows `AtiyahSinger.quantize_integral_of_uniform_bound` in
`AtiyahSinger/Analysis/CompactSymbolIntegral.lean`: Schwartz decay gives an integrable
majorant on the product of parameter and frequency spaces, and Fubini exchanges the
integrals. Tau Ceti's existing weighted Schwartz integrability lemma replaces the
source's polynomial-majorant construction.

## References

* Lean-Atiyah-Singer, `AtiyahSinger/Analysis/CompactSymbolIntegral.lean`,
  `quantize_integral_of_uniform_bound`: the source formalization.
  <https://github.com/alpha-squared-labs/Lean-Atiyah-Singer>.
* Mathlib, `MeasureTheory/Integral/Prod.lean`: the Bochner–Fubini theorem.
  <https://github.com/leanprover-community/mathlib4>.
* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Chapter III,
  proof of Theorem 9.7, p. 214: compact-group averaging of operator homotopies.
  The parameter/Fourier integral exchange is a supplementary analytic input in the
  source formalization.
  <https://doi.org/10.1515/9781400883912>.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped FourierTransform SchwartzMap RealInnerProductSpace

namespace TauCeti

section Coefficients

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  (a : Y → E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) {m : ℝ}

private theorem integrable_quantizeSchwartzValue_family_integrand
    (hc : Continuous (fun p : Y × E ↦ a p.1 (x, p.2)))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ,
      ‖a y (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    Integrable (fun p : Y × E ↦
      𝐞 ⟪p.2, x⟫ • a p.1 (x, (2 * π) • p.2) (𝓕 u p.2)) (μ.prod volume) := by
  obtain ⟨C, -, h⟩ := hbound
  have ha := hc.comp (continuous_fst.prodMk (continuous_snd.const_smul (2 * π)))
  have hp : Continuous (fun p : Y × E ↦ 𝐞 ⟪p.2, x⟫) :=
    Real.continuous_fourierChar.comp (continuous_snd.inner continuous_const)
  have hv : Continuous (fun p : Y × E ↦ 𝓕 u p.2) :=
    (𝓕 u).continuous.comp continuous_snd
  have hHc : Continuous (fun p : Y × E ↦
      𝐞 ⟪p.2, x⟫ • a p.1 (x, (2 * π) • p.2) (𝓕 u p.2)) :=
    hp.smul (ha.clm_apply hv)
  have hHm : AEStronglyMeasurable (fun p : Y × E ↦
      𝐞 ⟪p.2, x⟫ • a p.1 (x, (2 * π) • p.2) (𝓕 u p.2)) (μ.prod volume) := by
    borelize W
    refine (stronglyMeasurable_iff_measurable_separable.2 ⟨hHc.measurable, ?_⟩).aestronglyMeasurable
    -- The continuous image of the sigma-compact parameter/frequency space is separable.
    obtain ⟨K, hK, hcover⟩ := isSigmaCompact_range hHc
    rw [← hcover]
    exact TopologicalSpace.IsSeparable.iUnion (fun k ↦ (hK k).isSeparable)
  have hi := (𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm
    (μ := (volume : Measure E)) (2 * π) m
  refine ((integrable_const (1 : ℝ) : Integrable (fun _ : Y ↦ (1 : ℝ)) μ).mul_prod
    (hi.const_mul C)).mono' hHm ?_
  filter_upwards [] with p
  simp only [Circle.norm_smul, one_mul]
  rw [← mul_assoc]
  exact ((a p.1 (x, (2 * π) • p.2)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (h p.1 _) (norm_nonneg _))

/-- Quantization commutes with a compact finite-measure parameter integral if, at the
position `x`, the coefficients are jointly continuous in parameter and frequency and
satisfy one polynomial growth bound for all parameters. -/
theorem quantizeSchwartzValue_integral_of_uniform_bound
    (hc : Continuous (fun p : Y × E ↦ a p.1 (x, p.2)))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ,
      ‖a y (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    quantizeSchwartzValue (fun p ↦ ∫ y, a y p ∂μ) u x =
      ∫ y, quantizeSchwartzValue (a y) u x ∂μ := by
  let H (y : Y) (ξ : E) : W := 𝐞 ⟪ξ, x⟫ • a y (x, (2 * π) • ξ) (𝓕 u ξ)
  have hHi : Integrable (Function.uncurry H) (μ.prod volume) :=
    integrable_quantizeSchwartzValue_family_integrand μ a u x hc hbound
  rw [quantizeSchwartzValue_def]
  calc
    _ = ∫ ξ, ∫ y, H y ξ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      have hi : Integrable (fun y ↦ a y (x, (2 * π) • ξ)) μ :=
        (hc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      simp only [H, ContinuousLinearMap.integral_apply hi, Circle.smul_def, integral_smul]
    _ = ∫ y, (∫ ξ, H y ξ) ∂μ := (integral_integral_swap hHi).symm
    _ = _ := by simp only [H, quantizeSchwartzValue_def]

end Coefficients

namespace Symbol

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ]
  {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
  (a : Y → Symbol n V W m)
  (hjets : ∀ k : ℕ, Continuous
    (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (a p.1).coefficient p.2))
  (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))

/-- Quantizing the integral of a compact symbol family on a Schwartz input gives the
parameter integral of the quantized values. The hypotheses are exactly those of
`Symbol.integral`. -/
@[simp]
theorem quantizeSchwartzValue_integral (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (integral μ a hjets hbound).coefficient u x =
      ∫ y, quantizeSchwartzValue (a y).coefficient u x ∂μ := by
  have hc : Continuous (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      (a p.1).coefficient p.2) := by
    have h := (hjets 0).eval
      (continuous_const (y := (0 : Fin 0 → CoordinateSpace n × CoordinateSpace n)))
    simpa only [iteratedFDeriv_zero_apply] using h
  obtain ⟨C, hC, h⟩ := hbound {x} isCompact_singleton [] []
  calc
    _ = quantizeSchwartzValue (fun p ↦ ∫ y, (a y).coefficient p ∂μ) u x :=
      quantizeSchwartzValue_congr_left (fun ξ ↦ coefficient_integral μ a hjets hbound (x, ξ)) u
    _ = _ := quantizeSchwartzValue_integral_of_uniform_bound μ
      (fun y ↦ (a y).coefficient) u x
      (hc.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
      ⟨C, hC, fun y ξ ↦ by
        simpa only [mixedDeriv_nil_nil, List.length_nil, Nat.cast_zero, sub_zero]
          using h y x (by simp) ξ⟩

end Symbol

end TauCeti
