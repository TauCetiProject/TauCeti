/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Integral

/-!
# Parameter integration and quantization

At each fixed position, Kohn–Nirenberg quantization on Schwartz inputs commutes with
integration over a parameter. The Fourier normalization remains `a(x, 2πζ)`.

`TauCeti.quantizeSchwartzValue_integral_of_integrable_bound` proves this for coefficient
maps `a y` over an s-finite measure, jointly measurable in the parameter and the frequency at
that position and dominated there by `G(y) ⟨ξ⟩ ^ m` with `G` integrable; the quantized values
are then integrable in the parameter
(`TauCeti.integrable_quantizeSchwartzValue_of_integrable_bound`). Integrals over a noncompact
parameter, such as the contour integrals of parameter-dependent symbols along a path to infinity,
need such a decaying majorant. `TauCeti.quantizeSchwartzValue_integral_of_uniform_bound` is the
case of a compact parameter space carrying a finite measure, with coefficients jointly continuous
in the parameter and the frequency and a parameter-uniform growth bound, and
`TauCeti.Symbol.quantizeSchwartzValue_integral` applies it to the native symbol integral using its
jointly continuous jets and uniform symbol estimates. No common compact spatial support is needed
for these pointwise identities.

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

section IntegrableBound

variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [SFinite μ]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  (a : Y → E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) {m : ℝ} {G : Y → ℝ}

omit [SFinite μ] in
/-- The integrand `(y, ζ) ↦ exp(2πi ⟪ζ, x⟫) a y (x, 2πζ) (𝓕 u ζ)` of the quantizations of a family
at `x` is integrable on the product when the coefficients at `x` are jointly a.e. strongly
measurable and dominated by `G y ⟨ξ⟩ ^ m` with `G` integrable. -/
private theorem integrable_quantizeSchwartzValue_family_integrand
    (hmeas : AEStronglyMeasurable (fun p : Y × E ↦ a p.1 (x, p.2)) (μ.prod volume))
    (hG : Integrable G μ) (hbound : ∀ y ξ, ‖a y (x, ξ)‖ ≤ G y * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    Integrable (fun p : Y × E ↦
      𝐞 ⟪p.2, x⟫ • a p.1 (x, (2 * π) • p.2) (𝓕 u p.2)) (μ.prod volume) := by
  have hscale : AEStronglyMeasurable (fun p : Y × E ↦ a p.1 (x, (2 * π) • p.2))
      (μ.prod volume) :=
    hmeas.comp_quasiMeasurePreserving ((QuasiMeasurePreserving.id μ).prodMap
      (Measure.quasiMeasurePreserving_smul volume Real.two_pi_pos.ne'))
  have hm : AEStronglyMeasurable (fun p : Y × E ↦
      𝐞 ⟪p.2, x⟫ • a p.1 (x, (2 * π) • p.2) (𝓕 u p.2)) (μ.prod volume) :=
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
      ).aestronglyMeasurable.comp_snd.smul
        (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hscale.prodMk (𝓕 u).continuous.aestronglyMeasurable.comp_snd))
  refine (hG.mul_prod ((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm
    (μ := (volume : Measure E)) (2 * π) m)).mono' hm (.of_forall fun p ↦ ?_)
  rw [Circle.norm_smul, ← mul_assoc]
  exact ((a p.1 (x, (2 * π) • p.2)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hbound p.1 _) (norm_nonneg _))

/-- **Quantization commutes with a parameter integral.** Let the coefficients `a y` at the
position `x` be jointly a.e. strongly measurable in the parameter and the frequency, and dominated
by `G y ⟨ξ⟩ ^ m` with `G` integrable. Then the quantization at `x` of `∫ a y dμ(y)` is the integral
of the quantizations at `x`. -/
theorem quantizeSchwartzValue_integral_of_integrable_bound
    (hmeas : AEStronglyMeasurable (fun p : Y × E ↦ a p.1 (x, p.2)) (μ.prod volume))
    (hG : Integrable G μ)
    (hbound : ∀ y ξ, ‖a y (x, ξ)‖ ≤ G y * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    quantizeSchwartzValue (fun p ↦ ∫ y, a y p ∂μ) u x =
      ∫ y, quantizeSchwartzValue (a y) u x ∂μ := by
  let H (y : Y) (ξ : E) : W := 𝐞 ⟪ξ, x⟫ • a y (x, (2 * π) • ξ) (𝓕 u ξ)
  have hHi : Integrable (Function.uncurry H) (μ.prod volume) :=
    integrable_quantizeSchwartzValue_family_integrand μ a u x hmeas hG hbound
  rw [quantizeSchwartzValue_def]
  calc
    _ = ∫ ξ, ∫ y, H y ξ ∂μ := by
      apply integral_congr_ae
      -- For almost every frequency, the coefficients are measurable in the parameter.
      filter_upwards [(Measure.quasiMeasurePreserving_smul (volume : Measure E)
        Real.two_pi_pos.ne').ae hmeas.prodMk_right] with ξ hξ
      have hi : Integrable (fun y ↦ a y (x, (2 * π) • ξ)) μ :=
        (hG.mul_const _).mono' hξ (.of_forall fun y ↦ hbound y _)
      simp only [H, ContinuousLinearMap.integral_apply hi, Circle.smul_def, integral_smul]
    _ = ∫ y, (∫ ξ, H y ξ) ∂μ := (integral_integral_swap hHi).symm
    _ = _ := by simp only [H, quantizeSchwartzValue_def]

omit [SFinite μ] in
/-- Under the hypotheses of `TauCeti.quantizeSchwartzValue_integral_of_integrable_bound`, the
quantizations at `x` are integrable in the parameter. -/
theorem integrable_quantizeSchwartzValue_of_integrable_bound
    (hmeas : AEStronglyMeasurable (fun p : Y × E ↦ a p.1 (x, p.2)) (μ.prod volume))
    (hG : Integrable G μ) (hbound : ∀ y ξ, ‖a y (x, ξ)‖ ≤ G y * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    Integrable (fun y ↦ quantizeSchwartzValue (a y) u x) μ := by
  simpa only [quantizeSchwartzValue_def] using
    (integrable_quantizeSchwartzValue_family_integrand μ a u x hmeas hG hbound).integral_prod_left

end IntegrableBound

section Coefficients

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  (a : Y → E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) {m : ℝ}

/-- Quantization commutes with a compact finite-measure parameter integral if, at the
position `x`, the coefficients are jointly continuous in parameter and frequency and
satisfy one polynomial growth bound for all parameters. -/
theorem quantizeSchwartzValue_integral_of_uniform_bound
    (hc : Continuous (fun p : Y × E ↦ a p.1 (x, p.2)))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ,
      ‖a y (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    quantizeSchwartzValue (fun p ↦ ∫ y, a y p ∂μ) u x =
      ∫ y, quantizeSchwartzValue (a y) u x ∂μ := by
  obtain ⟨C, -, h⟩ := hbound
  refine quantizeSchwartzValue_integral_of_integrable_bound μ a u x ?_ (integrable_const C) h
  borelize (V →L[ℂ] W)
  refine (stronglyMeasurable_iff_measurable_separable.2 ⟨hc.measurable, ?_⟩).aestronglyMeasurable
  -- The continuous image of the sigma-compact parameter/frequency space is separable.
  obtain ⟨K, hK, hcover⟩ := isSigmaCompact_range hc
  rw [← hcover]
  exact TopologicalSpace.IsSeparable.iUnion (fun k ↦ (hK k).isSeparable)

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
