/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Weighted-orbit `L¹` bilinear operators

Let `X` be an `R₁` Borel space with an inner-regular measure `μ` (`μ.InnerRegularCompactLTTop`),
let `B : K →L[𝕜] E₁ →L[𝕜] F` be a continuous bilinear map, and let `U : X → E₀ →L[𝕜] E₁` be a
strongly continuous family of bounded linear operators satisfying the uniform bound
`‖B k (U x v)‖ ≤ C * ‖k‖ * ‖v‖`.

For every Bochner-integrable weight `h : X → K` and every `v : E₀`, the orbit integrand
`x ↦ B (h x) (U x v)` is Bochner integrable without assuming separability of `K`, `E₁`, `F`,
second countability of `X`, σ-finiteness of `μ`, or operator-norm continuity of `U`: `h` vanishes
outside a σ-finite set, on which the inner regularity of `μ` makes the continuous map
`x ↦ B.flip (U x v)` almost everywhere strongly measurable. Integrating against `h ∈ Lp K 1 μ`
therefore produces a continuous bilinear operator `TauCeti.weightedOrbitL1`:

`Lp K 1 μ →L[𝕜] E₀ →L[𝕜] F`, `(h, v) ↦ ∫ x, B (h x) (U x v) ∂μ`.

This abstracts the shared Bochner-integral construction behind group convolution
(`MeasureTheory.Lp.convolutionL`), twisted C⋆-algebra convolution (`CStarAction.convolutionLp`), and
vector-valued covariant integrated forms (`CovariantRepresentation.integratedOperatorBochnerL1`).

## Main definitions

* `TauCeti.weightedOrbitL1`: the continuous bilinear map `(h, v) ↦ ∫ x, B (h x) (U x v) ∂μ`.

## Main statements

* `TauCeti.integrable_weightedOrbit`: integrability of `x ↦ B (h x) (U x v)` for integrable `h`.
* `TauCeti.norm_integral_weightedOrbit_le`: norm bound for `∫ x, B (h x) (U x v) ∂μ`.
* `TauCeti.weightedOrbitL1_apply`, `TauCeti.weightedOrbitL1_toL1`: evaluation formulas.
* `TauCeti.norm_weightedOrbitL1_apply_apply_le`, `TauCeti.norm_weightedOrbitL1_apply_le`,
  `TauCeti.norm_weightedOrbitL1_le`: operator norm bounds.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

section WeightedOrbit

variable {X 𝕜 K E₀ E₁ F : Type*}
  [MeasurableSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The weighted-orbit integrand `x ↦ B (h x) (U x v)` is Bochner integrable whenever `h` is
integrable, `U` is strongly continuous, `μ` is inner regular on sets of finite measure in an `R₁`
Borel space, and `‖B k (U x v)‖ ≤ C * ‖k‖ * ‖v‖`. -/
theorem integrable_weightedOrbit [TopologicalSpace X] [R1Space X] [BorelSpace X]
    {μ : Measure X} [μ.InnerRegularCompactLTTop]
    (B : K →L[𝕜] E₁ →L[𝕜] F) (U : X → E₀ →L[𝕜] E₁)
    (hU_cont : ∀ v, Continuous fun x => U x v)
    {C : ℝ} (hBU : ∀ x k v, ‖B k (U x v)‖ ≤ C * ‖k‖ * ‖v‖)
    {h : X → K} (hh : Integrable h μ) (v : E₀) :
    Integrable (fun x => B (h x) (U x v)) μ := by
  have hmeas : AEStronglyMeasurable (fun x => B (h x) (U x v)) μ := by
    simpa only [Function.comp_apply, ContinuousLinearMap.flip_apply] using
      hh.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
        (B.flip.continuous.comp (hU_cont v))
  exact ((hh.norm.const_mul C).mul_const ‖v‖).mono' hmeas
    (.of_forall fun x => hBU x (h x) v)

/-- Norm bound for the Bochner integral of a weighted orbit `x ↦ B (h x) (U x v)`. -/
theorem norm_integral_weightedOrbit_le [NormedSpace ℝ F] {μ : Measure X}
    (B : K →L[𝕜] E₁ →L[𝕜] F) (U : X → E₀ →L[𝕜] E₁)
    {C : ℝ} (hBU : ∀ x k v, ‖B k (U x v)‖ ≤ C * ‖k‖ * ‖v‖)
    {h : X → K} (hh : Integrable h μ) (v : E₀) :
    ‖∫ x, B (h x) (U x v) ∂μ‖ ≤ C * (∫ x, ‖h x‖ ∂μ) * ‖v‖ := by
  calc
    ‖∫ x, B (h x) (U x v) ∂μ‖ ≤ ∫ x, C * ‖h x‖ * ‖v‖ ∂μ :=
      norm_integral_le_of_norm_le ((hh.norm.const_mul C).mul_const ‖v‖)
        (.of_forall fun x => hBU x (h x) v)
    _ = C * (∫ x, ‖h x‖ ∂μ) * ‖v‖ := by
      rw [integral_mul_const, integral_const_mul]

section Constructor

variable [TopologicalSpace X] [R1Space X] [BorelSpace X]
  [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F]
  (μ : Measure X) [μ.InnerRegularCompactLTTop]
  (B : K →L[𝕜] E₁ →L[𝕜] F) (U : X → E₀ →L[𝕜] E₁)
  (hU_cont : ∀ v, Continuous fun x => U x v)
  {C : ℝ} (hBU : ∀ x k v, ‖B k (U x v)‖ ≤ C * ‖k‖ * ‖v‖)

/-- **Weighted-orbit `L¹` bilinear operator**: given a continuous bilinear map
`B : K →L[𝕜] E₁ →L[𝕜] F` and a strongly continuous family of bounded linear operators
`U : X → E₀ →L[𝕜] E₁` satisfying `‖B k (U x v)‖ ≤ C * ‖k‖ * ‖v‖`, sends `(h, v) : Lp K 1 μ × E₀`
to the Bochner integral `∫ x, B (h x) (U x v) ∂μ`. -/
def weightedOrbitL1 : Lp K 1 μ →L[𝕜] E₀ →L[𝕜] F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜
      (fun (h : Lp K 1 μ) (v : E₀) => ∫ x, B (h x) (U x v) ∂μ)
      (fun h₁ h₂ v => by
        rw [← integral_add (integrable_weightedOrbit B U hU_cont hBU (L1.integrable_coeFn h₁) v)
          (integrable_weightedOrbit B U hU_cont hBU (L1.integrable_coeFn h₂) v)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add h₁ h₂] with x hx
        rw [hx, Pi.add_apply, map_add, add_apply])
      (fun c h v => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c h] with x hx
        rw [hx, Pi.smul_apply, map_smul, smul_apply])
      (fun h v₁ v₂ => by
        rw [← integral_add (integrable_weightedOrbit B U hU_cont hBU (L1.integrable_coeFn h) v₁)
          (integrable_weightedOrbit B U hU_cont hBU (L1.integrable_coeFn h) v₂)]
        simp_rw [map_add])
      (fun c h v => by
        rw [← integral_smul]
        simp_rw [map_smul]))
    C fun h v => by
      simpa only [LinearMap.mk₂_apply, L1.norm_eq_integral_norm] using
        norm_integral_weightedOrbit_le B U hBU (L1.integrable_coeFn h) v

variable {μ B U hU_cont hBU}

/-- Evaluation formula for `weightedOrbitL1`. -/
theorem weightedOrbitL1_apply (h : Lp K 1 μ) (v : E₀) :
    weightedOrbitL1 μ B U hU_cont hBU h v = ∫ x, B (h x) (U x v) ∂μ :=
  (rfl)

/-- Evaluation of `weightedOrbitL1` on the `L¹` class of an integrable function `h`. -/
theorem weightedOrbitL1_toL1 {h : X → K} (hh : Integrable h μ) (v : E₀) :
    weightedOrbitL1 μ B U hU_cont hBU (hh.toL1 h) v = ∫ x, B (h x) (U x v) ∂μ := by
  rw [weightedOrbitL1_apply]
  refine integral_congr_ae ?_
  filter_upwards [hh.coeFn_toL1] with x hx
  rw [hx]

/-- Pointwise norm bound for `weightedOrbitL1`. -/
theorem norm_weightedOrbitL1_apply_apply_le (h : Lp K 1 μ) (v : E₀) :
    ‖weightedOrbitL1 μ B U hU_cont hBU h v‖ ≤ C * ‖h‖ * ‖v‖ := by
  simpa only [weightedOrbitL1_apply, L1.norm_eq_integral_norm] using
    norm_integral_weightedOrbit_le B U hBU (L1.integrable_coeFn h) v

/-- Operator norm bound on `weightedOrbitL1 μ B U hU_cont hBU h`. -/
theorem norm_weightedOrbitL1_apply_le (hC : 0 ≤ C) (h : Lp K 1 μ) :
    ‖weightedOrbitL1 μ B U hU_cont hBU h‖ ≤ C * ‖h‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg h)) fun v =>
    norm_weightedOrbitL1_apply_apply_le h v

/-- Bilinear operator norm bound for `weightedOrbitL1`. -/
theorem norm_weightedOrbitL1_le (hC : 0 ≤ C) :
    ‖weightedOrbitL1 μ B U hU_cont hBU‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound₂ _ hC fun h v =>
    norm_weightedOrbitL1_apply_apply_le h v

end Constructor

end WeightedOrbit

end TauCeti
