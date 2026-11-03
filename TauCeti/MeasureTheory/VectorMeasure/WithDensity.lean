/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Integration against a vector measure with density

For a measure `ν` and an integrable `g : X → F`, Mathlib's `ν.withDensityᵥ g` is the vector
measure `s ↦ ∫ x in s, g x ∂ν`, and its variation is `ν.withDensity ‖g‖ₑ`
(`MeasureTheory.Measure.variation_withDensityᵥ`). This file computes integrals against it through
a continuous bilinear pairing `B : E →L[ℝ] F →L[ℝ] G`:

`∫ᵛ x, f x ∂[B; ν.withDensityᵥ g] = ∫ x, B (f x) (g x) ∂ν`

for every `f` integrable against the variation of `ν.withDensityᵥ g`. Every `ν`-a.e. strongly
measurable, essentially bounded `f` is such a function. So integration against a measure given by
a density reduces to Bochner integration against the underlying positive measure.

Over an `RCLike` field `𝕜` with the multiplication pairing, a finite positive measure `ν` is
regarded as the scalar measure `ν.withDensityᵥ (fun _ => 1)`. It takes the value `ν.real s` on a
measurable set `s` and has variation `ν`, and integration against it is Bochner integration
against `ν`. A change of `g` on a `ν`-null set does not change `ν.withDensityᵥ g`
(Mathlib's `MeasureTheory.WithDensityᵥEq.congr_ae`). A change of `f` on a `ν`-null set does not
change the integral (`MeasureTheory.VectorMeasure.integral_withDensityᵥ_congr_ae`).

## Main declarations

* `MeasureTheory.VectorMeasure.integral_withDensityᵥ`: integration against `ν.withDensityᵥ g`
  through a bilinear pairing is the Bochner integral of the pairing against `ν`.
* `MeasureTheory.VectorMeasure.integral_mul_withDensityᵥ`: the scalar form
  `∫ᵛ x, f x ∂[mul ℝ 𝕜; ν.withDensityᵥ g] = ∫ x, f x * g x ∂ν` for essentially bounded `f`.
* `MeasureTheory.withDensityᵥ_one_apply`, `MeasureTheory.Measure.variation_withDensityᵥ_one` and
  `MeasureTheory.VectorMeasure.integral_mul_withDensityᵥ_one`: a finite positive measure as a
  scalar measure, its values, its variation, and integration against it.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill, 1987, Chapter 6.
-/

public section

open Filter
open scoped ENNReal NNReal

namespace MeasureTheory

variable {X E F G : Type*} [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The variation of a vector measure with density with respect to `ν` is absolutely continuous
with respect to `ν`. -/
theorem Measure.variation_withDensityᵥ_absolutelyContinuous [CompleteSpace F] (ν : Measure X)
    (g : X → F) : (ν.withDensityᵥ g).variation ≪ ν := by
  by_cases hg : Integrable g ν
  · rw [Measure.variation_withDensityᵥ hg]
    exact withDensity_absolutelyContinuous _ _
  · simp [Measure.withDensityᵥ, hg]

namespace VectorMeasure

variable [CompleteSpace F] {g : X → F} {f : X → E}

omit [NormedSpace ℝ E] in
/-- A `ν`-a.e. strongly measurable, essentially bounded function is integrable against the vector
measure with an integrable density with respect to `ν`. -/
theorem integrable_withDensityᵥ_of_bound (hg : Integrable g ν) (hf : AEStronglyMeasurable f ν)
    (C : ℝ) (hfC : ∀ᵐ x ∂ν, ‖f x‖ ≤ C) : (ν.withDensityᵥ g).Integrable f := by
  have hac := Measure.variation_withDensityᵥ_absolutelyContinuous ν g
  have : IsFiniteMeasure (ν.withDensityᵥ g).variation := by
    rw [Measure.variation_withDensityᵥ hg]
    exact isFiniteMeasure_withDensity hg.2.ne
  exact Integrable.of_bound (hf.mono_ac hac) C (hac.ae_le hfC)

/-- A change of the integrand on a `ν`-null set does not change its integral against a vector
measure with density with respect to `ν`. -/
theorem integral_withDensityᵥ_congr_ae (B : E →L[ℝ] F →L[ℝ] G) {f₁ f₂ : X → E}
    (h : f₁ =ᵐ[ν] f₂) :
    ∫ᵛ x, f₁ x ∂[B; ν.withDensityᵥ g] = ∫ᵛ x, f₂ x ∂[B; ν.withDensityᵥ g] :=
  integral_congr_ae ((Measure.variation_withDensityᵥ_absolutelyContinuous ν g).ae_le h)

/-- The Bochner integral of `x ↦ B (f x) (g x)` against `ν` is the integral, against the variation
`ν.withDensity ‖g‖ₑ` of `ν.withDensityᵥ g`, of the pairing of `f` with the direction of `g`. -/
private theorem integral_eq_integral_variation_withDensityᵥ (B : E →L[ℝ] F →L[ℝ] G)
    (hg : Integrable g ν) (f : X → E) :
    ∫ x, B (f x) (g x) ∂ν = ∫ x, B (f x) (‖g x‖⁻¹ • g x) ∂(ν.withDensityᵥ g).variation := by
  rw [Measure.variation_withDensityᵥ hg, integral_withDensity_eq_integral_toReal_smul₀
    hg.aestronglyMeasurable.enorm (ae_of_all _ fun _ => enorm_lt_top)]
  congr with x
  rcases eq_or_ne (g x) 0 with hx | hx
  · simp [hx]
  · rw [toReal_enorm, ← (B (f x)).map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx),
      one_smul]

/-- **Integration against a vector measure with density.** For an integrable density `g` with
respect to `ν` and a function `f` integrable against the variation of `ν.withDensityᵥ g`,
the integral of `f` against `ν.withDensityᵥ g` through a bilinear pairing `B` is the Bochner
integral of `x ↦ B (f x) (g x)` against `ν`. -/
theorem integral_withDensityᵥ (B : E →L[ℝ] F →L[ℝ] G) (hg : Integrable g ν)
    (hf : (ν.withDensityᵥ g).Integrable f) :
    ∫ᵛ x, f x ∂[B; ν.withDensityᵥ g] = ∫ x, B (f x) (g x) ∂ν := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG, MeasureTheory.integral_of_not_completeSpace hG]
  -- We prove the equality with the right-hand side written as an integral against the variation
  -- `ρ`, by induction on `f ∈ L¹(ρ)`.
  set ρ := (ν.withDensityᵥ g).variation
  set u : X → F := fun x => ‖g x‖⁻¹ • g x
  have hrhs := integral_eq_integral_variation_withDensityᵥ B hg
  have hu : AEStronglyMeasurable u ρ :=
    (hg.aestronglyMeasurable.norm.inv₀.smul hg.aestronglyMeasurable).mono_ac
      (Measure.variation_withDensityᵥ_absolutelyContinuous ν g)
  have hnorm (f : X → E) (x : X) : ‖B (f x) (u x)‖ ≤ ‖B‖ * ‖f x‖ :=
    (B.le_opNorm₂ _ _).trans (mul_le_of_le_one_right (by positivity)
      (by simp [u, norm_smul, inv_mul_le_one]))
  have hint {f : X → E} (hf : Integrable f ρ) : Integrable (fun x => B (f x) (u x)) ρ :=
    (hf.norm.const_mul ‖B‖).mono' (B.aestronglyMeasurable_comp₂ hf.1 hu)
      (ae_of_all _ (hnorm f))
  rw [hrhs]
  refine Integrable.induction (μ := ρ)
    (fun f => ∫ᵛ x, f x ∂[B; ν.withDensityᵥ g] = ∫ x, B (f x) (u x) ∂ρ) ?_ ?_ ?_ ?_ hf
  · intro c s hs hsρ
    have : IsFiniteMeasure (ρ.restrict s) := ⟨by simpa [hs] using hsρ⟩
    rw [integral_indicator_const _ hs, ← hrhs, withDensityᵥ_apply hg hs,
      ← (B c).integral_comp_comm hg.integrableOn, ← MeasureTheory.integral_indicator hs]
    congr with x
    by_cases hx : x ∈ s <;> simp [hx]
  · intro f₁ f₂ _ hf₁ hf₂ h₁ h₂
    simp only [Pi.add_apply, ContinuousLinearMap.map_add₂]
    rw [integral_fun_add hf₁ hf₂, h₁, h₂, MeasureTheory.integral_add (hint hf₁) (hint hf₂)]
  · -- Both sides are continuous on `L¹(ρ)`; the right-hand side is `‖B‖`-Lipschitz.
    refine isClosed_eq continuous_integral
      (LipschitzWith.of_dist_le_mul (K := ‖B‖₊) fun f₁ f₂ => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, L1.norm_eq_integral_norm, coe_nnnorm, ← integral_const_mul,
      ← MeasureTheory.integral_sub (hint (L1.integrable_coeFn f₁))
        (hint (L1.integrable_coeFn f₂))]
    refine norm_integral_le_of_norm_le ((L1.integrable_coeFn _).norm.const_mul _) ?_
    filter_upwards [Lp.coeFn_sub f₁ f₂] with x hx
    rw [← ContinuousLinearMap.map_sub₂, hx]
    exact hnorm (f₁ - f₂ : X → E) x
  · intro f₁ f₂ h _ h₁
    rw [← integral_congr_ae h, h₁]
    exact MeasureTheory.integral_congr_ae (h.mono fun x hx => by simp [hx])

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Integration against a scalar measure with density.** For an integrable scalar density `g`
with respect to `ν` and a `ν`-a.e. strongly measurable, essentially bounded `f`,
`∫ᵛ x, f x ∂[mul ℝ 𝕜; ν.withDensityᵥ g] = ∫ x, f x * g x ∂ν`. -/
theorem integral_mul_withDensityᵥ {g : X → 𝕜} (hg : Integrable g ν) {f : X → 𝕜}
    (hf : AEStronglyMeasurable f ν) (M : ℝ) (hfM : ∀ᵐ x ∂ν, ‖f x‖ ≤ M) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ 𝕜; ν.withDensityᵥ g] = ∫ x, f x * g x ∂ν := by
  simp [integral_withDensityᵥ _ hg (integrable_withDensityᵥ_of_bound hg hf M hfM)]

end VectorMeasure

variable {𝕜 : Type*} [RCLike 𝕜] [IsFiniteMeasure ν]

/-- A finite positive measure, regarded as a scalar measure with constant density `1`, takes the
value `ν.real s` on a measurable set `s`. -/
@[simp]
theorem withDensityᵥ_one_apply {s : Set X} (hs : MeasurableSet s) :
    ν.withDensityᵥ (fun _ => (1 : 𝕜)) s = (ν.real s : 𝕜) := by
  rw [withDensityᵥ_apply (integrable_const _) hs, setIntegral_const, RCLike.real_smul_eq_coe_mul,
    mul_one]

/-- A finite positive measure, regarded as a scalar measure with constant density `1`, has
variation the measure itself. -/
@[simp]
theorem Measure.variation_withDensityᵥ_one :
    (ν.withDensityᵥ fun _ => (1 : 𝕜)).variation = ν := by
  simp [Measure.variation_withDensityᵥ (integrable_const _)]

/-- Integration against a finite positive measure, regarded as a scalar measure with constant
density `1`, is Bochner integration against the measure. Both sides vanish when `f` is not
integrable. -/
@[simp]
theorem VectorMeasure.integral_mul_withDensityᵥ_one (f : X → 𝕜) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ 𝕜; ν.withDensityᵥ fun _ => (1 : 𝕜)] =
      ∫ x, f x ∂ν := by
  by_cases hf : Integrable f ν
  · rw [integral_withDensityᵥ _ (integrable_const _)
      (by rwa [VectorMeasure.Integrable, Measure.variation_withDensityᵥ_one])]
    simp
  · rw [integral_undef (by rwa [VectorMeasure.Integrable, Measure.variation_withDensityᵥ_one]),
      MeasureTheory.integral_undef hf]

end MeasureTheory
