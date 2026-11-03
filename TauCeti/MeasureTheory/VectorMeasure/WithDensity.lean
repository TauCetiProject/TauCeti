/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import TauCeti.MeasureTheory.VectorMeasure.ScalarIntegral

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

The density may also be taken with respect to a vector measure `μ`: Mathlib's
`μ.withDensity g B` is the vector measure `s ↦ ∫ᵛ x in s, g x ∂[B; μ]` when `g` is integrable
against `μ`, and `0` otherwise. Its variation is at most `‖B‖` times `|μ|.withDensity ‖g‖ₑ`, so it
is finite and absolutely continuous with respect to `|μ|`. For a scalar measure `μ`, consider the
weighted measure `g · μ = μ.withDensity g (mul ℝ 𝕜)`. Its variation is at most `M • |μ|` when
`‖g‖ ≤ M` holds `|μ|`-a.e. For a density `g` integrable against `μ`, `g · μ` has variation exactly
`|μ|.withDensity ‖g‖ₑ` and satisfies the change-of-density formula

`∫ᵛ x, f x ∂[mul ℝ 𝕜; g · μ] = ∫ᵛ x, f x * g x ∂[mul ℝ 𝕜; μ]`.

Consequently `h · (g · μ) = (h * g) · μ` for such `g`, and, when `|μ|` is finite, a constant
density `c` gives `c • μ`. A change of `g` on a `|μ|`-null set does not change `g · μ` (Mathlib's
`MeasureTheory.VectorMeasure.withDensity_congr`). Weighted measures of this kind describe the
matrix elements of a Borel functional calculus: the scalar measure of `⟪ξ, g(a) ψ⟫` is `g` times
that of `⟪ξ, ψ⟫`.

## Main declarations

* `MeasureTheory.VectorMeasure.integral_withDensityᵥ`: integration against `ν.withDensityᵥ g`
  through a bilinear pairing is the Bochner integral of the pairing against `ν`.
* `MeasureTheory.VectorMeasure.integral_mul_withDensityᵥ`: the scalar form
  `∫ᵛ x, f x ∂[mul ℝ 𝕜; ν.withDensityᵥ g] = ∫ x, f x * g x ∂ν` for essentially bounded `f`.
* `MeasureTheory.withDensityᵥ_one_apply`, `MeasureTheory.Measure.variation_withDensityᵥ_one` and
  `MeasureTheory.VectorMeasure.integral_mul_withDensityᵥ_one`: a finite positive measure as a
  scalar measure, its values, its variation, and integration against it.
* `MeasureTheory.VectorMeasure.withDensity_of_not_integrable`,
  `MeasureTheory.VectorMeasure.variation_withDensity_le_smul`,
  `MeasureTheory.VectorMeasure.variation_withDensity_absolutelyContinuous` and the instance
  `MeasureTheory.VectorMeasure.isFiniteMeasure_variation_withDensity`: the junk value of
  `μ.withDensity g B` and control of its variation.
* `MeasureTheory.VectorMeasure.variation_withDensity_mul` and
  `MeasureTheory.VectorMeasure.variation_withDensity_mul_le_smul`: the variation of `g · μ` and
  its bound.
* `MeasureTheory.VectorMeasure.integrable_withDensity_mul_iff` and
  `MeasureTheory.VectorMeasure.integral_withDensity_mul`: integrability and integration against
  `g · μ`.
* `MeasureTheory.VectorMeasure.withDensity_withDensity_mul` and
  `MeasureTheory.VectorMeasure.withDensity_const_mul`: composition of densities and constant
  densities.

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
    rw [dist_eq_norm, dist_eq_norm, L1.norm_eq_integral_norm, coe_nnnorm,
      ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub (hint (L1.integrable_coeFn f₁)) (hint (L1.integrable_coeFn f₂))]
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

/-! ### Vector measures with density with respect to a vector measure -/

namespace VectorMeasure

section General

variable {μ : VectorMeasure X F} {g : X → E} {B : E →L[ℝ] F →L[ℝ] G}

/-- A density that is not integrable against `μ` gives the zero vector measure. -/
theorem withDensity_of_not_integrable (hg : ¬μ.Integrable g) : μ.withDensity g B = 0 := by
  rw [withDensity, dite_eq_right hg]

/-- The variation of the vector measure `μ.withDensity g B` is at most `‖B‖` times the measure with
density `‖g‖ₑ` with respect to the variation of `μ`. -/
theorem variation_withDensity_le_smul (μ : VectorMeasure X F) (g : X → E)
    (B : E →L[ℝ] F →L[ℝ] G) :
    (μ.withDensity g B).variation ≤ ‖B‖₊ • μ.variation.withDensity fun x => ‖g x‖ₑ := by
  refine variation_WithDensity_le.trans (Measure.le_iff.2 fun s hs => ?_)
  rw [MeasureTheory.withDensity_apply _ hs, Measure.smul_apply,
    MeasureTheory.withDensity_apply _ hs, ← lintegral_smul_measure, ← Measure.restrict_smul]
  exact lintegral_mono' (Measure.restrict_mono le_rfl (variation_transpose_le μ B)) le_rfl

/-- The variation of a vector measure with density with respect to `μ` is absolutely continuous
with respect to the variation of `μ`. -/
theorem variation_withDensity_absolutelyContinuous (μ : VectorMeasure X F) (g : X → E)
    (B : E →L[ℝ] F →L[ℝ] G) : (μ.withDensity g B).variation ≪ μ.variation :=
  (Measure.absolutelyContinuous_of_le variation_WithDensity_le).trans
    ((withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_variation_transpose μ B))

/-- A vector measure with density with respect to a vector measure has finite variation. This
holds for every density: a non-integrable density gives the zero vector measure. -/
instance isFiniteMeasure_variation_withDensity :
    IsFiniteMeasure (μ.withDensity g B).variation := by
  by_cases hg : μ.Integrable g
  · have := isFiniteMeasure_withDensity (μ := μ.variation) hg.2.ne
    exact isFiniteMeasure_of_le _ (variation_withDensity_le_smul μ g B)
  · rw [withDensity_of_not_integrable hg, variation_zero]
    infer_instance

end General

section Scalar

variable {μ : VectorMeasure X 𝕜} {f g : X → 𝕜}

/-- **The variation of a scalar measure with density.** For a density `g` integrable against a
scalar measure `μ`, the variation of `g · μ = μ.withDensity g (mul ℝ 𝕜)` is the measure with
density `‖g‖ₑ` with respect to the variation of `μ`. -/
theorem variation_withDensity_mul (hg : μ.Integrable g) :
    (μ.withDensity g (ContinuousLinearMap.mul ℝ 𝕜)).variation =
      μ.variation.withDensity fun x => ‖g x‖ₑ := by
  rw [variation_withDensity hg fun x y => by simp, variation_transpose_eq _ _ fun x y => by simp]

/-- If a scalar density `g` is bounded by `M` almost everywhere for the variation of `μ`, then the
variation of `g · μ` is at most `M` times the variation of `μ`. -/
theorem variation_withDensity_mul_le_smul {M : ℝ} (hgM : ∀ᵐ x ∂μ.variation, ‖g x‖ ≤ M) :
    (μ.withDensity g (ContinuousLinearMap.mul ℝ 𝕜)).variation ≤
      ENNReal.ofReal M • μ.variation := by
  refine (variation_withDensity_le_smul μ g _).trans ?_
  rw [ContinuousLinearMap.opNNNorm_mul, one_smul, ← withDensity_const]
  exact withDensity_mono (hgM.mono fun x hx => by
    dsimp only
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx)

/-- A function `f` is integrable against the scalar measure `g · μ` exactly when `f * g` is
integrable against `μ`. -/
theorem integrable_withDensity_mul_iff (hg : μ.Integrable g) :
    (μ.withDensity g (ContinuousLinearMap.mul ℝ 𝕜)).Integrable f ↔
      μ.Integrable fun x => f x * g x := by
  have hgm : AEStronglyMeasurable g μ.variation := hg.1
  rw [VectorMeasure.Integrable, variation_withDensity_mul hg,
    integrable_withDensity_iff_integrable_smul₀' hgm.enorm (ae_of_all _ fun _ => enorm_lt_top)]
  -- The direction `‖g x‖⁻¹ • g x` of `g` has norm at most one and is a.e. strongly measurable.
  -- Multiplying by it, or by its conjugate, converts `‖g‖ • f` into `f * g` and back.
  have hu : AEStronglyMeasurable (fun x => ‖g x‖⁻¹ • g x) μ.variation :=
    hgm.norm.inv₀.smul hgm
  have hub : ∀ᵐ x ∂μ.variation, ‖‖g x‖⁻¹ • g x‖ ≤ 1 :=
    ae_of_all _ fun x => by simp [norm_smul, inv_mul_le_one]
  constructor
  · intro hf
    refine (hf.mul_bdd hu hub).congr (ae_of_all _ fun x => ?_)
    rcases eq_or_ne (g x) 0 with hx | hx
    · simp [hx]
    · have hn : (‖g x‖ : 𝕜) ≠ 0 := by simpa using hx
      simp only [toReal_enorm, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv]
      field_simp
  · intro hf
    refine (hf.mul_bdd (c := 1) hu.star (hub.mono fun x hx => ?_)).congr
      (ae_of_all _ fun x => ?_)
    · simpa only [Pi.star_apply, star_smul, star_trivial, RCLike.star_def, norm_smul,
        RCLike.norm_conj] using hx
    rcases eq_or_ne (g x) 0 with hx | hx
    · simp [hx]
    · have hn : (‖g x‖ : 𝕜) ≠ 0 := by simpa using hx
      simp only [toReal_enorm, RCLike.real_smul_eq_coe_mul, Pi.star_apply, star_mul',
        RCLike.star_def, map_inv₀, RCLike.conj_ofReal]
      rw [mul_assoc, mul_left_comm (g x), RCLike.mul_conj]
      field_simp

/-- **Change of density for scalar measures.** For a density `g` integrable against a scalar
measure `μ`, integrating `f` against `g · μ = μ.withDensity g (mul ℝ 𝕜)` is integrating `f * g`
against `μ`:

`∫ᵛ x, f x ∂[mul ℝ 𝕜; g · μ] = ∫ᵛ x, f x * g x ∂[mul ℝ 𝕜; μ]`.

No hypothesis on `f` is needed: when `f` is not integrable against `g · μ`, both sides vanish. -/
theorem integral_withDensity_mul (hg : μ.Integrable g) (f : X → 𝕜) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ 𝕜; μ.withDensity g (ContinuousLinearMap.mul ℝ 𝕜)] =
      ∫ᵛ x, f x * g x ∂[ContinuousLinearMap.mul ℝ 𝕜; μ] := by
  set η := μ.withDensity g (ContinuousLinearMap.mul ℝ 𝕜)
  have hρ : η.variation = μ.variation.withDensity fun x => ‖g x‖ₑ := variation_withDensity_mul hg
  have hmul {f : X → 𝕜} (hf : η.Integrable f) : μ.Integrable fun x => f x * g x :=
    (integrable_withDensity_mul_iff hg).1 hf
  by_cases hf : η.Integrable f; swap
  · rw [integral_undef hf, integral_undef (mt (integrable_withDensity_mul_iff hg).2 hf)]
  have hlint (u : X → 𝕜) :
      ∫⁻ x, ‖u x‖ₑ ∂η.variation = ∫⁻ x, ‖u x‖ₑ * ‖g x‖ₑ ∂μ.variation := by
    rw [hρ, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hg.1.enorm
      (ae_of_all _ fun _ => enorm_lt_top)]
    simp_rw [Pi.mul_apply, mul_comm]
  refine Integrable.induction (μ := η.variation)
    (fun f => ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ 𝕜; η] =
      ∫ᵛ x, f x * g x ∂[ContinuousLinearMap.mul ℝ 𝕜; μ]) ?_ ?_ ?_ ?_ hf
  · -- On an indicator `c • 1_s`, both sides are `c * ∫ᵛ x in s, g x ∂[mul ℝ 𝕜; μ]`.
    intro c s hs _
    rw [integral_indicator_const _ hs, withDensity_apply hg, ContinuousLinearMap.mul_apply',
      ← integral_const_mul, ← integral_indicator hs]
    congr with x
    by_cases hx : x ∈ s <;> simp [hx]
  · intro f₁ f₂ _ hf₁ hf₂ h₁ h₂
    simp only [Pi.add_apply, add_mul]
    rw [integral_fun_add hf₁ hf₂, h₁, h₂, integral_fun_add (hmul hf₁) (hmul hf₂)]
  · -- Both sides are continuous on `L¹(|g · μ|)`; the right-hand side is `1`-Lipschitz.
    refine isClosed_eq continuous_integral (LipschitzWith.of_edist_le fun f₁ f₂ => ?_).continuous
    rw [edist_eq_enorm_sub, ← integral_fun_sub (hmul (L1.integrable_coeFn f₁))
      (hmul (L1.integrable_coeFn f₂)), L1.edist_def]
    simp_rw [← sub_mul, edist_eq_enorm_sub, hlint, ← enorm_mul]
    refine enorm_integral_le_lintegral_enorm.trans ?_
    rw [enorm_eq_nnnorm, ContinuousLinearMap.opNNNorm_mul, ENNReal.coe_one, one_mul]
  · -- A `|g · μ|`-null set meets `{g ≠ 0}` in a `|μ|`-null set, where `f * g` does not see `f`.
    intro f₁ f₂ hae _ h₁
    rw [← integral_congr_ae hae, h₁]
    refine integral_congr_ae ?_
    rw [hρ, EventuallyEq, ae_withDensity_iff' hg.1.enorm] at hae
    filter_upwards [hae] with x hx
    rcases eq_or_ne (g x) 0 with hgx | hgx
    · simp [hgx]
    · rw [hx (by simpa using hgx)]

/-- **Composition of scalar densities.** Taking density `h` with respect to `g · μ` is taking
density `h * g` with respect to `μ`: `h · (g · μ) = (h * g) · μ`. When `h` is not integrable
against `g · μ`, both sides are `0`. -/
theorem withDensity_withDensity_mul (hg : μ.Integrable g) (h : X → 𝕜) :
    (μ.withDensity g (ContinuousLinearMap.mul ℝ 𝕜)).withDensity h
        (ContinuousLinearMap.mul ℝ 𝕜) =
      μ.withDensity (fun x => h x * g x) (ContinuousLinearMap.mul ℝ 𝕜) := by
  by_cases hh : (μ.withDensity g (ContinuousLinearMap.mul ℝ 𝕜)).Integrable h; swap
  · rw [withDensity_of_not_integrable hh,
      withDensity_of_not_integrable (mt (integrable_withDensity_mul_iff hg).2 hh)]
  ext s hs : 1
  rw [withDensity_apply hh, withDensity_apply ((integrable_withDensity_mul_iff hg).1 hh),
    restrict_withDensity hg, integral_withDensity_mul hg.restrict]

/-- A constant density `c` with respect to a scalar measure of finite variation multiplies the
measure by `c`. -/
@[simp]
theorem withDensity_const_mul [IsFiniteMeasure μ.variation] (c : 𝕜) :
    μ.withDensity (fun _ => c) (ContinuousLinearMap.mul ℝ 𝕜) = c • μ := by
  ext s hs : 1
  rw [withDensity_apply (integrable_const c), setIntegral_const, ContinuousLinearMap.mul_apply',
    smul_apply, smul_eq_mul]

end Scalar

end VectorMeasure

end MeasureTheory
