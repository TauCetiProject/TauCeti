/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
public import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# Scaling the measure on `Lᵖ` and comparing regular Haar measures

For a positive scalar `c : ℝ≥0`, the measures `c • μ` and `μ` have the same null sets and
`‖f‖_{Lᵖ(c • μ)} = c^(1/p) ‖f‖_{Lᵖ(μ)}` (`MeasureTheory.lpNorm_smul_measure_of_ne_zero`), with the
convention `1 / ∞ = 0`. Rescaling representatives by `c^(1/p)` therefore identifies
`Lp E p (c • μ)` linear-isometrically with `Lp E p μ` (`MeasureTheory.Lp.smulMeasureₗᵢ`). At
`p = 1`, the map multiplies functions by `c` and preserves Bochner integrals:
`∫ (smulMeasureₗᵢ f) ∂μ = ∫ f ∂(c • μ)`.

On a locally compact group `G`, any two regular left Haar measures `μ` and `ν` satisfy
`μ = haarScalarFactor μ ν • ν` (`MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular`),
without assuming second countability or σ-compactness of `G`. Composing `TauCeti.castLpₗᵢ` with
`MeasureTheory.Lp.smulMeasureₗᵢ` gives a canonical isometric identification
`MeasureTheory.Lp.haarMeasureCongrₗᵢ : Lp E p μ ≃ₗᵢ[𝕜] Lp E p ν` compatible with reflexivity,
symmetry, composition, pointwise `star`, and (at `p = 1`) Haar integration.

## Main definitions

* `MeasureTheory.Lp.smulMeasureₗᵢ`: the `𝕜`-linear isometric equivalence
  `Lp E p (c • μ) ≃ₗᵢ[𝕜] Lp E p μ` sending `f` to `c^(1/p) • f` for `c ≠ 0`.
* `MeasureTheory.Lp.haarMeasureCongrₗᵢ`: the canonical `𝕜`-linear isometric equivalence
  `Lp E p μ ≃ₗᵢ[𝕜] Lp E p ν` between `Lᵖ` spaces of regular left Haar measures `μ` and `ν`.

## Main results

* `MeasureTheory.memLp_smul_measure_nnreal_iff`: `MemLp f p (c • μ) ↔ MemLp f p μ` for `c ≠ 0`.
* `MeasureTheory.Lp.coeFn_smulMeasureₗᵢ`, `MeasureTheory.Lp.integral_smulMeasureₗᵢ`,
  `MeasureTheory.Lp.star_smulMeasureₗᵢ`: almost-everywhere formula, integral preservation at
  `p = 1`, and compatibility with pointwise `star`.
* `MeasureTheory.Lp.coeFn_haarMeasureCongrₗᵢ`, `MeasureTheory.Lp.haarMeasureCongrₗᵢ_trans`,
  `MeasureTheory.Lp.haarMeasureCongrₗᵢ_symm`, `MeasureTheory.Lp.integral_haarMeasureCongrₗᵢ`:
  functoriality and integral preservation when changing regular Haar normalization.
-/

public section

noncomputable section

open scoped ENNReal NNReal

namespace MeasureTheory

section SMulMeasure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- Scaling a measure by a nonzero `c : ℝ≥0` does not change `Lᵖ` membership. -/
theorem memLp_smul_measure_nnreal_iff {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {c : ℝ≥0} (hc : c ≠ 0) {f : α → ε} :
    MemLp f p (c • μ) ↔ MemLp f p μ :=
  ⟨fun hf ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using hf.smul_measure_nnreal (c := c⁻¹),
    fun hf ↦ hf.smul_measure_nnreal⟩

namespace Lp

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]

variable (μ p 𝕜) in
/-- Auxiliary `𝕜`-linear map rescaling `Lp E p (c • μ)` to `Lp E p μ` by `(c : ℝ) ^ p.toReal⁻¹`. -/
private def smulMeasureₗ {c : ℝ≥0} (hc : c ≠ 0) : Lp E p (c • μ) →ₗ[𝕜] Lp E p μ where
  toFun f := (c : ℝ) ^ p.toReal⁻¹ • ((memLp_smul_measure_nnreal_iff hc).1 (Lp.memLp f)).toLp f
  map_add' f g := by
    have hf := (memLp_smul_measure_nnreal_iff hc).1 (Lp.memLp f)
    have hg := (memLp_smul_measure_nnreal_iff hc).1 (Lp.memLp g)
    have hfg := (memLp_smul_measure_nnreal_iff hc).1 (Lp.memLp (f + g))
    rw [← smul_add]
    congr 1
    refine Lp.ext ?_
    filter_upwards [hfg.coeFn_toLp, Lp.coeFn_add (hf.toLp f) (hg.toLp g), hf.coeFn_toLp,
      hg.coeFn_toLp, (Measure.ae_smul_measure_iff hc).1 (Lp.coeFn_add f g)]
      with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₅, h₂, Pi.add_apply, Pi.add_apply, h₃, h₄]
  map_smul' k f := by
    have hf := (memLp_smul_measure_nnreal_iff hc).1 (Lp.memLp f)
    have hkf := (memLp_smul_measure_nnreal_iff hc).1 (Lp.memLp (k • f))
    rw [RingHom.id_apply]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_smul ((c : ℝ) ^ p.toReal⁻¹) (hkf.toLp (k • f)), hkf.coeFn_toLp,
      (Measure.ae_smul_measure_iff hc).1 (Lp.coeFn_smul k f),
      Lp.coeFn_smul k ((c : ℝ) ^ p.toReal⁻¹ • hf.toLp f),
      Lp.coeFn_smul ((c : ℝ) ^ p.toReal⁻¹) (hf.toLp f), hf.coeFn_toLp]
      with x h₁ h₂ h₃ h₄ h₅ h₆
    rw [h₁, Pi.smul_apply, h₂, h₃, Pi.smul_apply, h₄, Pi.smul_apply, h₅, Pi.smul_apply, h₆,
      smul_comm]

private theorem coeFn_smulMeasureₗ {c : ℝ≥0} (hc : c ≠ 0) (f : Lp E p (c • μ)) :
    smulMeasureₗ μ p 𝕜 hc f =ᵐ[μ] fun x ↦ (c : ℝ) ^ p.toReal⁻¹ • f x := by
  have hf := (memLp_smul_measure_nnreal_iff hc).1 (Lp.memLp f)
  filter_upwards [Lp.coeFn_smul ((c : ℝ) ^ p.toReal⁻¹) (hf.toLp f), hf.coeFn_toLp] with x h₁ h₂
  rw [smulMeasureₗ, LinearMap.coe_mk, AddHom.coe_mk, h₁, Pi.smul_apply, h₂]

variable [Fact (1 ≤ p)]

variable (μ p 𝕜) in
/-- **Measure-scaling linear isometry on `Lᵖ`.** For `c : ℝ≥0` with `c ≠ 0`, multiplying
representatives by `(c : ℝ) ^ p.toReal⁻¹` (with `1 / ∞ = 0`) is a `𝕜`-linear isometric equivalence
`Lp E p (c • μ) ≃ₗᵢ[𝕜] Lp E p μ`. -/
def smulMeasureₗᵢ {c : ℝ≥0} (hc : c ≠ 0) : Lp E p (c • μ) ≃ₗᵢ[𝕜] Lp E p μ where
  toLinearEquiv :=
    { smulMeasureₗ μ p 𝕜 hc with
      invFun g :=
        (c : ℝ)⁻¹ ^ p.toReal⁻¹ • ((Lp.memLp g).smul_measure_nnreal (c := c)).toLp g
      left_inv f := by
        simp only [LinearMap.toFun_eq_coe]
        set hg := (Lp.memLp (smulMeasureₗ μ p 𝕜 hc f)).smul_measure_nnreal (c := c)
        refine Lp.ext <| (Measure.ae_smul_measure_iff hc).2 ?_
        filter_upwards [(Measure.ae_smul_measure_iff hc).1
            (Lp.coeFn_smul ((c : ℝ)⁻¹ ^ p.toReal⁻¹) (hg.toLp _)),
          (Measure.ae_smul_measure_iff hc).1 hg.coeFn_toLp,
          coeFn_smulMeasureₗ (𝕜 := 𝕜) hc f] with x h₁ h₂ h₃
        rw [h₁, Pi.smul_apply, h₂, h₃, smul_smul, ← Real.mul_rpow (by positivity) (by positivity),
          inv_mul_cancel₀ (NNReal.coe_ne_zero.2 hc), Real.one_rpow, one_smul]
      right_inv g := by
        simp only [LinearMap.toFun_eq_coe]
        set h : Lp E p (c • μ) :=
          (c : ℝ)⁻¹ ^ p.toReal⁻¹ • ((Lp.memLp g).smul_measure_nnreal (c := c)).toLp g
        refine Lp.ext ?_
        filter_upwards [coeFn_smulMeasureₗ (𝕜 := 𝕜) hc h,
          (Measure.ae_smul_measure_iff hc).1
            (Lp.coeFn_smul ((c : ℝ)⁻¹ ^ p.toReal⁻¹)
              (((Lp.memLp g).smul_measure_nnreal (c := c)).toLp g)),
          (Measure.ae_smul_measure_iff hc).1
            ((Lp.memLp g).smul_measure_nnreal (c := c)).coeFn_toLp] with x h₁ h₂ h₃
        rw [h₁, h₂, Pi.smul_apply, h₃, smul_smul, ← Real.mul_rpow (by positivity) (by positivity),
          mul_inv_cancel₀ (NNReal.coe_ne_zero.2 hc), Real.one_rpow, one_smul] }
  norm_map' f := by
    simp only [LinearEquiv.coe_mk, smulMeasureₗ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [norm_smul, Real.norm_of_nonneg (by positivity), Lp.norm_toLp, Lp.norm_def]
    set g : α → E := ⇑f
    rw [eLpNorm_smul_measure_of_ne_zero' hc g p μ, ENNReal.smul_def, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_rpow]

/-- Almost-everywhere formula for `Lp.smulMeasureₗᵢ`. -/
theorem coeFn_smulMeasureₗᵢ {c : ℝ≥0} (hc : c ≠ 0) (f : Lp E p (c • μ)) :
    smulMeasureₗᵢ μ p 𝕜 hc f =ᵐ[μ] fun x ↦ (c : ℝ) ^ p.toReal⁻¹ • f x :=
  coeFn_smulMeasureₗ hc f

/-- Almost-everywhere formula for `(Lp.smulMeasureₗᵢ).symm`. -/
theorem coeFn_smulMeasureₗᵢ_symm {c : ℝ≥0} (hc : c ≠ 0) (g : Lp E p μ) :
    (smulMeasureₗᵢ μ p 𝕜 hc).symm g =ᵐ[c • μ] fun x ↦ (c⁻¹ : ℝ) ^ p.toReal⁻¹ • g x := by
  filter_upwards [Lp.coeFn_smul ((c : ℝ)⁻¹ ^ p.toReal⁻¹)
      (((Lp.memLp g).smul_measure_nnreal (c := c)).toLp g),
    ((Lp.memLp g).smul_measure_nnreal (c := c)).coeFn_toLp] with x h₁ h₂
  exact h₁.trans (by rw [Pi.smul_apply, h₂])

/-- At `p = 1`, `Lp.smulMeasureₗᵢ` multiplies representatives by `(c : ℝ)`. -/
theorem coeFn_smulMeasureₗᵢ_one {c : ℝ≥0} (hc : c ≠ 0) (f : Lp E 1 (c • μ)) :
    smulMeasureₗᵢ μ 1 𝕜 hc f =ᵐ[μ] fun x ↦ (c : ℝ) • f x := by
  simpa using coeFn_smulMeasureₗᵢ (p := 1) (𝕜 := 𝕜) hc f

/-- At `p = 1`, `Lp.smulMeasureₗᵢ` preserves Bochner integrals:
`∫ (smulMeasureₗᵢ f) ∂μ = ∫ f ∂(c • μ)`. -/
@[simp]
theorem integral_smulMeasureₗᵢ {c : ℝ≥0} (hc : c ≠ 0) (f : Lp E 1 (c • μ)) :
    ∫ x, smulMeasureₗᵢ μ 1 𝕜 hc f x ∂μ = ∫ x, f x ∂(c • μ) := by
  rw [integral_congr_ae (coeFn_smulMeasureₗᵢ_one (𝕜 := 𝕜) hc f), integral_smul,
    integral_smul_nnreal_measure, NNReal.smul_def]

/-- `Lp.smulMeasureₗᵢ` commutes with pointwise `star`. -/
theorem star_smulMeasureₗᵢ [StarAddMonoid E] [NormedStarGroup E] [StarModule ℝ E]
    {c : ℝ≥0} (hc : c ≠ 0) (f : Lp E p (c • μ)) :
    star (smulMeasureₗᵢ μ p 𝕜 hc f) = smulMeasureₗᵢ μ p 𝕜 hc (star f) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (smulMeasureₗᵢ μ p 𝕜 hc f), coeFn_smulMeasureₗᵢ (𝕜 := 𝕜) hc f,
    coeFn_smulMeasureₗᵢ (𝕜 := 𝕜) hc (star f),
    (Measure.ae_smul_measure_iff hc).1 (Lp.coeFn_star f)] with x h₁ h₂ h₃ h₄
  rw [h₁, Pi.star_apply, h₂, star_smul, star_trivial, h₃, h₄, Pi.star_apply]

end Lp

end SMulMeasure

/-! ### Comparing regular left Haar measures on `Lᵖ` -/

namespace Lp

section HaarMeasure

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ ν : Measure G} [μ.IsHaarMeasure] [μ.Regular] [ν.IsHaarMeasure] [ν.Regular]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]

variable (μ ν p 𝕜) in
/-- **Canonical `Lᵖ` isometric equivalence between regular left Haar normalizations**, rescaling
representatives by `(haarScalarFactor μ ν : ℝ) ^ p.toReal⁻¹`. -/
def haarMeasureCongrₗᵢ : Lp E p μ ≃ₗᵢ[𝕜] Lp E p ν :=
  (TauCeti.castLpₗᵢ (Measure.isMulLeftInvariant_eq_smul_of_regular μ ν)).trans
    (smulMeasureₗᵢ ν p 𝕜 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne')

/-- Explicit decomposition of `Lp.haarMeasureCongrₗᵢ` into `TauCeti.castLpₗᵢ` followed by
`Lp.smulMeasureₗᵢ`. -/
theorem haarMeasureCongrₗᵢ_def :
    haarMeasureCongrₗᵢ (E := E) μ ν p 𝕜 =
      (TauCeti.castLpₗᵢ (Measure.isMulLeftInvariant_eq_smul_of_regular μ ν)).trans
        (smulMeasureₗᵢ ν p 𝕜 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne') :=
  (rfl)

/-- Almost-everywhere formula for `Lp.haarMeasureCongrₗᵢ`: it rescales representatives by
`(haarScalarFactor μ ν : ℝ) ^ p.toReal⁻¹`. -/
theorem coeFn_haarMeasureCongrₗᵢ (f : Lp E p μ) :
    haarMeasureCongrₗᵢ μ ν p 𝕜 f =ᵐ[ν]
      fun x ↦ (Measure.haarScalarFactor μ ν : ℝ) ^ p.toReal⁻¹ • f x := by
  have hc := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  have heq := Measure.isMulLeftInvariant_eq_smul_of_regular μ ν
  filter_upwards [coeFn_smulMeasureₗᵢ (p := p) (𝕜 := 𝕜) hc (TauCeti.castLpₗᵢ (𝕜 := 𝕜) heq f)]
    with x hx
  rw [haarMeasureCongrₗᵢ, LinearIsometryEquiv.trans_apply, hx, TauCeti.coeFn_castLpₗᵢ]

/-- At `p = 1`, `Lp.haarMeasureCongrₗᵢ` multiplies representatives by `haarScalarFactor μ ν`. -/
theorem coeFn_haarMeasureCongrₗᵢ_one (f : Lp E 1 μ) :
    haarMeasureCongrₗᵢ μ ν 1 𝕜 f =ᵐ[ν] fun x ↦ (Measure.haarScalarFactor μ ν : ℝ) • f x := by
  simpa using coeFn_haarMeasureCongrₗᵢ (μ := μ) (ν := ν) (p := 1) (𝕜 := 𝕜) f

/-- Comparing a regular left Haar measure with itself is the identity on `Lᵖ`. -/
@[simp]
theorem haarMeasureCongrₗᵢ_refl :
    haarMeasureCongrₗᵢ μ μ p 𝕜 = LinearIsometryEquiv.refl 𝕜 (Lp E p μ) := by
  ext f : 1
  refine Lp.ext ?_
  filter_upwards [coeFn_haarMeasureCongrₗᵢ (μ := μ) (ν := μ) (p := p) (𝕜 := 𝕜) f] with x hx
  simp [hx]

/-- `Lp.haarMeasureCongrₗᵢ` composes functorially across three regular Haar measures. -/
theorem haarMeasureCongrₗᵢ_trans (ρ : Measure G) [ρ.IsHaarMeasure] [ρ.Regular] :
    (haarMeasureCongrₗᵢ μ ν p 𝕜).trans (haarMeasureCongrₗᵢ ν ρ p 𝕜) =
      haarMeasureCongrₗᵢ (E := E) μ ρ p 𝕜 := by
  have hρν : ρ ≪ ν := by
    rw [Measure.isMulLeftInvariant_eq_smul_of_regular ρ ν]
    exact Measure.smul_absolutelyContinuous
  ext f : 1
  refine Lp.ext ?_
  filter_upwards [coeFn_haarMeasureCongrₗᵢ (μ := ν) (ν := ρ) (p := p) (𝕜 := 𝕜)
      (haarMeasureCongrₗᵢ μ ν p 𝕜 f),
    hρν.ae_eq (coeFn_haarMeasureCongrₗᵢ (μ := μ) (ν := ν) (p := p) (𝕜 := 𝕜) f),
    coeFn_haarMeasureCongrₗᵢ (μ := μ) (ν := ρ) (p := p) (𝕜 := 𝕜) f] with x h₁ h₂ h₃
  rw [LinearIsometryEquiv.trans_apply, h₁, h₂, h₃, smul_smul,
    ← Real.mul_rpow (by positivity) (by positivity), mul_comm, ← NNReal.coe_mul,
    ← Measure.haarScalarFactor_eq_mul μ ν ρ]

/-- The inverse of `Lp.haarMeasureCongrₗᵢ μ ν` is `Lp.haarMeasureCongrₗᵢ ν μ`. -/
@[simp]
theorem haarMeasureCongrₗᵢ_symm :
    (haarMeasureCongrₗᵢ μ ν p 𝕜).symm = haarMeasureCongrₗᵢ (E := E) ν μ p 𝕜 := by
  ext f : 1
  rw [LinearIsometryEquiv.symm_apply_eq, ← LinearIsometryEquiv.trans_apply,
    haarMeasureCongrₗᵢ_trans, haarMeasureCongrₗᵢ_refl]
  rfl

/-- At `p = 1`, `Lp.haarMeasureCongrₗᵢ` preserves Haar integrals:
`∫ (haarMeasureCongrₗᵢ μ ν f) ∂ν = ∫ f ∂μ`. -/
@[simp]
theorem integral_haarMeasureCongrₗᵢ (f : Lp E 1 μ) :
    ∫ x, haarMeasureCongrₗᵢ μ ν 1 𝕜 f x ∂ν = ∫ x, f x ∂μ := by
  rw [haarMeasureCongrₗᵢ, LinearIsometryEquiv.trans_apply, integral_smulMeasureₗᵢ]
  have heq := Measure.isMulLeftInvariant_eq_smul_of_regular μ ν
  have hcast (x : G) : TauCeti.castLpₗᵢ (𝕜 := 𝕜) heq f x = f x :=
    TauCeti.coeFn_castLpₗᵢ heq f x
  simp_rw [hcast]
  rw [← heq]

/-- `Lp.haarMeasureCongrₗᵢ` commutes with pointwise `star`. -/
theorem star_haarMeasureCongrₗᵢ [StarAddMonoid E] [NormedStarGroup E] [StarModule ℝ E]
    (f : Lp E p μ) :
    star (haarMeasureCongrₗᵢ μ ν p 𝕜 f) = haarMeasureCongrₗᵢ μ ν p 𝕜 (star f) := by
  have hνμ : ν ≪ μ := by
    rw [Measure.isMulLeftInvariant_eq_smul_of_regular ν μ]
    exact Measure.smul_absolutelyContinuous
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (haarMeasureCongrₗᵢ μ ν p 𝕜 f),
    coeFn_haarMeasureCongrₗᵢ (μ := μ) (ν := ν) (p := p) (𝕜 := 𝕜) f,
    coeFn_haarMeasureCongrₗᵢ (μ := μ) (ν := ν) (p := p) (𝕜 := 𝕜) (star f),
    hνμ.ae_eq (Lp.coeFn_star f)] with x h₁ h₂ h₃ h₄
  rw [h₁, Pi.star_apply, h₂, star_smul, star_trivial, h₃, h₄, Pi.star_apply]

end HaarMeasure

end Lp

end MeasureTheory
