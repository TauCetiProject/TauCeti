/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.MeasureTheory.Measure.Decomposition.RNDeriv
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The weight ↔ measure isometry `L²(w·μ) ≃ₗᵢ L²(μ)`

For an almost-everywhere-positive real weight `w` on an arbitrary measurable space, multiplication
by `√w` is a linear isometric equivalence from the weighted `L²` space `L²(w·μ; E)` onto
`L²(μ; E)`, where `w·μ := μ.withDensity (ENNReal.ofReal ∘ w)` and `E` is any real normed space. It
is an *equivalence* precisely because `w > 0` almost everywhere: the inverse is multiplication by
`(√w)⁻¹`.

This is the single map converting a weight-in-the-measure normalization to a weight-in-the-function
normalization. Combined with `HilbertBasis.mapₗᵢ` (transport of a Hilbert basis across a `≃ₗᵢ`), it
moves an orthogonal-polynomial basis of a weighted measure to the `√w`-envelope basis of the
reference measure and back.

The construction is purely measure-theoretic, so it is stated over an arbitrary `MeasurableSpace`.
We also record the corresponding `L²` seminorm and membership identities for a square-root
Radon–Nikodym derivative `√(dμ/dν)` when `μ ≪ ν`, `μ` is σ-finite, and `μ` admits a Lebesgue
decomposition against `ν`.

## Main definitions

* `TauCeti.weightL2Isometry` — the isometric equivalence `L²(w·μ; E) ≃ₗᵢ[𝕜] L²(μ; E)`.

## Main statements

* `TauCeti.eLpNorm_sqrt_smul_eq_eLpNorm_withDensity` — the underlying seminorm identity: the
  `L²(μ)` seminorm of `√w · g` equals the `L²(w·μ)` seminorm of `g`.
* `TauCeti.coeFn_weightL2Isometry` — the forward map is multiplication by `√w`.
* `TauCeti.coeFn_weightL2Isometry_symm` — the inverse map is multiplication by `(√w)⁻¹`.
* `MeasureTheory.Measure.eLpNorm_sqrt_toReal_rnDeriv_smul`,
  `MeasureTheory.Measure.eLpNorm_mul_sqrt_toReal_rnDeriv`,
  `MeasureTheory.Measure.memLp_sqrt_toReal_rnDeriv_smul_iff`, and
  `MeasureTheory.Measure.memLp_mul_sqrt_toReal_rnDeriv_iff` — under those measure hypotheses,
  scaling a (not necessarily measurable) function by `√(dμ/dν)` preserves the `L²` seminorm and
  `L²` membership between `μ` and `ν`.
* `MeasureTheory.Measure.eLpNorm_sqrt_toReal_rnDeriv` and
  `MeasureTheory.Measure.eLpNorm_sqrt_toReal_rnDeriv_eq_one` — `√(dμ/dν)` has `L²(ν)` seminorm
  `(μ univ)^(1/2)` (and `1` for probability measures).
-/

public section

open MeasureTheory

namespace TauCeti

open scoped ENNReal NNReal

variable (𝕜 : Type*) {E α : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E] [MeasurableSpace α]
  (μ : Measure α) (w : α → ℝ)

/-- **Core seminorm identity.** The `L²(μ)` seminorm of `√w · g` equals the `L²(w·μ)` seminorm of
`g`, where `w·μ = μ.withDensity (ENNReal.ofReal ∘ w)`. Beyond a.e. measurability of the data, no
condition on `w` is needed: where `w` is negative, both `√w` and `ENNReal.ofReal w` vanish. -/
theorem eLpNorm_sqrt_smul_eq_eLpNorm_withDensity (hwm : AEMeasurable w μ) {g : α → E}
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => √(w x) • g x) 2 μ
      = eLpNorm g 2 (μ.withDensity fun x => ENNReal.ofReal (w x)) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (f := fun x => √(w x) • g x) (hwm.sqrt.aestronglyMeasurable.smul hg),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (hg.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ μ hwm.ennreal_ofReal
      (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine congrArg (· ^ _) (lintegral_congr fun x => ?_)
  rcases le_or_gt 0 (w x) with hx | hx
  · simp [eNorm_smul, Real.eNorm_of_nonneg, mul_pow, ← ENNReal.ofReal_pow, hx]
  · simp [Real.sqrt_eq_zero'.2 hx.le, ENNReal.ofReal_of_nonpos hx.le]

/-- The forward direction `√w · f` of a class in `L²(w·μ)` is in `L²(μ)`. -/
private theorem memLp_sqrt_smul (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ)
    (f : Lp E 2 (μ.withDensity fun x => ENNReal.ofReal (w x))) :
    MemLp (fun x => √(w x) • (f : α → E) x) 2 μ := by
  rw [memLp_iff, eLpNorm_sqrt_smul_eq_eLpNorm_withDensity μ w hwm
    ((Lp.aestronglyMeasurable f).mono_ac (absolutelyContinuous_withDensity_ofReal hwm hwpos))]
  exact Lp.eLpNorm_lt_top f

/-- The inverse direction `(√w)⁻¹ · g` of a class in `L²(μ)` is in `L²(w·μ)`. -/
private theorem memLp_inv_sqrt_smul (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ)
    (g : Lp E 2 μ) :
    MemLp (fun x => (√(w x))⁻¹ • (g : α → E) x) 2
      (μ.withDensity fun x => ENNReal.ofReal (w x)) := by
  rw [memLp_iff, ← eLpNorm_sqrt_smul_eq_eLpNorm_withDensity μ w hwm
    (g := fun x => (√(w x))⁻¹ • (g : α → E) x)
    (hwm.sqrt.inv.aestronglyMeasurable.smul (Lp.aestronglyMeasurable g))]
  refine (eLpNorm_congr_ae ?_).trans_lt (Lp.eLpNorm_lt_top g)
  filter_upwards [hwpos] with x hx
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hx).ne', one_smul]

/-- **The weight ↔ measure isometry.** For an almost-everywhere-positive weight `w`, multiplication
by `√w` is a linear isometric equivalence `L²(w·μ; E) ≃ₗᵢ[𝕜] L²(μ; E)`. -/
noncomputable def weightL2Isometry (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) :
    Lp E 2 (μ.withDensity fun x => ENNReal.ofReal (w x)) ≃ₗᵢ[𝕜] Lp E 2 μ where
  toFun f := (memLp_sqrt_smul μ w hwpos hwm f).toLp _
  invFun g := (memLp_inv_sqrt_smul μ w hwpos hwm g).toLp _
  map_add' f₁ f₂ := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [(Lp.coeFn_add f₁ f₂).filter_mono
      (absolutelyContinuous_withDensity_ofReal hwm hwpos).ae_le] with x hx
    simp only [Pi.add_apply, hx, smul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [(Lp.coeFn_smul c f).filter_mono
      (absolutelyContinuous_withDensity_ofReal hwm hwpos).ae_le] with x hx
    rw [Pi.smul_apply, hx, Pi.smul_apply, smul_comm]
  left_inv f := by
    have hac := withDensity_absolutelyContinuous μ fun x => ENNReal.ofReal (w x)
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp
        (memLp_inv_sqrt_smul μ w hwpos hwm ((memLp_sqrt_smul μ w hwpos hwm f).toLp _)),
      (MemLp.coeFn_toLp (memLp_sqrt_smul μ w hwpos hwm f)).filter_mono hac.ae_le,
      hwpos.filter_mono hac.ae_le] with x h1 h2 hx
    rw [h1, h2, smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 hx).ne', one_smul]
  right_inv g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp
        (memLp_sqrt_smul μ w hwpos hwm ((memLp_inv_sqrt_smul μ w hwpos hwm g).toLp _)),
      (MemLp.coeFn_toLp (memLp_inv_sqrt_smul μ w hwpos hwm g)).filter_mono
        (absolutelyContinuous_withDensity_ofReal hwm hwpos).ae_le,
      hwpos] with x h1 h2 hx
    rw [h1, h2, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hx).ne', one_smul]
  -- The forward map is `MemLp.toLp (√w • f)` by construction, so `Lp.norm_toLp` applies to it.
  norm_map' f := (Lp.norm_toLp _ (memLp_sqrt_smul μ w hwpos hwm f)).trans <| by
    rw [Lp.norm_def, eLpNorm_sqrt_smul_eq_eLpNorm_withDensity μ w hwm
      ((Lp.aestronglyMeasurable f).mono_ac (absolutelyContinuous_withDensity_ofReal hwm hwpos))]

/-- The forward isometry is multiplication by `√w`. -/
theorem coeFn_weightL2Isometry (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ)
    (f : Lp E 2 (μ.withDensity fun x => ENNReal.ofReal (w x))) :
    weightL2Isometry 𝕜 μ w hwpos hwm f =ᵐ[μ] fun x => √(w x) • (f : α → E) x :=
  MemLp.coeFn_toLp (memLp_sqrt_smul μ w hwpos hwm f)

/-- The inverse isometry is multiplication by `(√w)⁻¹`. -/
theorem coeFn_weightL2Isometry_symm (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ)
    (g : Lp E 2 μ) :
    (weightL2Isometry 𝕜 μ w hwpos hwm).symm g =ᵐ[μ] fun x => (√(w x))⁻¹ • (g : α → E) x :=
  (MemLp.coeFn_toLp (memLp_inv_sqrt_smul μ w hwpos hwm g)).filter_mono
    (absolutelyContinuous_withDensity_ofReal hwm hwpos).ae_le

end TauCeti

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- For `μ ≪ ν` with `μ` σ-finite and admitting a Lebesgue decomposition with respect to `ν`, and
any function `f : α → E` into a real normed space (not assumed measurable), scaling `f` by
`√(dμ/dν)` preserves the `L²` seminorm: `‖√(dμ/dν) • f‖_{L²(ν)} = ‖f‖_{L²(μ)}`. -/
theorem eLpNorm_sqrt_toReal_rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν] [SigmaFinite μ] (hμν : μ ≪ ν) (f : α → E) :
    eLpNorm (fun x ↦ √((μ.rnDeriv ν x).toReal) • f x) 2 ν = eLpNorm f 2 μ := by
  set r : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hr_meas : Measurable r := (measurable_rnDeriv μ ν).ennreal_toReal
  have hwd : ν.withDensity (fun x ↦ ENNReal.ofReal (r x)) = μ := by
    refine (withDensity_congr_ae ?_).trans (withDensity_rnDeriv_eq μ ν hμν)
    filter_upwards [μ.rnDeriv_lt_top ν] with x hlt
    exact ENNReal.ofReal_toReal hlt.ne
  by_cases hf : AEStronglyMeasurable f μ
  · set f₀ := hf.mk f
    have hae_ν : (fun x ↦ √(r x) • f x) =ᵐ[ν] fun x ↦ √(r x) • f₀ x := by
      have h1 : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ 0 → f x = f₀ x :=
        (ae_withDensity_iff (measurable_rnDeriv μ ν)).mp
          (hf.ae_eq_mk.filter_mono (ae_mono (withDensity_rnDeriv_le μ ν)))
      filter_upwards [h1] with x hx
      by_cases h0 : μ.rnDeriv ν x = 0 <;> simp [r, h0, hx]
    rw [eLpNorm_congr_ae hae_ν, eLpNorm_congr_ae hf.ae_eq_mk,
      TauCeti.eLpNorm_sqrt_smul_eq_eLpNorm_withDensity ν r hr_meas.aemeasurable
        hf.stronglyMeasurable_mk.aestronglyMeasurable, hwd]
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    refine eLpNorm_of_not_aestronglyMeasurable fun hν ↦ hf ?_
    refine (hr_meas.sqrt.inv.stronglyMeasurable.smul
        hν.stronglyMeasurable_mk).aestronglyMeasurable.congr ?_
    filter_upwards [hμν hν.ae_eq_mk, ae_sqrt_toReal_rnDeriv_pos hμν] with x hx hpos
    dsimp [r]
    rw [← hx, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

/-- Scalar form of `MeasureTheory.Measure.eLpNorm_sqrt_toReal_rnDeriv_smul`: for `μ ≪ ν` with `μ`
σ-finite and admitting a Lebesgue decomposition with respect to `ν`, and any `f : α → ℝ` (not
assumed measurable), `‖f · √(dμ/dν)‖_{L²(ν)} = ‖f‖_{L²(μ)}`. -/
theorem eLpNorm_mul_sqrt_toReal_rnDeriv {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν]
    [SigmaFinite μ] (hμν : μ ≪ ν) (f : α → ℝ) :
    eLpNorm (fun x ↦ f x * √((μ.rnDeriv ν x).toReal)) 2 ν = eLpNorm f 2 μ := by
  simpa [smul_eq_mul, mul_comm] using eLpNorm_sqrt_toReal_rnDeriv_smul hμν f

/-- For `μ ≪ ν` with `μ` σ-finite and admitting a Lebesgue decomposition with respect to `ν`,
scaling by `√(dμ/dν)` preserves `L²` membership between `μ` and `ν`. -/
theorem memLp_sqrt_toReal_rnDeriv_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν] [SigmaFinite μ] (hμν : μ ≪ ν) {f : α → E} :
    MemLp (fun x ↦ √((μ.rnDeriv ν x).toReal) • f x) 2 ν ↔ MemLp f 2 μ := by
  simp only [memLp_iff, eLpNorm_sqrt_toReal_rnDeriv_smul hμν f]

/-- Scalar form of `MeasureTheory.Measure.memLp_sqrt_toReal_rnDeriv_smul_iff`: for `μ ≪ ν` with `μ`
σ-finite and admitting a Lebesgue decomposition with respect to `ν`, multiplying by `√(dμ/dν)`
preserves `L²` membership between `μ` and `ν`. -/
theorem memLp_mul_sqrt_toReal_rnDeriv_iff {μ ν : Measure α} [μ.HaveLebesgueDecomposition ν]
    [SigmaFinite μ] (hμν : μ ≪ ν) {f : α → ℝ} :
    MemLp (fun x ↦ f x * √((μ.rnDeriv ν x).toReal)) 2 ν ↔ MemLp f 2 μ := by
  simp only [memLp_iff, eLpNorm_mul_sqrt_toReal_rnDeriv hμν f]

/-- For `μ ≪ ν` with `μ` σ-finite and admitting a Lebesgue decomposition with respect to `ν`, the
`L²(ν)` seminorm of `√(dμ/dν)` is `(μ univ) ^ (1 / 2)`. -/
theorem eLpNorm_sqrt_toReal_rnDeriv (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
    [SigmaFinite μ] (hμν : μ ≪ ν) :
    eLpNorm (fun x ↦ √((μ.rnDeriv ν x).toReal)) 2 ν = μ Set.univ ^ (2 : ℝ)⁻¹ := by
  simpa [eLpNorm_const' (1 : ℝ) two_ne_zero ENNReal.ofNat_ne_top] using
    eLpNorm_mul_sqrt_toReal_rnDeriv hμν (fun _ ↦ 1)

/-- For a probability measure `μ ≪ ν` admitting a Lebesgue decomposition with respect to `ν`, the
`L²(ν)` seminorm of `√(dμ/dν)` is `1`. -/
theorem eLpNorm_sqrt_toReal_rnDeriv_eq_one (μ ν : Measure α) [IsProbabilityMeasure μ]
    [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    eLpNorm (fun x ↦ √((μ.rnDeriv ν x).toReal)) 2 ν = 1 := by
  simp [eLpNorm_sqrt_toReal_rnDeriv μ ν hμν]

end MeasureTheory.Measure
