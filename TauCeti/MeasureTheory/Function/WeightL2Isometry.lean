/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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

## Main definitions

* `TauCeti.weightL2Isometry` — the isometric equivalence `L²(w·μ; E) ≃ₗᵢ[𝕜] L²(μ; E)`.

## Main statements

* `TauCeti.eLpNorm_sqrt_smul_eq_eLpNorm_withDensity` — the underlying seminorm identity: the
  `L²(μ)` seminorm of `√w · g` equals the `L²(w·μ)` seminorm of `g`.
* `TauCeti.coeFn_weightL2Isometry` — the forward map is multiplication by `√w`.
* `TauCeti.coeFn_weightL2Isometry_symm` — the inverse map is multiplication by `(√w)⁻¹`.
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
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (f := fun x => √(w x) • g x) (hwm.sqrt.aestronglyMeasurable.smul hg),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (hg.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ μ hwm.ennreal_ofReal
      (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine congrArg (· ^ _) (lintegral_congr fun x => ?_)
  rcases le_or_gt 0 (w x) with hx | hx
  · simp [enorm_smul, Real.enorm_of_nonneg, mul_pow, ← ENNReal.ofReal_pow, hx]
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
