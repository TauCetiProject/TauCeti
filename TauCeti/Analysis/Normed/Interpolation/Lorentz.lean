/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.L1Linfty
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
public import TauCeti.MeasureTheory.Integral.HardyInequality

/-!
# Real interpolation of `(L¹, L^∞)`: the Lorentz gauges

For an element `u` of `L¹ + L^∞` represented by `f`, the norm of `u` in the real interpolation
space `(L¹, L^∞)_{θ,q}` is, by the formula `K(t, u) = ∫₀ᵗ ‖f‖*` for the `K`-functional
(`TauCeti.CompatibleCouple.ofReal_kFunctional_lebesgue_one_top`),

`‖u‖_{θ,q} = ‖t ↦ t ^ (-θ) ∫₀ᵗ ‖f‖*‖_{L^q(dt / t)}`

(`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top`). With `1 / p = 1 - θ`, it is equivalent
to the **Lorentz gauge**

`‖f‖_{p,q} = ‖t ↦ t ^ (1 / p) ‖f‖* t‖_{L^q(dt / t)}`:

for `θ > 0` and `1 ≤ q ≤ ∞`,

`‖f‖_{p,q} ≤ ‖u‖_{θ,q} ≤ θ⁻¹ ‖f‖_{p,q}`

(`eLpNorm_rpow_mul_decreasingRearrangement_le_kMethodENorm_lebesgue_one_top`,
`kMethodENorm_lebesgue_one_top_le_ofReal_inv_mul_eLpNorm_rpow_mul_decreasingRearrangement`, both
in the namespace `TauCeti.CompatibleCouple`). The lower bound holds because `‖f‖*` is
nonincreasing, so `∫₀ᵗ ‖f‖* ≥ t ‖f‖* t`, and the upper bound is Hardy's inequality
`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_le`. So `(L¹, L^∞)_{θ,q}` is the Lorentz space
`L^{p,q}` with equivalent norms (`TauCeti.CompatibleCouple.mem_kMethod_lebesgue_one_top_iff`).

For `q = p` the Lorentz gauge is the `Lᵖ` seminorm, since the decreasing rearrangement has the same
`Lᵖ` seminorm as `f`. Hence for `1 < p ≤ ∞` and `θ = 1 - 1 / p`,

`‖f‖_p ≤ ‖u‖_{θ,p} ≤ (1 - 1 / p)⁻¹ ‖f‖_p`

(`TauCeti.CompatibleCouple.eLpNorm_le_kMethodENorm_lebesgue_one_top`,
`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_le_ofReal_inv_mul_eLpNorm`):
`(L¹, L^∞)_{1 - 1 / p, p} = Lᵖ` with equivalent norms. The identity behind this,
`‖t ↦ t ^ (1 / p) g* t‖_{L^p(dt / t)} = ‖g‖_p`, is
`MeasureTheory.Measure.eLpNorm_multHaar_ofReal_rpow_inv_mul_decreasingRearrangement`.

All statements are for the Lebesgue couple `TauCeti.CompatibleCouple.lebesgue` at the exponents
`1` and `∞`, whose real interpolation spaces are normed spaces.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.2 (Theorem 5.2.1) and §5.3.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- **The Lorentz gauge for `q = p` is the `Lᵖ` seminorm**:
`‖t ↦ t ^ (1 / p) g* t‖_{L^p(dt / t)} = ‖g‖_p`. -/
theorem eLpNorm_multHaar_ofReal_rpow_inv_mul_decreasingRearrangement {g : α → ℝ≥0∞}
    (hg : AEMeasurable g μ) (p : ℝ≥0∞) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement g t) p
      TauCeti.multHaar = eLpNorm g p μ := by
  rw [TauCeti.eLpNorm_multHaar_ofReal_rpow_inv_mul p
      (μ.measurable_decreasingRearrangement g).aemeasurable,
    μ.eLpNorm_decreasingRearrangement hg]

end MeasureTheory.Measure

namespace TauCeti.CompatibleCouple

variable {𝕜 E : Type*} {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E} {θ : ℝ} {q : ℝ≥0∞}

/-- **The real interpolation norm of `(L¹, L^∞)`.** For an element `v` of `L¹ + L^∞` represented
by `f`, `‖v‖_{θ,q} = ‖t ↦ t ^ (-θ) ∫₀ᵗ ‖f‖*‖_{L^q(dt / t)}`. -/
theorem kMethodENorm_lebesgue_one_top
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (θ : ℝ) (q : ℝ≥0∞) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v =
      eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) *
        ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s) q multHaar := by
  have hmono : Monotone fun t : ℝ ↦ ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s :=
    fun _ _ hst ↦ lintegral_mono_set (Ioc_subset_Ioc_right hst)
  have hmeas : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) *
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s :=
    (Measurable.ennreal_ofReal (by fun_prop)).mul hmono.measurable
  rw [kMethodENorm_def]
  refine eLpNorm_congr_eNorm_ae (aestronglyMeasurable_rpow_neg_mul_kFunctional θ v)
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_pos_multHaar] with t ht
  rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ofReal_kFunctional_lebesgue_one_top hv ht.le,
    eNorm_eq_self]

/-- **`(L¹, L^∞)_{θ,q}` is contained in the Lorentz space.** The Lorentz gauge
`‖t ↦ t ^ (1 - θ) ‖f‖* t‖_{L^q(dt / t)}` of `f` is at most the real interpolation norm
`‖v‖_{θ,q}` of the element `v` of `L¹ + L^∞` it represents. -/
theorem eLpNorm_rpow_mul_decreasingRearrangement_le_kMethodENorm_lebesgue_one_top
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (θ : ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) t) q
        multHaar ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [kMethodENorm_lebesgue_one_top hv]
  refine eLpNorm_mono_eNorm_ae ((Measurable.ennreal_ofReal (by fun_prop)).mul
    (μ.measurable_decreasingRearrangement _)).aestronglyMeasurable ?_
  filter_upwards [ae_pos_multHaar] with t ht
  simp only [eNorm_eq_self]
  -- `‖f‖*` is nonincreasing, so `t ‖f‖* t ≤ ∫₀ᵗ ‖f‖*`
  have hint : ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t ≤
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
    calc ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t
        = ∫⁻ _ in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) t := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
      _ ≤ ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s :=
          setLIntegral_mono' measurableSet_Ioc fun s hs ↦
            μ.antitone_decreasingRearrangement _ hs.2
  calc ENNReal.ofReal (t ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) t
      = ENNReal.ofReal (t ^ (-θ)) *
          (ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), sub_eq_neg_add,
          Real.rpow_add ht, Real.rpow_one]
    _ ≤ _ := by gcongr

/-- **The Lorentz space is contained in `(L¹, L^∞)_{θ,q}`.** For `θ > 0` and `1 ≤ q ≤ ∞`, the
real interpolation norm `‖v‖_{θ,q}` of an element `v` of `L¹ + L^∞` represented by `f` is at most
`θ⁻¹` times the Lorentz gauge `‖t ↦ t ^ (1 - θ) ‖f‖* t‖_{L^q(dt / t)}`. -/
theorem kMethodENorm_lebesgue_one_top_le_ofReal_inv_mul_eLpNorm_rpow_mul_decreasingRearrangement
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (hθ : 0 < θ) (hq : 1 ≤ q) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤ ENNReal.ofReal θ⁻¹ *
      eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) t) q
        multHaar := by
  rw [kMethodENorm_lebesgue_one_top hv]
  exact eLpNorm_rpow_neg_mul_setLIntegral_le hθ hq _

/-- **`(L¹, L^∞)_{θ,q}` is the Lorentz space `L^{p,q}`**, `1 / p = 1 - θ`. For `θ > 0` and
`1 ≤ q ≤ ∞`, an element `v` of `L¹ + L^∞` represented by `f` lies in `(L¹, L^∞)_{θ,q}` exactly
when its Lorentz gauge `‖t ↦ t ^ (1 - θ) ‖f‖* t‖_{L^q(dt / t)}` is finite. -/
theorem mem_kMethod_lebesgue_one_top_iff
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (hθ : 0 < θ) (hq : 1 ≤ q) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q ↔
      eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) t) q
        multHaar < ∞ := by
  rw [mem_kMethod_iff]
  refine ⟨(eLpNorm_rpow_mul_decreasingRearrangement_le_kMethodENorm_lebesgue_one_top hv θ
    q).trans_lt, fun h ↦ ?_⟩
  exact (kMethodENorm_lebesgue_one_top_le_ofReal_inv_mul_eLpNorm_rpow_mul_decreasingRearrangement hv
    hθ hq).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)

/-- **`(L¹, L^∞)_{1 - 1 / p, p}` embeds in `Lᵖ`.** For an element `v` of `L¹ + L^∞` represented
by `f`, `‖f‖_p ≤ ‖v‖_{1 - 1 / p, p}`. -/
theorem eLpNorm_le_kMethodENorm_lebesgue_one_top
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (p : ℝ≥0∞) :
    eLpNorm f p μ ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm (1 - p.toReal⁻¹) p v := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hv
  have h := eLpNorm_rpow_mul_decreasingRearrangement_le_kMethodENorm_lebesgue_one_top hv
    (1 - p.toReal⁻¹) p
  rwa [sub_sub_cancel, μ.eLpNorm_multHaar_ofReal_rpow_inv_mul_decreasingRearrangement hf.eNorm,
    eLpNorm_eNorm f hf] at h

/-- **`Lᵖ` embeds in `(L¹, L^∞)_{1 - 1 / p, p}`.** For `1 < p ≤ ∞` and an element `v` of
`L¹ + L^∞` represented by `f`, `‖v‖_{1 - 1 / p, p} ≤ (1 - 1 / p)⁻¹ ‖f‖_p`. -/
theorem kMethodENorm_lebesgue_one_top_le_ofReal_inv_mul_eLpNorm
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {p : ℝ≥0∞} (hp : 1 < p) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm (1 - p.toReal⁻¹) p v ≤
      ENNReal.ofReal (1 - p.toReal⁻¹)⁻¹ * eLpNorm f p μ := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hv
  have hθ : 0 < 1 - p.toReal⁻¹ := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp
    · exact sub_pos.2 (inv_lt_one_of_one_lt₀ (by
        simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp))
  have h :=
    kMethodENorm_lebesgue_one_top_le_ofReal_inv_mul_eLpNorm_rpow_mul_decreasingRearrangement hv
    hθ hp.le
  rwa [sub_sub_cancel, μ.eLpNorm_multHaar_ofReal_rpow_inv_mul_decreasingRearrangement hf.eNorm,
    eLpNorm_eNorm f hf] at h

end TauCeti.CompatibleCouple
