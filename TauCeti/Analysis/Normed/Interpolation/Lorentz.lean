/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.L1Linfty
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
public import TauCeti.MeasureTheory.Function.Lorentz
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Integral.Hardy

/-!
# Real interpolation of `(L¹, L^∞)` and Lorentz classes

For `0 < θ < 1`, `1 / p = 1 - θ`, and `1 ≤ q ≤ ∞`, Peetre's `K`-method applied to the Lebesgue
couple `(L¹(μ; E), L^∞(μ; E))` (`TauCeti.CompatibleCouple.lebesgue`) coincides with the Lorentz
class `L^{p, q}(μ; E)` (`TauCeti.MemLorentz`), with equivalent norms:

* **Lower bound (constant `1`):** `t ‖f‖*(t) ≤ ∫₀ᵗ ‖f‖* ≤ K(t, v)`, giving `‖f‖_{p, q} ≤ ‖v‖_{θ, q}`
  for all `q ∈ [0, ∞]` over any normed field `𝕜`
  (`TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_lebesgue_one_top`).
* **Upper bounds:** when `E` is also a real normed space, `K(t, v) = ∫₀ᵗ ‖f‖*` and the prefix Hardy
  bound (`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`) gives `‖v‖_{θ, q} ≤ θ⁻¹ ‖f‖_{p, q}`
  (`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_le_eLorentzNorm`); without
  `NormedSpace ℝ E`, indicator truncation gives `‖v‖_{θ, q} ≤ 2 θ⁻¹ ‖f‖_{p, q}`
  (`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_le_two_mul_eLorentzNorm`).
* **Embedding into `L¹ + L^∞` and characterization:** every `f ∈ L^{p, q}` (`q ≠ 0`) has
  `∫₀ᵗ ‖f‖* < ∞` (`TauCeti.MemLorentz.lintegral_decreasingRearrangement_Ioc_lt_top`), hence
  represents an element of `L¹ + L^∞` (`TauCeti.MemLorentz.exists_l1AddLinfty`), and for `1 ≤ q ≤ ∞`
  `(L¹, L^∞)_{θ, q}` represents precisely `L^{p, q}`
  (`TauCeti.CompatibleCouple.exists_mem_kMethod_lebesgue_one_top_iff_memLorentz`).
* **Diagonal isomorphism and sharpness:** `(L¹, L^∞)_{θ, p} ≃L[𝕜] L^p(μ; E)`
  (`TauCeti.CompatibleCouple.lebesgueOneTopKMethodEquivLp`), and `t ↦ t ^ (θ - 1)` on `(0, ∞)`
  attains `‖v‖_{θ, ∞} = θ⁻¹ ‖f‖_{p, ∞}`
  (`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_rpow_sub_one`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.2–§5.3 (Theorems 5.2.1 and 5.3.1).
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., GTM 249, Springer, 2014, §1.4.
-/

public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

section Helpers

variable {θ : ℝ} {p : ℝ≥0∞}

private theorem exp_ne_zero_of_inv_eq (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) : p ≠ 0 := fun h ↦ by
  rw [h, ENNReal.inv_zero] at hp; exact ENNReal.ofReal_ne_top hp.symm

private theorem exp_ne_top_of_inv_eq (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    p ≠ ∞ := fun h ↦
  (ENNReal.ofReal_pos.2 (sub_pos.2 hθ.2)).ne (by simpa [h] using hp.symm)

private theorem toReal_inv_eq_one_sub (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    (p⁻¹).toReal = 1 - θ := by
  rw [hp, ENNReal.toReal_ofReal (sub_nonneg.2 hθ.2.le)]

private theorem mul_decreasingRearrangement_le_setLIntegral_Ioc {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (h : α → ℝ≥0∞) (t : ℝ) :
    ENNReal.ofReal t * μ.decreasingRearrangement h t ≤
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement h s := by
  calc ENNReal.ofReal t * μ.decreasingRearrangement h t
      = ∫⁻ _ in Ioc 0 t, μ.decreasingRearrangement h t := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
    _ ≤ ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement h s :=
        setLIntegral_mono (μ.measurable_decreasingRearrangement h) fun s hs ↦
          μ.antitone_decreasingRearrangement h hs.2

end Helpers

section EmbeddingIntoSum

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {θ : ℝ} {p q : ℝ≥0∞}

/-- Quantitative bound `∫₀ᵗ ‖f‖* ≤ ‖f‖_{p, ∞} * (t ^ θ / θ)` for `0 < θ < 1`, `1 / p = 1 - θ`, and
`t ≥ 0`. -/
theorem lintegral_decreasingRearrangement_Ioc_le_eLorentzNorm_top {ε : Type*} [TopologicalSpace ε]
    [ENorm ε] {f : α → ε} (hf : AEStronglyMeasurable f μ) (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s ≤
      eLorentzNorm f p ∞ μ * ENNReal.ofReal (t ^ θ / θ) := by
  obtain rfl | ht0 := ht.eq_or_lt
  · simp
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  calc ∫⁻ s in Ioo 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
      ≤ ∫⁻ s in Ioo 0 t, eLorentzNorm f p ∞ μ * ENNReal.ofReal (s ^ (θ - 1)) := by
        refine setLIntegral_mono_ae ((measurable_const.mul
          ((measurable_id.pow_const _).ennreal_ofReal)).aemeasurable)
          (Eventually.of_forall fun s hs ↦ ?_)
        have hle : ENNReal.ofReal (s ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) s ≤
            eLorentzNorm f p ∞ μ := by
          rw [eLorentzNorm_top_eq_iSup_Ioi hf (exp_ne_zero_of_inv_eq hp),
            toReal_inv_eq_one_sub hθ hp]
          exact le_iSup₂_of_le s hs.1 le_rfl
        have hmul : ENNReal.ofReal (s ^ (θ - 1)) * ENNReal.ofReal (s ^ (1 - θ)) = 1 := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _), ← Real.rpow_add hs.1,
            sub_add_sub_cancel, sub_self, Real.rpow_zero, ENNReal.ofReal_one]
        calc μ.decreasingRearrangement (‖f ·‖ₑ) s
            = ENNReal.ofReal (s ^ (θ - 1)) *
                (ENNReal.ofReal (s ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) s) := by
              rw [← mul_assoc, hmul, one_mul]
          _ ≤ eLorentzNorm f p ∞ μ * ENNReal.ofReal (s ^ (θ - 1)) := by
              rw [mul_comm (eLorentzNorm f p ∞ μ)]; exact mul_le_mul_right hle _
    _ = eLorentzNorm f p ∞ μ * ∫⁻ s in Ioo 0 t, ENNReal.ofReal (s ^ (θ - 1)) :=
        lintegral_const_mul _ ((measurable_id.pow_const _).ennreal_ofReal)
    _ = eLorentzNorm f p ∞ μ * ENNReal.ofReal (t ^ θ / θ) := by
        rw [lintegral_ofReal_rpow_Ioo (by linarith [hθ.1]) ht0.le, sub_add_cancel]

/-- Every function in `L^{p, q}` with `1 < p < ∞` (`1 / p = 1 - θ`, `0 < θ < 1`) and `q ≠ 0` has
finite rearrangement integral `∫₀ᵗ ‖f‖*` on bounded intervals. -/
theorem MemLorentz.lintegral_decreasingRearrangement_Ioc_lt_top {ε : Type*} [TopologicalSpace ε]
    [ENorm ε] {f : α → ε} (hf : MemLorentz f p q μ) (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : q ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s < ∞ :=
  (lintegral_decreasingRearrangement_Ioc_le_eLorentzNorm_top hf.aestronglyMeasurable hθ hp
    ht).trans_lt <| ENNReal.mul_lt_top
      (hf.mono_exponent (exp_ne_zero_of_inv_eq hp) (exp_ne_top_of_inv_eq hθ hp) hq
        le_top).eLorentzNorm_lt_top ENNReal.ofReal_lt_top

/-- Every function in `L^{p, q}(μ; E)` (`0 < θ < 1`, `1 / p = 1 - θ`, `q ≠ 0`) represents an element
of `L¹(μ; E) + L^∞(μ; E)`. No real normed space structure on `E` is needed. -/
theorem MemLorentz.exists_l1AddLinfty {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {f : α → E} (hf : MemLorentz f p q μ) (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : q ≠ 0) :
    ∃ u : L1AddLinfty 𝕜 E μ, ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f :=
  (L1AddLinfty.exists_toAEEqFun_ae_eq_iff_lintegral_decreasingRearrangement_lt_top one_pos).2
    ⟨hf.aestronglyMeasurable, hf.lintegral_decreasingRearrangement_Ioc_lt_top hθ hp hq zero_le_one⟩

end EmbeddingIntoSum

namespace CompatibleCouple

variable {𝕜 E α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {θ : ℝ} {p q : ℝ≥0∞}

/-! ### Compatibility between `l1Linfty` and `lebesgue 𝕜 E μ 1 ∞` -/

/-- The embedding of the sum space of `lebesgue 𝕜 E μ 1 ∞` into `L¹ + L^∞` preserves the `K`-method
norm. -/
theorem kMethodENorm_l1Linfty_sumSpaceEmbed (θ : ℝ) (q : ℝ≥0∞)
    (v : (lebesgue 𝕜 E μ 1 ∞).SumSpace) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v) =
      (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [kMethodENorm_def, kMethodENorm_def]
  exact eLpNorm_congr_ae (ae_pos_multHaar.mono fun t ht ↦ by
    dsimp only; rw [kFunctional_l1Linfty_sumSpaceEmbed ht.le])

theorem mem_kMethod_lebesgue_one_top_iff_l1Linfty {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q ↔
      (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v ∈ (l1Linfty 𝕜 E μ).kMethod θ q := by
  rw [mem_kMethod_iff, mem_kMethod_iff, kMethodENorm_l1Linfty_sumSpaceEmbed]

/-! ### Equivalence of the `K`-method norm and the Lorentz gauge -/

/-- **Lower bound (`‖f‖_{p, q} ≤ ‖u‖_{θ, q}`).** For `0 < θ < 1`, `1 / p = 1 - θ`, and any
`q ∈ [0, ∞]`, the Lorentz gauge is bounded by the `K`-method norm of `(L¹, L^∞)`. -/
theorem eLorentzNorm_le_kMethodENorm_l1Linfty (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    eLorentzNorm f p q μ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u := by
  rw [eLorentzNorm_eq_eLpNorm ((AEEqFun.aestronglyMeasurable _).congr hu)
    (exp_ne_zero_of_inv_eq hp), kMethodENorm_def]
  refine eLpNorm_mono_eNorm_ae
    (measurable_rpow_mul_decreasingRearrangement _ _ _).aestronglyMeasurable
    (ae_pos_multHaar.mono fun t ht ↦ ?_)
  simp only [eNorm_eq_self]
  calc ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t
      = ENNReal.ofReal (t ^ (-θ)) * (ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t) := by
        rw [toReal_inv_eq_one_sub hθ hp, show 1 - θ = -θ + 1 by ring, Real.rpow_add_one ht.ne',
          ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), mul_assoc]
    _ ≤ ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) :=
        mul_le_mul_right ((mul_decreasingRearrangement_le_setLIntegral_Ioc μ _ t).trans
          (lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu ht.le)) _
    _ = ‖t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u‖ₑ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
          Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))]

/-- **Lower bound (`‖f‖_{p, q} ≤ ‖v‖_{θ, q}`)** for the Lebesgue couple `(L¹, L^∞)`. -/
theorem eLorentzNorm_le_kMethodENorm_lebesgue_one_top (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    eLorentzNorm f p q μ ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v :=
  kMethodENorm_l1Linfty_sumSpaceEmbed θ q v ▸ eLorentzNorm_le_kMethodENorm_l1Linfty hθ hp hv

private theorem measurable_rpow_neg_mul_setLIntegral_Ioc (θ : ℝ) (φ : ℝ → ℝ≥0∞) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, φ s :=
  ((measurable_id.pow_const (-θ)).ennreal_ofReal).mul
    (Monotone.measurable fun _ _ h ↦ lintegral_mono_set (Ioc_subset_Ioc_right h))

/-- **General upper bound (`‖u‖_{θ, q} ≤ 2 θ⁻¹ ‖f‖_{p, q}`).** Over any normed field `𝕜` (without
requiring `NormedSpace ℝ E`), indicator truncation and the prefix Hardy inequality bound the
`K`-method norm of `(L¹, L^∞)` by `2 θ⁻¹` times the Lorentz gauge for `1 ≤ q ≤ ∞`. -/
theorem kMethodENorm_l1Linfty_le_two_mul_eLorentzNorm (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : 1 ≤ q) {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u ≤ 2 * ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  set g : ℝ → ℝ≥0∞ := fun t ↦
    ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
  rw [kMethodENorm_def, eLorentzNorm_eq_eLpNorm ((AEEqFun.aestronglyMeasurable _).congr hu)
    (exp_ne_zero_of_inv_eq hp), toReal_inv_eq_one_sub hθ hp]
  calc eLpNorm (fun t ↦ t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) q multHaar
      ≤ eLpNorm (fun t ↦ 2 * g t) q multHaar :=
        eLpNorm_mono_eNorm_ae (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u)
          (ae_pos_multHaar.mono fun t ht ↦ by
            rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _)
              (kFunctional_nonneg ht.le)), eNorm_eq_self,
              ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
            exact (mul_le_mul_right (ofReal_kFunctional_l1Linfty_le_two_mul hu ht.le) _).trans_eq
              (mul_left_comm _ _ _))
    _ = 2 * eLpNorm g q multHaar := eLpNorm_const_mul_ennreal
        (measurable_rpow_neg_mul_setLIntegral_Ioc θ _).aestronglyMeasurable
    _ ≤ _ := (mul_le_mul_right (eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ.1 hq
        (μ.measurable_decreasingRearrangement _).aemeasurable) 2).trans_eq (mul_assoc _ _ _).symm

/-- **General upper bound (`‖v‖_{θ, q} ≤ 2 θ⁻¹ ‖f‖_{p, q}`)** for the Lebesgue couple `(L¹, L^∞)`,
without requiring `NormedSpace ℝ E`. -/
theorem kMethodENorm_lebesgue_one_top_le_two_mul_eLorentzNorm (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : 1 ≤ q) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤ 2 * ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ :=
  kMethodENorm_l1Linfty_sumSpaceEmbed θ q v ▸
    kMethodENorm_l1Linfty_le_two_mul_eLorentzNorm hθ hp hq hv

/-- **Sharp Hardy upper bound (`‖u‖_{θ, q} ≤ θ⁻¹ ‖f‖_{p, q}`)** when `E` is also a real normed
space: combining `K(t, u) = ∫₀ᵗ ‖f‖*` with the prefix Hardy inequality gives the sharp constant
`θ⁻¹` for `0 < θ < 1`, `1 / p = 1 - θ`, and `1 ≤ q ≤ ∞`. -/
theorem kMethodENorm_l1Linfty_le_eLorentzNorm [NormedSpace ℝ E] (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : 1 ≤ q) {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [kMethodENorm_def, eLorentzNorm_eq_eLpNorm ((AEEqFun.aestronglyMeasurable _).congr hu)
    (exp_ne_zero_of_inv_eq hp), toReal_inv_eq_one_sub hθ hp]
  refine (eLpNorm_mono_eNorm_ae (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u)
    (ae_pos_multHaar.mono fun t ht ↦ ?_)).trans
    (eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ.1 hq
      (μ.measurable_decreasingRearrangement _).aemeasurable)
  rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
    eNorm_eq_self, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    ofReal_kFunctional_l1Linfty hu ht.le]

/-- **Sharp Hardy upper bound (`‖v‖_{θ, q} ≤ θ⁻¹ ‖f‖_{p, q}`)** for the Lebesgue couple `(L¹, L^∞)`
when `E` is also a real normed space. -/
theorem kMethodENorm_lebesgue_one_top_le_eLorentzNorm [NormedSpace ℝ E] (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : 1 ≤ q) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ :=
  kMethodENorm_l1Linfty_sumSpaceEmbed θ q v ▸ kMethodENorm_l1Linfty_le_eLorentzNorm hθ hp hq hv

/-! ### Membership characterization `(L¹, L^∞)_{θ, q} = L^{p, q}` -/

/-- An element `u` of `L¹ + L^∞` represented by `f` lies in `(L¹, L^∞)_{θ, q}` (`0 < θ < 1`,
`1 / p = 1 - θ`, `1 ≤ q ≤ ∞`) if and only if `f ∈ L^{p, q}(μ; E)`. -/
theorem mem_kMethod_l1Linfty_iff_memLorentz (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : 1 ≤ q) {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    u ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔ MemLorentz f p q μ := by
  rw [mem_kMethod_iff, memLorentz_iff]
  exact ⟨fun h ↦ (eLorentzNorm_le_kMethodENorm_l1Linfty hθ hp hu).trans_lt h,
    fun h ↦ (kMethodENorm_l1Linfty_le_two_mul_eLorentzNorm hθ hp hq hu).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofNat_lt_top ENNReal.ofReal_lt_top) h)⟩

/-- An element `v` of the sum space of `lebesgue 𝕜 E μ 1 ∞` represented by `f` lies in
`(L¹, L^∞)_{θ, q}` (`0 < θ < 1`, `1 / p = 1 - θ`, `1 ≤ q ≤ ∞`) if and only if
`f ∈ L^{p, q}(μ; E)`. -/
theorem mem_kMethod_lebesgue_one_top_iff_memLorentz (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : 1 ≤ q) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q ↔ MemLorentz f p q μ :=
  mem_kMethod_lebesgue_one_top_iff_l1Linfty.trans (mem_kMethod_l1Linfty_iff_memLorentz hθ hp hq hv)

/-- **Real interpolation of `(L¹, L^∞)` at function level:** for `0 < θ < 1`, `1 / p = 1 - θ`, and
`1 ≤ q ≤ ∞`, a function `f : α → E` is represented by an element of `(L¹, L^∞)_{θ, q}` if and only
if `f` belongs to the Lorentz class `L^{p, q}(μ; E)`. -/
theorem exists_mem_kMethod_lebesgue_one_top_iff_memLorentz (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : 1 ≤ q) {f : α → E} :
    (∃ v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q,
      ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) ↔
      MemLorentz f p q μ := by
  refine ⟨fun ⟨v, hv, hvf⟩ ↦ (mem_kMethod_lebesgue_one_top_iff_memLorentz hθ hp hq hvf).1 hv,
    fun hf ↦ ?_⟩
  obtain ⟨u, hu⟩ := hf.exists_l1AddLinfty (𝕜 := 𝕜) hθ hp (zero_lt_one.trans_le hq).ne'
  obtain ⟨v, rfl⟩ := lebesgue_one_top_sumSpaceEmbed_surjective u
  exact ⟨v, (mem_kMethod_lebesgue_one_top_iff_memLorentz hθ hp hq hu).2 hf, hu⟩

/-! ### Diagonal Banach-space isomorphism `(L¹, L^∞)_{θ, p} ≃L[𝕜] L^p` -/

section Diagonal

private theorem memLp_toAEEqFun_kMethodSpace (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    MemLp (L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)))
      p μ := by
  rw [← memLorentz_self, memLorentz_iff]
  exact (eLorentzNorm_le_kMethodENorm_lebesgue_one_top hθ hp EventuallyEq.rfl).trans_lt
    (mem_kMethod_iff.1 (KMethodSpace.toSumₗ_mem u))

variable [Fact (1 ≤ p)]

private theorem coeFn_lpToLebesgueOneTopSum (g : Lp E p μ) :
    ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
      (lpToLebesgueSum (𝕜 := 𝕜) (Fact.out : 1 ≤ p) le_top g))) =ᵐ[μ] ⇑g := by
  rw [sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]

private theorem norm_toLp_kMethodSpace_le (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ))
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ‖(memLp_toAEEqFun_kMethodSpace hθ hp u).toLp _‖ ≤ ‖u‖ := by
  rw [Lp.norm_toLp, KMethodSpace.norm_def]
  exact ENNReal.toReal_mono (mem_kMethod_iff.1 (KMethodSpace.toSumₗ_mem u)).ne (by
    rw [← eLorentzNorm_self]
    exact eLorentzNorm_le_kMethodENorm_lebesgue_one_top hθ hp EventuallyEq.rfl)

private theorem lpToLebesgueSum_mem_kMethod (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ))
    (g : Lp E p μ) :
    lpToLebesgueSum (𝕜 := 𝕜) (Fact.out : 1 ≤ p) le_top g ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ p :=
  (mem_kMethod_lebesgue_one_top_iff_memLorentz hθ hp Fact.out (coeFn_lpToLebesgueOneTopSum g)).2
    (memLorentz_self.2 (Lp.memLp g))

private theorem norm_lpToLebesgueOneTopKMethod_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (g : Lp E p μ) :
    ‖KMethodSpace.mk (lpToLebesgueSum (𝕜 := 𝕜) (Fact.out : 1 ≤ p) le_top g)
      (lpToLebesgueSum_mem_kMethod hθ hp g)‖ ≤ 2 * θ⁻¹ * ‖g‖ := by
  have hle := kMethodENorm_lebesgue_one_top_le_two_mul_eLorentzNorm (q := p) hθ hp Fact.out
    (coeFn_lpToLebesgueOneTopSum (𝕜 := 𝕜) g)
  rw [eLorentzNorm_self] at hle
  rw [KMethodSpace.norm_mk, Lp.norm_def, ← ENNReal.toReal_ofReal (inv_nonneg.2 hθ.1.le),
    ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    ENNReal.ofReal_ne_top) (Lp.eLpNorm_ne_top g)) hle

private def lebesgueOneTopKMethodToLp (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun u := (memLp_toAEEqFun_kMethodSpace hθ hp u).toLp _
      map_add' u v := by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (by simp only [map_add]; exact AEEqFun.coeFn_add _ _)
      map_smul' c u := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (by simp only [map_smul]; exact AEEqFun.coeFn_smul _ _) }
    1 fun u ↦ (norm_toLp_kMethodSpace_le hθ hp u).trans_eq (one_mul _).symm

private def lpToLebesgueOneTopKMethod (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    Lp E p μ →L[𝕜] (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p :=
  LinearMap.mkContinuous
    { toFun g := KMethodSpace.mk (lpToLebesgueSum (𝕜 := 𝕜) (Fact.out : 1 ≤ p) le_top g)
        (lpToLebesgueSum_mem_kMethod hθ hp g)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    (2 * θ⁻¹) (norm_lpToLebesgueOneTopKMethod_le hθ hp)

/-- **Diagonal real interpolation isomorphism:** for `0 < θ < 1` and `1 / p = 1 - θ`, the real
interpolation space `(L¹(μ; E), L^∞(μ; E))_{θ, p}` is isomorphic as a normed space over `𝕜` to
`L^p(μ; E)`, with forward norm at most `1` and inverse norm at most `2 θ⁻¹` (and at most `θ⁻¹` when
`E` is also a real normed space). -/
def lebesgueOneTopKMethodEquivLp (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p ≃L[𝕜] Lp E p μ :=
  ContinuousLinearEquiv.equivOfInverse
    (lebesgueOneTopKMethodToLp hθ hp) (lpToLebesgueOneTopKMethod hθ hp)
    (fun u ↦ KMethodSpace.ext <| (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective <|
      L1AddLinfty.toAEEqFun_injective <| AEEqFun.ext <| by
        simp only [lpToLebesgueOneTopKMethod, lebesgueOneTopKMethodToLp,
          LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, KMethodSpace.toSumₗ_mk,
          sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
        exact MemLp.coeFn_toLp _)
    (fun g ↦ Lp.ext <| (memLp_toAEEqFun_kMethodSpace hθ hp _).coeFn_toLp.trans <| by
      simp only [lpToLebesgueOneTopKMethod, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
        AddHom.coe_mk, KMethodSpace.toSumₗ_mk, sumSpaceEmbed_lpToLebesgueSum,
        L1AddLinfty.toAEEqFun_ofLp]
      exact EventuallyEq.rfl)

theorem coeFn_lebesgueOneTopKMethodEquivLp (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ⇑(lebesgueOneTopKMethodEquivLp hθ hp u) =ᵐ[μ]
      ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u))) :=
  (memLp_toAEEqFun_kMethodSpace hθ hp u).coeFn_toLp

@[simp]
theorem toSumₗ_lebesgueOneTopKMethodEquivLp_symm (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (g : Lp E p μ) :
    KMethodSpace.toSumₗ ((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hθ hp).symm g) =
      lpToLebesgueSum (𝕜 := 𝕜) (Fact.out : 1 ≤ p) le_top g := by
  simp [lebesgueOneTopKMethodEquivLp, lpToLebesgueOneTopKMethod]

theorem norm_lebesgueOneTopKMethodEquivLp_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ‖lebesgueOneTopKMethodEquivLp hθ hp u‖ ≤ ‖u‖ :=
  norm_toLp_kMethodSpace_le hθ hp u

theorem norm_lebesgueOneTopKMethodEquivLp_symm_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (g : Lp E p μ) :
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hθ hp).symm g‖ ≤ 2 * θ⁻¹ * ‖g‖ :=
  norm_lpToLebesgueOneTopKMethod_le hθ hp g

/-- When `E` is also a real normed space, the inverse isomorphism
`L^p(μ; E) → (L¹, L^∞)_{θ, p}` has norm bounded by the sharp Hardy constant `θ⁻¹`. -/
theorem norm_lebesgueOneTopKMethodEquivLp_symm_le_of_normedSpace_real [NormedSpace ℝ E]
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (g : Lp E p μ) :
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hθ hp).symm g‖ ≤ θ⁻¹ * ‖g‖ := by
  have hle := kMethodENorm_lebesgue_one_top_le_eLorentzNorm (q := p) hθ hp Fact.out
    (coeFn_lpToLebesgueOneTopSum (𝕜 := 𝕜) g)
  rw [eLorentzNorm_self] at hle
  rw [KMethodSpace.norm_def, toSumₗ_lebesgueOneTopKMethodEquivLp_symm, Lp.norm_def,
    ← ENNReal.toReal_ofReal (inv_nonneg.2 hθ.1.le), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top g)) hle

section OpNorm

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' E]

theorem opNorm_lebesgueOneTopKMethodEquivLp_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜') (E := E) (μ := μ) hθ hp).toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa using norm_lebesgueOneTopKMethodEquivLp_le hθ hp u

theorem opNorm_lebesgueOneTopKMethodEquivLp_symm_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    ‖((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜') (E := E) (μ := μ) hθ hp).symm).toContinuousLinearMap‖
      ≤ 2 * θ⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg zero_le_two (inv_nonneg.2 hθ.1.le))
    (norm_lebesgueOneTopKMethodEquivLp_symm_le hθ hp)

theorem opNorm_lebesgueOneTopKMethodEquivLp_symm_le_of_normedSpace_real [NormedSpace ℝ E]
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    ‖((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜') (E := E) (μ := μ) hθ hp).symm).toContinuousLinearMap‖
      ≤ θ⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hθ.1.le)
    (norm_lebesgueOneTopKMethodEquivLp_symm_le_of_normedSpace_real hθ hp)

end OpNorm

end Diagonal

/-! ### Sharpness of the Hardy constant `θ⁻¹` -/

section Sharpness

private theorem eLorentzNorm_rpow_sub_one_Ioi (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    eLorentzNorm (fun t : ℝ ↦ t ^ (θ - 1)) p ∞ (volume.restrict (Ioi 0)) = 1 := by
  have hpow : (fun t : ℝ ↦ t ^ (θ - 1)) = fun t : ℝ ↦ t ^ (-(p⁻¹).toReal) := by
    ext t; rw [toReal_inv_eq_one_sub hθ hp, neg_sub]
  exact hpow ▸ eLorentzNorm_rpow_neg_inv_Ioi (exp_ne_zero_of_inv_eq hp) (exp_ne_top_of_inv_eq hθ hp)

/-- **Sharpness of `θ⁻¹`:** on `(0, ∞)` with Lebesgue measure, any element `v` of `L¹ + L^∞`
representing `t ↦ t ^ (θ - 1)` (`0 < θ < 1`) has `(L¹, L^∞)_{θ, ∞}` norm equal to `θ⁻¹`, whereas
`‖t ↦ t ^ (θ - 1)‖_{p, ∞} = 1` (`1 / p = 1 - θ`). -/
theorem kMethodENorm_lebesgue_one_top_rpow_sub_one (hθ : θ ∈ Ioo 0 1)
    {v : (lebesgue ℝ ℝ (volume.restrict (Ioi 0)) 1 ∞).SumSpace}
    (hv : ⇑(L1AddLinfty.toAEEqFun ℝ
      ((lebesgue ℝ ℝ (volume.restrict (Ioi 0)) 1 ∞).sumSpaceEmbed v)) =ᵐ[volume.restrict (Ioi 0)]
      fun t : ℝ ↦ t ^ (θ - 1)) :
    (lebesgue ℝ ℝ (volume.restrict (Ioi 0)) 1 ∞).kMethodENorm θ ∞ v = ENNReal.ofReal θ⁻¹ := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  have hlor := eLorentzNorm_rpow_sub_one_Ioi (p := (ENNReal.ofReal (1 - θ))⁻¹) hθ (inv_inv _)
  refine le_antisymm
    ((kMethodENorm_lebesgue_one_top_le_eLorentzNorm hθ (inv_inv _) le_top hv).trans_eq
      (by rw [hlor, mul_one])) ?_
  have hμ : (multHaar : Measure ℝ) ≠ 0 := fun h ↦ by simpa [h] using multHaar_Icc_one_exp_one
  have hae : (fun s : ℝ ↦ ‖s ^ (θ - 1)‖ₑ) =ᵐ[ν] fun s : ℝ ↦ ENNReal.ofReal (s ^ (θ - 1)) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) ↦
      Real.eNorm_of_nonneg (Real.rpow_nonneg hs.le _)
  have hanti : AntitoneOn (fun s : ℝ ↦ ENNReal.ofReal (s ^ (θ - 1))) (Ioi 0) :=
    fun s₁ (hs₁ : 0 < s₁) _ _ hle ↦
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs₁ hle (sub_nonpos.2 hθ.2.le))
  have hcont : ∀ s > 0, ContinuousWithinAt (fun r : ℝ ↦ ENNReal.ofReal (r ^ (θ - 1))) (Ici s) s :=
    fun s hs ↦ (ENNReal.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const s (θ - 1) (Or.inl hs.ne'))).continuousWithinAt
  rw [kMethodENorm_def, ← show eLpNorm (fun _ : ℝ ↦ ENNReal.ofReal θ⁻¹) ∞ multHaar =
    ENNReal.ofReal θ⁻¹ by simp [eLpNorm_const _ ENNReal.top_ne_zero hμ]]
  refine eLpNorm_mono_eNorm_ae aestronglyMeasurable_const (ae_pos_multHaar.mono fun t ht ↦ ?_)
  have hint : ∫⁻ s in Ioc 0 t, ν.decreasingRearrangement (fun x : ℝ ↦ ‖x ^ (θ - 1)‖ₑ) s =
      ENNReal.ofReal (t ^ θ / θ) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      setLIntegral_congr_fun measurableSet_Ioo fun s hs ↦ by
        rw [Measure.decreasingRearrangement_congr_ae _ hae,
          Measure.decreasingRearrangement_eq_of_antitoneOn hanti hcont hs.1],
      lintegral_ofReal_rpow_Ioo (by linarith [hθ.1]) ht.le, sub_add_cancel]
  simp only [eNorm_eq_self]
  calc ENNReal.ofReal θ⁻¹
      = ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal (t ^ θ / θ) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le]
        congr 1; have := (Real.rpow_pos_of_pos ht θ).ne'; field_simp
    _ ≤ ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal ((lebesgue ℝ ℝ ν 1 ∞).kFunctional t v) :=
        hint ▸ mul_le_mul_right
          (lintegral_decreasingRearrangement_le_ofReal_kFunctional_lebesgue_one_top hv ht.le) _
    _ = ‖t ^ (-θ) * (lebesgue ℝ ℝ ν 1 ∞).kFunctional t v‖ₑ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
          Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))]

/-- On `(0, ∞)`, `t ↦ t ^ (θ - 1)` (`0 < θ < 1`, `1 / p = 1 - θ`) represents an element of
`(L¹, L^∞)_{θ, ∞}` that attains the upper bound `‖v‖_{θ, ∞} = θ⁻¹ ‖f‖_{p, ∞}` with nonzero norm. -/
theorem exists_kMethod_lebesgue_one_top_rpow_sub_one (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    ∃ v ∈ (lebesgue ℝ ℝ (volume.restrict (Ioi 0)) 1 ∞).kMethod θ ∞,
      (⇑(L1AddLinfty.toAEEqFun ℝ ((lebesgue ℝ ℝ (volume.restrict (Ioi 0)) 1 ∞).sumSpaceEmbed v))
        =ᵐ[volume.restrict (Ioi 0)] fun t : ℝ ↦ t ^ (θ - 1)) ∧
      eLorentzNorm (fun t : ℝ ↦ t ^ (θ - 1)) p ∞ (volume.restrict (Ioi 0)) = 1 ∧
      (lebesgue ℝ ℝ (volume.restrict (Ioi 0)) 1 ∞).kMethodENorm θ ∞ v = ENNReal.ofReal θ⁻¹ := by
  have hlor := eLorentzNorm_rpow_sub_one_Ioi hθ hp
  obtain ⟨v, hv, hvf⟩ := (exists_mem_kMethod_lebesgue_one_top_iff_memLorentz (𝕜 := ℝ) (E := ℝ) hθ hp
    le_top).2 (by rw [memLorentz_iff, hlor]; exact ENNReal.one_lt_top)
  exact ⟨v, hv, hvf, hlor, kMethodENorm_lebesgue_one_top_rpow_sub_one hθ hvf⟩

end Sharpness

end CompatibleCouple

end TauCeti
