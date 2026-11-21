/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.L1Linfty
public import TauCeti.Analysis.Normed.Interpolation.RealMethod.Basic
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
* **Extended `K`-method gauge on indicators and operator interpolation:** for `θ < 1` and when
  `E` is also a real normed space (`[NormedSpace ℝ E]`),
  `kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ)` for any sum-space element `u`
  in `(L¹, L^∞)` represented almost everywhere by the indicator `c 1_A`
  (`TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_indicator`, transported to `lebesgue 𝕜 E μ 1 ∞`
  via `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_sumSpaceEmbed`). Under the same real
  normed-space assumption on the source `E`, functoriality yields operator interpolation in
  Lorentz gauges (`TauCeti.CompatibleCouple.eLorentzNorm_map_le_of_lebesgue_one_top`, which
  specializes on the diagonal `q = p` to `Lᵖ` via `TauCeti.eLorentzNorm_self`).

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

private theorem one_le_of_inv_eq (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    1 ≤ p :=
  ENNReal.inv_le_one.1 <| hp.trans_le <| ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)

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

/-- The embedding `sumSpaceEmbed` preserves `K`-method membership between the sum space of
`lebesgue 𝕜 E μ 1 ∞` and `L¹(μ; E) + L^∞(μ; E)`. -/
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
    (μ.measurable_rpow_mul_decreasingRearrangement _ _).aestronglyMeasurable
    (ae_pos_multHaar.mono fun t ht ↦ ?_)
  simp only [eNorm_eq_self]
  calc ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t
      = ENNReal.ofReal (t ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) t := by
        rw [toReal_inv_eq_one_sub hθ hp]
    _ ≤ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s :=
        rpow_one_sub_mul_le_rpow_neg_mul_lintegral_Ioc
          ((μ.antitone_decreasingRearrangement _).antitoneOn (Ioi 0)) θ ht
    _ ≤ ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) :=
        mul_le_mul_right
          (lintegral_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu ht.le) _
    _ = ‖t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u‖ₑ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
          Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))]

/-- **Lower bound (`‖f‖_{p, q} ≤ ‖v‖_{θ, q}`)** for the Lebesgue couple `(L¹, L^∞)`. -/
theorem eLorentzNorm_le_kMethodENorm_lebesgue_one_top (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    eLorentzNorm f p q μ ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v :=
  kMethodENorm_l1Linfty_sumSpaceEmbed θ q v ▸ eLorentzNorm_le_kMethodENorm_l1Linfty hθ hp hv

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
    _ = 2 * eLpNorm g q multHaar := eLpNorm_const_mul_ennreal_of_pos (zero_lt_one.trans_le hq)
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

/-! ### Diagonal normed-space isomorphism `(L¹, L^∞)_{θ, p} ≃L[𝕜] L^p` -/

section Diagonal

private theorem memLp_toAEEqFun_kMethodSpace (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    MemLp (L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)))
      p μ := by
  rw [← memLorentz_self, memLorentz_iff]
  exact (eLorentzNorm_le_kMethodENorm_lebesgue_one_top hθ hp EventuallyEq.rfl).trans_lt
    (mem_kMethod_iff.1 (KMethodSpace.toSumₗ_mem u))

section

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

end

/-- **Diagonal real interpolation isomorphism:** for `0 < θ < 1` and `1 / p = 1 - θ`, the real
interpolation space `(L¹(μ; E), L^∞(μ; E))_{θ, p}` is isomorphic as a normed space over `𝕜` to
`L^p(μ; E)`, with forward norm at most `1` and inverse norm at most `2 θ⁻¹` (and at most `θ⁻¹` when
`E` is also a real normed space). -/
def lebesgueOneTopKMethodEquivLp (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)))⟩
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p ≃L[𝕜] Lp E p μ :=
  letI : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  ContinuousLinearEquiv.ofContinuousLinearMap
    (lebesgueOneTopKMethodToLp hθ hp) (lpToLebesgueOneTopKMethod hθ hp)
    (ContinuousLinearMap.ext <|
      show Function.RightInverse (lpToLebesgueOneTopKMethod hθ hp)
        (lebesgueOneTopKMethodToLp hθ hp) from
      fun g ↦ Lp.ext <| (memLp_toAEEqFun_kMethodSpace hθ hp _).coeFn_toLp.trans <| by
      simp only [lpToLebesgueOneTopKMethod, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
        AddHom.coe_mk, KMethodSpace.toSumₗ_mk, sumSpaceEmbed_lpToLebesgueSum,
        L1AddLinfty.toAEEqFun_ofLp]
      exact EventuallyEq.rfl)
    (ContinuousLinearMap.ext <|
      show Function.LeftInverse (lpToLebesgueOneTopKMethod hθ hp)
        (lebesgueOneTopKMethodToLp hθ hp) from
      fun u ↦ KMethodSpace.ext <| (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective <|
      L1AddLinfty.toAEEqFun_injective <| AEEqFun.ext <| by
        simp only [lpToLebesgueOneTopKMethod, lebesgueOneTopKMethodToLp,
          LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, KMethodSpace.toSumₗ_mk,
          sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
        exact MemLp.coeFn_toLp _)

/-- The diagonal isomorphism `(L¹, L^∞)_{θ, p} ≃L[𝕜] L^p(μ; E)` sends `u` to an `L^p` element
representing the same function almost everywhere as `u` in `L¹ + L^∞`. -/
theorem coeFn_lebesgueOneTopKMethodEquivLp (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ⇑(lebesgueOneTopKMethodEquivLp hθ hp u) =ᵐ[μ]
      ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u))) :=
  (memLp_toAEEqFun_kMethodSpace hθ hp u).coeFn_toLp

/-- In the ambient sum space of `(L¹, L^∞)`, the inverse isomorphism
`L^p(μ; E) → (L¹, L^∞)_{θ, p}` agrees with `lpToLebesgueSum`. -/
@[simp]
theorem toSumₗ_lebesgueOneTopKMethodEquivLp_symm (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (g : Lp E p μ) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)))⟩
    KMethodSpace.toSumₗ ((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hθ hp).symm g) =
      lpToLebesgueSum (𝕜 := 𝕜) (Fact.out : 1 ≤ p) le_top g := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  simp [lebesgueOneTopKMethodEquivLp, lpToLebesgueOneTopKMethod]

/-- Mapping an element of `(L¹, L^∞)_{θ, p}` to `L^p` via `lebesgueOneTopKMethodEquivLp` and then
embedding into `L¹ + L^∞` agrees with the canonical map from the `K`-method space into the sum. -/
@[simp]
theorem ofLp_lebesgueOneTopKMethodEquivLp (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.left.le)))⟩
    (L1AddLinfty.ofLp (lebesgueOneTopKMethodEquivLp hθ hp u) : L1AddLinfty 𝕜 E μ) =
      (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u) := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  refine L1AddLinfty.toAEEqFun_injective ?_
  rw [L1AddLinfty.toAEEqFun_ofLp]
  exact AEEqFun.ext (coeFn_lebesgueOneTopKMethodEquivLp hθ hp u)

/-- The diagonal equivalence `lebesgueOneTopKMethodEquivLp` sends an endpoint intersection element
embedded via `ofInter` to its canonical image in `L^p`. -/
@[simp]
theorem lebesgueOneTopKMethodEquivLp_ofInter (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (x : (lebesgue 𝕜 E μ 1 ∞).inter) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.left.le)))⟩
    lebesgueOneTopKMethodEquivLp hθ hp (KMethodSpace.ofInter θ p hθ x) =
      lebesgueInterToLp (Fact.out : 1 ≤ p) le_top x := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  exact L1AddLinfty.ofLp_injective (𝕜 := 𝕜) (by
    rw [ofLp_lebesgueOneTopKMethodEquivLp, KMethodSpace.toSumₗ_ofInter, sumSpaceEmbed_fstToSum,
      lebesgue_embed₀, interFst_apply, ofLp_lebesgueInterToLp])

/-- The forward isomorphism `(L¹, L^∞)_{θ, p} → L^p(μ; E)` is norm-nonincreasing
(`‖·‖_p ≤ ‖·‖_{θ, p}`). -/
theorem norm_lebesgueOneTopKMethodEquivLp_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)))⟩
    ‖lebesgueOneTopKMethodEquivLp hθ hp u‖ ≤ ‖u‖ := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  exact norm_toLp_kMethodSpace_le hθ hp u

/-- Over any normed field `𝕜` (without requiring `NormedSpace ℝ E`), the inverse isomorphism
`L^p(μ; E) → (L¹, L^∞)_{θ, p}` satisfies `‖·‖_{θ, p} ≤ 2 θ⁻¹ ‖·‖_p`. -/
theorem norm_lebesgueOneTopKMethodEquivLp_symm_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (g : Lp E p μ) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)))⟩
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hθ hp).symm g‖ ≤ 2 * θ⁻¹ * ‖g‖ := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  exact norm_lpToLebesgueOneTopKMethod_le hθ hp g

/-- When `E` is also a real normed space, the inverse isomorphism
`L^p(μ; E) → (L¹, L^∞)_{θ, p}` has norm bounded by the sharp Hardy constant `θ⁻¹`. -/
theorem norm_lebesgueOneTopKMethodEquivLp_symm_le_of_normedSpace_real [NormedSpace ℝ E]
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (g : Lp E p μ) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)))⟩
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hθ hp).symm g‖ ≤ θ⁻¹ * ‖g‖ := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  have hle := kMethodENorm_lebesgue_one_top_le_eLorentzNorm (q := p) hθ hp Fact.out
    (coeFn_lpToLebesgueOneTopSum (𝕜 := 𝕜) g)
  rw [eLorentzNorm_self] at hle
  rw [KMethodSpace.norm_def, toSumₗ_lebesgueOneTopKMethodEquivLp_symm, Lp.norm_def,
    ← ENNReal.toReal_ofReal (inv_nonneg.2 hθ.1.le), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top g)) hle

section OpNorm

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' E]

/-- Over a nontrivially normed field, the forward isomorphism `(L¹, L^∞)_{θ, p} →L[𝕜'] L^p(μ; E)`
has operator norm at most `1`. -/
theorem opNorm_lebesgueOneTopKMethodEquivLp_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)))⟩
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜') (E := E) (μ := μ) hθ hp).toContinuousLinearMap‖
      ≤ 1 := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa using norm_lebesgueOneTopKMethodEquivLp_le hθ hp u

/-- Over any nontrivially normed field (without requiring `NormedSpace ℝ E`), the inverse
isomorphism `L^p(μ; E) →L[𝕜'] (L¹, L^∞)_{θ, p}` has operator norm at most `2 θ⁻¹`. -/
theorem opNorm_lebesgueOneTopKMethodEquivLp_symm_le (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)))⟩
    ‖((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜') (E := E) (μ := μ) hθ hp).symm).toContinuousLinearMap‖
      ≤ 2 * θ⁻¹ := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  exact ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg zero_le_two (inv_nonneg.2 hθ.1.le))
    (norm_lebesgueOneTopKMethodEquivLp_symm_le hθ hp)

/-- When `E` is also a real normed space, the inverse isomorphism
`L^p(μ; E) →L[𝕜'] (L¹, L^∞)_{θ, p}` has operator norm bounded by the sharp Hardy constant
`θ⁻¹`. -/
theorem opNorm_lebesgueOneTopKMethodEquivLp_symm_le_of_normedSpace_real [NormedSpace ℝ E]
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) :
    letI : Fact (1 ≤ p) :=
      ⟨ENNReal.inv_le_one.1 (hp.trans_le (ENNReal.ofReal_le_one.2 (sub_le_self 1 hθ.1.le)))⟩
    ‖((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜') (E := E) (μ := μ) hθ hp).symm).toContinuousLinearMap‖
      ≤ θ⁻¹ := by
  have : Fact (1 ≤ p) := ⟨one_le_of_inv_eq hθ hp⟩
  exact ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hθ.1.le)
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
  -- Express `ENNReal.ofReal θ⁻¹` as a constant `L^∞(dt / t)` seminorm so `eLpNorm_mono_eNorm_ae`
  -- compares the `ℝ≥0∞`-valued constant with the `ℝ`-valued `K`-functional integrand across `‖·‖ₑ`.
  have hconst : eLpNorm (fun _ : ℝ ↦ ENNReal.ofReal θ⁻¹) ∞ multHaar = ENNReal.ofReal θ⁻¹ := by
    simp [eLpNorm_const _ ENNReal.top_ne_zero hμ]
  rw [kMethodENorm_def, ← hconst]
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

/-! ### Extended `K`-method gauge on indicator functions -/

section Indicator

variable [NormedSpace ℝ E]

private theorem kMethodENorm_l1Linfty_indicator_of_measure_eq_top {u : L1AddLinfty 𝕜 E μ}
    {A : Set α} {c : E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ ↦ c)
    {θ : ℝ} (hθ : θ < 1) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hc0 : ‖c‖ₑ ≠ 0) (hAtop : μ A = ∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ
  have hK : ∀ᵐ t ∂multHaar,
      ‖t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u‖ₑ =
        ‖c‖ₑ * ENNReal.ofReal (t ^ (1 - θ)) := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ofReal_kFunctional_l1Linfty_indicator hu ht.le, hAtop, min_eq_left le_top,
      mul_left_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← Real.rpow_add_one ht.ne', neg_add_eq_sub]
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ))) multHaar :=
    ((measurable_id.pow_const (1 - θ)).ennreal_ofReal).aestronglyMeasurable
  have hdiv : eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ))) q multHaar = ∞ := by
    rcases eq_or_ne q ∞ with rfl | hqtop
    · rw [eLpNorm_exponent_top hmeas, eLpNormEssSup_eq_essSup_eNorm]
      simp only [eNorm_eq_self]
      rw [essSup_multHaar_eq_iSup_Ioi (f := fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)))
        fun t ht ↦ (ENNReal.continuous_ofReal.continuousAt.comp
          (Real.continuousAt_rpow_const t _ (Or.inl ht.ne'))).continuousWithinAt]
      refine eq_top_iff.2 (le_of_tendsto
        (ENNReal.tendsto_ofReal_atTop.comp (tendsto_rpow_atTop h1θ))
        ((eventually_gt_atTop 0).mono fun t ht ↦ le_iSup₂_of_le t ht le_rfl))
    · have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hqtop hmeas]
      simp only [eNorm_eq_self]
      have hpow_eq : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) ^ q.toReal) =ᵐ[multHaar]
          fun t ↦ ENNReal.ofReal (t ^ ((1 - θ) * q.toReal)) := by
        filter_upwards [ae_pos_multHaar] with t ht
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) hq_pos.le,
          ← Real.rpow_mul ht.le]
      rw [lintegral_congr_ae hpow_eq, lintegral_multHaar_rpow_eq_top (mul_pos h1θ hq_pos),
        ENNReal.top_rpow_of_pos (one_div_pos.2 hq_pos)]
  have hnorm_top : (l1Linfty 𝕜 E μ).kMethodENorm θ q u = ∞ := by
    rw [kMethodENorm_def,
      eLpNorm_congr_eNorm_ae (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u)
        (hmeas.aemeasurable.const_mul ‖c‖ₑ).aestronglyMeasurable
        (hK.mono fun _ ht ↦ by simp only [eNorm_eq_self, ht]),
      eLpNorm_const_mul_ennreal hmeas, hdiv, ENNReal.mul_top hc0]
  rw [hnorm_top, hAtop, ENNReal.top_rpow_of_pos h1θ,
    ENNReal.mul_top (ENNReal.mul_pos (kMethodConst_ne_zero θ hq0) hc0).ne']

private theorem kMethodENorm_l1Linfty_indicator_of_measure_pos {u : L1AddLinfty 𝕜 E μ}
    {A : Set α} {c : E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ ↦ c)
    (θ : ℝ) (q : ℝ≥0∞) (hc0 : ‖c‖ₑ ≠ 0) (hA0 : μ A ≠ 0) (hAtop : μ A ≠ ∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  set m : ℝ := (μ A).toReal
  have hm : 0 < m := ENNReal.toReal_pos hA0 hAtop
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.2 (by simpa using hc0)
  have heq : (fun t : ℝ ↦ t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) =ᵐ[multHaar]
      fun t : ℝ ↦ t ^ (-θ) * min (‖c‖ * m) (t * ‖c‖) := by
    filter_upwards [ae_pos_multHaar] with t ht
    have hK_ofReal : ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) =
        ENNReal.ofReal (min (‖c‖ * m) (t * ‖c‖)) := by
      rw [ofReal_kFunctional_l1Linfty_indicator hu ht.le, ← ENNReal.ofReal_toReal hAtop,
        ← ofReal_norm, ← ENNReal.ofReal_min, ← ENNReal.ofReal_mul (norm_nonneg c),
        mul_min_of_nonneg _ _ (norm_nonneg c), mul_comm ‖c‖ t, min_comm]
    have hK : (l1Linfty 𝕜 E μ).kFunctional t u = min (‖c‖ * m) (t * ‖c‖) := by
      have := congrArg ENNReal.toReal hK_ofReal
      rwa [ENNReal.toReal_ofReal (kFunctional_nonneg ht.le),
        ENNReal.toReal_ofReal (le_min (mul_nonneg (norm_nonneg c) hm.le)
          (mul_nonneg ht.le (norm_nonneg c)))] at this
    rw [hK]
  rw [kMethodENorm_def, eLpNorm_congr_ae heq,
    eLpNorm_rpow_neg_mul_min θ q (mul_pos hc_pos hm) hc_pos, Real.mul_rpow hc_pos.le hm.le,
    mul_right_comm (‖c‖ ^ (1 - θ)), ← Real.rpow_add hc_pos, sub_add_cancel, Real.rpow_one,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm, ← ENNReal.ofReal_rpow_of_pos hm,
    ENNReal.ofReal_toReal hAtop]
  ring

/-- Extended `K`-method gauge of a sum-space element `u` in `(L¹, L^∞)` represented almost
everywhere by the indicator `c 1_A`: when `E` is also a real normed space (`[NormedSpace ℝ E]`),
for `θ < 1` and every `q ∈ [0, ∞]`,
`kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ(A) ^ (1 - θ)`. -/
theorem kMethodENorm_l1Linfty_indicator {u : L1AddLinfty 𝕜 E μ} {A : Set α} {c : E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ ↦ c)
    {θ : ℝ} (hθ : θ < 1) (q : ℝ≥0∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ
  rcases eq_or_ne q 0 with rfl | hq0
  · have hmeas_min : AEStronglyMeasurable (fun s : ℝ ↦ s ^ (-θ) * min 1 s) multHaar :=
      ((continuousOn_id.rpow_const fun _ ht ↦ Or.inl (ne_of_gt ht)).mul
        (continuous_const.min continuous_id).continuousOn).aestronglyMeasurable_multHaar
    rw [kMethodENorm_def, kMethodConst_def,
      eLpNorm_exponent_zero (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u),
      eLpNorm_exponent_zero hmeas_min]
    simp
  have hzero_of : (∀ t : ℝ, 0 < t → ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) = 0) →
      (l1Linfty 𝕜 E μ).kMethodENorm θ q u = 0 := fun hK ↦ by
    have hzero : (fun t : ℝ ↦ t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) =ᵐ[multHaar] 0 := by
      filter_upwards [ae_pos_multHaar] with t ht
      have hK0 : (l1Linfty 𝕜 E μ).kFunctional t u = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.1 (hK t ht)) (kFunctional_nonneg ht.le)
      simp [hK0]
    rw [kMethodENorm_def, eLpNorm_congr_ae hzero, eLpNorm_zero]
  rcases eq_or_ne ‖c‖ₑ 0 with hc0 | hc0
  · rw [hzero_of fun t ht ↦ by rw [ofReal_kFunctional_l1Linfty_indicator hu ht.le, hc0, zero_mul],
      hc0, mul_zero, zero_mul]
  rcases eq_or_ne (μ A) 0 with hA0 | hA0
  · rw [hzero_of fun t ht ↦ by
        rw [ofReal_kFunctional_l1Linfty_indicator hu ht.le, hA0, min_zero, mul_zero],
      hA0, ENNReal.zero_rpow_of_pos h1θ, mul_zero]
  rcases eq_or_ne (μ A) ∞ with hAtop | hAtop
  · exact kMethodENorm_l1Linfty_indicator_of_measure_eq_top hu hθ hq0 hc0 hAtop
  · exact kMethodENorm_l1Linfty_indicator_of_measure_pos hu θ q hc0 hA0 hAtop

end Indicator

/-! ### Operator interpolation in Lorentz gauges -/

section Map

variable {β F : Type*} {mβ : MeasurableSpace β} {ν : Measure β}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ E]

/-- **Operator interpolation in Lorentz gauges.** When the source `E` is also a real normed space
(`[NormedSpace ℝ E]`), a `𝕜`-linear map `T` between the sum spaces of `(L¹(μ; E), L^∞(μ; E))` and
`(L¹(ν; F), L^∞(ν; F))` restricting to maps with `L¹` bound `M₀ > 0` and `L^∞` bound `M₁ > 0`
satisfies
`‖T v‖_{L^{p, q}(ν)} ≤ θ⁻¹ M₀ ^ (1 - θ) M₁ ^ θ ‖v‖_{L^{p, q}(μ)}`
for `0 < θ < 1`, `p⁻¹ = ENNReal.ofReal (1 - θ)`, and `1 ≤ q ≤ ∞`. -/
theorem eLorentzNorm_map_le_of_lebesgue_one_top
    (T : (lebesgue 𝕜 E μ 1 ∞).SumSpace →ₗ[𝕜] (lebesgue 𝕜 F ν 1 ∞).SumSpace)
    {T₀ : Lp E 1 μ → Lp F 1 ν} {T₁ : Lp E ∞ μ → Lp F ∞ ν}
    (hT₀ : ∀ x, T ((lebesgue 𝕜 E μ 1 ∞).fstToSum x) = (lebesgue 𝕜 F ν 1 ∞).fstToSum (T₀ x))
    (hT₁ : ∀ x, T ((lebesgue 𝕜 E μ 1 ∞).sndToSum x) = (lebesgue 𝕜 F ν 1 ∞).sndToSum (T₁ x))
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E} {g : β → F}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (hTv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 F ν 1 ∞).sumSpaceEmbed (T v))) =ᵐ[ν] g)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p q : ℝ≥0∞} (hp : p⁻¹ = ENNReal.ofReal (1 - θ)) (hq : 1 ≤ q) :
    eLorentzNorm g p q ν ≤
      ENNReal.ofReal (θ⁻¹ * M₀ ^ (1 - θ) * M₁ ^ θ) * eLorentzNorm f p q μ := by
  calc eLorentzNorm g p q ν
      ≤ (lebesgue 𝕜 F ν 1 ∞).kMethodENorm θ q (T v) :=
          eLorentzNorm_le_kMethodENorm_lebesgue_one_top hθ hp hTv
    _ ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v :=
          kMethodENorm_map_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁ v
    _ ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * (ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ) := by
          gcongr
          exact kMethodENorm_lebesgue_one_top_le_eLorentzNorm hθ hp hq hv
    _ = ENNReal.ofReal (θ⁻¹ * M₀ ^ (1 - θ) * M₁ ^ θ) * eLorentzNorm f p q μ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring

end Map

end CompatibleCouple

end TauCeti
