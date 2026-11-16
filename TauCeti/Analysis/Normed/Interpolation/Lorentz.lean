/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.L1Linfty
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
public import TauCeti.MeasureTheory.Function.Lorentz
import TauCeti.MeasureTheory.Integral.Hardy

/-!
# Real interpolation of `(L¹, L^∞)` and Lorentz spaces

Combining Peetre's formula `K(t, u) = ∫₀ᵗ ‖f‖*` for the couple `(L¹, L^∞)`
(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty`) with the weighted Hardy inequality on
`(0, ∞)` with `dt / t` (`TauCeti.eLpNorm_rpow_neg_mul_lintegral_Ioc_le`) identifies the real
interpolation spaces `(L¹, L^∞)_{θ, q}` with the Lorentz spaces `L^{p, q}`, where
`1 / p = 1 - θ` and `1 ≤ q ≤ ∞`.

For every element `u` of `L¹ + L^∞` (or of the sum space of `CompatibleCouple.lebesgue 𝕜 E μ 1 ∞`)
represented by `f`, the `K`-method norm and the Lorentz gauge are equivalent with explicit
constants independent of `f`, `q`, and the measure space:

`‖f‖_{L^{p, q}} ≤ ‖u‖_{θ, q} ≤ θ⁻¹ ‖f‖_{L^{p, q}}`

(`TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_l1Linfty`,
`TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_le_mul_eLorentzNorm`, and their counterparts for
`CompatibleCouple.lebesgue 𝕜 E μ 1 ∞`). For `0 < θ < 1` and `1 ≤ q ≤ ∞`, a function `f`
represents an element of `(L¹, L^∞)_{θ, q}` if and only if it is almost everywhere strongly
measurable and has finite Lorentz gauge `‖f‖_{L^{p, q}} < ∞`
(`TauCeti.CompatibleCouple.exists_toAEEqFun_mem_kMethod_l1Linfty_iff`,
`TauCeti.CompatibleCouple.exists_toAEEqFun_mem_kMethod_lebesgue_one_top_iff`).

On the diagonal `q = p`, where `‖f‖_{L^{p, p}} = ‖f‖_{Lᵖ}` (`TauCeti.eLorentzNorm_self`), this
yields a continuous linear equivalence

`(L¹, L^∞)_{θ, p} ≃L[𝕜] Lᵖ`

(`TauCeti.CompatibleCouple.lebesgueOneTopKMethodEquivLp`), with forward norm bound `1` and inverse
norm bound `θ⁻¹`. Combining the norm equivalence with the functoriality of the real method
(`TauCeti.CompatibleCouple.kMethodENorm_map_le`) yields operator interpolation in Lorentz and
Lebesgue gauges (`TauCeti.CompatibleCouple.eLorentzNorm_map_le_of_lebesgue_one_top`,
`TauCeti.CompatibleCouple.eLpNorm_map_le_of_lebesgue_one_top`). As a check, the `K`-method norm
of an indicator `c 1_A` is `c_{θ, q} ‖c‖ μ(A) ^ (1 - θ)`
(`TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_indicator`).

As in `TauCeti.Analysis.Normed.Interpolation.L1Linfty`, Peetre's formula assumes `[NormedSpace ℝ E]`
in addition to `[NormedSpace 𝕜 E]`.

## Main declarations

* `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_sumSpaceEmbed`: the `K`-method norms of
  `l1Linfty` and `lebesgue 𝕜 E μ 1 ∞` agree under `sumSpaceEmbed`.
* `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_eq`,
  `TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_eq`: expression of the `K`-method norm
  in terms of `∫₀ᵗ ‖f‖*`.
* `TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_l1Linfty`,
  `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_le_mul_eLorentzNorm` (and `lebesgue_one_top`
  variants): two-sided equivalence `‖f‖_{L^{p, q}} ≤ ‖u‖_{θ, q} ≤ θ⁻¹ ‖f‖_{L^{p, q}}`.
* `TauCeti.CompatibleCouple.exists_toAEEqFun_mem_kMethod_l1Linfty_iff`,
  `TauCeti.CompatibleCouple.exists_toAEEqFun_mem_kMethod_lebesgue_one_top_iff`: membership
  characterization `(L¹, L^∞)_{θ, q} = L^{p, q}`.
* `TauCeti.CompatibleCouple.lebesgueOneTopKMethodEquivLp`: the continuous linear equivalence
  `(L¹, L^∞)_{θ, p} ≃L[𝕜] Lᵖ` for `0 < θ < 1` and `p.toReal⁻¹ = 1 - θ`.
* `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_indicator`,
  `TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_indicator`: exact formula on indicators.
* `TauCeti.CompatibleCouple.eLorentzNorm_map_le_of_lebesgue_one_top`,
  `TauCeti.CompatibleCouple.eLpNorm_map_le_of_lebesgue_one_top`: operator interpolation bounds in
  Lorentz and `Lᵖ` gauges.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.2–5.3 (Theorems 5.2.1 and 5.3.1).
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*,
  Princeton University Press, 1971, Chapter V, §3.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {𝕜 E : Type*} {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### Agreement of `l1Linfty` and `lebesgue 𝕜 E μ 1 ∞` -/

/-- The `K`-method norms of `l1Linfty` and `lebesgue 𝕜 E μ 1 ∞` agree under `sumSpaceEmbed`. -/
theorem kMethodENorm_l1Linfty_sumSpaceEmbed (θ : ℝ) (q : ℝ≥0∞)
    (v : (lebesgue 𝕜 E μ 1 ∞).SumSpace) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v) =
      (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [kMethodENorm_def, kMethodENorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with t ht
  rw [kFunctional_l1Linfty_sumSpaceEmbed ht.le]

/-- Membership in the real interpolation space agrees between `l1Linfty` and `lebesgue 𝕜 E μ 1 ∞`
under `sumSpaceEmbed`. -/
theorem sumSpaceEmbed_mem_kMethod_l1Linfty_iff {θ : ℝ} {q : ℝ≥0∞}
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} :
    (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔
      v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q := by
  simp only [mem_kMethod_iff, kMethodENorm_l1Linfty_sumSpaceEmbed]

/-! ### Integral formula and Lorentz norm equivalence -/

variable [NormedSpace ℝ E]

/-- Formula for the `K`-method norm of `l1Linfty` in terms of the decreasing rearrangement. -/
theorem kMethodENorm_l1Linfty_eq {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (θ : ℝ) (q : ℝ≥0∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u =
      eLpNorm (fun t : ℝ ↦
        ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s)
        q multHaar := by
  have hg₁ : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u)
      multHaar := aestronglyMeasurable_rpow_neg_mul_kFunctional θ u
  have heq : ∀ᵐ t ∂multHaar,
      ‖t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u‖ₑ =
        ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ofReal_kFunctional_l1Linfty hu ht.le]
  have hg₂ : AEStronglyMeasurable (fun t : ℝ ↦
        ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s)
      multHaar := (hg₁.eNorm.congr heq).aestronglyMeasurable
  rw [kMethodENorm_def]
  exact eLpNorm_congr_eNorm_ae hg₁ hg₂ (heq.mono fun _ ht ↦ by simp only [eNorm_eq_self, ht])

/-- Formula for the `K`-method norm of `lebesgue 𝕜 E μ 1 ∞` in terms of the decreasing
rearrangement. -/
theorem kMethodENorm_lebesgue_one_top_eq {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (θ : ℝ) (q : ℝ≥0∞) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v =
      eLpNorm (fun t : ℝ ↦
        ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s)
        q multHaar := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed, kMethodENorm_l1Linfty_eq hv]

/-- **Lower bound for the `K`-method norm of `(L¹, L^∞)`.** For `u ∈ L¹ + L^∞` represented by `f`
and `p.toReal⁻¹ = 1 - θ`, `‖f‖_{L^{p, q}} ≤ ‖u‖_{θ, q}` for every `q ∈ [0, ∞]`. -/
theorem eLorentzNorm_le_kMethodENorm_l1Linfty {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} {p q : ℝ≥0∞}
    (hp : p.toReal⁻¹ = 1 - θ) :
    eLorentzNorm f p q μ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  rw [eLorentzNorm_def]
  simp only [hp0, ↓reduceIte, hp, kMethodENorm_l1Linfty_eq hu]
  exact eLpNorm_rpow_one_sub_le_eLpNorm_rpow_neg_mul_lintegral_Ioc
    ((μ.antitone_decreasingRearrangement _).antitoneOn _) θ q

/-- **Lower bound for the `K`-method norm of `lebesgue 𝕜 E μ 1 ∞`.** For `v` represented by `f`
and `p.toReal⁻¹ = 1 - θ`, `‖f‖_{L^{p, q}} ≤ ‖v‖_{θ, q}` for every `q ∈ [0, ∞]`. -/
theorem eLorentzNorm_le_kMethodENorm_lebesgue_one_top {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} {p q : ℝ≥0∞} (hp : p.toReal⁻¹ = 1 - θ) :
    eLorentzNorm f p q μ ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact eLorentzNorm_le_kMethodENorm_l1Linfty hv hp

/-- **Upper bound for the `K`-method norm of `(L¹, L^∞)`.** By the weighted Hardy inequality, for
`0 < θ`, `p ≠ 0` with `p.toReal⁻¹ = 1 - θ`, and `1 ≤ q ≤ ∞`,
`‖u‖_{θ, q} ≤ θ⁻¹ ‖f‖_{L^{p, q}}`. -/
theorem kMethodENorm_l1Linfty_le_mul_eLorentzNorm {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) (hq : 1 ≤ q) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [kMethodENorm_l1Linfty_eq hu, eLorentzNorm_def]
  simp only [hp0, ↓reduceIte, hp]
  exact eLpNorm_rpow_neg_mul_lintegral_Ioc_le hθ hq _

/-- **Upper bound for the `K`-method norm of `lebesgue 𝕜 E μ 1 ∞`.** For `0 < θ`, `p ≠ 0` with
`p.toReal⁻¹ = 1 - θ`, and `1 ≤ q ≤ ∞`, `‖v‖_{θ, q} ≤ θ⁻¹ ‖f‖_{L^{p, q}}`. -/
theorem kMethodENorm_lebesgue_one_top_le_mul_eLorentzNorm {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) (hq : 1 ≤ q) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact kMethodENorm_l1Linfty_le_mul_eLorentzNorm hv hθ hp0 hp hq

/-! ### Membership characterization `(L¹, L^∞)_{θ, q} = L^{p, q}` -/

/-- `p.toReal⁻¹ = 1 - θ` with `θ < 1` forces `0 < p < ∞`. -/
private theorem ne_zero_and_ne_top_of_inv_toReal_eq_one_sub {θ : ℝ} (hθ : θ < 1) {p : ℝ≥0∞}
    (hp : p.toReal⁻¹ = 1 - θ) : p ≠ 0 ∧ p ≠ ∞ := by
  have hp_pos : 0 < p.toReal := inv_pos.1 (by linarith)
  exact ⟨by rintro rfl; simp at hp_pos, by rintro rfl; simp at hp_pos⟩

omit [NormedSpace ℝ E] in
/-- A function with finite weak-`Lᵖ` gauge (`1 / p = 1 - θ`, `0 < θ < 1`) satisfies
`∫₀¹ ‖f‖* < ∞`, and hence represents an element of `L¹ + L^∞`. -/
private theorem lintegral_Ioc_zero_one_decreasingRearrangement_lt_top {f : α → E} {θ : ℝ}
    (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞} (hp : p.toReal⁻¹ = 1 - θ)
    (hfin : eLorentzNorm f p ∞ μ < ∞) :
    ∫⁻ s in Ioc 0 1, μ.decreasingRearrangement (‖f ·‖ₑ) s < ∞ := by
  obtain ⟨hp0, _⟩ := ne_zero_and_ne_top_of_inv_toReal_eq_one_sub hθ.2 hp
  set M : ℝ≥0∞ := eLorentzNorm f p ∞ μ with hM_def
  have hbound : ∀ s : ℝ, 0 < s →
      μ.decreasingRearrangement (‖f ·‖ₑ) s ≤ M * ENNReal.ofReal (s ^ (θ - 1)) := fun s hs ↦ by
    have hle : ENNReal.ofReal (s ^ (1 - θ)) * μ.decreasingRearrangement (‖f ·‖ₑ) s ≤ M := by
      rw [hM_def, eLorentzNorm_exponent_top_right f hp0 μ, hp]
      exact le_iSup₂_of_le s hs le_rfl
    have hmul := mul_le_mul_right hle (ENNReal.ofReal (s ^ (θ - 1)))
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← Real.rpow_add hs,
      show θ - 1 + (1 - θ) = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      mul_comm (ENNReal.ofReal _)] at hmul
    exact hmul
  have hint_eq : ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (θ - 1)) =
      ∫⁻ s in Iic (1 : ℝ), ENNReal.ofReal (s ^ θ) ∂multHaar := by
    rw [multHaar_def, ← lintegral_indicator measurableSet_Iic,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _
        measurable_inv.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
      ← Ioi_inter_Iic, inter_comm, ← setLIntegral_indicator measurableSet_Iic]
    refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
    dsimp only [Pi.mul_apply]
    by_cases hs1 : s ≤ 1
    · rw [indicator_of_mem (mem_Iic.2 hs1), indicator_of_mem (mem_Iic.2 hs1),
        ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le), ← Real.rpow_neg_one s, ← Real.rpow_add hs,
        neg_add_eq_sub]
    · rw [indicator_of_notMem (by simpa using hs1), indicator_of_notMem (by simpa using hs1),
        mul_zero]
  calc ∫⁻ s in Ioc (0 : ℝ) 1, μ.decreasingRearrangement (‖f ·‖ₑ) s
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1, M * ENNReal.ofReal (s ^ (θ - 1)) :=
          setLIntegral_mono' measurableSet_Ioc fun s hs ↦ hbound s hs.1
    _ = M * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (θ - 1)) :=
          lintegral_const_mul' _ _ hfin.ne
    _ = M * ENNReal.ofReal (1 ^ θ * θ⁻¹) := by
          rw [hint_eq, lintegral_Iic_multHaar_rpow hθ.1 one_pos]
    _ < ∞ := ENNReal.mul_lt_top hfin ENNReal.ofReal_lt_top

/-- **Real interpolation identification `(L¹, L^∞)_{θ, q} = L^{p, q}`.** For `0 < θ < 1`,
`p.toReal⁻¹ = 1 - θ`, and `1 ≤ q ≤ ∞`, a function `f` represents an element of
`(l1Linfty 𝕜 E μ).kMethod θ q` if and only if it is almost everywhere strongly measurable and has
finite Lorentz gauge `eLorentzNorm f p q μ < ∞`. -/
theorem exists_toAEEqFun_mem_kMethod_l1Linfty_iff {f : α → E} {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {p q : ℝ≥0∞} (hp : p.toReal⁻¹ = 1 - θ) (hq : 1 ≤ q) :
    (∃ u ∈ (l1Linfty 𝕜 E μ).kMethod θ q, ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) ↔
      AEStronglyMeasurable f μ ∧ eLorentzNorm f p q μ < ∞ := by
  refine ⟨fun ⟨u, hu_mem, hu⟩ ↦ ⟨(AEEqFun.aestronglyMeasurable _).congr hu,
      (eLorentzNorm_le_kMethodENorm_l1Linfty hu hp).trans_lt (mem_kMethod_iff.1 hu_mem)⟩,
    fun ⟨hf, hfin⟩ ↦ ?_⟩
  obtain ⟨hp0, hptop⟩ := ne_zero_and_ne_top_of_inv_toReal_eq_one_sub hθ.2 hp
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hweak_fin : eLorentzNorm f p ∞ μ < ∞ :=
    (eLorentzNorm_top_le_mul_eLorentzNorm f hp0 hptop hq0 μ).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hint_fin : ∫⁻ s in Ioc 0 1, μ.decreasingRearrangement (‖f ·‖ₑ) s < ∞ :=
    lintegral_Ioc_zero_one_decreasingRearrangement_lt_top hθ hp hweak_fin
  obtain ⟨u, hu⟩ :=
    (L1AddLinfty.exists_toAEEqFun_ae_eq_iff_lintegral_decreasingRearrangement_lt_top
      (𝕜 := 𝕜) one_pos).2 ⟨hf, hint_fin⟩
  refine ⟨u, mem_kMethod_iff.2 ?_, hu⟩
  exact (kMethodENorm_l1Linfty_le_mul_eLorentzNorm hu hθ.1 hp0 hp hq).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

/-- **Real interpolation identification `(L¹, L^∞)_{θ, q} = L^{p, q}` for `lebesgue 𝕜 E μ 1 ∞`.**
For `0 < θ < 1`, `p.toReal⁻¹ = 1 - θ`, and `1 ≤ q ≤ ∞`, a function `f` represents an element of
`(lebesgue 𝕜 E μ 1 ∞).kMethod θ q` if and only if it is almost everywhere strongly measurable and
has finite Lorentz gauge `eLorentzNorm f p q μ < ∞`. -/
theorem exists_toAEEqFun_mem_kMethod_lebesgue_one_top_iff {f : α → E} {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {p q : ℝ≥0∞} (hp : p.toReal⁻¹ = 1 - θ) (hq : 1 ≤ q) :
    (∃ v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q,
        ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) ↔
      AEStronglyMeasurable f μ ∧ eLorentzNorm f p q μ < ∞ := by
  rw [← exists_toAEEqFun_mem_kMethod_l1Linfty_iff (𝕜 := 𝕜) hθ hp hq]
  refine ⟨fun ⟨v, hv, hvf⟩ ↦ ⟨_, sumSpaceEmbed_mem_kMethod_l1Linfty_iff.2 hv, hvf⟩,
    fun ⟨u, hu, huf⟩ ↦ ?_⟩
  obtain ⟨v, rfl⟩ := lebesgue_one_top_sumSpaceEmbed_surjective (𝕜 := 𝕜) (E := E) (μ := μ) u
  exact ⟨v, sumSpaceEmbed_mem_kMethod_l1Linfty_iff.1 hu, huf⟩

/-! ### Diagonal Banach space isomorphism `(L¹, L^∞)_{θ, p} ≃L[𝕜] Lᵖ` -/

private theorem eLpNorm_toAEEqFun_le_kMethodENorm {θ : ℝ} {p : ℝ≥0∞}
    (hp : p.toReal⁻¹ = 1 - θ) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    eLpNorm (L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u))) p μ ≤
      (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ p (KMethodSpace.toSumₗ u) := by
  rw [← eLorentzNorm_self (AEEqFun.aestronglyMeasurable _) p]
  exact eLorentzNorm_le_kMethodENorm_lebesgue_one_top Filter.EventuallyEq.rfl hp

private theorem kMethodENorm_lpToLebesgueSum_le {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p.toReal⁻¹ = 1 - θ) (f : Lp E p μ) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ p (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f) ≤
      ENNReal.ofReal θ⁻¹ * eLpNorm f p μ := by
  obtain ⟨hp0, _⟩ := ne_zero_and_ne_top_of_inv_toReal_eq_one_sub hθ.2 hp
  have hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
      (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f))) =ᵐ[μ] ⇑f := by
    rw [sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
  rw [← eLorentzNorm_self (Lp.aestronglyMeasurable f) p]
  exact kMethodENorm_lebesgue_one_top_le_mul_eLorentzNorm hv hθ.1 hp0 hp Fact.out

private def lebesgueOneTopKMethodToLp {θ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun u := ⟨L1AddLinfty.toAEEqFun 𝕜
          ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)),
        (eLpNorm_toAEEqFun_le_kMethodENorm hp u).trans_lt
          (mem_kMethod_iff.1 (KMethodSpace.toSumₗ_mem u))⟩
      map_add' _ _ := Subtype.ext (by simp)
      map_smul' c x := Lp.ext <| by
        dsimp only [RingHom.id_apply]
        rw [map_smul, map_smul, map_smul]
        exact (AEEqFun.coeFn_smul c _).trans (Lp.coeFn_smul c
          (⟨L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ x)),
            (eLpNorm_toAEEqFun_le_kMethodENorm hp x).trans_lt
              (mem_kMethod_iff.1 (KMethodSpace.toSumₗ_mem x))⟩ : Lp E p μ)).symm }
    1 fun u ↦ by
      change ‖(⟨_, _⟩ : Lp E p μ)‖ ≤ 1 * ‖u‖
      rw [one_mul, Lp.norm_def, KMethodSpace.norm_def]
      exact ENNReal.toReal_mono (mem_kMethod_iff.1 (KMethodSpace.toSumₗ_mem u)).ne
        (eLpNorm_toAEEqFun_le_kMethodENorm hp u)

private def lpToLebesgueOneTopKMethod {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p.toReal⁻¹ = 1 - θ) :
    Lp E p μ →L[𝕜] (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p :=
  LinearMap.mkContinuous
    { toFun f := KMethodSpace.mk (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f)
        (mem_kMethod_iff.2 ((kMethodENorm_lpToLebesgueSum_le hθ hp f).trans_lt
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp f).eLpNorm_lt_top)))
      map_add' _ _ := KMethodSpace.ext (by simp)
      map_smul' _ _ := KMethodSpace.ext (by simp) }
    θ⁻¹ fun f ↦ by
      change ‖KMethodSpace.mk _ _‖ ≤ θ⁻¹ * ‖f‖
      rw [KMethodSpace.norm_mk, Lp.norm_def, ← ENNReal.toReal_ofReal (inv_nonneg.2 hθ.1.le),
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f))
        (kMethodENorm_lpToLebesgueSum_le hθ hp f)

variable (𝕜) in
/-- **Diagonal real interpolation isomorphism `(L¹, L^∞)_{θ, p} ≃L[𝕜] Lᵖ`.** For `0 < θ < 1` and
`p` with `p.toReal⁻¹ = 1 - θ`, the real interpolation space `(L¹, L^∞)_{θ, p}` is linearly
homeomorphic to `Lp E p μ`, with forward norm at most `1`
(`norm_lebesgueOneTopKMethodEquivLp_le`) and inverse norm at most `θ⁻¹`
(`norm_lebesgueOneTopKMethodEquivLp_symm_le`). -/
def lebesgueOneTopKMethodEquivLp {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p ≃L[𝕜] Lp E p μ :=
  ContinuousLinearEquiv.equivOfInverse
    (lebesgueOneTopKMethodToLp hp)
    (lpToLebesgueOneTopKMethod hθ hp)
    (fun u ↦ KMethodSpace.ext <| (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective <|
      L1AddLinfty.toAEEqFun_injective <| by
        change L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
            (KMethodSpace.toSumₗ (KMethodSpace.mk
              (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top (lebesgueOneTopKMethodToLp hp u)) _))) = _
        rw [KMethodSpace.toSumₗ_mk, sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
        rfl)
    (fun f ↦ Subtype.ext <| by
        change L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
            (KMethodSpace.toSumₗ (KMethodSpace.mk
              (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f) _))) = _
        rw [KMethodSpace.toSumₗ_mk, sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp])

@[simp]
theorem toAEEqFun_lebesgueOneTopKMethodEquivLp {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p.toReal⁻¹ = 1 - θ) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    (lebesgueOneTopKMethodEquivLp 𝕜 hθ hp u : α →ₘ[μ] E) =
      L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)) :=
  (rfl)

@[simp]
theorem ofLp_lebesgueOneTopKMethodEquivLp {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p.toReal⁻¹ = 1 - θ) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    (L1AddLinfty.ofLp (lebesgueOneTopKMethodEquivLp 𝕜 hθ hp u) : L1AddLinfty 𝕜 E μ) =
      (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u) :=
  L1AddLinfty.toAEEqFun_injective (by simp)

@[simp]
theorem toSumₗ_lebesgueOneTopKMethodEquivLp_symm {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p.toReal⁻¹ = 1 - θ) (f : Lp E p μ) :
    KMethodSpace.toSumₗ ((lebesgueOneTopKMethodEquivLp 𝕜 hθ hp).symm f) =
      lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f :=
  KMethodSpace.toSumₗ_mk _ _

@[simp]
theorem lebesgueOneTopKMethodEquivLp_ofInter {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p.toReal⁻¹ = 1 - θ) (x : (lebesgue 𝕜 E μ 1 ∞).inter) :
    lebesgueOneTopKMethodEquivLp 𝕜 hθ hp (KMethodSpace.ofInter θ p hθ x) =
      lebesgueInterToLp (Fact.out : 1 ≤ p) le_top x :=
  L1AddLinfty.ofLp_injective (𝕜 := 𝕜) (by
    rw [ofLp_lebesgueOneTopKMethodEquivLp, KMethodSpace.toSumₗ_ofInter, sumSpaceEmbed_fstToSum,
      lebesgue_embed₀, interFst_apply, ofLp_lebesgueInterToLp])

theorem norm_lebesgueOneTopKMethodEquivLp_le {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p.toReal⁻¹ = 1 - θ) (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ‖lebesgueOneTopKMethodEquivLp 𝕜 hθ hp u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def, KMethodSpace.norm_def]
  exact ENNReal.toReal_mono (mem_kMethod_iff.1 (KMethodSpace.toSumₗ_mem u)).ne
    (eLpNorm_toAEEqFun_le_kMethodENorm hp u)

theorem norm_lebesgueOneTopKMethodEquivLp_symm_le {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p.toReal⁻¹ = 1 - θ) (f : Lp E p μ) :
    ‖(lebesgueOneTopKMethodEquivLp 𝕜 hθ hp).symm f‖ ≤ θ⁻¹ * ‖f‖ := by
  rw [KMethodSpace.norm_def, toSumₗ_lebesgueOneTopKMethodEquivLp_symm, Lp.norm_def,
    ← ENNReal.toReal_ofReal (inv_nonneg.2 hθ.1.le), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f))
    (kMethodENorm_lpToLebesgueSum_le hθ hp f)

/-! ### Exact `K`-method norm on indicator functions -/

/-- Exact `K`-method norm of an indicator `c 1_A` in `(L¹, L^∞)`: for `θ < 1` and every
`q ∈ [0, ∞]`, `‖c 1_A‖_{θ, q} = c_{θ, q} ‖c‖ μ(A) ^ (1 - θ)`. -/
theorem kMethodENorm_l1Linfty_indicator {u : L1AddLinfty 𝕜 E μ} {A : Set α} {c : E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ ↦ c)
    {θ : ℝ} (hθ : θ < 1) (q : ℝ≥0∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ
  have hmeas_min : AEStronglyMeasurable (fun s : ℝ ↦ s ^ (-θ) * min 1 s) multHaar :=
    ((continuousOn_id.rpow_const fun _ ht ↦ Or.inl (ne_of_gt ht)).mul
      (continuous_const.min continuous_id).continuousOn).aestronglyMeasurable_multHaar
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [kMethodENorm_def, kMethodConst_def,
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
  · set p : ℝ≥0∞ := ENNReal.ofReal (1 - θ)⁻¹
    have hp0 : p ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 h1θ)).ne'
    have hptop : p ≠ ∞ := ENNReal.ofReal_ne_top
    have hp : p.toReal⁻¹ = 1 - θ := by
      rw [ENNReal.toReal_ofReal (inv_nonneg.2 h1θ.le), inv_inv]
    have hlo : eLorentzNorm (A.indicator fun _ ↦ c) p q μ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u :=
      eLorentzNorm_le_kMethodENorm_l1Linfty hu hp
    rw [eLorentzNorm_indicator A c hp0 hptop hq0 μ, hp, hAtop, ENNReal.top_rpow_of_pos h1θ] at hlo
    have hpref0 : ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) ≠ 0 := by
      rcases eq_or_ne q ∞ with rfl | hqtop
      · simp
      · exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos
          (div_pos (ENNReal.toReal_pos hp0 hptop) (ENNReal.toReal_pos hq0 hqtop)) _)).ne'
    rw [ENNReal.mul_top (ENNReal.mul_pos hpref0 hc0).ne'] at hlo
    rw [eq_top_iff.2 hlo, hAtop, ENNReal.top_rpow_of_pos h1θ,
      ENNReal.mul_top (ENNReal.mul_pos (kMethodConst_ne_zero θ hq0) hc0).ne']
  -- Finite positive measure: reduce to `kMethodConst θ q` by dilation `t ↦ (μ A)⁻¹ * t`.
  set m : ℝ := (μ A).toReal
  have hm : 0 < m := ENNReal.toReal_pos hA0 hAtop
  have hm_eq : ENNReal.ofReal m = μ A := ENNReal.ofReal_toReal hAtop
  have hc_eNorm : ENNReal.ofReal ‖c‖ = ‖c‖ₑ := by
    rw [← Real.eNorm_of_nonneg (norm_nonneg c), eNorm_norm]
  have hmp : MeasurePreserving (m⁻¹ * ·) multHaar multHaar :=
    ⟨measurable_const_mul m⁻¹, map_multHaar_mul_left (inv_pos.2 hm)⟩
  have heq : (fun t : ℝ ↦ t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) =ᵐ[multHaar]
      (‖c‖ * m ^ (1 - θ)) • ((fun s : ℝ ↦ s ^ (-θ) * min 1 s) ∘ (m⁻¹ * ·)) := by
    filter_upwards [ae_pos_multHaar] with t ht
    have hK_ofReal : ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) =
        ENNReal.ofReal (‖c‖ * min t m) := by
      rw [ofReal_kFunctional_l1Linfty_indicator hu ht.le, ← hm_eq, ← hc_eNorm,
        ← ENNReal.ofReal_min, ENNReal.ofReal_mul (norm_nonneg c)]
    have hK : (l1Linfty 𝕜 E μ).kFunctional t u = ‖c‖ * min t m := by
      have := congrArg ENNReal.toReal hK_ofReal
      rwa [ENNReal.toReal_ofReal (kFunctional_nonneg ht.le),
        ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg c) (le_min ht.le hm.le))] at this
    rw [hK, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    have hmin : min t m = m * min 1 (m⁻¹ * t) := by
      rw [mul_min_of_nonneg _ _ hm.le, mul_one, mul_inv_cancel_left₀ hm.ne', min_comm]
    rw [hmin, Real.mul_rpow (inv_nonneg.2 hm.le) ht.le, Real.inv_rpow hm.le,
      Real.rpow_neg hm.le, inv_inv, show m ^ (1 - θ) = m ^ (-θ) * m by
        rw [← Real.rpow_add_one hm.ne', neg_add_eq_sub]]
    have hmθ : m ^ θ ≠ 0 := (Real.rpow_pos_of_pos hm θ).ne'
    rw [Real.rpow_neg hm.le]
    field_simp [hmθ]
  rw [kMethodENorm_def, eLpNorm_congr_ae heq, eLpNorm_const_smul,
    eLpNorm_comp_measurePreserving hmeas_min hmp, ← kMethodConst_def,
    Real.eNorm_of_nonneg (mul_nonneg (norm_nonneg c) (Real.rpow_nonneg hm.le _)),
    ENNReal.ofReal_mul (norm_nonneg c), hc_eNorm,
    ← ENNReal.ofReal_rpow_of_pos hm, hm_eq]
  ring

/-- Exact `K`-method norm of an indicator `c 1_A` in `lebesgue 𝕜 E μ 1 ∞`: for `θ < 1` and every
`q ∈ [0, ∞]`, `‖c 1_A‖_{θ, q} = c_{θ, q} ‖c‖ μ(A) ^ (1 - θ)`. -/
theorem kMethodENorm_lebesgue_one_top_indicator {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {A : Set α}
    {c : E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ]
      A.indicator fun _ ↦ c)
    {θ : ℝ} (hθ : θ < 1) (q : ℝ≥0∞) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed, kMethodENorm_l1Linfty_indicator hv hθ q]

/-! ### Operator interpolation in Lorentz and Lebesgue gauges -/

section Map

variable {β F : Type*} {mβ : MeasurableSpace β} {ν : Measure β}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]

/-- **Operator interpolation in Lorentz gauges.** A linear map `T` between the sum spaces of
`(L¹(μ; E), L^∞(μ; E))` and `(L¹(ν; F), L^∞(ν; F))` restricting to maps with `L¹` bound `M₀ > 0`
and `L^∞` bound `M₁ > 0` satisfies
`‖T v‖_{L^{p, q}(ν)} ≤ θ⁻¹ M₀ ^ (1 - θ) M₁ ^ θ ‖v‖_{L^{p, q}(μ)}`
for `0 < θ`, `p ≠ 0` with `p.toReal⁻¹ = 1 - θ`, and `1 ≤ q ≤ ∞`. -/
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
    {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) (hq : 1 ≤ q) :
    eLorentzNorm g p q ν ≤
      ENNReal.ofReal (θ⁻¹ * M₀ ^ (1 - θ) * M₁ ^ θ) * eLorentzNorm f p q μ := by
  calc eLorentzNorm g p q ν
      ≤ (lebesgue 𝕜 F ν 1 ∞).kMethodENorm θ q (T v) :=
          eLorentzNorm_le_kMethodENorm_lebesgue_one_top hTv hp
    _ ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v :=
          kMethodENorm_map_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁ v
    _ ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * (ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ) := by
          gcongr
          exact kMethodENorm_lebesgue_one_top_le_mul_eLorentzNorm hv hθ hp0 hp hq
    _ = ENNReal.ofReal (θ⁻¹ * M₀ ^ (1 - θ) * M₁ ^ θ) * eLorentzNorm f p q μ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring

/-- **Diagonal operator interpolation in `Lᵖ` gauges.** Under the same hypotheses as
`eLorentzNorm_map_le_of_lebesgue_one_top` with `q = p` and `1 ≤ p`,
`‖T v‖_{Lᵖ(ν)} ≤ θ⁻¹ M₀ ^ (1 - θ) M₁ ^ θ ‖v‖_{Lᵖ(μ)}`. -/
theorem eLpNorm_map_le_of_lebesgue_one_top
    (T : (lebesgue 𝕜 E μ 1 ∞).SumSpace →ₗ[𝕜] (lebesgue 𝕜 F ν 1 ∞).SumSpace)
    {T₀ : Lp E 1 μ → Lp F 1 ν} {T₁ : Lp E ∞ μ → Lp F ∞ ν}
    (hT₀ : ∀ x, T ((lebesgue 𝕜 E μ 1 ∞).fstToSum x) = (lebesgue 𝕜 F ν 1 ∞).fstToSum (T₀ x))
    (hT₁ : ∀ x, T ((lebesgue 𝕜 E μ 1 ∞).sndToSum x) = (lebesgue 𝕜 F ν 1 ∞).sndToSum (T₁ x))
    {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖)
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E} {g : β → F}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (hTv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 F ν 1 ∞).sumSpaceEmbed (T v))) =ᵐ[ν] g)
    {θ : ℝ} (hθ : 0 < θ) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p.toReal⁻¹ = 1 - θ) :
    eLpNorm g p ν ≤ ENNReal.ofReal (θ⁻¹ * M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p μ := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hv
  have hg : AEStronglyMeasurable g ν := (AEEqFun.aestronglyMeasurable _).congr hTv
  rw [← eLorentzNorm_self hf p, ← eLorentzNorm_self hg p]
  exact eLorentzNorm_map_le_of_lebesgue_one_top T hT₀ hT₁ hM₀ hM₁ h₀ h₁ hv hTv hθ
    (zero_lt_one.trans_le hp1).ne' hp hp1

end Map

end TauCeti.CompatibleCouple
