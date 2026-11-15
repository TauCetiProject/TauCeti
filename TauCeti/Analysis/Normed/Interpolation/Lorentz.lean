/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.L1Linfty
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
public import TauCeti.MeasureTheory.Function.LorentzSeminorm.CompareExp
import TauCeti.MeasureTheory.Integral.Hardy

/-!
# Real interpolation of `(L¹, L^∞)` and Lorentz spaces

Combining Peetre's `K`-functional formula `K(t, u) = ∫₀ᵗ (‖f‖ₑ)*` for `(L¹, L^∞)`
(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty`) with Hardy's weighted inequality near `0`
(`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`) and the reverse antitone bound
(`TauCeti.eLpNorm_rpow_one_sub_mul_le_of_antitoneOn`) identifies the real interpolation spaces of
`(L¹(μ; E), L^∞(μ; E))` with the Lorentz classes `L^{p,q}(μ; E)` for `1 / p = 1 - θ`:

`‖f‖_{L^{p,q}} ≤ ‖u‖_{θ,q} ≤ θ⁻¹ ‖f‖_{L^{p,q}}`

for every `θ > 0` and `1 ≤ q ≤ ∞`, where `E` is a normed space over both `ℝ` and the scalar field
`𝕜` of the couple. In particular:
* For `0 < θ < 1`, `p = (1 - θ)⁻¹`, and `1 ≤ q ≤ ∞`, an element of `L¹ + L^∞` belongs to
  `(L¹, L^∞)_{θ,q}` iff any representing function belongs to `L^{p,q}(μ; E)`, and conversely every
  function in `L^{p,q}(μ; E)` represents a unique element of `(L¹, L^∞)_{θ,q}`.
* At the endpoint `θ = 1` (`p = ∞`), the constants match at `1`, giving the exact norm identity
  `‖u‖_{1,q} = ‖f‖_{L^{∞,q}}` for `1 ≤ q ≤ ∞` (and `‖u‖_{1,∞} = ‖f‖_{L^∞}`).
* On the diagonal `q = p` (`1 < p ≤ ∞`, `θ = 1 - 1 / p`), `L^{p,p} = Lᵖ`, yielding a continuous
  linear isomorphism `(L¹, L^∞)_{1 - 1/p, p} ≃L[𝕜] Lᵖ(μ; E)`
  (`TauCeti.CompatibleCouple.lebesgueOneTopKMethodEquivLp`).

## Main declarations

* `TauCeti.MemLorentz.exists_l1AddLinfty_toAEEqFun_ae_eq`,
  `TauCeti.MemLorentz.exists_lebesgue_one_top_sumSpace_ae_eq`: every function in `L^{p,q}` with
  `1 < p ≤ ∞` and `q ≠ 0` represents an element of `L¹ + L^∞`.
* `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_eq_eLpNorm`,
  `TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_eq_eLpNorm`: rearrangement integral
  formula for the `K`-method norm of `(L¹, L^∞)`.
* `TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_l1Linfty`,
  `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_le_eLorentzNorm`: sharp two-sided norm bounds
  between `(L¹, L^∞)_{θ,q}` and `L^{p,q}` (`1 / p = 1 - θ`), along with their counterparts for
  `lebesgue 𝕜 E μ 1 ∞` and `KMethodSpace`.
* `TauCeti.CompatibleCouple.mem_kMethod_l1Linfty_iff_memLorentz`,
  `TauCeti.CompatibleCouple.mem_kMethod_lebesgue_one_top_iff_memLorentz`,
  `TauCeti.CompatibleCouple.memLorentz_iff_exists_mem_kMethod_lebesgue_one_top`: exact membership
  characterizations `(L¹, L^∞)_{θ,q} = L^{p,q}` for `0 < θ < 1` and `1 ≤ q ≤ ∞`.
* `TauCeti.CompatibleCouple.lebesgueOneTopKMethodEquivLp`: the continuous linear equivalence
  `(L¹, L^∞)_{1 - 1/p, p} ≃L[𝕜] Lᵖ(μ; E)` for `1 < p ≤ ∞`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.2–5.3 (Theorems 5.2.1 and 5.3.1).
* C. Bennett and R. Sharpley, *Interpolation of Operators*, Academic Press, 1988, Chapter 4,
  Theorem 4.3.
-/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section Representability

variable {E α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]

/-- Every function in `L^{p,q}(μ; E)` with `1 < p ≤ ∞` and `q ≠ 0` represents an element of
`L¹ + L^∞`. -/
theorem MemLorentz.exists_l1AddLinfty_toAEEqFun_ae_eq (𝕜 : Type*) [NormedField 𝕜]
    [NormedSpace 𝕜 E] {f : α → E} {p q : ℝ≥0∞} (hf : MemLorentz f p q μ) (hp : 1 < p)
    (hq : q ≠ 0) :
    ∃ u : L1AddLinfty 𝕜 E μ, ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f :=
  (L1AddLinfty.exists_toAEEqFun_ae_eq_iff_lintegral_decreasingRearrangement_lt_top one_pos).2
    ⟨hf.aestronglyMeasurable, hf.setLIntegral_decreasingRearrangement_lt_top hp hq zero_le_one⟩

/-- Every function in `L^{p,q}(μ; E)` with `1 < p ≤ ∞` and `q ≠ 0` represents an element of the
sum space of the Lebesgue couple `(L¹, L^∞)`. -/
theorem MemLorentz.exists_lebesgue_one_top_sumSpace_ae_eq (𝕜 : Type*) [NormedField 𝕜]
    [NormedSpace 𝕜 E] {f : α → E} {p q : ℝ≥0∞} (hf : MemLorentz f p q μ) (hp : 1 < p)
    (hq : q ≠ 0) :
    ∃ v : (CompatibleCouple.lebesgue 𝕜 E μ 1 ∞).SumSpace,
      ⇑(L1AddLinfty.toAEEqFun 𝕜 ((CompatibleCouple.lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ]
        f := by
  obtain ⟨u, hu⟩ := hf.exists_l1AddLinfty_toAEEqFun_ae_eq 𝕜 hp hq
  obtain ⟨v, rfl⟩ := CompatibleCouple.lebesgue_one_top_sumSpaceEmbed_surjective u
  exact ⟨v, hu⟩

end Representability

namespace CompatibleCouple

variable {𝕜 E α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### Transport between `l1Linfty` and the Lebesgue couple `(L¹, L^∞)` -/

/-- The Lebesgue couple `(L¹, L^∞)` and `l1Linfty` have the same `K`-functional, hence the same
`K`-method norm, read through `sumSpaceEmbed`. -/
@[simp]
theorem kMethodENorm_l1Linfty_sumSpaceEmbed (θ : ℝ) (q : ℝ≥0∞)
    (v : (lebesgue 𝕜 E μ 1 ∞).SumSpace) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v) =
      (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [kMethodENorm_def, kMethodENorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with t ht
  rw [kFunctional_l1Linfty_sumSpaceEmbed ht.le]

/-- An element `v` of the sum space of the Lebesgue couple `(L¹, L^∞)` lies in `(L¹, L^∞)_{θ,q}`
iff its image in `L¹ + L^∞` lies in the `K`-method space of `l1Linfty`. -/
@[simp]
theorem mem_kMethod_l1Linfty_sumSpaceEmbed_iff {θ : ℝ} {q : ℝ≥0∞}
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} :
    (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔
      v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q := by
  rw [mem_kMethod_iff, mem_kMethod_iff, kMethodENorm_l1Linfty_sumSpaceEmbed]

variable [NormedSpace ℝ E]

/-! ### Rearrangement formula and two-sided Lorentz norm bounds -/

/-- **Rearrangement formula for the `K`-method norm of `(L¹, L^∞)`.** For an element `u` of
`L¹ + L^∞` represented by `f`, `‖u‖_{θ,q} = ‖t ↦ t ^ (-θ) ∫₀ᵗ (‖f‖ₑ)*‖_{L^q(dt / t)}`. -/
theorem kMethodENorm_l1Linfty_eq_eLpNorm {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (θ : ℝ) (q : ℝ≥0∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u =
      eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) *
        ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s) q multHaar := by
  rw [kMethodENorm_def, ← eLpNorm_eNorm _
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u)]
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with t ht
  rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ofReal_kFunctional_l1Linfty hu ht.le]

/-- **Rearrangement formula for the `K`-method norm of the Lebesgue couple `(L¹, L^∞)`.** -/
theorem kMethodENorm_lebesgue_one_top_eq_eLpNorm {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (θ : ℝ) (q : ℝ≥0∞) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v =
      eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) *
        ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s) q multHaar := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed, kMethodENorm_l1Linfty_eq_eLpNorm hv]

/-- **Lower bound `‖f‖_{L^{p,q}} ≤ ‖u‖_{θ,q}` for `(L¹, L^∞)`.** Whenever `p ≠ 0` and
`1 / p = 1 - θ`, the Lorentz gauge of any representative `f` of `u ∈ L¹ + L^∞` is bounded by the
`K`-method norm of `u`, with constant `1` and for all `q ∈ [0, ∞]`. -/
theorem eLorentzNorm_le_kMethodENorm_l1Linfty {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p.toReal⁻¹ = 1 - θ) (q : ℝ≥0∞) :
    eLorentzNorm f p q μ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  rw [eLorentzNorm_eq_eLpNorm_multHaar hp0 hf, hp, kMethodENorm_l1Linfty_eq_eLpNorm hu]
  exact eLpNorm_rpow_one_sub_mul_le_of_antitoneOn θ q
    ((μ.antitone_decreasingRearrangement (‖f ·‖ₑ)).antitoneOn _)

/-- **Lower bound `‖f‖_{L^{p,q}} ≤ ‖v‖_{θ,q}` for the Lebesgue couple `(L¹, L^∞)`.** -/
theorem eLorentzNorm_le_kMethodENorm_lebesgue_one_top {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E} (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) (q : ℝ≥0∞) :
    eLorentzNorm f p q μ ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact eLorentzNorm_le_kMethodENorm_l1Linfty hv hp0 hp q

/-- **Upper bound `‖u‖_{θ,q} ≤ θ⁻¹ ‖f‖_{L^{p,q}}` for `(L¹, L^∞)`.** For `θ > 0`, `1 ≤ q ≤ ∞`,
and `p ≠ 0` with `1 / p = 1 - θ`, Hardy's inequality bounds the `K`-method norm of `u` by `θ⁻¹`
times the Lorentz gauge of any representative `f`. -/
theorem kMethodENorm_l1Linfty_le_eLorentzNorm {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  rw [kMethodENorm_l1Linfty_eq_eLpNorm hu, eLorentzNorm_eq_eLpNorm_multHaar hp0 hf, hp]
  exact eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ hq _

/-- **Upper bound `‖v‖_{θ,q} ≤ θ⁻¹ ‖f‖_{L^{p,q}}` for the Lebesgue couple `(L¹, L^∞)`.** -/
theorem kMethodENorm_lebesgue_one_top_le_eLorentzNorm {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E} (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞} (hq : 1 ≤ q) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact kMethodENorm_l1Linfty_le_eLorentzNorm hv hθ hq hp0 hp

/-- At `θ = 1` (`p = ∞`) and `1 ≤ q ≤ ∞`, the lower and upper bounds match with constant `1`:
`‖u‖_{1,q} = ‖f‖_{L^{∞,q}}`. -/
theorem kMethodENorm_l1Linfty_one_eq_eLorentzNorm {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    (l1Linfty 𝕜 E μ).kMethodENorm 1 q u = eLorentzNorm f ∞ q μ := by
  refine le_antisymm ?_
    (eLorentzNorm_le_kMethodENorm_l1Linfty hu ENNReal.top_ne_zero (by simp) q)
  simpa using kMethodENorm_l1Linfty_le_eLorentzNorm hu one_pos hq ENNReal.top_ne_zero
    (p := ∞) (by simp)

/-- At `(θ, q) = (1, ∞)`, the `K`-method norm of `(L¹, L^∞)` equals the `L^∞` norm. -/
theorem kMethodENorm_l1Linfty_one_top_eq_eLpNorm {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    (l1Linfty 𝕜 E μ).kMethodENorm 1 ∞ u = eLpNorm f ∞ μ := by
  rw [kMethodENorm_l1Linfty_one_eq_eLorentzNorm hu le_top, eLorentzNorm_self]

/-- On the normed space `(L¹, L^∞)_{θ,q}`, `‖f‖_{L^{p,q}} ≤ ‖w‖ₑ` for `1 / p = 1 - θ`. -/
theorem eLorentzNorm_le_eNorm_kMethodSpace_lebesgue_one_top {θ : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ q)]
    {w : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ q} {f : α → E}
    (hw : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ w))) =ᵐ[μ] f)
    (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    eLorentzNorm f p q μ ≤ ‖w‖ₑ := by
  rw [← ofReal_norm, KMethodSpace.ofReal_norm]
  exact eLorentzNorm_le_kMethodENorm_lebesgue_one_top hw hp0 hp q

/-- On the normed space `(L¹, L^∞)_{θ,q}`, `‖w‖ₑ ≤ θ⁻¹ ‖f‖_{L^{p,q}}` for `θ > 0` and
`1 / p = 1 - θ`. -/
theorem eNorm_kMethodSpace_lebesgue_one_top_le_eLorentzNorm {θ : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ q)]
    {w : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ q} {f : α → E}
    (hw : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ w))) =ᵐ[μ] f)
    (hθ : 0 < θ) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    ‖w‖ₑ ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [← ofReal_norm, KMethodSpace.ofReal_norm]
  exact kMethodENorm_lebesgue_one_top_le_eLorentzNorm hw hθ Fact.out hp0 hp

/-! ### Exact membership characterizations `(L¹, L^∞)_{θ,q} = L^{p,q}` -/

private theorem one_lt_ofReal_inv_one_sub {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    1 < ENNReal.ofReal (1 - θ)⁻¹ :=
  ENNReal.one_lt_ofReal.2 ((one_lt_inv₀ (sub_pos.2 hθ.2)).2 (sub_lt_self 1 hθ.1))

private theorem toReal_inv_ofReal_inv_one_sub {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    (ENNReal.ofReal (1 - θ)⁻¹).toReal⁻¹ = 1 - θ := by
  rw [ENNReal.toReal_ofReal (inv_nonneg.2 (sub_nonneg.2 hθ.2.le)), inv_inv]

private theorem one_sub_toReal_inv_pos {p : ℝ≥0∞} (hp : 1 < p) : 0 < 1 - p.toReal⁻¹ := by
  rcases eq_or_ne p ∞ with rfl | hptop
  · simp
  · have hp_gt : 1 < p.toReal := by
      simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).2 hp
    exact sub_pos.2 (inv_lt_one_of_one_lt₀ hp_gt)

/-- For `θ > 0`, `1 ≤ q ≤ ∞`, and `p ≠ 0` with `1 / p = 1 - θ`, an element `u` of `L¹ + L^∞`
represented by `f` belongs to `(L¹, L^∞)_{θ,q}` iff `f ∈ L^{p,q}(μ; E)`. -/
theorem mem_kMethod_l1Linfty_iff_memLorentz_of_inv_eq {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    u ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔ MemLorentz f p q μ := by
  rw [mem_kMethod_iff, memLorentz_iff]
  exact ⟨fun h ↦ (eLorentzNorm_le_kMethodENorm_l1Linfty hu hp0 hp q).trans_lt h,
    fun h ↦ (kMethodENorm_l1Linfty_le_eLorentzNorm hu hθ hq hp0 hp).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)⟩

/-- For `θ > 0`, `1 ≤ q ≤ ∞`, and `p ≠ 0` with `1 / p = 1 - θ`, an element `v` of the sum space of
the Lebesgue couple `(L¹, L^∞)` represented by `f` belongs to `(L¹, L^∞)_{θ,q}` iff
`f ∈ L^{p,q}(μ; E)`. -/
theorem mem_kMethod_lebesgue_one_top_iff_memLorentz_of_inv_eq
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞} (hq : 1 ≤ q) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q ↔ MemLorentz f p q μ := by
  rw [← mem_kMethod_l1Linfty_sumSpaceEmbed_iff]
  exact mem_kMethod_l1Linfty_iff_memLorentz_of_inv_eq hv hθ hq hp0 hp

/-- **Real interpolation of `(L¹, L^∞)` is `L^{p,q}` (`0 < θ < 1`, `p = (1 - θ)⁻¹`).** -/
theorem mem_kMethod_l1Linfty_iff_memLorentz {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    u ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔ MemLorentz f (ENNReal.ofReal (1 - θ)⁻¹) q μ :=
  mem_kMethod_l1Linfty_iff_memLorentz_of_inv_eq hu hθ.1 hq
    (zero_lt_one.trans (one_lt_ofReal_inv_one_sub hθ)).ne' (toReal_inv_ofReal_inv_one_sub hθ)

/-- **Real interpolation of the Lebesgue couple `(L¹, L^∞)` is `L^{p,q}`
(`0 < θ < 1`, `p = (1 - θ)⁻¹`).** -/
theorem mem_kMethod_lebesgue_one_top_iff_memLorentz {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E} (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q ↔ MemLorentz f (ENNReal.ofReal (1 - θ)⁻¹) q μ :=
  mem_kMethod_lebesgue_one_top_iff_memLorentz_of_inv_eq hv hθ.1 hq
    (zero_lt_one.trans (one_lt_ofReal_inv_one_sub hθ)).ne' (toReal_inv_ofReal_inv_one_sub hθ)

variable (𝕜) in
/-- **Unconditional characterization of `L^{p,q}` via `(L¹, L^∞)_{θ,q}`** (`0 < θ < 1`,
`p = (1 - θ)⁻¹`, `1 ≤ q ≤ ∞`): an arbitrary function `f : α → E` belongs to `L^{p,q}(μ; E)` iff it
represents an element of `(L¹, L^∞)_{θ,q}` in `L¹ + L^∞`. -/
theorem memLorentz_iff_exists_mem_kMethod_l1Linfty
    {f : α → E} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    MemLorentz f (ENNReal.ofReal (1 - θ)⁻¹) q μ ↔
      ∃ u ∈ (l1Linfty 𝕜 E μ).kMethod θ q, ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f := by
  refine ⟨fun hf ↦ ?_,
    fun ⟨u, hu_mem, hu⟩ ↦ (mem_kMethod_l1Linfty_iff_memLorentz hu hθ hq).1 hu_mem⟩
  obtain ⟨u, hu⟩ := hf.exists_l1AddLinfty_toAEEqFun_ae_eq 𝕜 (one_lt_ofReal_inv_one_sub hθ)
    (zero_lt_one.trans_le hq).ne'
  exact ⟨u, (mem_kMethod_l1Linfty_iff_memLorentz hu hθ hq).2 hf, hu⟩

variable (𝕜) in
/-- **Unconditional characterization of `L^{p,q}` via the Lebesgue couple `(L¹, L^∞)_{θ,q}`**
(`0 < θ < 1`, `p = (1 - θ)⁻¹`, `1 ≤ q ≤ ∞`). -/
theorem memLorentz_iff_exists_mem_kMethod_lebesgue_one_top
    {f : α → E} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    MemLorentz f (ENNReal.ofReal (1 - θ)⁻¹) q μ ↔
      ∃ v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q,
        ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f := by
  refine ⟨fun hf ↦ ?_,
    fun ⟨v, hv_mem, hv⟩ ↦ (mem_kMethod_lebesgue_one_top_iff_memLorentz hv hθ hq).1 hv_mem⟩
  obtain ⟨v, hv⟩ := hf.exists_lebesgue_one_top_sumSpace_ae_eq 𝕜 (one_lt_ofReal_inv_one_sub hθ)
    (zero_lt_one.trans_le hq).ne'
  exact ⟨v, (mem_kMethod_lebesgue_one_top_iff_memLorentz hv hθ hq).2 hf, hv⟩

/-- Parameterization by `p`: for `1 < p ≤ ∞` and `1 ≤ q ≤ ∞`, `v ∈ (L¹, L^∞)_{1 - 1/p, q}` iff its
representative `f` belongs to `L^{p,q}(μ; E)`. -/
theorem mem_kMethod_lebesgue_one_top_one_sub_inv_iff_memLorentz
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {p q : ℝ≥0∞} (hp : 1 < p) (hq : 1 ≤ q) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod (1 - p.toReal⁻¹) q ↔ MemLorentz f p q μ :=
  mem_kMethod_lebesgue_one_top_iff_memLorentz_of_inv_eq hv (one_sub_toReal_inv_pos hp) hq
    (zero_lt_one.trans hp).ne' (sub_sub_cancel 1 p.toReal⁻¹).symm

/-- **Diagonal `Lᵖ` characterization:** for `1 < p ≤ ∞`, `v ∈ (L¹, L^∞)_{1 - 1/p, p}` iff its
representative `f` belongs to `Lᵖ(μ; E)`. -/
theorem mem_kMethod_lebesgue_one_top_self_iff_memLp {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {p : ℝ≥0∞} (hp : 1 < p) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod (1 - p.toReal⁻¹) p ↔ MemLp f p μ := by
  rw [mem_kMethod_lebesgue_one_top_one_sub_inv_iff_memLorentz hv hp hp.le, memLorentz_self_iff]

/-! ### The diagonal Banach-space isomorphism `(L¹, L^∞)_{1 - 1/p, p} ≃L[𝕜] Lᵖ` -/

section DiagonalEquiv

variable {p : ℝ≥0∞}

private def toLpLinear (hp : 1 < p) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p →ₗ[𝕜] Lp E p μ where
  toFun u := ⟨L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)),
    Lp.mem_Lp_iff_memLp.2
      ((mem_kMethod_lebesgue_one_top_self_iff_memLp EventuallyEq.rfl hp).1
        (KMethodSpace.toSumₗ_mem u))⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext <| by simp only [map_smul, RingHom.id_apply]; rfl

private theorem coe_toLpLinear (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    (toLpLinear hp u : α →ₘ[μ] E) =
      L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)) :=
  rfl

variable [Fact (1 ≤ p)]

private theorem norm_toLpLinear_le (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    ‖toLpLinear hp u‖ ≤ 1 * ‖u‖ := by
  rw [one_mul, ← eNorm_le_iff_norm_le, Lp.eNorm_def, coe_toLpLinear, ← eLorentzNorm_self]
  exact eLorentzNorm_le_eNorm_kMethodSpace_lebesgue_one_top EventuallyEq.rfl
    (zero_lt_one.trans hp).ne' (sub_sub_cancel 1 p.toReal⁻¹).symm

private def toLpCLM (hp : 1 < p) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous (toLpLinear hp) 1 (norm_toLpLinear_le hp)

private theorem toLpCLM_apply (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    toLpCLM hp u = toLpLinear hp u :=
  rfl

private theorem lpToLebesgueSum_mem_kMethod (hp : 1 < p) (f : Lp E p μ) :
    lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f ∈
      (lebesgue 𝕜 E μ 1 ∞).kMethod (1 - p.toReal⁻¹) p := by
  have hv : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
        (lpToLebesgueSum (𝕜 := 𝕜) (Fact.out : 1 ≤ p) le_top f))) =ᵐ[μ] ⇑f := by
    rw [sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
  exact (mem_kMethod_lebesgue_one_top_self_iff_memLp hv hp).2 (Lp.memLp f)

private def ofLpLinear (hp : 1 < p) :
    Lp E p μ →ₗ[𝕜] (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p where
  toFun f := KMethodSpace.mk (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f)
    (lpToLebesgueSum_mem_kMethod hp f)
  map_add' _ _ := KMethodSpace.ext (by simp)
  map_smul' _ _ := KMethodSpace.ext (by simp)

private theorem toSumₗ_ofLpLinear (hp : 1 < p) (f : Lp E p μ) :
    KMethodSpace.toSumₗ (ofLpLinear (𝕜 := 𝕜) hp f) =
      lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f := by
  simp [ofLpLinear]

private theorem norm_ofLpLinear_le (hp : 1 < p) (f : Lp E p μ) :
    ‖ofLpLinear (𝕜 := 𝕜) hp f‖ ≤ (1 - p.toReal⁻¹)⁻¹ * ‖f‖ := by
  have hθ : 0 < 1 - p.toReal⁻¹ := one_sub_toReal_inv_pos hp
  have hv : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
        (KMethodSpace.toSumₗ (ofLpLinear (𝕜 := 𝕜) hp f)))) =ᵐ[μ] ⇑f := by
    rw [toSumₗ_ofLpLinear, sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
  have h := eNorm_kMethodSpace_lebesgue_one_top_le_eLorentzNorm hv hθ
    (zero_lt_one.trans hp).ne' (sub_sub_cancel 1 p.toReal⁻¹).symm
  rw [eLorentzNorm_self, ← Lp.eNorm_def, ← ofReal_norm (ofLpLinear (𝕜 := 𝕜) hp f),
    ← ofReal_norm f, ← ENNReal.ofReal_mul (inv_nonneg.2 hθ.le),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.2 hθ.le) (norm_nonneg f))] at h
  exact h

private def ofLpCLM (hp : 1 < p) :
    Lp E p μ →L[𝕜] (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p :=
  LinearMap.mkContinuous (ofLpLinear (𝕜 := 𝕜) hp) (1 - p.toReal⁻¹)⁻¹ (norm_ofLpLinear_le hp)

private theorem ofLpCLM_apply (hp : 1 < p) (f : Lp E p μ) :
    ofLpCLM (𝕜 := 𝕜) hp f = ofLpLinear hp f :=
  rfl

/-- **Real interpolation `(L¹, L^∞)_{1 - 1/p, p} ≃L[𝕜] Lᵖ`.** For `1 < p ≤ ∞`, the real
interpolation space `(L¹(μ; E), L^∞(μ; E))_{1 - 1/p, p}` is continuously linearly isomorphic to
`Lᵖ(μ; E)`, with forward norm at most `1` and inverse norm at most `(1 - 1 / p)⁻¹` (so isometric at
`p = ∞`). -/
def lebesgueOneTopKMethodEquivLp (hp : 1 < p) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p ≃L[𝕜] Lp E p μ :=
  ContinuousLinearEquiv.equivOfInverse (toLpCLM (𝕜 := 𝕜) hp) (ofLpCLM (𝕜 := 𝕜) hp)
    (fun u ↦ KMethodSpace.ext <| (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective <|
      L1AddLinfty.toAEEqFun_injective <| by
        rw [ofLpCLM_apply, toLpCLM_apply, toSumₗ_ofLpLinear, sumSpaceEmbed_lpToLebesgueSum,
          L1AddLinfty.toAEEqFun_ofLp, coe_toLpLinear])
    (fun f ↦ Subtype.ext <| by
      rw [toLpCLM_apply, ofLpCLM_apply, coe_toLpLinear, toSumₗ_ofLpLinear,
        sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp])

private theorem lebesgueOneTopKMethodEquivLp_apply (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    lebesgueOneTopKMethodEquivLp hp u = toLpLinear hp u :=
  rfl

private theorem lebesgueOneTopKMethodEquivLp_symm_apply (hp : 1 < p) (f : Lp E p μ) :
    (lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hp).symm f = ofLpLinear hp f :=
  rfl

@[simp]
theorem coe_lebesgueOneTopKMethodEquivLp (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    (lebesgueOneTopKMethodEquivLp hp u : α →ₘ[μ] E) =
      L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)) :=
  (rfl)

@[simp]
theorem toSumₗ_lebesgueOneTopKMethodEquivLp_symm (hp : 1 < p) (f : Lp E p μ) :
    KMethodSpace.toSumₗ ((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hp).symm f) =
      lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f := by
  rw [lebesgueOneTopKMethodEquivLp_symm_apply, toSumₗ_ofLpLinear]

theorem norm_lebesgueOneTopKMethodEquivLp_le (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    ‖lebesgueOneTopKMethodEquivLp hp u‖ ≤ ‖u‖ := by
  rw [lebesgueOneTopKMethodEquivLp_apply]
  simpa only [one_mul] using norm_toLpLinear_le hp u

theorem norm_lebesgueOneTopKMethodEquivLp_symm_le (hp : 1 < p) (f : Lp E p μ) :
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hp).symm f‖ ≤ (1 - p.toReal⁻¹)⁻¹ * ‖f‖ := by
  rw [lebesgueOneTopKMethodEquivLp_symm_apply]
  exact norm_ofLpLinear_le hp f

end DiagonalEquiv

end CompatibleCouple

end TauCeti
