/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.L1Linfty
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
public import TauCeti.MeasureTheory.Function.LorentzSeminorm.CompareExp
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Integral.Hardy

/-!
# Real interpolation of `(L¹, L^∞)` and Lorentz spaces

Combining Peetre's `K`-functional formula `K(t, u) = ∫₀ᵗ (‖f‖ₑ)*` for `(L¹, L^∞)`
(`TauCeti.CompatibleCouple.ofReal_kFunctional_l1Linfty`) with Hardy's weighted inequality near `0`
(`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`) and the reverse antitone bound
(`TauCeti.eLpNorm_rpow_one_sub_mul_le_of_antitoneOn`) identifies the real interpolation spaces of
`(L¹(μ; E), L^∞(μ; E))` with the Lorentz classes `L^{p,q}(μ; E)` for `1 / p = 1 - θ`:

`‖f‖_{L^{p,q}} ≤ ‖u‖_{θ,q} ≤ θ⁻¹ ‖f‖_{L^{p,q}}`

for `0 < θ ≤ 1` and `1 ≤ q ≤ ∞`, where `E` is a normed space over both `ℝ` and the scalar field
`𝕜` of the couple. In particular:
* For `0 < θ < 1`, `p = (1 - θ)⁻¹`, and `1 ≤ q ≤ ∞`, an element of `L¹ + L^∞` belongs to
  `(L¹, L^∞)_{θ,q}` iff any representing function belongs to `L^{p,q}(μ; E)`, and conversely every
  function in `L^{p,q}(μ; E)` represents a unique element of `(L¹, L^∞)_{θ,q}`.
* At the endpoint `θ = 1` (`p = ∞`), `‖u‖_{1,q} = ‖f‖_{L^{∞,q}}` for all `q ∈ [0, ∞]` (and
  `‖u‖_{1,∞} = ‖f‖_{L^∞}`).
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
  `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_le_mul_eLorentzNorm`: explicit two-sided norm
  bounds between `(L¹, L^∞)_{θ,q}` and `L^{p,q}` (`1 / p = 1 - θ`), along with their counterparts
  for `lebesgue 𝕜 E μ 1 ∞` and `KMethodSpace`.
* `TauCeti.CompatibleCouple.mem_kMethod_l1Linfty_iff_memLorentz`,
  `TauCeti.CompatibleCouple.mem_kMethod_lebesgue_one_top_iff_memLorentz`,
  `TauCeti.CompatibleCouple.memLorentz_iff_exists_mem_kMethod_lebesgue_one_top_of_inv_eq`,
  `TauCeti.CompatibleCouple.memLorentz_iff_exists_mem_kMethod_lebesgue_one_top`: exact membership
  characterizations `(L¹, L^∞)_{θ,q} = L^{p,q}`.
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
    ⟨hf.aestronglyMeasurable, hf.setLIntegral_decreasingRearrangement_lt_top hp hq 1⟩

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

/-- **Lower bound `‖f‖_{L^{p,q}} ≤ ‖u‖_{θ,q}` for `(L¹, L^∞)`.** Whenever `1 / p = 1 - θ`, the
Lorentz gauge of any representative `f` of `u ∈ L¹ + L^∞` is bounded by the `K`-method norm of `u`,
with constant `1` and for all `q ∈ [0, ∞]`. -/
theorem eLorentzNorm_le_kMethodENorm_l1Linfty {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} {p : ℝ≥0∞}
    (hp : p.toReal⁻¹ = 1 - θ) (q : ℝ≥0∞) :
    eLorentzNorm f p q μ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [hf]
  rw [eLorentzNorm_eq_eLpNorm_multHaar hp0 hf, hp, kMethodENorm_l1Linfty_eq_eLpNorm hu]
  exact eLpNorm_rpow_one_sub_mul_le_of_antitoneOn θ q
    ((μ.antitone_decreasingRearrangement (‖f ·‖ₑ)).antitoneOn _)

/-- **Lower bound `‖f‖_{L^{p,q}} ≤ ‖v‖_{θ,q}` for the Lebesgue couple `(L¹, L^∞)`.** -/
theorem eLorentzNorm_le_kMethodENorm_lebesgue_one_top {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E} (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} {p : ℝ≥0∞} (hp : p.toReal⁻¹ = 1 - θ) (q : ℝ≥0∞) :
    eLorentzNorm f p q μ ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact eLorentzNorm_le_kMethodENorm_l1Linfty hv hp q

/-- **Upper bound `‖u‖_{θ,q} ≤ θ⁻¹ ‖f‖_{L^{p,q}}` for `(L¹, L^∞)`.** For `0 < θ ≤ 1`,
`1 ≤ q ≤ ∞`, and `p ≠ 0` with `1 / p = 1 - θ`, Hardy's inequality bounds the `K`-method norm of `u`
by `θ⁻¹` times the Lorentz gauge of any representative `f`. -/
theorem kMethodENorm_l1Linfty_le_mul_eLorentzNorm {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  rw [kMethodENorm_l1Linfty_eq_eLpNorm hu, eLorentzNorm_eq_eLpNorm_multHaar hp0 hf, hp]
  exact eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ hq _

/-- **Upper bound `‖v‖_{θ,q} ≤ θ⁻¹ ‖f‖_{L^{p,q}}` for the Lebesgue couple `(L¹, L^∞)`.** -/
theorem kMethodENorm_lebesgue_one_top_le_mul_eLorentzNorm {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E} (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞} (hq : 1 ≤ q) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact kMethodENorm_l1Linfty_le_mul_eLorentzNorm hv hθ hq hp0 hp

/-- At `θ = 1` (`p = ∞`), `‖u‖_{1,q} = ‖f‖_{L^{∞,q}}` for every `q ∈ [0, ∞]`. -/
theorem kMethodENorm_l1Linfty_one_eq_eLorentzNorm {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) (q : ℝ≥0∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm 1 q u = eLorentzNorm f ∞ q μ := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [kMethodENorm_def, eLpNorm_exponent_zero
      (aestronglyMeasurable_rpow_neg_mul_kFunctional 1 u), eLorentzNorm_exponent_zero_right hf]
  rcases le_or_gt 1 q with hq | hq
  · refine le_antisymm ?_ (eLorentzNorm_le_kMethodENorm_l1Linfty hu (by simp) q)
    simpa using kMethodENorm_l1Linfty_le_mul_eLorentzNorm hu one_pos hq ENNReal.top_ne_zero
      (p := ∞) (by simp)
  · by_cases h0 : (‖f ·‖ₑ) =ᵐ[μ] 0
    · have hu0 : u = 0 := L1AddLinfty.toAEEqFun_injective <| by
        rw [map_zero]
        refine AEEqFun.ext (hu.trans ?_)
        filter_upwards [h0, AEEqFun.coeFn_zero (α := α) (β := E) (μ := μ)] with x hx h0x
        rw [h0x, Pi.zero_apply]
        exact eNorm_eq_zero.1 hx
      rw [hu0, kMethodENorm_zero, (eLorentzNorm_eq_zero_iff ENNReal.top_ne_zero hq0).2 ⟨hf, h0⟩]
    · have htop : eLorentzNorm f ∞ q μ = ∞ := by
        by_contra hne
        exact h0 ((memLorentz_top_left_iff hq0 (hq.trans ENNReal.one_lt_top).ne).1
          (memLorentz_iff.2 (Ne.lt_top hne))).2
      refine le_antisymm ?_ (eLorentzNorm_le_kMethodENorm_l1Linfty hu (by simp) q)
      rw [htop]
      exact le_top

/-- At `(θ, q) = (1, ∞)`, the `K`-method norm of `(L¹, L^∞)` equals the `L^∞` norm. -/
theorem kMethodENorm_l1Linfty_one_top_eq_eLpNorm {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) :
    (l1Linfty 𝕜 E μ).kMethodENorm 1 ∞ u = eLpNorm f ∞ μ := by
  rw [kMethodENorm_l1Linfty_one_eq_eLorentzNorm hu, eLorentzNorm_self]

/-- At `θ = 1` (`p = ∞`), `‖v‖_{1,q} = ‖f‖_{L^{∞,q}}` for the Lebesgue couple `(L¹, L^∞)` and
every `q ∈ [0, ∞]`. -/
theorem kMethodENorm_lebesgue_one_top_one_eq_eLorentzNorm
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    (q : ℝ≥0∞) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm 1 q v = eLorentzNorm f ∞ q μ := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed, kMethodENorm_l1Linfty_one_eq_eLorentzNorm hv]

/-- At `(θ, q) = (1, ∞)`, the `K`-method norm of the Lebesgue couple `(L¹, L^∞)` equals the `L^∞`
norm. -/
theorem kMethodENorm_lebesgue_one_top_one_top_eq_eLpNorm
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm 1 ∞ v = eLpNorm f ∞ μ := by
  rw [kMethodENorm_lebesgue_one_top_one_eq_eLorentzNorm hv, eLorentzNorm_self]

/-- On the normed space `(L¹, L^∞)_{θ,q}`, `‖f‖_{L^{p,q}} ≤ ‖w‖ₑ` for `1 / p = 1 - θ`. -/
theorem eLorentzNorm_le_eNorm_kMethodSpace_lebesgue_one_top {θ : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ q)]
    {w : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ q} {f : α → E}
    (hw : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ w))) =ᵐ[μ] f)
    (hp : p.toReal⁻¹ = 1 - θ) :
    eLorentzNorm f p q μ ≤ ‖w‖ₑ := by
  rw [← ofReal_norm, KMethodSpace.ofReal_norm]
  exact eLorentzNorm_le_kMethodENorm_lebesgue_one_top hw hp q

/-- On the normed space `(L¹, L^∞)_{θ,q}`, `‖w‖ₑ ≤ θ⁻¹ ‖f‖_{L^{p,q}}` for `0 < θ ≤ 1` and
`p ≠ 0` with `1 / p = 1 - θ`. -/
theorem eNorm_kMethodSpace_lebesgue_one_top_le_mul_eLorentzNorm {θ : ℝ} {p q : ℝ≥0∞}
    [Fact (1 ≤ q)] {w : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ q} {f : α → E}
    (hw : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ w))) =ᵐ[μ] f)
    (hθ : 0 < θ) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    ‖w‖ₑ ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [← ofReal_norm, KMethodSpace.ofReal_norm]
  exact kMethodENorm_lebesgue_one_top_le_mul_eLorentzNorm hw hθ Fact.out hp0 hp

/-- On the normed space `(L¹, L^∞)_{1,q}`, `‖w‖ₑ = ‖f‖_{L^{∞,q}}`. -/
theorem eNorm_kMethodSpace_lebesgue_one_top_one_eq_eLorentzNorm {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {w : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace 1 q} {f : α → E}
    (hw : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ w))) =ᵐ[μ] f) :
    ‖w‖ₑ = eLorentzNorm f ∞ q μ := by
  rw [← ofReal_norm, KMethodSpace.ofReal_norm,
    kMethodENorm_lebesgue_one_top_one_eq_eLorentzNorm hw]

/-- On the normed space `(L¹, L^∞)_{1,∞}`, `‖w‖ₑ = ‖f‖_{L^∞}`. -/
theorem eNorm_kMethodSpace_lebesgue_one_top_one_top_eq_eLpNorm
    {w : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace 1 ∞} {f : α → E}
    (hw : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ w))) =ᵐ[μ] f) :
    ‖w‖ₑ = eLpNorm f ∞ μ := by
  rw [eNorm_kMethodSpace_lebesgue_one_top_one_eq_eLorentzNorm hw, eLorentzNorm_self]

/-! ### Exact membership characterizations `(L¹, L^∞)_{θ,q} = L^{p,q}` -/

/-- For `0 < θ ≤ 1`, `1 ≤ q ≤ ∞`, and `p ≠ 0` with `1 / p = 1 - θ`, an element `u` of `L¹ + L^∞`
represented by `f` belongs to `(L¹, L^∞)_{θ,q}` iff `f ∈ L^{p,q}(μ; E)`. -/
theorem mem_kMethod_l1Linfty_iff_memLorentz_of_inv_eq {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞}
    (hq : 1 ≤ q) (hp0 : p ≠ 0) (hp : p.toReal⁻¹ = 1 - θ) :
    u ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔ MemLorentz f p q μ := by
  rw [mem_kMethod_iff, memLorentz_iff]
  exact ⟨fun h ↦ (eLorentzNorm_le_kMethodENorm_l1Linfty hu hp q).trans_lt h,
    fun h ↦ (kMethodENorm_l1Linfty_le_mul_eLorentzNorm hu hθ hq hp0 hp).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)⟩

/-- For `0 < θ ≤ 1`, `1 ≤ q ≤ ∞`, and `p ≠ 0` with `1 / p = 1 - θ`, an element `v` of the sum
space of the Lebesgue couple `(L¹, L^∞)` represented by `f` belongs to `(L¹, L^∞)_{θ,q}` iff
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
    (zero_lt_one.trans (ENNReal.one_lt_ofReal_inv_one_sub hθ.1 hθ.2)).ne'
    (ENNReal.toReal_inv_ofReal_inv_one_sub hθ.2.le)

/-- **Real interpolation of the Lebesgue couple `(L¹, L^∞)` is `L^{p,q}`
(`0 < θ < 1`, `p = (1 - θ)⁻¹`).** -/
theorem mem_kMethod_lebesgue_one_top_iff_memLorentz {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E} (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q ↔ MemLorentz f (ENNReal.ofReal (1 - θ)⁻¹) q μ :=
  mem_kMethod_lebesgue_one_top_iff_memLorentz_of_inv_eq hv hθ.1 hq
    (zero_lt_one.trans (ENNReal.one_lt_ofReal_inv_one_sub hθ.1 hθ.2)).ne'
    (ENNReal.toReal_inv_ofReal_inv_one_sub hθ.2.le)

variable (𝕜) in
/-- For `0 < θ ≤ 1`, `1 ≤ q ≤ ∞`, and `p ≠ 0` with `1 / p = 1 - θ`, an arbitrary function
`f : α → E` belongs to `L^{p,q}(μ; E)` iff it represents an element of `(L¹, L^∞)_{θ,q}` in
`L¹ + L^∞`. -/
theorem memLorentz_iff_exists_mem_kMethod_l1Linfty_of_inv_eq
    {f : α → E} {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞} (hq : 1 ≤ q) (hp0 : p ≠ 0)
    (hp : p.toReal⁻¹ = 1 - θ) :
    MemLorentz f p q μ ↔
      ∃ u ∈ (l1Linfty 𝕜 E μ).kMethod θ q, ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f := by
  have hp1 : 1 < p := by
    by_contra! hle
    have hptop : p ≠ ∞ := (hle.trans_lt ENNReal.one_lt_top).ne
    have h1le : 1 ≤ p.toReal⁻¹ :=
      (one_le_inv₀ (ENNReal.toReal_pos hp0 hptop)).2
        (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle)
    linarith
  refine ⟨fun hf ↦ ?_, fun ⟨u, hu_mem, hu⟩ ↦
    (mem_kMethod_l1Linfty_iff_memLorentz_of_inv_eq hu hθ hq hp0 hp).1 hu_mem⟩
  obtain ⟨u, hu⟩ := hf.exists_l1AddLinfty_toAEEqFun_ae_eq 𝕜 hp1 (zero_lt_one.trans_le hq).ne'
  exact ⟨u, (mem_kMethod_l1Linfty_iff_memLorentz_of_inv_eq hu hθ hq hp0 hp).2 hf, hu⟩

variable (𝕜) in
/-- For `0 < θ ≤ 1`, `1 ≤ q ≤ ∞`, and `p ≠ 0` with `1 / p = 1 - θ`, an arbitrary function
`f : α → E` belongs to `L^{p,q}(μ; E)` iff it represents an element of `(L¹, L^∞)_{θ,q}` for the
Lebesgue couple `(L¹, L^∞)`. -/
theorem memLorentz_iff_exists_mem_kMethod_lebesgue_one_top_of_inv_eq
    {f : α → E} {θ : ℝ} (hθ : 0 < θ) {p q : ℝ≥0∞} (hq : 1 ≤ q) (hp0 : p ≠ 0)
    (hp : p.toReal⁻¹ = 1 - θ) :
    MemLorentz f p q μ ↔
      ∃ v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q,
        ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f := by
  rw [memLorentz_iff_exists_mem_kMethod_l1Linfty_of_inv_eq 𝕜 hθ hq hp0 hp]
  constructor
  · rintro ⟨u, hu_mem, hu⟩
    obtain ⟨v, rfl⟩ := lebesgue_one_top_sumSpaceEmbed_surjective u
    exact ⟨v, mem_kMethod_l1Linfty_sumSpaceEmbed_iff.1 hu_mem, hu⟩
  · rintro ⟨v, hv_mem, hv⟩
    exact ⟨_, mem_kMethod_l1Linfty_sumSpaceEmbed_iff.2 hv_mem, hv⟩

variable (𝕜) in
/-- **Unconditional characterization of `L^{p,q}` via `(L¹, L^∞)_{θ,q}`** (`0 < θ < 1`,
`p = (1 - θ)⁻¹`, `1 ≤ q ≤ ∞`): an arbitrary function `f : α → E` belongs to `L^{p,q}(μ; E)` iff it
represents an element of `(L¹, L^∞)_{θ,q}` in `L¹ + L^∞`. -/
theorem memLorentz_iff_exists_mem_kMethod_l1Linfty
    {f : α → E} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    MemLorentz f (ENNReal.ofReal (1 - θ)⁻¹) q μ ↔
      ∃ u ∈ (l1Linfty 𝕜 E μ).kMethod θ q, ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f :=
  memLorentz_iff_exists_mem_kMethod_l1Linfty_of_inv_eq 𝕜 hθ.1 hq
    (zero_lt_one.trans (ENNReal.one_lt_ofReal_inv_one_sub hθ.1 hθ.2)).ne'
    (ENNReal.toReal_inv_ofReal_inv_one_sub hθ.2.le)

variable (𝕜) in
/-- **Unconditional characterization of `L^{p,q}` via the Lebesgue couple `(L¹, L^∞)_{θ,q}`**
(`0 < θ < 1`, `p = (1 - θ)⁻¹`, `1 ≤ q ≤ ∞`). -/
theorem memLorentz_iff_exists_mem_kMethod_lebesgue_one_top
    {f : α → E} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    MemLorentz f (ENNReal.ofReal (1 - θ)⁻¹) q μ ↔
      ∃ v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q,
        ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f :=
  memLorentz_iff_exists_mem_kMethod_lebesgue_one_top_of_inv_eq 𝕜 hθ.1 hq
    (zero_lt_one.trans (ENNReal.one_lt_ofReal_inv_one_sub hθ.1 hθ.2)).ne'
    (ENNReal.toReal_inv_ofReal_inv_one_sub hθ.2.le)

/-- Parameterization by `p`: for `1 < p ≤ ∞` and `1 ≤ q ≤ ∞`, `u ∈ (L¹, L^∞)_{1 - 1/p, q}` in
`L¹ + L^∞` iff its representative `f` belongs to `L^{p,q}(μ; E)`. -/
theorem mem_kMethod_l1Linfty_one_sub_inv_iff_memLorentz
    {u : L1AddLinfty 𝕜 E μ} {f : α → E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f)
    {p q : ℝ≥0∞} (hp : 1 < p) (hq : 1 ≤ q) :
    u ∈ (l1Linfty 𝕜 E μ).kMethod (1 - p.toReal⁻¹) q ↔ MemLorentz f p q μ :=
  mem_kMethod_l1Linfty_iff_memLorentz_of_inv_eq hu (ENNReal.one_sub_toReal_inv_pos hp) hq
    (zero_lt_one.trans hp).ne' (sub_sub_cancel 1 p.toReal⁻¹).symm

/-- Parameterization by `p`: for `1 < p ≤ ∞` and `1 ≤ q ≤ ∞`, `v ∈ (L¹, L^∞)_{1 - 1/p, q}` iff its
representative `f` belongs to `L^{p,q}(μ; E)`. -/
theorem mem_kMethod_lebesgue_one_top_one_sub_inv_iff_memLorentz
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {p q : ℝ≥0∞} (hp : 1 < p) (hq : 1 ≤ q) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod (1 - p.toReal⁻¹) q ↔ MemLorentz f p q μ :=
  mem_kMethod_lebesgue_one_top_iff_memLorentz_of_inv_eq hv (ENNReal.one_sub_toReal_inv_pos hp) hq
    (zero_lt_one.trans hp).ne' (sub_sub_cancel 1 p.toReal⁻¹).symm

/-- **Diagonal `Lᵖ` characterization for `l1Linfty`:** for `1 < p ≤ ∞`,
`u ∈ (L¹, L^∞)_{1 - 1/p, p}` iff its representative `f` belongs to `Lᵖ(μ; E)`. -/
theorem mem_kMethod_l1Linfty_self_iff_memLp {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {p : ℝ≥0∞} (hp : 1 < p) :
    u ∈ (l1Linfty 𝕜 E μ).kMethod (1 - p.toReal⁻¹) p ↔ MemLp f p μ := by
  rw [mem_kMethod_l1Linfty_one_sub_inv_iff_memLorentz hu hp hp.le, memLorentz_self_iff]

/-- **Diagonal `Lᵖ` characterization:** for `1 < p ≤ ∞`, `v ∈ (L¹, L^∞)_{1 - 1/p, p}` iff its
representative `f` belongs to `Lᵖ(μ; E)`. -/
theorem mem_kMethod_lebesgue_one_top_self_iff_memLp {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {p : ℝ≥0∞} (hp : 1 < p) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod (1 - p.toReal⁻¹) p ↔ MemLp f p μ := by
  rw [mem_kMethod_lebesgue_one_top_one_sub_inv_iff_memLorentz hv hp hp.le, memLorentz_self_iff]

/-! ### The diagonal Banach-space isomorphism `(L¹, L^∞)_{1 - 1/p, p} ≃L[𝕜] Lᵖ` -/

section DiagonalEquiv

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem lpToLebesgueSum_mem_kMethod (hp : 1 < p) (f : Lp E p μ) :
    lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f ∈
      (lebesgue 𝕜 E μ 1 ∞).kMethod (1 - p.toReal⁻¹) p := by
  have hv : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
        (lpToLebesgueSum (𝕜 := 𝕜) (Fact.out : 1 ≤ p) le_top f))) =ᵐ[μ] ⇑f := by
    rw [sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
  exact (mem_kMethod_lebesgue_one_top_self_iff_memLp hv hp).2 (Lp.memLp f)

private def toLpLinearEquiv (hp : 1 < p) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p ≃ₗ[𝕜] Lp E p μ where
  toFun u := ⟨L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)),
    Lp.mem_Lp_iff_memLp.2
      ((mem_kMethod_lebesgue_one_top_self_iff_memLp EventuallyEq.rfl hp).1
        (KMethodSpace.toSumₗ_mem u))⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' c _ := Lp.ext <| by
    simp only [map_smul, RingHom.id_apply]
    refine (AEEqFun.coeFn_smul c _).trans ?_
    exact (Lp.coeFn_smul c ⟨_, _⟩).symm
  invFun f := KMethodSpace.mk (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f)
    (lpToLebesgueSum_mem_kMethod hp f)
  left_inv u := KMethodSpace.ext <| (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective <|
    L1AddLinfty.toAEEqFun_injective <| by
      simp [KMethodSpace.toSumₗ_mk]
  right_inv f := Subtype.ext <| by
    simp [KMethodSpace.toSumₗ_mk]

private theorem coe_toLpLinearEquiv (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    (toLpLinearEquiv hp u : α →ₘ[μ] E) =
      L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)) := by
  simp [toLpLinearEquiv]

private theorem toSumₗ_toLpLinearEquiv_symm (hp : 1 < p) (f : Lp E p μ) :
    KMethodSpace.toSumₗ ((toLpLinearEquiv (𝕜 := 𝕜) hp).symm f) =
      lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f :=
  KMethodSpace.toSumₗ_mk _ _

private theorem norm_toLpLinearEquiv_le (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    ‖toLpLinearEquiv hp u‖ ≤ 1 * ‖u‖ := by
  rw [one_mul, ← eNorm_le_iff_norm_le, Lp.eNorm_def, coe_toLpLinearEquiv, ← eLorentzNorm_self]
  exact eLorentzNorm_le_eNorm_kMethodSpace_lebesgue_one_top EventuallyEq.rfl
    (sub_sub_cancel 1 p.toReal⁻¹).symm

private theorem norm_toLpLinearEquiv_symm_le (hp : 1 < p) (f : Lp E p μ) :
    ‖(toLpLinearEquiv (𝕜 := 𝕜) hp).symm f‖ ≤ (1 - p.toReal⁻¹)⁻¹ * ‖f‖ := by
  have hθ : 0 < 1 - p.toReal⁻¹ := ENNReal.one_sub_toReal_inv_pos hp
  have hv : ⇑(L1AddLinfty.toAEEqFun 𝕜
      ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
        (KMethodSpace.toSumₗ ((toLpLinearEquiv (𝕜 := 𝕜) hp).symm f)))) =ᵐ[μ] ⇑f := by
    rw [toSumₗ_toLpLinearEquiv_symm, sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
  have h := eNorm_kMethodSpace_lebesgue_one_top_le_mul_eLorentzNorm hv hθ
    (zero_lt_one.trans hp).ne' (sub_sub_cancel 1 p.toReal⁻¹).symm
  rwa [eLorentzNorm_self, ← Lp.eNorm_def,
    ← ofReal_norm ((toLpLinearEquiv (𝕜 := 𝕜) hp).symm f),
    ← ofReal_norm f, ← ENNReal.ofReal_mul (inv_nonneg.2 hθ.le),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.2 hθ.le) (norm_nonneg f))] at h

/-- **Real interpolation `(L¹, L^∞)_{1 - 1/p, p} ≃L[𝕜] Lᵖ`.** For `1 < p ≤ ∞`, the real
interpolation space `(L¹(μ; E), L^∞(μ; E))_{1 - 1/p, p}` is continuously linearly isomorphic to
`Lᵖ(μ; E)`, with forward norm at most `1` and inverse norm at most `(1 - 1 / p)⁻¹` (so isometric at
`p = ∞`). -/
def lebesgueOneTopKMethodEquivLp (hp : 1 < p) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p ≃L[𝕜] Lp E p μ :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    (toLpLinearEquiv (𝕜 := 𝕜) (E := E) (μ := μ) hp) 1 (1 - p.toReal⁻¹)⁻¹
    (norm_toLpLinearEquiv_le hp) (norm_toLpLinearEquiv_symm_le hp)

@[simp]
theorem coe_lebesgueOneTopKMethodEquivLp (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    (lebesgueOneTopKMethodEquivLp hp u : α →ₘ[μ] E) =
      L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u)) := by
  simp [lebesgueOneTopKMethodEquivLp, LinearEquiv.toContinuousLinearEquivOfBounds, toLpLinearEquiv]

@[simp]
theorem toSumₗ_lebesgueOneTopKMethodEquivLp_symm (hp : 1 < p) (f : Lp E p μ) :
    KMethodSpace.toSumₗ ((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hp).symm f) =
      lpToLebesgueSum (Fact.out : 1 ≤ p) le_top f :=
  (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective <| L1AddLinfty.toAEEqFun_injective <| by
    rw [sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp,
      ← coe_lebesgueOneTopKMethodEquivLp hp, ContinuousLinearEquiv.apply_symm_apply]

@[simp]
theorem ofLp_lebesgueOneTopKMethodEquivLp (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    (L1AddLinfty.ofLp (lebesgueOneTopKMethodEquivLp hp u) : L1AddLinfty 𝕜 E μ) =
      (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (KMethodSpace.toSumₗ u) :=
  L1AddLinfty.toAEEqFun_injective (by simp)

@[simp]
theorem lpToLebesgueSum_lebesgueOneTopKMethodEquivLp (h₀ : 1 ≤ p) (h₁ : p ≤ ∞) (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    lpToLebesgueSum h₀ h₁ (lebesgueOneTopKMethodEquivLp hp u) = KMethodSpace.toSumₗ u :=
  (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective (by simp)

theorem norm_lebesgueOneTopKMethodEquivLp_le (hp : 1 < p)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - p.toReal⁻¹) p) :
    ‖lebesgueOneTopKMethodEquivLp hp u‖ ≤ ‖u‖ := by
  have h := norm_toLpLinearEquiv_le hp u
  rwa [one_mul] at h

theorem norm_lebesgueOneTopKMethodEquivLp_symm_le (hp : 1 < p) (f : Lp E p μ) :
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hp).symm f‖ ≤ (1 - p.toReal⁻¹)⁻¹ * ‖f‖ :=
  norm_toLpLinearEquiv_symm_le hp f

-- Not `@[simp]`: at `p = ∞`, `ENNReal.toReal_top` simplifies the dependent index
-- `1 - (∞ : ℝ≥0∞).toReal⁻¹` inside the domain type of `DFunLike.coe` and
-- `ContinuousLinearEquiv.symm`, which fails `simpNF`.
/-- At `p = ∞`, `lebesgueOneTopKMethodEquivLp` is norm-preserving. -/
theorem norm_lebesgueOneTopKMethodEquivLp_top (hp : (1 : ℝ≥0∞) < ∞)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace (1 - (∞ : ℝ≥0∞).toReal⁻¹) ∞) :
    ‖lebesgueOneTopKMethodEquivLp hp u‖ = ‖u‖ := by
  refine le_antisymm (norm_lebesgueOneTopKMethodEquivLp_le hp u) ?_
  have h := norm_lebesgueOneTopKMethodEquivLp_symm_le (𝕜 := 𝕜) hp
    (lebesgueOneTopKMethodEquivLp hp u)
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  simpa using h

/-- At `p = ∞`, `(lebesgueOneTopKMethodEquivLp _).symm` is norm-preserving. -/
theorem norm_lebesgueOneTopKMethodEquivLp_top_symm (hp : (1 : ℝ≥0∞) < ∞) (f : Lp E ∞ μ) :
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hp).symm f‖ = ‖f‖ := by
  rw [← norm_lebesgueOneTopKMethodEquivLp_top hp
    ((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hp).symm f),
    ContinuousLinearEquiv.apply_symm_apply]

end DiagonalEquiv

end CompatibleCouple

end TauCeti
