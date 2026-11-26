/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.MeasureTheory.Function.ContinuousApproximation
import TauCeti.Topology.Compactness.SigmaCompact

/-!
# The local `L¹` norm by duality with test vector fields

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `F` be a real Hilbert
space, and let `G : E → F →L[ℝ] ℝ` be a field of continuous linear functionals that is locally
integrable on `Ω` for a measure `μ`. Then

`∫⁻ x in Ω, ‖G x‖ₑ ∂μ = ⨆ { ∫ G x (φ x) ∂μ | φ ∈ 𝓓(Ω, F), ‖φ x‖ ≤ 1 for all x }`

(`MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm`), with
both sides possibly infinite. The measure is arbitrary: it may be a Haar measure, or a measure
such as the `k`-dimensional Hausdorff measure, which is not locally finite. The bound of each
pairing by `∫_Ω ‖G‖` holds for every real normed space `F`
(`TestFunction.enorm_integral_apply_le_setLIntegral_enorm`). For a complete normed space `F`, the
duality holds as soon as a measurable field `σ` with `‖σ x‖ ≤ 1` attains the norms,
`G x (σ x) = ‖G x‖`
(`MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm_of_norming`);
for a Hilbert space the normalized Riesz representatives of `G` form such a field.

This duality identifies a supremum over test vector fields, such as the total variation of a
function on `Ω` or the mass of a current, with the integral of a pointwise norm.

For the reverse inequality, fix a compact `K ⊆ Ω` and a compact neighbourhood `L ⊆ Ω` of `K`.
All errors are measured in `L¹` of the finite measure `ρ = ‖G‖ μ` on `L`, which controls the
pairings with `G`. The field `σ` on `K`, extended by zero, is approximated in `L¹(ρ)` by a
continuous field of norm at most one vanishing outside a neighbourhood of `K` (finite measures on
`E` are regular; `MeasureTheory.exists_continuous_norm_le_support_subset_integral_norm_sub_le`).
Its mollifications with normalized bumps of shrinking support are test vector fields of norm at
most one which converge to it in `L¹(ρ)` (`Continuous.exists_contDiff_norm_le_lintegral_sub_le`),
so they approximate the pairing with `σ` on `K`
(`MeasureTheory.LocallyIntegrableOn.exists_contDiff_enorm_integral_sub_setIntegral_le`).
An exhaustion of `Ω` by compact sets concludes.

## Main declarations

* `TestFunction.enorm_integral_apply_le_setLIntegral_enorm`: `|∫ G φ| ≤ ∫_Ω ‖G‖` for a test vector
  field `φ` on `Ω` with `‖φ‖ ≤ 1`.
* `MeasureTheory.LocallyIntegrableOn.exists_contDiff_lt_ofReal_integral_apply`: given a norming
  field, every `c < ∫_W ‖G‖` is exceeded by the pairing with a smooth field of compact support in
  the open set `W`, of norm at most one.
* `MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm_of_norming`,
  `MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm`: the
  supremum of the pairings is `∫_Ω ‖G‖`, given a norming field, or for a Hilbert space `F`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.1 (the variation of a Sobolev function).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Metric Set
open scoped ENNReal Distributions Topology Convolution ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} {Ω : Opens E}

namespace TestFunction

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pairing a field of continuous linear functionals `G` with a test vector field on `Ω` of norm
at most one gives at most `∫_Ω ‖G‖`. -/
theorem enorm_integral_apply_le_setLIntegral_enorm (φ : 𝓓(Ω, F))
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (G : E → F →L[ℝ] ℝ) :
    ‖∫ x, G x (φ x) ∂μ‖ₑ ≤ ∫⁻ x in Ω, ‖G x‖ₑ ∂μ := by
  refine (eNorm_integral_le_lintegral_eNorm _).trans
    ((lintegral_mono fun x => ?_).trans (lintegral_indicator_le _ _))
  by_cases hx : x ∈ (Ω : Set E)
  · rw [Set.indicator_of_mem hx, eNorm_le_iff_norm_le]
    exact ((G x).le_opNorm (φ x)).trans (mul_le_of_le_one_right (norm_nonneg _) (hφ x))
  · simp [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)]

end TestFunction

namespace MeasureTheory.LocallyIntegrableOn

variable [FiniteDimensional ℝ E] [BorelSpace E] {W : Set E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {G : E → F →L[ℝ] ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [CompleteSpace F] in
/-- The pairings of `G` on `L` with two fields of norm at most one differ by at most the distance
of the fields in `L¹` of the measure `‖G‖ μ` on `L`. -/
private theorem enorm_setIntegral_sub_le {L : Set E} (hGL : IntegrableOn G L μ) {g₁ g₂ : E → F}
    (hg₁ : AEStronglyMeasurable g₁ μ) (hg₂ : AEStronglyMeasurable g₂ μ) (h₁ : ∀ x, ‖g₁ x‖ ≤ 1)
    (h₂ : ∀ x, ‖g₂ x‖ ≤ 1) :
    ‖∫ x in L, G x (g₁ x) ∂μ - ∫ x in L, G x (g₂ x) ∂μ‖ₑ ≤
      ∫⁻ x, ‖g₁ x - g₂ x‖ₑ ∂(μ.restrict L).withDensity fun x => ‖G x‖ₑ := by
  have hGg (g : E → F) (hg : AEStronglyMeasurable g μ) (hg1 : ∀ x, ‖g x‖ ≤ 1) :
      IntegrableOn (fun x => G x (g x)) L μ :=
    hGL.norm.mono' (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : F →L[ℝ] ℝ) v => L v)
      (by fun_prop) hGL.aestronglyMeasurable hg.restrict)
      (ae_of_all _ fun x => ((G x).le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hg1 x)))
  rw [← integral_sub (hGg _ hg₁ h₁) (hGg _ hg₂ h₂)]
  simp_rw [← map_sub]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  rw [lintegral_withDensity_eq_lintegral_mul₀ (g := fun x => ‖g₁ x - g₂ x‖ₑ)
    hGL.aestronglyMeasurable.eNorm (hg₁.restrict.sub hg₂.restrict).eNorm]
  exact lintegral_mono fun x => (G x).le_opENorm _

/-- **Smooth approximation of a bounded field.** Let `G` be locally integrable on an open set `W`
and `σ` a measurable field with `‖σ x‖ ≤ 1`. For a compact `K ⊆ W`, the pairing `∫_K G σ` is
approximated by pairings `∫ G ψ` with smooth fields `ψ` of compact support in `W` and with
`‖ψ x‖ ≤ 1`. The measure `μ` is arbitrary. -/
theorem exists_contDiff_enorm_integral_sub_setIntegral_le (hG : LocallyIntegrableOn G W μ)
    (hW : IsOpen W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) {σ : E → F}
    (hσm : AEStronglyMeasurable σ (μ.restrict K)) (hσ : ∀ x, ‖σ x‖ ≤ 1) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ W ∧ (∀ x, ‖ψ x‖ ≤ 1) ∧
      ‖∫ x, G x (ψ x) ∂μ - ∫ x in K, G x (σ x) ∂μ‖ₑ ≤ ε := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  set L := cthickening δ K
  have hGL : IntegrableOn G L μ := hG.integrableOn_compact_subset hδW hK.cthickening
  -- The finite measure `ρ = ‖G‖ μ` on `L` controls the pairings with `G`.
  set ρ : Measure E := (μ.restrict L).withDensity fun x => ‖G x‖ₑ
  have : IsFiniteMeasure ρ := isFiniteMeasure_withDensity hGL.2.ne
  have hρμ : ρ ≪ μ := (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  -- Approximate `σ` on `K`, extended by zero, in `L¹(ρ)` by a smooth field `ψ` supported in `L`.
  set s : E → F := K.indicator σ with hs_def
  have hs1 (x : E) : ‖s x‖ ≤ 1 := by
    by_cases hx : x ∈ K <;> simp [hs_def, hx, hσ x]
  have hsμ : AEStronglyMeasurable s μ :=
    (aestronglyMeasurable_indicator_iff hK.measurableSet).2 hσm
  have hsi : Integrable s ρ := Integrable.of_bound (hsμ.mono_ac hρμ) 1 (ae_of_all _ hs1)
  -- First by a continuous field `h` vanishing outside the `δ / 2`-thickening of `K`, then by its
  -- mollification `ψ`.
  obtain ⟨r, -, hr0, hr⟩ := ENNReal.lt_iff_exists_real_btwn.1 (ENNReal.half_pos hε)
  obtain ⟨h, hh1, hhK, hhi, hhs⟩ := exists_continuous_norm_le_support_subset_integral_norm_sub_le
    hsi hs1 hK.isClosed isOpen_thickening (self_subset_thickening (half_pos hδ) K)
    Set.support_indicator_subset (ENNReal.ofReal_pos.1 hr0)
  obtain ⟨ψ, hψd, hψ1, hψs, hψh⟩ := h.continuous.exists_contDiff_norm_le_lintegral_sub_le
    (ν := ρ) hh1 (half_pos hδ) (ENNReal.half_pos hε).ne'
  have hψL : tsupport ψ ⊆ L := by
    refine hψs.trans ((cthickening_subset_of_subset _ ((closure_mono hhK).trans
      (closure_thickening_subset_cthickening _ _))).trans ?_)
    simpa using cthickening_cthickening_subset (half_pos hδ).le (half_pos hδ).le K
  have hhs' : ∫⁻ x, edist (s x) (h x) ∂ρ ≤ ε / 2 := by
    have := ofReal_integral_norm_eq_lintegral_eNorm (hsi.sub hhi)
    simp only [Pi.sub_apply, ← eDist_eq_eNorm_sub] at this
    exact this ▸ (ENNReal.ofReal_le_ofReal hhs).trans hr.le
  have hψn : ∫⁻ x, ‖ψ x - s x‖ₑ ∂ρ ≤ ε := by
    simp_rw [← eDist_eq_eNorm_sub] at hψh ⊢
    exact (lintegral_edist_triangle hψd.continuous.aestronglyMeasurable
      h.continuous.aestronglyMeasurable).trans
      ((add_le_add hψh hhs').trans (ENNReal.add_halves ε).le)
  refine ⟨ψ, hψd, hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hψL, hψL.trans hδW,
    hψ1, ?_⟩
  -- The pairing with `G` is controlled by the distance in `L¹(ρ)`.
  have h1 : ∫ x, G x (ψ x) ∂μ = ∫ x in L, G x (ψ x) ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (hψL h), map_zero]).symm
  have h2 : ∫ x in K, G x (σ x) ∂μ = ∫ x in L, G x (s x) ∂μ := by
    have hGs (x : E) : G x (s x) = K.indicator (fun x => G x (σ x)) x := by
      by_cases hx : x ∈ K <;> simp [hs_def, hx]
    simp_rw [hGs, setIntegral_indicator hK.measurableSet,
      inter_eq_right.mpr (show K ⊆ L from self_subset_cthickening K)]
  rw [h1, h2]
  exact (enorm_setIntegral_sub_le hGL hψd.continuous.aestronglyMeasurable hsμ hψ1 hs1).trans hψn

/-- **Approaching `∫_W ‖G‖` by pairings with test fields.** Let `G` be locally integrable on an
open set `W`, and let `σ` be a measurable field with `‖σ x‖ ≤ 1` and `G x (σ x) = ‖G x‖` for
almost every `x ∈ W`. Every `c < ∫_W ‖G‖` is exceeded by some pairing `∫ G ψ` with a smooth field
`ψ` of compact support in `W` and with `‖ψ x‖ ≤ 1`. The measure `μ` is arbitrary. -/
theorem exists_contDiff_lt_ofReal_integral_apply (hG : LocallyIntegrableOn G W μ) (hW : IsOpen W)
    {σ : E → F} (hσm : AEStronglyMeasurable σ (μ.restrict W)) (hσ : ∀ x, ‖σ x‖ ≤ 1)
    (hGσ : ∀ᵐ x ∂μ, x ∈ W → G x (σ x) = ‖G x‖) {c : ℝ≥0∞}
    (hc : c < ∫⁻ x in W, ‖G x‖ₑ ∂μ) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ W ∧ (∀ x, ‖ψ x‖ ≤ 1) ∧
      c < ENNReal.ofReal (∫ x, G x (ψ x) ∂μ) := by
  -- Exhaust `W` by compact sets, and pick one carrying more than `c` of `∫_W ‖G‖`.
  obtain ⟨V, hKc, hKW, hVm, hVU, -⟩ := Opens.exists_monotone_isCompact_closure_iUnion_eq ⟨W, hW⟩
  set K : ℕ → Set E := fun n => closure (V n)
  have hKm : Monotone K := fun m n h => closure_mono (hVm h)
  have hKU : ⋃ n, K n = W := Subset.antisymm (iUnion_subset hKW)
    (hVU.symm.subset.trans (iUnion_mono fun n => subset_closure))
  rw [← hKU, setLIntegral_iUnion_of_directed _ hKm.directed_le, lt_iSup_iff] at hc
  obtain ⟨n, hn⟩ := hc
  have hGK : IntegrableOn G (K n) μ := hG.integrableOn_compact_subset (hKW n) (hKc n)
  set a := ∫ x in K n, G x (σ x) ∂μ
  have ha : ∫⁻ x in K n, ‖G x‖ₑ ∂μ = ENNReal.ofReal a := by
    rw [← ofReal_integral_norm_eq_lintegral_eNorm hGK]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' (hKc n).measurableSet).2
      (hGσ.mono fun x hx hxK => hx (hKW n hxK))] with x hx
    exact hx.symm
  rw [ha] at hn
  have hct : c ≠ ⊤ := ne_top_of_lt hn
  have hca : c.toReal < a := (ENNReal.lt_ofReal_iff_toReal_lt hct).1 hn
  obtain ⟨ψ, hψd, hψc, hψW, hψ1, hψ⟩ := hG.exists_contDiff_enorm_integral_sub_setIntegral_le hW
    (hKc n) (hKW n) (hσm.mono_measure (Measure.restrict_mono (hKW n) le_rfl)) hσ
    (ε := ENNReal.ofReal ((a - c.toReal) / 2)) (by simp [hca])
  refine ⟨ψ, hψd, hψc, hψW, hψ1, (ENNReal.lt_ofReal_iff_toReal_lt hct).2 ?_⟩
  rw [Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff (by linarith)] at hψ
  linarith [neg_abs_le (∫ x, G x (ψ x) ∂μ - a)]

/-- **The local `L¹` norm by duality, with a norming field.** For a field `G` of continuous linear
functionals on a real Banach space `F`, locally integrable on `Ω`, and a measurable field `σ` with
`‖σ x‖ ≤ 1` attaining the norm, `G x (σ x) = ‖G x‖` for almost every `x ∈ Ω`, the integral
`∫_Ω ‖G‖` is the supremum of `∫ G x (φ x)` over test vector fields `φ ∈ 𝓓(Ω, F)` with
`‖φ x‖ ≤ 1`. The measure `μ` is arbitrary, and both sides may be infinite. -/
theorem iSup_ofReal_integral_apply_eq_setLIntegral_enorm_of_norming {Ω : Opens E}
    (hG : LocallyIntegrableOn G Ω μ) {σ : E → F} (hσm : AEStronglyMeasurable σ (μ.restrict Ω))
    (hσ : ∀ x, ‖σ x‖ ≤ 1) (hGσ : ∀ᵐ x ∂μ, x ∈ Ω → G x (σ x) = ‖G x‖) :
    ⨆ (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x, G x (φ x) ∂μ) =
      ∫⁻ x in Ω, ‖G x‖ₑ ∂μ  := by
  refine le_antisymm (iSup₂_le fun φ hφ => ?_) (le_of_forall_lt fun c hc => ?_)
  · exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans <|
      (Real.eNorm_eq_ofReal_abs _).symm.trans_le (φ.enorm_integral_apply_le_setLIntegral_enorm hφ G)
  obtain ⟨ψ, hψd, hψc, hψW, hψ1, hψ⟩ :=
    hG.exists_contDiff_lt_ofReal_integral_apply Ω.isOpen hσm hσ hGσ hc
  exact hψ.trans_le (le_iSup₂ (f := fun (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
    ENNReal.ofReal (∫ x, G x (φ x) ∂μ)) ⟨ψ, hψd, hψc, hψW⟩ hψ1)

end MeasureTheory.LocallyIntegrableOn

namespace MeasureTheory.LocallyIntegrableOn

variable [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {G : E → F →L[ℝ] ℝ}

/-- **The local `L¹` norm by duality.** For a field `G` of continuous linear functionals on a real
Hilbert space `F` that is locally integrable on `Ω`, `∫_Ω ‖G‖` is the supremum of `∫ G x (φ x)`
over test vector fields `φ ∈ 𝓓(Ω, F)` with `‖φ x‖ ≤ 1`. The measure `μ` is arbitrary, and both
sides may be infinite. -/
theorem iSup_ofReal_integral_apply_eq_setLIntegral_enorm (hG : LocallyIntegrableOn G Ω μ) :
    ⨆ (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x, G x (φ x) ∂μ) =
      ∫⁻ x in Ω, ‖G x‖ₑ ∂μ := by
  -- The unit field along the Riesz representative `g` of `G` attains the norm of `G`.
  set g : E → F := fun x => (InnerProductSpace.toDual ℝ F).symm (G x)
  have hgm : AEStronglyMeasurable g (μ.restrict Ω) :=
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp_aestronglyMeasurable
      hG.aestronglyMeasurable
  refine hG.iSup_ofReal_integral_apply_eq_setLIntegral_enorm_of_norming
    (σ := fun x => ‖g x‖⁻¹ • g x) (hgm.norm.aemeasurable.inv.aestronglyMeasurable.smul hgm)
    (fun x => ?_) (ae_of_all _ fun x _ => ?_)
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one
  · have hgG : ‖g x‖ = ‖G x‖ := (InnerProductSpace.toDual ℝ F).symm.norm_map (G x)
    have hGg : G x (g x) = ‖g x‖ ^ 2 := by
      rw [← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq]
    rw [map_smul, hGg, ← hgG, smul_eq_mul]
    rcases eq_or_ne ‖g x‖ 0 with h0 | h0
    · simp [h0]
    · field_simp

end MeasureTheory.LocallyIntegrableOn
