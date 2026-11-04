/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.MeasureTheory.Function.Lp.Subtype
public import TauCeti.MeasureTheory.Group.Arithmetic
public import TauCeti.MeasureTheory.Group.ModularCharacter
public import TauCeti.MeasureTheory.Group.SigmaCompactSupport
public import TauCeti.MeasureTheory.Integral.PeakFunction
public import TauCeti.MeasureTheory.Measure.Subtype
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-!
# Pullback Haar measures, coset integrals, and kernels on open subgroups

An open subgroup `H : OpenSubgroup G` of a locally compact topological group `G` is itself a locally
compact topological group (`OpenSubgroup.locallyCompactSpace`), and its inclusion `(↑) : H → G` is
an open measurable embedding. Pulling an ambient measure `μ` on `G` back to `H` via
`μ.comap ((↑) : H → G)` turns ambient analysis on `G` into subgroup analysis on `H`:

* **Haar measures, regularity, and modular character:** When `H` is an open subgroup of a Borel
  group `G`, `μ.comap ((↑) : H → G)` inherits left and right multiplication invariance,
  `IsOpenPosMeasure`, `IsHaarMeasure`, `Regular`, and `InnerRegular`; if `H` is moreover σ-compact
  and `μ` has `InnerRegularCompactLTTop` (as any regular Haar measure on a non-σ-compact group
  does), then `μ.comap (↑)` is both σ-finite and inner regular on `H`, and the modular character of
  `H` agrees with the restriction of the modular character of `G`
  (`OpenSubgroup.modularCharacter_eq`).
* **Translated-coset calculations:** For a measurable subgroup `H`, left translation `u ↦ g * u`
  from `(H, μ.comap (↑))` onto `(G, μ.restrict (g • H))` is a measure-preserving measurable
  embedding, identifying set integrals, lower Lebesgue integrals, `IntegrableOn`, and `Lᵖ` seminorms
  on left cosets `g • H` with integrals over `H` independent of the coset representative. For a
  regular Haar measure on a locally compact group, right translation `u ↦ u * g` scales the coset
  measure on `(· * g) '' H` by `Measure.modularCharacter g⁻¹`, giving the corresponding right-coset
  formulas and representative independence.
* **Countable `Lᵖ` families and kernels inside an open subgroup:** Countably many `Lᵖ` classes
  (`1 ≤ p < ∞`) simultaneously belong to the range of `MeasureTheory.Lp.extendByZeroComapₗᵢ` for a
  single σ-compact open subgroup `H`, and normalized nonnegative `L¹` peak kernels supported in any
  identity neighbourhood `U ∈ 𝓝 1` can be chosen inside `H`.

## Main statements

* `OpenSubgroup.instIsHaarMeasureComap`, `OpenSubgroup.instRegularComap`,
  `OpenSubgroup.innerRegular_comap_of_isSigmaCompact`, `OpenSubgroup.modularCharacter_eq`:
  Haar, regularity, and modular-character inheritance on open subgroups.
* `MeasureTheory.setIntegral_leftCoset_eq_comap`,
  `MeasureTheory.integral_mul_left_comap_eq_of_inv_mul_mem`,
  `MeasureTheory.setIntegral_rightCoset_eq_modularCharacter_smul_comap`,
  `MeasureTheory.modularCharacter_smul_integral_mul_right_comap_eq_of_mul_inv_mem`:
  translated-coset integral formulas and coset-representative independence.
* `MeasureTheory.Lp.exists_openSubgroup_isSigmaCompact_mem_range_extendByZeroComapₗᵢ`: countably
  many `Lᵖ` elements (`p < ∞`) come by zero extension from one σ-compact open subgroup.
* `OpenSubgroup.exists_lp_one_nonneg_integral_eq_one_norm_eq_one`: normalized nonnegative `L¹`
  kernels chosen inside a given open subgroup and identity neighbourhood.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §§2.2–2.4.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979),
  §§5.7 and 15.17.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

/-! ### Haar measure, regularity, and modular character on open subgroups -/

namespace OpenSubgroup

section HaarAndRegularity

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

@[to_additive]
instance instIsMulLeftInvariantComap [MeasurableMul G] [OpensMeasurableSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : OpenSubgroup G) :
    (μ.comap ((↑) : H → G)).IsMulLeftInvariant :=
  Measure.IsMulLeftInvariant.comap μ (f := SubgroupClass.subtype H)
    (MeasurableEmbedding.subtype_coe H.isOpen.measurableSet)

@[to_additive]
instance instIsMulRightInvariantComap [MeasurableMul G] [OpensMeasurableSpace G]
    (μ : Measure G) [μ.IsMulRightInvariant] (H : OpenSubgroup G) :
    (μ.comap ((↑) : H → G)).IsMulRightInvariant :=
  Measure.IsMulRightInvariant.comap μ (f := SubgroupClass.subtype H)
    (MeasurableEmbedding.subtype_coe H.isOpen.measurableSet)

@[to_additive]
instance instIsOpenPosMeasureComap [BorelSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
    (H : OpenSubgroup G) : (μ.comap ((↑) : H → G)).IsOpenPosMeasure :=
  Measure.IsOpenPosMeasure.comap μ H.isOpen.isOpenEmbedding_subtypeVal

/-- Pulling a Haar measure back to an open subgroup yields a Haar measure on the open subgroup. -/
@[to_additive /-- Pulling an additive Haar measure back to an open additive subgroup yields an
additive Haar measure on the open subgroup. -/]
instance instIsHaarMeasureComap [ContinuousMul G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (H : OpenSubgroup G) : (μ.comap ((↑) : H → G)).IsHaarMeasure where

@[to_additive]
instance instRegularComap [BorelSpace G] (μ : Measure G) [μ.Regular] (H : OpenSubgroup G) :
    (μ.comap ((↑) : H → G)).Regular :=
  Measure.Regular.comap' μ H.isOpen.isOpenEmbedding_subtypeVal

@[to_additive]
instance instInnerRegularComap [BorelSpace G] (μ : Measure G) [μ.InnerRegular]
    (H : OpenSubgroup G) : (μ.comap ((↑) : H → G)).InnerRegular :=
  Measure.InnerRegular.comap' μ H.isOpen.isOpenEmbedding_subtypeVal

@[to_additive]
instance instInnerRegularCompactLTTopComap [OpensMeasurableSpace G] (μ : Measure G)
    [μ.InnerRegularCompactLTTop] (H : OpenSubgroup G) :
    (μ.comap ((↑) : H → G)).InnerRegularCompactLTTop :=
  Measure.InnerRegularCompactLTTop.comap_subtype_coe H.isOpen.measurableSet

/-- On a σ-compact open subgroup `H`, the pullback of any measure with `InnerRegularCompactLTTop`
and finite measure on compacts (such as a regular Haar measure on a non-σ-compact group) is inner
regular on `H`. -/
@[to_additive /-- On a σ-compact open additive subgroup `H`, the pullback of any measure with
`InnerRegularCompactLTTop` and finite measure on compacts is inner regular on `H`. -/]
theorem innerRegular_comap_of_isSigmaCompact [BorelSpace G] (H : OpenSubgroup G) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]
    (hH : IsSigmaCompact (H : Set G)) : (μ.comap ((↑) : H → G)).InnerRegular := by
  have : SigmaFinite (μ.comap ((↑) : H → G)) := hH.sigmaFinite_comap (μ := μ)
  infer_instance

end HaarAndRegularity

section ModularCharacter

/-- **Modular character on an open subgroup.** On a locally compact topological group `G`, the
modular character of an open subgroup `H` is the restriction of the modular character of `G`. -/
@[simp]
theorem modularCharacter_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (H : OpenSubgroup G) (u : H) :
    Measure.modularCharacter u = Measure.modularCharacter (u : G) := by
  borelize G
  set μ : Measure G := Measure.haar
  set ν : Measure H := μ.comap ((↑) : H → G)
  have hcoe : MeasurableEmbedding ((↑) : H → G) :=
    MeasurableEmbedding.subtype_coe H.isOpen.measurableSet
  have hmap : Measure.map (· * u) ν = Measure.modularCharacter (u : G) • ν := by
    ext E hE
    rw [Measure.map_apply (measurable_mul_const u) hE, smul_apply, Measure.nnreal_smul_coe_apply,
      hcoe.comap_apply, hcoe.comap_apply]
    have himg : ((↑) : H → G) '' ((· * u) ⁻¹' E) = (· * (u : G)) ⁻¹' (((↑) : H → G) '' E) := by
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v * u, hv, rfl⟩
      · rintro ⟨w, hw, hwx⟩
        exact ⟨w * u⁻¹, by simpa using hw, by simp [hwx]⟩
    rw [himg, Measure.measure_preimage_mul_right_eq_modularCharacter_mul_of_regular]
  have hsmul : Measure.modularCharacter u • ν = Measure.modularCharacter (u : G) • ν := by
    rw [← Measure.map_right_mul_eq_modularCharacter_smul_of_regular (μ := ν) u, hmap]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have hKpos : ν K ≠ 0 := (ν.measure_pos_of_mem_nhds hK1).ne'
  have hKtop : ν K ≠ ∞ := hK.measure_lt_top.ne
  have heval := congrArg (fun m : Measure H ↦ m K) hsmul
  simp only [smul_apply, Measure.nnreal_smul_coe_apply] at heval
  exact_mod_cast ENNReal.mul_left_inj hKpos hKtop |>.1 heval

end ModularCharacter

end OpenSubgroup

/-! ### Translated-coset calculations -/

namespace MeasureTheory

section LeftCosets

variable {G S : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
  [SetLike S G] {H : S}

/-- Left coset parametrization `u ↦ g * u` from a measurable subobject `H` to `G` is a measurable
embedding. -/
@[to_additive /-- Left coset parametrization `u ↦ g + u` from a measurable additive subobject `H` to
`G` is a measurable embedding. -/]
theorem measurableEmbedding_mul_left_subtype_coe (hH : MeasurableSet (H : Set G)) (g : G) :
    MeasurableEmbedding (fun u : H ↦ g * (u : G)) :=
  (MeasurableEquiv.mulLeft g).measurableEmbedding.comp (MeasurableEmbedding.subtype_coe hH)

/-- Left coset parametrization `u ↦ g * u` pushes `μ.comap ((↑) : H → G)` forward to
`μ.restrict (g • (H : Set G))` whenever `μ` is left-invariant. -/
@[to_additive /-- Left coset parametrization `u ↦ g + u` pushes `μ.comap ((↑) : H → G)` forward to
`μ.restrict (g +ᵥ (H : Set G))` whenever `μ` is left-invariant. -/]
theorem measurePreserving_mul_left_subtype_coe [μ.IsMulLeftInvariant]
    (hH : MeasurableSet (H : Set G)) (g : G) :
    MeasurePreserving (fun u : H ↦ g * (u : G)) (μ.comap ((↑) : H → G))
      (μ.restrict (g • (H : Set G))) := by
  have hmp : MeasurePreserving ((↑) : H → G) (μ.comap ((↑) : H → G)) (μ.restrict (H : Set G)) :=
    measurePreserving_subtype_coe (μa := μ) hH
  simpa only [Function.comp_def, ← smul_eq_mul, image_smul] using
    ((measurePreserving_mul_left μ g).restrict_image_emb
      (MeasurableEquiv.mulLeft g).measurableEmbedding (H : Set G)).comp hmp

/-- **Lower Lebesgue integral over a left coset.** -/
@[to_additive setLIntegral_leftAddCoset_eq_comap
  /-- **Lower Lebesgue integral over a left additive coset.** -/]
theorem setLIntegral_leftCoset_eq_comap [μ.IsMulLeftInvariant] (hH : MeasurableSet (H : Set G))
    (g : G) (f : G → ℝ≥0∞) :
    ∫⁻ x in g • (H : Set G), f x ∂μ = ∫⁻ u : H, f (g * (u : G)) ∂(μ.comap ((↑) : H → G)) := by
  rw [← (measurePreserving_mul_left_subtype_coe (μ := μ) hH g).map_eq,
    (measurableEmbedding_mul_left_subtype_coe hH g).lintegral_map]

/-- **Bochner integral over a left coset.** -/
@[to_additive setIntegral_leftAddCoset_eq_comap
  /-- **Bochner integral over a left additive coset.** -/]
theorem setIntegral_leftCoset_eq_comap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [μ.IsMulLeftInvariant] (hH : MeasurableSet (H : Set G)) (g : G) (f : G → E) :
    ∫ x in g • (H : Set G), f x ∂μ = ∫ u : H, f (g * (u : G)) ∂(μ.comap ((↑) : H → G)) := by
  rw [← (measurePreserving_mul_left_subtype_coe (μ := μ) hH g).map_eq,
    (measurableEmbedding_mul_left_subtype_coe hH g).integral_map]

/-- **Integrability on a left coset.** -/
@[to_additive integrableOn_leftAddCoset_iff_comap
  /-- **Integrability on a left additive coset.** -/]
theorem integrableOn_leftCoset_iff_comap {E : Type*} [NormedAddCommGroup E]
    [μ.IsMulLeftInvariant] (hH : MeasurableSet (H : Set G)) (g : G) {f : G → E} :
    IntegrableOn f (g • (H : Set G)) μ ↔
      Integrable (fun u : H ↦ f (g * (u : G))) (μ.comap ((↑) : H → G)) := by
  rw [IntegrableOn, ← (measurePreserving_mul_left_subtype_coe (μ := μ) hH g).map_eq,
    (measurableEmbedding_mul_left_subtype_coe hH g).integrable_map_iff]
  rfl

/-- **`Lᵖ` seminorm on a left coset.** -/
@[to_additive eLpNorm_restrict_leftAddCoset_eq_comap
  /-- **`Lᵖ` seminorm on a left additive coset.** -/]
theorem eLpNorm_restrict_leftCoset_eq_comap {ε : Type*} [TopologicalSpace ε]
    [ESeminormedAddMonoid ε] [μ.IsMulLeftInvariant] (hH : MeasurableSet (H : Set G)) (g : G)
    (f : G → ε) (p : ℝ≥0∞) :
    eLpNorm f p (μ.restrict (g • (H : Set G))) =
      eLpNorm (fun u : H ↦ f (g * (u : G))) p (μ.comap ((↑) : H → G)) := by
  rw [← (measurePreserving_mul_left_subtype_coe (μ := μ) hH g).map_eq,
    (measurableEmbedding_mul_left_subtype_coe hH g).eLpNorm_map_measure]
  rfl

/-- **Left-coset representative independence for lower Lebesgue integrals.** -/
@[to_additive /-- **Left-coset representative independence for lower Lebesgue integrals.** -/]
theorem lintegral_mul_left_comap_eq_of_inv_mul_mem [SubgroupClass S G] [μ.IsMulLeftInvariant]
    (hH : MeasurableSet (H : Set G)) {g₁ g₂ : G} (hg : g₁⁻¹ * g₂ ∈ H) (f : G → ℝ≥0∞) :
    ∫⁻ u : H, f (g₁ * (u : G)) ∂(μ.comap ((↑) : H → G)) =
      ∫⁻ u : H, f (g₂ * (u : G)) ∂(μ.comap ((↑) : H → G)) := by
  have : (μ.comap ((↑) : H → G)).IsMulLeftInvariant :=
    Measure.IsMulLeftInvariant.comap μ (f := SubgroupClass.subtype H)
      (MeasurableEmbedding.subtype_coe hH)
  rw [← lintegral_mul_left_eq_self (fun u : H ↦ f (g₁ * (u : G))) ⟨g₁⁻¹ * g₂, hg⟩]
  congr 1 with u
  simp [MulMemClass.coe_mul, ← mul_assoc]

/-- **Left-coset representative independence for Bochner integrals.** -/
@[to_additive /-- **Left-coset representative independence for Bochner integrals.** -/]
theorem integral_mul_left_comap_eq_of_inv_mul_mem [SubgroupClass S G] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [μ.IsMulLeftInvariant]
    (hH : MeasurableSet (H : Set G)) {g₁ g₂ : G} (hg : g₁⁻¹ * g₂ ∈ H) (f : G → E) :
    ∫ u : H, f (g₁ * (u : G)) ∂(μ.comap ((↑) : H → G)) =
      ∫ u : H, f (g₂ * (u : G)) ∂(μ.comap ((↑) : H → G)) := by
  have : (μ.comap ((↑) : H → G)).IsMulLeftInvariant :=
    Measure.IsMulLeftInvariant.comap μ (f := SubgroupClass.subtype H)
      (MeasurableEmbedding.subtype_coe hH)
  rw [← integral_mul_left_eq_self (fun u : H ↦ f (g₁ * (u : G))) ⟨g₁⁻¹ * g₂, hg⟩]
  congr 1 with u
  simp [MulMemClass.coe_mul, ← mul_assoc]

end LeftCosets

section RightCosets

/-- Right coset parametrization `u ↦ u * g` from a measurable subobject `H` to `G` is a measurable
embedding. -/
@[to_additive /-- Right coset parametrization `u ↦ u + g` from a measurable additive subobject `H`
to `G` is a measurable embedding. -/]
theorem measurableEmbedding_mul_right_subtype_coe {G S : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [SetLike S G] {H : S} (hH : MeasurableSet (H : Set G)) (g : G) :
    MeasurableEmbedding (fun u : H ↦ (u : G) * g) :=
  (MeasurableEquiv.mulRight g).measurableEmbedding.comp (MeasurableEmbedding.subtype_coe hH)

variable {G S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular] [SetLike S G] {H : S}

/-- For a regular Haar measure `μ`, restricting `μ` to the right coset `(· * g) '' H` equals
`Measure.modularCharacter g⁻¹` times the pushforward of `μ.comap (↑)` along `u ↦ u * g`. -/
theorem restrict_rightCoset_eq_modularCharacter_smul_map_comap (hH : MeasurableSet (H : Set G))
    (g : G) :
    μ.restrict ((· * g) '' (H : Set G)) =
      Measure.modularCharacter g⁻¹ •
        Measure.map (fun u : H ↦ (u : G) * g) (μ.comap ((↑) : H → G)) := by
  have hsub : Measure.map ((↑) : H → G) (μ.comap ((↑) : H → G)) = μ.restrict (H : Set G) :=
    map_comap_subtype_coe hH μ
  have hmap : Measure.map (fun u : H ↦ (u : G) * g) (μ.comap ((↑) : H → G)) =
      Measure.modularCharacter g • μ.restrict ((· * g) '' (H : Set G)) := by
    have hcomp : (fun u : H ↦ (u : G) * g) = (· * g) ∘ ((↑) : H → G) := rfl
    rw [hcomp, ← Measure.map_map (measurable_mul_const g) measurable_subtype_coe, hsub]
    have hres := (MeasurableEquiv.mulRight g).measurableEmbedding.restrict_map μ
      ((· * g) '' (H : Set G))
    rw [MeasurableEquiv.coe_mulRight, preimage_image_eq _ (mul_left_injective g),
      Measure.map_right_mul_eq_modularCharacter_smul_of_regular, Measure.restrict_smul] at hres
    exact hres.symm
  rw [hmap, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- Pulling a regular Haar measure `μ` back along `u ↦ (u : G) * g` scales `μ.comap (↑)` by
`Measure.modularCharacter g⁻¹`. -/
theorem comap_mul_right_subtype_coe (hH : MeasurableSet (H : Set G)) (g : G) :
    μ.comap (fun u : H ↦ (u : G) * g) =
      Measure.modularCharacter g⁻¹ • μ.comap ((↑) : H → G) := by
  have hcoe : MeasurableEmbedding ((↑) : H → G) := MeasurableEmbedding.subtype_coe hH
  ext E hE
  rw [(measurableEmbedding_mul_right_subtype_coe hH g).comap_apply, smul_apply,
    Measure.nnreal_smul_coe_apply, hcoe.comap_apply]
  have himg : (fun u : H ↦ (u : G) * g) '' E = (· * g⁻¹) ⁻¹' (((↑) : H → G) '' E) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by simp [mul_assoc]⟩
    · rintro ⟨u, hu, hux⟩
      exact ⟨u, hu, by simpa [eq_mul_inv_iff_mul_eq] using hux⟩
  rw [himg, Measure.measure_preimage_mul_right_eq_modularCharacter_mul_of_regular]

/-- **Lower Lebesgue integral over a right coset.** -/
theorem setLIntegral_rightCoset_eq_modularCharacter_mul_comap (hH : MeasurableSet (H : Set G))
    (g : G) (f : G → ℝ≥0∞) :
    ∫⁻ x in (· * g) '' (H : Set G), f x ∂μ =
      Measure.modularCharacter g⁻¹ * ∫⁻ u : H, f ((u : G) * g) ∂(μ.comap ((↑) : H → G)) := by
  rw [restrict_rightCoset_eq_modularCharacter_smul_map_comap hH g, lintegral_smul_measure,
    ENNReal.smul_def, smul_eq_mul, (measurableEmbedding_mul_right_subtype_coe hH g).lintegral_map]

/-- **Bochner integral over a right coset.** -/
theorem setIntegral_rightCoset_eq_modularCharacter_smul_comap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hH : MeasurableSet (H : Set G)) (g : G) (f : G → E) :
    ∫ x in (· * g) '' (H : Set G), f x ∂μ =
      Measure.modularCharacter g⁻¹ • ∫ u : H, f ((u : G) * g) ∂(μ.comap ((↑) : H → G)) := by
  rw [restrict_rightCoset_eq_modularCharacter_smul_map_comap hH g, integral_smul_nnreal_measure,
    (measurableEmbedding_mul_right_subtype_coe hH g).integral_map]

/-- **Integrability on a right coset.** -/
theorem integrableOn_rightCoset_iff_comap {E : Type*} [NormedAddCommGroup E]
    (hH : MeasurableSet (H : Set G)) (g : G) {f : G → E} :
    IntegrableOn f ((· * g) '' (H : Set G)) μ ↔
      Integrable (fun u : H ↦ f ((u : G) * g)) (μ.comap ((↑) : H → G)) := by
  have hc0 : (Measure.modularCharacter g⁻¹ : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.modularCharacterFun_pos g⁻¹).ne'
  rw [IntegrableOn, restrict_rightCoset_eq_modularCharacter_smul_map_comap hH g,
    ENNReal.smul_def, integrable_smul_measure hc0 ENNReal.coe_ne_top,
    (measurableEmbedding_mul_right_subtype_coe hH g).integrable_map_iff]
  rfl

/-- **Right-coset representative independence for lower Lebesgue integrals.** -/
theorem modularCharacter_mul_lintegral_mul_right_comap_eq_of_mul_inv_mem [SubgroupClass S G]
    (hH : MeasurableSet (H : Set G)) {g₁ g₂ : G} (hg : g₁ * g₂⁻¹ ∈ H) (f : G → ℝ≥0∞) :
    Measure.modularCharacter g₁⁻¹ * ∫⁻ u : H, f ((u : G) * g₁) ∂(μ.comap ((↑) : H → G)) =
      Measure.modularCharacter g₂⁻¹ * ∫⁻ u : H, f ((u : G) * g₂) ∂(μ.comap ((↑) : H → G)) := by
  rw [← setLIntegral_rightCoset_eq_modularCharacter_mul_comap hH g₁ f,
    ← setLIntegral_rightCoset_eq_modularCharacter_mul_comap hH g₂ f]
  have hcoset : (· * g₁) '' (H : Set G) = (· * g₂) '' (H : Set G) := by
    simpa [← image_smul, op_smul_eq_mul] using
      ((rightCoset_eq_iff (Subgroup.ofClass H) (x := g₂) (y := g₁)).2 hg).symm
  rw [hcoset]

/-- **Right-coset representative independence for Bochner integrals.** -/
theorem modularCharacter_smul_integral_mul_right_comap_eq_of_mul_inv_mem [SubgroupClass S G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hH : MeasurableSet (H : Set G))
    {g₁ g₂ : G} (hg : g₁ * g₂⁻¹ ∈ H) (f : G → E) :
    Measure.modularCharacter g₁⁻¹ • ∫ u : H, f ((u : G) * g₁) ∂(μ.comap ((↑) : H → G)) =
      Measure.modularCharacter g₂⁻¹ • ∫ u : H, f ((u : G) * g₂) ∂(μ.comap ((↑) : H → G)) := by
  rw [← setIntegral_rightCoset_eq_modularCharacter_smul_comap hH g₁ f,
    ← setIntegral_rightCoset_eq_modularCharacter_smul_comap hH g₂ f]
  have hcoset : (· * g₁) '' (H : Set G) = (· * g₂) '' (H : Set G) := by
    simpa [← image_smul, op_smul_eq_mul] using
      ((rightCoset_eq_iff (Subgroup.ofClass H) (x := g₂) (y := g₁)).2 hg).symm
  rw [hcoset]

end RightCosets

/-! ### Countable `Lᵖ` families and kernels inside open subgroups -/

namespace Lp

/-- **Countably many `Lᵖ` functions (`1 ≤ p < ∞`) come from a single σ-compact open subgroup.**
On a locally compact Hausdorff group with a measure satisfying `InnerRegularCompactLTTop`, any
countable family in `Lp E p μ` (`p ≠ ∞`) lies in the range of `Lp.extendByZeroComapₗᵢ` for one
σ-compact open subgroup `H`. -/
@[to_additive /-- **Countably many `Lᵖ` functions (`1 ≤ p < ∞`) come from a single σ-compact open
additive subgroup.** -/]
theorem exists_openSubgroup_isSigmaCompact_mem_range_extendByZeroComapₗᵢ
    {G E ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {μ : Measure G} [μ.InnerRegularCompactLTTop] [NormedAddCommGroup E]
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) [Countable ι] (f : ι → Lp E p μ) :
    ∃ H : OpenSubgroup G, IsSigmaCompact (H : Set G) ∧
      ∀ i, f i ∈ Set.range (extendByZeroComapₗᵢ (E := E) (p := p) 𝕜 μ H.isOpen.measurableSet) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  obtain ⟨H, hH, hfH⟩ := exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero fun i ↦
    (Lp.memLp (f i)).aefinStronglyMeasurable hp₀ hp
  exact ⟨H, hH, fun i ↦ (mem_range_extendByZeroComapₗᵢ_iff H.isOpen.measurableSet).2 (hfH i)⟩

end Lp

end MeasureTheory

namespace OpenSubgroup

/-- **`L¹` peak kernels inside an open subgroup.** For a locally finite measure positive on nonempty
open sets, every open subgroup `H` and neighbourhood `U ∈ 𝓝 1` admit a nonnegative subtype kernel
`k₀ ∈ L¹(H, μ.comap (↑))` of unit integral and unit norm whose extension by zero to `G` vanishes
almost everywhere outside `U`. -/
@[to_additive exists_lp_one_nonneg_integral_eq_one_norm_eq_one
  /-- **`L¹` peak kernels inside an open additive subgroup.** -/]
theorem exists_lp_one_nonneg_integral_eq_one_norm_eq_one {G : Type*} [Group G]
    [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (H : OpenSubgroup G) (μ : Measure G) [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ]
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ k₀ : Lp ℝ 1 (μ.comap ((↑) : H → G)),
      0 ≤ k₀ ∧ ∫ u : H, k₀ u ∂(μ.comap ((↑) : H → G)) = 1 ∧ ‖k₀‖ = 1 ∧
        ∀ᵐ x ∂μ, x ∉ U →
          Lp.extendByZeroComapₗᵢ ℝ μ H.isOpen.measurableSet k₀ x = 0 := by
  obtain ⟨k, hk0, hk_int, hk_norm, hkUH⟩ :=
    TauCeti.exists_nonneg_integral_eq_one_norm_eq_one μ
      (inter_mem hU (H.isOpen.mem_nhds H.one_mem))
  have hH : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  have hk_compl : (k : G → ℝ) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 :=
    (ae_restrict_iff' hH.compl).2 (hkUH.mono fun x hx hxH ↦ hx fun hxUH ↦ hxH hxUH.2)
  refine ⟨Lp.restrictComapCLM ℝ μ 1 hH k, Lp.restrictComapCLM_nonneg hH hk0,
    (Lp.integral_restrictComapCLM_of_ae_restrict_compl_eq_zero hH hk_compl).trans hk_int,
    (Lp.norm_restrictComapCLM_of_ae_restrict_compl_eq_zero hH hk_compl).trans hk_norm, ?_⟩
  rw [Lp.extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero hH hk_compl]
  exact hkUH.mono fun x hx hxU ↦ hx fun hxUH ↦ hxU hxUH.1

end OpenSubgroup
