/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import TauCeti.MeasureTheory.Group.ModularCharacter
public import TauCeti.MeasureTheory.Integral.ComapSubtype
public import TauCeti.MeasureTheory.Integral.PeakFunction
public import TauCeti.MeasureTheory.Measure.Regular
public import TauCeti.MeasureTheory.Measure.Typeclasses.SFinite
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic

/-!
# Restricted Haar measures, coset integrals, convolution and peak kernels on open subgroups

Let `H : OpenSubgroup G` be an open subgroup of a topological group `G` carrying a measure `μ`.
Because `(↑) : H → G` is an open embedding, the subtype pullback measure `μ.comap ((↑) : H → G)`
inherits left and right invariance, openness positivity, finiteness on compact sets, left Haar
structure, outer regularity, compact inner regularity on finite-measure sets, inner regularity, and
regularity directly as typeclass instances. When `H` is σ-compact and `μ` is finite on compact
sets, `μ.comap ((↑) : H → G)` is σ-finite (`OpenSubgroup.sigmaFinite_comap`), hence inner regular
whenever `μ` is inner regular on sets of finite measure (`OpenSubgroup.innerRegular_comap`). On a
locally compact group, the modular character of `H` agrees with the restriction of the modular
character of `G` (`OpenSubgroup.modularCharacter_coe`).

This file develops five families of results for `(H, μ.comap ((↑) : H → G))`:

1. **Ambient integral agreement and subgroup independence**: when `f` vanishes `μ`-almost everywhere
   outside `H`, its Bochner integral on `G` agrees with that of its restriction to
   `(H, μ.comap (↑))` and is independent of the open subgroup `H` chosen
   (`OpenSubgroup.integral_eq_comap`, `OpenSubgroup.integral_comap_congr`); the generic subtype
   bridges in `TauCeti.MeasureTheory.Integral.ComapSubtype` give the corresponding facts for
   `AEStronglyMeasurable`, `lintegral`, `eLpNorm`, `MemLp`, and `Integrable` via
   `H.isOpen.measurableSet`.
2. **Left-coset calculations**: for a left-invariant measure `μ` and any `g : G`, pushing
   `μ.comap (↑)` forward along `y : H ↦ g * y` yields `μ.restrict (g • (H : Set G))`, reducing set
   integrals, `Lᵖ` seminorms, `MemLp`, and `IntegrableOn` on `g • (H : Set G)` to
   `(H, μ.comap (↑))`.
3. **Right-coset calculations**: for a regular left Haar measure `μ` on a locally compact group and
   any `g : G`, `μ.restrict (MulOpposite.op g • (H : Set G))` equals `Measure.modularCharacter g⁻¹`
   times the pushforward of `μ.comap (↑)` along `y : H ↦ (y : G) * g`, yielding weighted right-coset
   formulas for set integrals, `Lᵖ` seminorms, `MemLp`, and `IntegrableOn`.
4. **Pointwise convolution reduction**: when a kernel `h` vanishes `μ`-almost everywhere outside
   `H`, the convolution integral `∫ y, h y • f (y⁻¹ * x) ∂μ` reduces at every `x : G` to
   `(H, μ.comap (↑))`, is independent of `H`, and on each right coset `x = z * g` (`z : H`)
   becomes the `H`-convolution against the coset slice `w : H ↦ f ((w : G) * g)`. When `f` also
   vanishes `μ`-almost everywhere outside `H` and `μ` is a regular Haar measure, the convolution
   integrand is `μ`-almost everywhere zero—hence its integral vanishes—at every `x ∉ H`.
5. **Peak kernels inside `H`**: since `H` is open it contains a neighbourhood of the identity, so
   for any identity neighbourhood `U` there exist nonnegative `C_c(G, ℝ)` unit-integral peak kernels
   supported inside both `U` and `H` and norm-one `L¹(G, μ; 𝕜)` unit-integral peak kernels vanishing
   almost everywhere outside both `U` and `H`.

## Main results

* `OpenSubgroup.instIsMulLeftInvariantComap`, `OpenSubgroup.instIsHaarMeasureComap`,
  `OpenSubgroup.instRegularComap`, `OpenSubgroup.instInnerRegularCompactLTTopComap`: invariant,
  Haar, and regular measure instances on `μ.comap ((↑) : H → G)`.
* `OpenSubgroup.sigmaFinite_comap`, `OpenSubgroup.innerRegular_comap`: σ-finiteness and inner
  regularity of `μ.comap ((↑) : H → G)` when `IsSigmaCompact (H : Set G)`.
* `OpenSubgroup.modularCharacter_coe`:
  `Measure.modularCharacter (y : G) = Measure.modularCharacter y` for `y : H`.
* `OpenSubgroup.integral_eq_comap`, `OpenSubgroup.integral_comap_congr`: ambient Bochner integral
  agreement and subgroup independence.
* `OpenSubgroup.map_mul_left_comap`, `OpenSubgroup.setIntegral_smul_eq_integral_comap`,
  `OpenSubgroup.restrict_op_smul_eq_smul_map_comap`,
  `OpenSubgroup.setIntegral_op_smul_eq_integral_comap`: left- and right-coset measure and integral
  identities.
* `OpenSubgroup.integral_smul_inv_mul_eq_comap`, `OpenSubgroup.integral_smul_inv_mul_comap_congr`,
  `OpenSubgroup.integral_smul_inv_mul_mul_eq_comap`,
  `OpenSubgroup.integral_smul_inv_mul_eq_zero_of_notMem`: pointwise convolution reduction and
  vanishing outside `H`.
* `OpenSubgroup.exists_nonneg_tsupport_subset_integral_eq_one` and
  `OpenSubgroup.exists_integral_eq_one_norm_eq_one`: nonnegative `C_c(G, ℝ)` unit-integral kernels
  supported inside both `U` and `H`, and norm-one `L¹(G, μ; 𝕜)` unit-integral kernels vanishing
  almost everywhere outside both `U` and `H`, for any identity neighbourhood `U` and open subgroup
  `H`.

## References

* E. Hewitt, K. A. Ross, *Abstract Harmonic Analysis I*, 2nd ed., Springer (1979), §15.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Appendix G.
-/

public section

open Filter MeasureTheory MulOpposite Set Topology
open scoped CompactlySupported ENNReal NNReal Pointwise

namespace OpenSubgroup

section Instances

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (H : OpenSubgroup G)
  (μ : Measure G)

/-- An open subgroup of a group with measurable multiplication has measurable multiplication. -/
@[to_additive /-- An open additive subgroup of an additive group with measurable addition has
measurable addition. -/]
instance instMeasurableMul [MeasurableMul G] : MeasurableMul H where
  measurable_const_mul c := ((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk
  measurable_mul_const c := ((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk

/-- An open subgroup of a group with measurable inversion has measurable inversion. -/
@[to_additive /-- An open additive subgroup of an additive group with measurable negation has
measurable negation. -/]
instance instMeasurableInv [MeasurableInv G] : MeasurableInv H where
  measurable_inv := (measurable_inv.comp measurable_subtype_coe).subtype_mk

/-- The subtype inclusion `(↑) : H → G` of an open subgroup is a measurable embedding. -/
@[to_additive /-- The subtype inclusion `(↑) : H → G` of an open additive subgroup is a measurable
embedding. -/]
theorem measurableEmbedding_coe [OpensMeasurableSpace G] :
    MeasurableEmbedding ((↑) : H → G) :=
  MeasurableEmbedding.subtype_coe H.isOpen.measurableSet

/-- Pulling a left-invariant measure back to an open subgroup yields a left-invariant measure. -/
@[to_additive /-- Pulling a left-invariant measure back to an open additive subgroup yields a
left-invariant measure. -/]
instance instIsMulLeftInvariantComap [OpensMeasurableSpace G] [MeasurableMul G]
    [μ.IsMulLeftInvariant] : (μ.comap ((↑) : H → G)).IsMulLeftInvariant :=
  Measure.IsMulLeftInvariant.comap (f := SubgroupClass.subtype H) μ H.measurableEmbedding_coe

/-- Pulling a right-invariant measure back to an open subgroup yields a right-invariant measure. -/
@[to_additive /-- Pulling a right-invariant measure back to an open additive subgroup yields a
right-invariant measure. -/]
instance instIsMulRightInvariantComap [OpensMeasurableSpace G] [MeasurableMul G]
    [μ.IsMulRightInvariant] : (μ.comap ((↑) : H → G)).IsMulRightInvariant :=
  Measure.IsMulRightInvariant.comap (f := SubgroupClass.subtype H) μ H.measurableEmbedding_coe

/-- Pulling a measure finite on compact sets back to an open subgroup yields a measure finite on
compact sets. -/
@[to_additive /-- Pulling a measure finite on compact sets back to an open additive subgroup yields
a measure finite on compact sets. -/]
instance instIsFiniteMeasureOnCompactsComap [OpensMeasurableSpace G]
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (μ.comap ((↑) : H → G)) :=
  IsFiniteMeasureOnCompacts.comap' μ continuous_subtype_val H.measurableEmbedding_coe

/-- Pulling an outer regular measure back to an open subgroup yields an outer regular measure. -/
@[to_additive /-- Pulling an outer regular measure back to an open additive subgroup yields an outer
regular measure. -/]
instance instOuterRegularComap [OpensMeasurableSpace G] [μ.OuterRegular] :
    (μ.comap ((↑) : H → G)).OuterRegular :=
  Measure.OuterRegular.comap' μ continuous_subtype_val H.measurableEmbedding_coe

/-- Pulling a measure positive on nonempty open sets back to an open subgroup yields a measure
positive on nonempty open sets. -/
@[to_additive /-- Pulling a measure positive on nonempty open sets back to an open additive subgroup
yields a measure positive on nonempty open sets. -/]
instance instIsOpenPosMeasureComap [BorelSpace G] [μ.IsOpenPosMeasure] :
    (μ.comap ((↑) : H → G)).IsOpenPosMeasure :=
  Measure.IsOpenPosMeasure.comap μ H.isOpen.isOpenEmbedding_subtypeVal

/-- Pulling a left Haar measure back to an open subgroup yields a left Haar measure. -/
@[to_additive /-- Pulling a left additive Haar measure back to an open additive subgroup yields a
left additive Haar measure. -/]
instance instIsHaarMeasureComap [BorelSpace G] [MeasurableMul G] [μ.IsHaarMeasure] :
    (μ.comap ((↑) : H → G)).IsHaarMeasure := {}

/-- Pulling a measure that is inner regular for compact sets on finite-measure sets back to an open
subgroup preserves compact inner regularity on finite-measure sets. -/
@[to_additive /-- Pulling a measure that is inner regular for compact sets on finite-measure sets
back to an open additive subgroup preserves compact inner regularity on finite-measure sets. -/]
instance instInnerRegularCompactLTTopComap [BorelSpace G] [μ.InnerRegularCompactLTTop] :
    (μ.comap ((↑) : H → G)).InnerRegularCompactLTTop :=
  Measure.InnerRegularCompactLTTop.comap' μ H.isOpen.isOpenEmbedding_subtypeVal

/-- Pulling an inner regular measure back to an open subgroup yields an inner regular measure. -/
@[to_additive /-- Pulling an inner regular measure back to an open additive subgroup yields an inner
regular measure. -/]
instance instInnerRegularComap [BorelSpace G] [μ.InnerRegular] :
    (μ.comap ((↑) : H → G)).InnerRegular :=
  Measure.InnerRegular.comap' μ H.isOpen.isOpenEmbedding_subtypeVal

/-- Pulling a regular measure back to an open subgroup yields a regular measure. -/
@[to_additive /-- Pulling a regular measure back to an open additive subgroup yields a regular
measure. -/]
instance instRegularComap [BorelSpace G] [μ.Regular] : (μ.comap ((↑) : H → G)).Regular :=
  Measure.Regular.comap' μ H.isOpen.isOpenEmbedding_subtypeVal

/-- If `H` is σ-compact and `μ` is finite on compact sets, the restricted measure
`μ.comap ((↑) : H → G)` is σ-finite. -/
@[to_additive /-- If `H` is σ-compact and `μ` is finite on compact sets, the restricted measure
`μ.comap ((↑) : H → G)` is σ-finite. -/]
theorem sigmaFinite_comap [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
    (hH : IsSigmaCompact (H : Set G)) : SigmaFinite (μ.comap ((↑) : H → G)) :=
  hH.sigmaFinite_comap_subtype H.isOpen.measurableSet

/-- If `H` is σ-compact and `μ` is finite on compact sets and inner regular on sets of finite
measure, then `μ.comap ((↑) : H → G)` is inner regular on all measurable sets. -/
@[to_additive /-- If `H` is σ-compact and `μ` is finite on compact sets and inner regular on sets of
finite measure, then `μ.comap ((↑) : H → G)` is inner regular on all measurable sets. -/]
theorem innerRegular_comap [BorelSpace G] [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] (hH : IsSigmaCompact (H : Set G)) :
    (μ.comap ((↑) : H → G)).InnerRegular := by
  have := H.sigmaFinite_comap μ hH
  infer_instance

end Instances

section ModularCharacter

/-- On a locally compact topological group `G`, the modular character of `G` restricts on any open
subgroup `H` to the modular character of `H`. -/
@[simp]
theorem modularCharacter_coe {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (H : OpenSubgroup G) (y : H) :
    Measure.modularCharacter (y : G) = Measure.modularCharacter y := by
  borelize G
  let μ : Measure G := Measure.haar
  let ν : Measure H := μ.comap ((↑) : H → G)
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have hK0 : ν K ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hKtop : ν K ≠ ∞ := hK.measure_lt_top.ne
  -- Compare right translation of `K` by `y` on `H` with right translation of `(↑) '' K` on `G`.
  have himg : ((↑) : H → G) '' ((· * y) ⁻¹' K) = (· * (y : G)) ⁻¹' (((↑) : H → G) '' K) := by
    simp only [← Set.image_mul_right', Set.image_image]
    rfl
  have hν : (Measure.modularCharacter y : ℝ≥0∞) * ν K = ν ((· * y) ⁻¹' K) := by
    simpa [ν] using
      (Measure.measure_preimage_mul_right_eq_modularCharacter_mul_of_regular ν y K).symm
  have hμ : ν ((· * y) ⁻¹' K) = (Measure.modularCharacter (y : G) : ℝ≥0∞) * ν K := by
    rw [H.measurableEmbedding_coe.comap_apply, himg,
      Measure.measure_preimage_mul_right_eq_modularCharacter_mul_of_regular μ (y : G),
      ← H.measurableEmbedding_coe.comap_apply]
  exact ENNReal.coe_inj.1 ((ENNReal.mul_left_inj hK0 hKtop).1 (hμ.symm.trans hν.symm))

end ModularCharacter

section AmbientAgreement

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  {μ : Measure G} {H H₁ H₂ : OpenSubgroup G}

/-- If `f` vanishes `μ`-almost everywhere outside an open subgroup `H`, its ambient Bochner
integral equals its Bochner integral on `(H, μ.comap (↑))`. -/
@[to_additive /-- If `f` vanishes `μ`-almost everywhere outside an open additive subgroup `H`, its
ambient Bochner integral equals its Bochner integral on `(H, μ.comap (↑))`. -/]
theorem integral_eq_comap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : G → E}
    (hf : f =ᵐ[μ.restrict (H : Set G)ᶜ] 0) :
    ∫ x, f x ∂μ = ∫ x : H, f x ∂(μ.comap ((↑) : H → G)) :=
  integral_eq_subtype_comap_of_ae_eq_zero H.isOpen.measurableSet hf

/-- Subgroup independence of the Bochner integral for a function vanishing almost everywhere outside
`H₁` and `H₂`. -/
@[to_additive /-- Subgroup independence of the Bochner integral for a function vanishing almost
everywhere outside `H₁` and `H₂`. -/]
theorem integral_comap_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : G → E}
    (hf₁ : f =ᵐ[μ.restrict (H₁ : Set G)ᶜ] 0) (hf₂ : f =ᵐ[μ.restrict (H₂ : Set G)ᶜ] 0) :
    ∫ x : H₁, f x ∂(μ.comap ((↑) : H₁ → G)) = ∫ x : H₂, f x ∂(μ.comap ((↑) : H₂ → G)) :=
  integral_subtype_comap_congr H₁.isOpen.measurableSet H₂.isOpen.measurableSet hf₁ hf₂

end AmbientAgreement

section LeftCoset

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant] (H : OpenSubgroup G)

/-- Left translation `y : H ↦ g * y` of an open subgroup is a measurable embedding into `G`. -/
@[to_additive /-- Left translation `y : H ↦ g + y` of an open additive subgroup is a measurable
embedding into `G`. -/]
theorem measurableEmbedding_mul_left (g : G) :
    MeasurableEmbedding (fun y : H ↦ g * (y : G)) :=
  (MeasurableEquiv.mulLeft g).measurableEmbedding.comp H.measurableEmbedding_coe

/-- For a left-invariant measure `μ`, pushing `μ.comap ((↑) : H → G)` forward along `y : H ↦ g * y`
gives the restriction `μ.restrict (g • (H : Set G))` to the left coset. -/
@[to_additive /-- For a left-invariant measure `μ`, pushing `μ.comap ((↑) : H → G)` forward along
`y : H ↦ g + y` gives the restriction `μ.restrict (g +ᵥ (H : Set G))` to the left coset. -/]
theorem map_mul_left_comap (g : G) :
    (μ.comap ((↑) : H → G)).map (fun y : H ↦ g * (y : G)) = μ.restrict (g • (H : Set G)) := by
  have hpre : (fun x ↦ g * x) ⁻¹' (g • (H : Set G)) = (H : Set G) := by
    ext x
    simp [mem_leftCoset_iff]
  have hmap := (MeasurableEquiv.mulLeft g).restrict_map μ (g • (H : Set G))
  rw [MeasurableEquiv.coe_mulLeft, map_mul_left_eq_self, hpre,
    ← map_comap_subtype_coe H.isOpen.measurableSet,
    Measure.map_map (measurable_const_mul g) measurable_subtype_coe] at hmap
  exact hmap.symm

/-- Almost-everywhere properties on the left coset `g • (H : Set G)` reduce to
`(H, μ.comap (↑))`. -/
@[to_additive /-- Almost-everywhere properties on the left coset `g +ᵥ (H : Set G)` reduce to
`(H, μ.comap (↑))`. -/]
theorem ae_restrict_smul_iff_comap (g : G) {P : G → Prop} :
    (∀ᵐ z ∂μ.restrict (g • (H : Set G)), P z) ↔
      ∀ᵐ y : H ∂(μ.comap ((↑) : H → G)), P (g * (y : G)) := by
  rw [← H.map_mul_left_comap g, (H.measurableEmbedding_mul_left g).ae_map_iff]

/-- Almost-everywhere strong measurability on the left coset `g • (H : Set G)` reduces to
`(H, μ.comap (↑))`. -/
@[to_additive /-- Almost-everywhere strong measurability on the left coset `g +ᵥ (H : Set G)`
reduces to `(H, μ.comap (↑))`. -/]
theorem aestronglyMeasurable_smul_iff_comap {β : Type*} [TopologicalSpace β] (g : G) {f : G → β} :
    AEStronglyMeasurable f (μ.restrict (g • (H : Set G))) ↔
      AEStronglyMeasurable (fun y : H ↦ f (g * (y : G))) (μ.comap ((↑) : H → G)) := by
  rw [← H.map_mul_left_comap g, (H.measurableEmbedding_mul_left g).aestronglyMeasurable_map_iff]
  rfl

/-- Lower Lebesgue integral over a left coset `g • (H : Set G)` in terms of `(H, μ.comap (↑))`. -/
@[to_additive /-- Lower Lebesgue integral over a left coset `g +ᵥ (H : Set G)` in terms of
`(H, μ.comap (↑))`. -/]
theorem setLIntegral_smul_eq_lintegral_comap (g : G) (f : G → ℝ≥0∞) :
    ∫⁻ z in g • (H : Set G), f z ∂μ = ∫⁻ y : H, f (g * (y : G)) ∂(μ.comap ((↑) : H → G)) := by
  rw [← H.map_mul_left_comap g, (H.measurableEmbedding_mul_left g).lintegral_map]

/-- The `Lᵖ` seminorm on a left coset `g • (H : Set G)` equals the `Lᵖ` seminorm of
`y : H ↦ f (g * y)` on `(H, μ.comap (↑))`. -/
@[to_additive /-- The `Lᵖ` seminorm on a left coset `g +ᵥ (H : Set G)` equals the `Lᵖ` seminorm of
`y : H ↦ f (g + y)` on `(H, μ.comap (↑))`. -/]
theorem eLpNorm_restrict_smul_eq_comap {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (g : G) (f : G → ε) (p : ℝ≥0∞) :
    eLpNorm f p (μ.restrict (g • (H : Set G))) =
      eLpNorm (fun y : H ↦ f (g * (y : G))) p (μ.comap ((↑) : H → G)) := by
  rw [← H.map_mul_left_comap g, (H.measurableEmbedding_mul_left g).eLpNorm_map_measure]
  rfl

/-- Membership in `Lᵖ` on a left coset `g • (H : Set G)` reduces to `(H, μ.comap (↑))`. -/
@[to_additive /-- Membership in `Lᵖ` on a left coset `g +ᵥ (H : Set G)` reduces to
`(H, μ.comap (↑))`. -/]
theorem memLp_restrict_smul_iff_comap {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (g : G) {f : G → ε} {p : ℝ≥0∞} :
    MemLp f p (μ.restrict (g • (H : Set G))) ↔
      MemLp (fun y : H ↦ f (g * (y : G))) p (μ.comap ((↑) : H → G)) := by
  rw [← H.map_mul_left_comap g, (H.measurableEmbedding_mul_left g).memLp_map_measure_iff]
  rfl

/-- Integrability on a left coset `g • (H : Set G)` reduces to `(H, μ.comap (↑))`. -/
@[to_additive /-- Integrability on a left coset `g +ᵥ (H : Set G)` reduces to
`(H, μ.comap (↑))`. -/]
theorem integrableOn_smul_iff_comap {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]
    (g : G) {f : G → ε} :
    IntegrableOn f (g • (H : Set G)) μ ↔
      Integrable (fun y : H ↦ f (g * (y : G))) (μ.comap ((↑) : H → G)) := by
  rw [IntegrableOn, ← H.map_mul_left_comap g, (H.measurableEmbedding_mul_left g).integrable_map_iff]
  rfl

/-- Bochner integral over a left coset `g • (H : Set G)` in terms of `(H, μ.comap (↑))`. -/
@[to_additive /-- Bochner integral over a left coset `g +ᵥ (H : Set G)` in terms of
`(H, μ.comap (↑))`. -/]
theorem setIntegral_smul_eq_integral_comap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : G) (f : G → E) :
    ∫ z in g • (H : Set G), f z ∂μ = ∫ y : H, f (g * (y : G)) ∂(μ.comap ((↑) : H → G)) := by
  rw [← H.map_mul_left_comap g, (H.measurableEmbedding_mul_left g).integral_map]

end LeftCoset

section RightCoset

/-- Right translation `y : H ↦ (y : G) * g` of an open subgroup is a measurable embedding into
`G`. -/
@[to_additive /-- Right translation `y : H ↦ (y : G) + g` of an open additive subgroup is a
measurable embedding into `G`. -/]
theorem measurableEmbedding_mul_right {G : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] (H : OpenSubgroup G) (g : G) :
    MeasurableEmbedding (fun y : H ↦ (y : G) * g) :=
  (MeasurableEquiv.mulRight g).measurableEmbedding.comp H.measurableEmbedding_coe

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  (H : OpenSubgroup G)

/-- For a regular left Haar measure `μ` on a locally compact group, restricting `μ` to the right
coset `MulOpposite.op g • (H : Set G)` equals `Measure.modularCharacter g⁻¹` times the pushforward
of `μ.comap ((↑) : H → G)` along `y : H ↦ (y : G) * g`. -/
theorem restrict_op_smul_eq_smul_map_comap (g : G) :
    μ.restrict (op g • (H : Set G)) =
      Measure.modularCharacter g⁻¹ •
        (μ.comap ((↑) : H → G)).map (fun y : H ↦ (y : G) * g) := by
  have hpre : (fun x ↦ x * g) ⁻¹' (op g • (H : Set G)) = (H : Set G) := by
    ext x
    simp [mem_rightCoset_iff]
  have hmap := (MeasurableEquiv.mulRight g).restrict_map μ (op g • (H : Set G))
  rw [MeasurableEquiv.coe_mulRight, Measure.map_right_mul_eq_modularCharacter_smul_of_regular,
    Measure.restrict_smul, hpre, ← map_comap_subtype_coe H.isOpen.measurableSet,
    Measure.map_map (measurable_mul_const g) measurable_subtype_coe] at hmap
  have hinv : Measure.modularCharacter g⁻¹ * Measure.modularCharacter g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc μ.restrict (op g • (H : Set G))
      = (Measure.modularCharacter g⁻¹ * Measure.modularCharacter g) •
          μ.restrict (op g • (H : Set G)) := by rw [hinv, one_smul]
    _ = Measure.modularCharacter g⁻¹ •
          (Measure.modularCharacter g • μ.restrict (op g • (H : Set G))) := mul_smul _ _ _
    _ = Measure.modularCharacter g⁻¹ •
          (μ.comap ((↑) : H → G)).map (fun y : H ↦ (y : G) * g) := by
          rw [hmap]
          rfl

/-- Almost-everywhere properties on the right coset `MulOpposite.op g • (H : Set G)` reduce to
`(H, μ.comap (↑))`. -/
theorem ae_restrict_op_smul_iff_comap (g : G) {P : G → Prop} :
    (∀ᵐ z ∂μ.restrict (op g • (H : Set G)), P z) ↔
      ∀ᵐ y : H ∂(μ.comap ((↑) : H → G)), P ((y : G) * g) := by
  have hc : Measure.modularCharacter g⁻¹ ≠ 0 := (Measure.modularCharacterFun_pos g⁻¹).ne'
  rw [H.restrict_op_smul_eq_smul_map_comap g, Measure.ae_smul_measure_iff hc,
    (H.measurableEmbedding_mul_right g).ae_map_iff]

/-- Almost-everywhere strong measurability on the right coset `MulOpposite.op g • (H : Set G)`
reduces to `(H, μ.comap (↑))`. -/
theorem aestronglyMeasurable_op_smul_iff_comap {β : Type*} [TopologicalSpace β] (g : G)
    {f : G → β} :
    AEStronglyMeasurable f (μ.restrict (op g • (H : Set G))) ↔
      AEStronglyMeasurable (fun y : H ↦ f ((y : G) * g)) (μ.comap ((↑) : H → G)) := by
  have hc : Measure.modularCharacter g ≠ 0 := (Measure.modularCharacterFun_pos g).ne'
  rw [H.restrict_op_smul_eq_smul_map_comap g]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have hf' : AEStronglyMeasurable f ((μ.comap ((↑) : H → G)).map (fun y : H ↦ (y : G) * g)) := by
      simpa [smul_smul, mul_inv_cancel₀ hc] using hf.smul_measure (Measure.modularCharacter g)
    exact (H.measurableEmbedding_mul_right g).aestronglyMeasurable_map_iff.1 hf'
  · exact ((H.measurableEmbedding_mul_right g).aestronglyMeasurable_map_iff.2 hf).smul_measure _

/-- Lower Lebesgue integral over a right coset `MulOpposite.op g • (H : Set G)` against a regular
left Haar measure. -/
theorem setLIntegral_op_smul_eq_lintegral_comap (g : G) (f : G → ℝ≥0∞) :
    ∫⁻ z in op g • (H : Set G), f z ∂μ =
      Measure.modularCharacter g⁻¹ *
        ∫⁻ y : H, f ((y : G) * g) ∂(μ.comap ((↑) : H → G)) := by
  rw [H.restrict_op_smul_eq_smul_map_comap g, lintegral_smul_measure, ENNReal.smul_def,
    smul_eq_mul, (H.measurableEmbedding_mul_right g).lintegral_map]

/-- The `Lᵖ` seminorm on a right coset `MulOpposite.op g • (H : Set G)` against a regular left Haar
measure scales by `(Measure.modularCharacter g⁻¹) ^ p.toReal⁻¹`. -/
theorem eLpNorm_restrict_op_smul_eq_comap {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (g : G) (f : G → ε) (p : ℝ≥0∞) :
    eLpNorm f p (μ.restrict (op g • (H : Set G))) =
      Measure.modularCharacter g⁻¹ ^ p.toReal⁻¹ •
        eLpNorm (fun y : H ↦ f ((y : G) * g)) p (μ.comap ((↑) : H → G)) := by
  have hc : Measure.modularCharacter g⁻¹ ≠ 0 := (Measure.modularCharacterFun_pos g⁻¹).ne'
  rw [H.restrict_op_smul_eq_smul_map_comap g, eLpNorm_smul_measure_of_ne_zero' hc,
    (H.measurableEmbedding_mul_right g).eLpNorm_map_measure]
  rfl

/-- Membership in `Lᵖ` on a right coset `MulOpposite.op g • (H : Set G)` against a regular left Haar
measure reduces to `(H, μ.comap (↑))`. -/
theorem memLp_restrict_op_smul_iff_comap {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (g : G) {f : G → ε} {p : ℝ≥0∞} :
    MemLp f p (μ.restrict (op g • (H : Set G))) ↔
      MemLp (fun y : H ↦ f ((y : G) * g)) p (μ.comap ((↑) : H → G)) := by
  have hc : Measure.modularCharacter g ≠ 0 := (Measure.modularCharacterFun_pos g).ne'
  rw [H.restrict_op_smul_eq_smul_map_comap g]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have hf' : MemLp f p ((μ.comap ((↑) : H → G)).map (fun y : H ↦ (y : G) * g)) := by
      simpa [smul_smul, mul_inv_cancel₀ hc] using
        hf.smul_measure_nnreal (c := Measure.modularCharacter g)
    exact (H.measurableEmbedding_mul_right g).memLp_map_measure_iff.1 hf'
  · exact ((H.measurableEmbedding_mul_right g).memLp_map_measure_iff.2 hf).smul_measure_nnreal

/-- Integrability on a right coset `MulOpposite.op g • (H : Set G)` against a regular left Haar
measure reduces to `(H, μ.comap (↑))`. -/
theorem integrableOn_op_smul_iff_comap {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]
    (g : G) {f : G → ε} :
    IntegrableOn f (op g • (H : Set G)) μ ↔
      Integrable (fun y : H ↦ f ((y : G) * g)) (μ.comap ((↑) : H → G)) := by
  have hc : (Measure.modularCharacter g⁻¹ : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.modularCharacterFun_pos g⁻¹).ne'
  rw [IntegrableOn, H.restrict_op_smul_eq_smul_map_comap g, ENNReal.smul_def,
    integrable_smul_measure hc ENNReal.coe_ne_top,
    (H.measurableEmbedding_mul_right g).integrable_map_iff]
  rfl

/-- Bochner integral over a right coset `MulOpposite.op g • (H : Set G)` against a regular left Haar
measure. -/
theorem setIntegral_op_smul_eq_integral_comap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : G) (f : G → E) :
    ∫ z in op g • (H : Set G), f z ∂μ =
      (Measure.modularCharacter g⁻¹ : ℝ) •
        ∫ y : H, f ((y : G) * g) ∂(μ.comap ((↑) : H → G)) := by
  rw [H.restrict_op_smul_eq_smul_map_comap g, integral_smul_nnreal_measure, NNReal.smul_def,
    (H.measurableEmbedding_mul_right g).integral_map]

end RightCoset

section Convolution

section SingleFactor

variable {G α : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G} [Zero α]
  {H H₁ H₂ : OpenSubgroup G}

/-- When a kernel `h` vanishes `μ`-almost everywhere outside an open subgroup `H`, the convolution
integrand `y ↦ h y • f (y⁻¹ * x)` also vanishes `μ`-almost everywhere outside `H`. -/
@[to_additive (dont_translate := α β) ae_restrict_compl_smul_neg_add_eq_zero
/-- When a kernel `h` vanishes `μ`-almost everywhere outside an open additive subgroup `H`, the
convolution integrand `y ↦ h y • f (-y + x)` also vanishes `μ`-almost everywhere outside `H`. -/]
theorem ae_restrict_compl_smul_inv_mul_eq_zero {β : Type*} [Zero β] [SMulWithZero α β] {h : G → α}
    (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0) (f : G → β) (x : G) :
    (fun y ↦ h y • f (y⁻¹ * x)) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  filter_upwards [hh] with y hy
  simp only [Pi.zero_apply] at hy ⊢
  rw [hy, zero_smul]

variable [OpensMeasurableSpace G] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SMulWithZero α E]

/-- **Pointwise convolution reduction to an open subgroup.** If `h` vanishes `μ`-almost everywhere
outside `H`, then at every `x : G` the ambient convolution integral `∫ y, h y • f (y⁻¹ * x) ∂μ`
equals the integral over `(H, μ.comap (↑))`. -/
@[to_additive (dont_translate := α E) integral_smul_neg_add_eq_comap
/-- **Pointwise convolution reduction to an open additive subgroup.** If `h` vanishes `μ`-almost
everywhere outside `H`, then at every `x : G` the ambient convolution integral
`∫ y, h y • f (-y + x) ∂μ` equals the integral over `(H, μ.comap (↑))`. -/]
theorem integral_smul_inv_mul_eq_comap {h : G → α}
    (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0) (f : G → E) (x : G) :
    ∫ y, h y • f (y⁻¹ * x) ∂μ =
      ∫ y : H, h y • f ((y : G)⁻¹ * x) ∂(μ.comap ((↑) : H → G)) :=
  H.integral_eq_comap (ae_restrict_compl_smul_inv_mul_eq_zero hh f x)

/-- **Subgroup independence for pointwise convolution.** If `h` vanishes `μ`-almost everywhere
outside open subgroups `H₁` and `H₂`, the restricted convolution integrals on `(H₁, μ.comap (↑))`
and `(H₂, μ.comap (↑))` coincide at every `x : G`. -/
@[to_additive (dont_translate := α E) integral_smul_neg_add_comap_congr
/-- **Subgroup independence for pointwise convolution.** If `h` vanishes `μ`-almost everywhere
outside open additive subgroups `H₁` and `H₂`, the restricted convolution integrals on
`(H₁, μ.comap (↑))` and `(H₂, μ.comap (↑))` coincide at every `x : G`. -/]
theorem integral_smul_inv_mul_comap_congr {h : G → α}
    (hh₁ : h =ᵐ[μ.restrict (H₁ : Set G)ᶜ] 0) (hh₂ : h =ᵐ[μ.restrict (H₂ : Set G)ᶜ] 0)
    (f : G → E) (x : G) :
    ∫ y : H₁, h y • f ((y : G)⁻¹ * x) ∂(μ.comap ((↑) : H₁ → G)) =
      ∫ y : H₂, h y • f ((y : G)⁻¹ * x) ∂(μ.comap ((↑) : H₂ → G)) :=
  integral_comap_congr (ae_restrict_compl_smul_inv_mul_eq_zero hh₁ f x)
    (ae_restrict_compl_smul_inv_mul_eq_zero hh₂ f x)

/-- **Right-coset reduction of pointwise convolution.** If `h` vanishes `μ`-almost everywhere
outside `H`, then at any point `(z : G) * g` of the right coset `MulOpposite.op g • (H : Set G)`
(`z : H`), the ambient convolution `∫ y, h y • f (y⁻¹ * (z * g)) ∂μ` equals the `H`-convolution of
`h|_H` with the right-coset slice `w : H ↦ f ((w : G) * g)`. -/
@[to_additive (dont_translate := α E) integral_smul_neg_add_add_eq_comap
/-- **Right-coset reduction of pointwise convolution.** If `h` vanishes `μ`-almost everywhere
outside `H`, then at any point `(z : G) + g` (`z : H`), the ambient convolution
`∫ y, h y • f (-y + (z + g)) ∂μ` equals the `H`-convolution of `h|_H` with the coset slice
`w : H ↦ f ((w : G) + g)`. -/]
theorem integral_smul_inv_mul_mul_eq_comap {h : G → α}
    (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0) (f : G → E) (z : H) (g : G) :
    ∫ y, h y • f (y⁻¹ * ((z : G) * g)) ∂μ =
      ∫ y : H, h y • f (((y⁻¹ * z : H) : G) * g) ∂(μ.comap ((↑) : H → G)) := by
  rw [H.integral_smul_inv_mul_eq_comap hh f ((z : G) * g)]
  congr with y
  rw [← mul_assoc]
  rfl

/-- At any `z : H`, the ambient convolution `∫ y, h y • f (y⁻¹ * z) ∂μ` of a kernel `h` supported on
`H` equals the intrinsic convolution on `(H, μ.comap (↑))`. -/
@[to_additive (dont_translate := α E) integral_smul_neg_add_coe_eq_comap
/-- At any `z : H`, the ambient convolution `∫ y, h y • f (-y + z) ∂μ` of a kernel `h` supported on
`H` equals the intrinsic convolution on `(H, μ.comap (↑))`. -/]
theorem integral_smul_inv_mul_coe_eq_comap {h : G → α}
    (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0) (f : G → E) (z : H) :
    ∫ y, h y • f (y⁻¹ * (z : G)) ∂μ =
      ∫ y : H, h y • f ((y⁻¹ * z : H) : G) ∂(μ.comap ((↑) : H → G)) := by
  simpa using H.integral_smul_inv_mul_mul_eq_comap hh f z 1

end SingleFactor

section TwoFactors

variable {G α : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  [μ.Regular] [Zero α] {H : OpenSubgroup G}

/-- For a regular left Haar measure `μ`, if both `h` and `f` vanish `μ`-almost everywhere outside an
open subgroup `H`, then at every `x ∉ H` the convolution integrand `y ↦ h y • f (y⁻¹ * x)` vanishes
`μ`-almost everywhere on `G`. -/
theorem ae_smul_inv_mul_eq_zero_of_notMem {β : Type*} [Zero β] [SMulWithZero α β]
    {h : G → α} {f : G → β}
    (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0) (hf : f =ᵐ[μ.restrict (H : Set G)ᶜ] 0)
    {x : G} (hx : x ∉ (H : Set G)) :
    (fun y ↦ h y • f (y⁻¹ * x)) =ᵐ[μ] 0 := by
  have hh' : ∀ᵐ y ∂μ, y ∈ (H : Set G)ᶜ → h y = 0 :=
    (ae_restrict_iff' H.isOpen.measurableSet.compl).1 hh
  have hf' : ∀ᵐ z ∂μ, z ∈ (H : Set G)ᶜ → f z = 0 :=
    (ae_restrict_iff' H.isOpen.measurableSet.compl).1 hf
  filter_upwards [hh', (Measure.quasiMeasurePreserving_inv_mul_of_regular μ x).ae hf'] with y hy hfy
  by_cases hyH : y ∈ (H : Set G)
  · have hyx : y⁻¹ * x ∈ (H : Set G)ᶜ := fun hmem ↦ hx (by simpa using H.mul_mem hyH hmem)
    simp [hfy hyx]
  · simp [hy hyH]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulWithZero α E]

/-- For a regular left Haar measure `μ`, if both `h` and `f` vanish `μ`-almost everywhere outside an
open subgroup `H`, then `∫ y, h y • f (y⁻¹ * x) ∂μ = 0` at every `x ∉ H`. -/
theorem integral_smul_inv_mul_eq_zero_of_notMem {h : G → α} {f : G → E}
    (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0) (hf : f =ᵐ[μ.restrict (H : Set G)ᶜ] 0)
    {x : G} (hx : x ∉ (H : Set G)) :
    ∫ y, h y • f (y⁻¹ * x) ∂μ = 0 :=
  integral_eq_zero_of_ae (H.ae_smul_inv_mul_eq_zero_of_notMem hh hf hx)

/-- For a regular left Haar measure `μ`, if both `h` and `f` vanish `μ`-almost everywhere outside an
open subgroup `H`, so does the pointwise convolution `x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ`. -/
theorem ae_restrict_compl_integral_smul_inv_mul_eq_zero {h : G → α} {f : G → E}
    (hh : h =ᵐ[μ.restrict (H : Set G)ᶜ] 0) (hf : f =ᵐ[μ.restrict (H : Set G)ᶜ] 0) :
    (fun x ↦ ∫ y, h y • f (y⁻¹ * x) ∂μ) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 :=
  (ae_restrict_iff' H.isOpen.measurableSet.compl).2 <|
    .of_forall fun _ hx ↦ H.integral_smul_inv_mul_eq_zero_of_notMem hh hf hx

end TwoFactors

end Convolution

section Kernels

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (H : OpenSubgroup G)

/-- **Continuous peak kernels inside an open subgroup.** On a locally compact `R₁` group with a
measure positive on nonempty open sets and finite on compact sets, every neighbourhood `U` of `1`
carries a nonnegative compactly supported continuous function `φ` of unit integral supported inside
both `U` and `H`. -/
@[to_additive exists_nonneg_tsupport_subset_integral_eq_one
/-- **Continuous peak kernels inside an open additive subgroup.** On a locally compact
`R₁` additive group with a measure positive on nonempty open sets and finite on compact sets, every
neighbourhood `U` of `0` carries a nonnegative compactly supported continuous function `φ` of unit
integral supported inside both `U` and `H`. -/]
theorem exists_nonneg_tsupport_subset_integral_eq_one [R1Space G] [LocallyCompactSpace G]
    (μ : Measure G) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ φ : C_c(G, ℝ), 0 ≤ φ ∧ tsupport φ ⊆ U ∧ tsupport φ ⊆ H ∧ ∫ x, φ x ∂μ = 1 := by
  obtain ⟨φ, hφ0, hφUH, hφ1⟩ := TauCeti.exists_nonneg_tsupport_subset_integral_eq_one μ
    (inter_mem hU (H.isOpen.mem_nhds H.one_mem))
  exact ⟨φ, hφ0, hφUH.trans inter_subset_left, hφUH.trans inter_subset_right, hφ1⟩

/-- **`L¹` peak kernels inside an open subgroup.** For a locally finite measure positive on nonempty
open sets, every neighbourhood `U` of `1` carries an `L¹` class `f` of unit integral and unit `L¹`
norm vanishing almost everywhere outside both `U` and `H`. -/
@[to_additive (dont_translate := 𝕜) exists_integral_eq_one_norm_eq_one
/-- **`L¹` peak kernels inside an open additive subgroup.** For a locally finite measure positive on
nonempty open sets, every neighbourhood `U` of `0` carries an `L¹` class `f` of unit integral and
unit `L¹` norm vanishing almost everywhere outside both `U` and `H`. -/]
theorem exists_integral_eq_one_norm_eq_one (𝕜 : Type*) [RCLike 𝕜] (μ : Measure G)
    [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ f : G →₁[μ] 𝕜, ∫ x, f x ∂μ = 1 ∧ ‖f‖ = 1 ∧
      (∀ᵐ x ∂μ, x ∉ U → f x = 0) ∧ (f : G → 𝕜) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  obtain ⟨f, hf1, hfn, hfUH⟩ := TauCeti.exists_integral_eq_one_norm_eq_one 𝕜 μ
    (inter_mem hU (H.isOpen.mem_nhds H.one_mem))
  refine ⟨f, hf1, hfn, ?_, (ae_restrict_iff' H.isOpen.measurableSet.compl).2 ?_⟩
  · filter_upwards [hfUH] with x hx hxU
    exact hx fun hxUH ↦ hxU hxUH.1
  · filter_upwards [hfUH] with x hx hxH
    exact hx fun hxUH ↦ hxH hxUH.2

end Kernels

end OpenSubgroup
