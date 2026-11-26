/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.Measure
public import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# Normalized Haar measure on compact groups

This file normalizes Mathlib's Haar measure on a compact topological group to a probability
measure, and records its left, right, and inversion invariance. The right and inversion
invariances come from
`MeasureTheory.Measure.isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure` and
`MeasureTheory.Measure.isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure`, which hold for every
finite Haar measure on a locally compact group.

Since `haarProb` is a Haar measure and a probability measure, Mathlib's generic API applies to
it directly: `MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure` identifies it with
any other Haar probability measure, and `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_mul_right_eq_self` and `MeasureTheory.integral_inv_eq_self` give the
translation and inversion identities used for averaging representations.

Normalized Haar measure is also compatible with passing to a closed subgroup of finite index.
A measurable subgroup of finite index `n` has mass `n⁻¹` for every left-invariant probability
measure (`Subgroup.measure_eq_inv_index`), since its `n` left cosets have equal mass and
partition the group (`Subgroup.index_mul_measure`). If `φ : H →* G` is a continuous injective
homomorphism of compact groups whose range has finite index `n` in `G`, then pulling
`haarProb G` back along `φ` gives `n⁻¹ • haarProb H`
(`TauCeti.comap_haarProb_eq_inv_index_smul`): the pullback is left-invariant with total mass
`n⁻¹`, so it is determined by uniqueness of Haar measure. Equivalently, the restriction of
`haarProb G` to `range φ` is `n⁻¹` times the pushforward of `haarProb H`
(`TauCeti.restrict_haarProb_range_eq_inv_index_smul_map`). The case of the inclusion of a
compact subgroup `K ≤ L` of finite relative index is
`TauCeti.comap_inclusion_haarProb_eq_inv_relIndex_smul`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar probability measure on a compact topological group. -/
noncomputable def haarProb : Measure G :=
  ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar

/-- The definition of normalized Haar measure as a rescaling of Mathlib's Haar measure. -/
theorem haarProb_def :
    haarProb G = ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar := by
  rw [haarProb]

instance isProbabilityMeasure_haarProb : IsProbabilityMeasure (haarProb G) := by
  rw [haarProb_def]
  infer_instance

instance isHaarMeasure_haarProb : (haarProb G).IsHaarMeasure := by
  rw [haarProb_def]
  exact Measure.IsHaarMeasure.smul Measure.haar
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _))

/-- Normalized Haar measure is invariant under right multiplication. -/
instance isMulRightInvariant_haarProb : (haarProb G).IsMulRightInvariant :=
  Measure.isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure _

/-- Normalized Haar measure is invariant under inversion. -/
instance isInvInvariant_haarProb : (haarProb G).IsInvInvariant :=
  Measure.isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure _

end CompactGroup

section FiniteIndex

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- **Normalized Haar measure on a finite-index subgroup.** Pulling the normalized Haar measure
of `G` back along a continuous injective homomorphism `φ : H →* G` of compact groups whose range
has finite index `n` gives `n⁻¹` times the normalized Haar measure of `H`. -/
theorem comap_haarProb_eq_inv_index_smul (φ : H →* G) (hφ : Continuous φ)
    (hinj : Function.Injective φ) [φ.range.FiniteIndex] :
    (haarProb G).comap φ = (φ.range.index : ℝ≥0∞)⁻¹ • haarProb H := by
  have hemb : MeasurableEmbedding φ := (hφ.isClosedEmbedding hinj).measurableEmbedding
  have hidx : (φ.range.index : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  have : ((haarProb G).comap φ).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap _ hemb
  have : ((φ.range.index : ℝ≥0∞)⁻¹ • haarProb H).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_top.mpr hidx)
  have : IsFiniteMeasure ((φ.range.index : ℝ≥0∞)⁻¹ • haarProb H) :=
    ⟨by simpa using ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hidx)⟩
  refine Measure.isMulLeftInvariant_eq_of_measure_univ_eq _ _ ?_
  have hmeas : MeasurableSet (φ.range : Set G) := by
    rw [MonoidHom.coe_range]
    exact hemb.measurableSet_range
  rw [hemb.comap_apply, image_univ, ← MonoidHom.coe_range,
    Subgroup.measure_eq_inv_index _ hmeas]
  simp

/-- The restriction of the normalized Haar measure of `G` to the range of a continuous injective
homomorphism `φ : H →* G` of compact groups, of finite index `n`, is `n⁻¹` times the pushforward
of the normalized Haar measure of `H`. -/
theorem restrict_haarProb_range_eq_inv_index_smul_map (φ : H →* G) (hφ : Continuous φ)
    (hinj : Function.Injective φ) [φ.range.FiniteIndex] :
    (haarProb G).restrict (φ.range : Set G) =
      (φ.range.index : ℝ≥0∞)⁻¹ • (haarProb H).map φ := by
  rw [MonoidHom.coe_range, ← (hφ.isClosedEmbedding hinj).measurableEmbedding.map_comap,
    comap_haarProb_eq_inv_index_smul φ hφ hinj, Measure.map_smul]
  exact hφ.measurable.aemeasurable

/-- **Normalized Haar measure on a closed subgroup of finite index.** For subgroups `K ≤ L` of a
group, both compact and with `K` of finite index in `L`, the pullback of the normalized Haar
measure of `L` along the inclusion `K →* L` is `[L : K]⁻¹` times the normalized Haar measure
of `K`. -/
theorem comap_inclusion_haarProb_eq_inv_relIndex_smul {X : Type*} [Group X]
    [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {K L : Subgroup X} [CompactSpace K] [CompactSpace L] (hKL : K ≤ L) [K.IsFiniteRelIndex L] :
    (haarProb L).comap (Subgroup.inclusion hKL) = (K.relIndex L : ℝ≥0∞)⁻¹ • haarProb K := by
  have : (Subgroup.inclusion hKL).range.FiniteIndex := by
    rw [Subgroup.inclusion_range]
    infer_instance
  rw [comap_haarProb_eq_inv_index_smul _ (continuous_inclusion hKL)
    (Subgroup.inclusion_injective hKL), Subgroup.inclusion_range, Subgroup.relIndex]

end FiniteIndex

end TauCeti
