/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.LaurentCover.Basic

import TauCeti.RingTheory.Huber.OpenMapping
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Topological exactness of the Laurent cover

For a complete Hausdorff strongly noetherian Tate ring `A`, the augmented sequence for the
Laurent cover `|f| ≤ 1`, `|f| ≥ 1` is strictly exact. The augmentation is a closed embedding,
so the topology on `A` agrees with the equalizer topology inherited from the product of the
two coordinate rings. The difference of restrictions is an open quotient map onto the
coordinate ring of the overlap.

These are the topological statements needed to interpret Laurent-cover gluing in topological
rings. Algebraic exactness is supplied by `laurentCover_exact`; the open mapping theorem over
a Tate ring supplies strictness. The `T0Space` assumption implies Hausdorffness for these
uniform additive groups.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Lemma 8.33 and Remark 8.20.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  arXiv:1407.5647.
-/

public section

open Topology TauCeti.Huber TauCeti.Huber.PairOfDefinition
open UniformSpace (Completion)

namespace TauCeti.ValuationSpectrum

attribute [local instance] Classical.decEq

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] [IsStronglyNoetherian A]
  (P : PairOfDefinition A) (f : A)

section Augmentation

variable (S₁ S₂ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (hden₂ : HasDenominatorPower P ({1} : Finset A) f S₂)

/-- The augmentation for a Laurent cover is a closed embedding. In particular, the topology
on `A` is the subspace topology on the equalizer of the two restrictions to the overlap. -/
theorem isClosedEmbedding_laurentCover :
    letI hden₁ := hasDenominatorPower_denom_one P ({f, 1} : Finset A) S₁
    letI := locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
    letI := locUniformSpace P ({1} : Finset A) f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P ({1} : Finset A) f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P ({1} : Finset A) f S₂ hden₂
    IsClosedEmbedding
      (RingHom.prod (toCompletionLoc P ({f, 1} : Finset A) 1 S₁ hden₁)
          (toCompletionLoc P ({1} : Finset A) f S₂ hden₂)) := by
  let hden₁ := hasDenominatorPower_denom_one P ({f, 1} : Finset A) S₁
  let S₁₂ := Localization.Away (1 * f)
  let hden₁₂ := hasDenominatorPower_mul P ({f, 1} : Finset A) ({1} : Finset A)
    ({f * f, f, 1} : Finset A) 1 f S₁ S₂ S₁₂
    (by simp) (by simp) hden₁ hden₂
  let _ := locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  let _ := locUniformSpace P ({1} : Finset A) f S₂ hden₂
  let _ := locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
  have _ := isUniformAddGroup_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ := continuousSMul_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₁
  have _ := isHuberRing_completion_locTopology P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ := continuousSMul_completion_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ : (uniformity (Completion S₁)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  have _ := isUniformAddGroup_locUniformSpace P ({1} : Finset A) f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P ({1} : Finset A) f S₂ hden₂
  have _ := continuousSMul_locUniformSpace P ({1} : Finset A) f S₂ hden₂
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₂
  have _ := isHuberRing_completion_locTopology P ({1} : Finset A) f S₂ hden₂
  have _ := continuousSMul_completion_locUniformSpace P ({1} : Finset A) f S₂ hden₂
  have _ : (uniformity (Completion S₂)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  have _ := isUniformAddGroup_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
  let ρ := RingHom.prod (toCompletionLoc P ({f, 1} : Finset A) 1 S₁ hden₁)
    (toCompletionLoc P ({1} : Finset A) f S₂ hden₂)
  -- Exactness identifies the range with the closed equalizer of the overlap restrictions.
  have hrange : IsClosed (Set.range ρ) := by
    have he := laurentCover_exact P f S₁ S₂ S₁₂ hden₂
    have hc := (continuous_restrictionRingHom P ({f, 1} : Finset A) 1 S₁ hden₁
      ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂ f rfl (by simp)).comp
        (continuous_fst (X := Completion S₁) (Y := Completion S₂))
    have hd := (continuous_restrictionRingHom P ({1} : Finset A) f S₂ hden₂
      ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f) (by simp)).comp
        (continuous_snd (X := Completion S₁) (Y := Completion S₂))
    convert isClosed_eq hc hd using 1
    ext x
    exact (he x).symm.trans sub_eq_zero
  -- Henkel makes the bijection onto this closed range a homeomorphism.
  exact RingHom.isClosedEmbedding_of_isClosed_range_of_isTateRing ρ
    (fun a ↦ by simp [ρ, Completion.algebraMap_def])
    ((continuous_toCompletionLoc P ({f, 1} : Finset A) 1 S₁ hden₁).prodMk
      (continuous_toCompletionLoc P ({1} : Finset A) f S₂ hden₂))
    (laurentCover_injective P f S₁ S₂ hden₂) hrange

end Augmentation

section Differential

variable (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  (S₂ : Type*) [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (hden₂ : HasDenominatorPower P ({1} : Finset A) f S₂)

/-- The difference of the two restrictions in a Laurent cover is an open quotient map.
Thus the topology on the overlap ring agrees with the quotient topology from the product
of the two coordinate rings. -/
theorem isOpenQuotientMap_laurentCover
    (S₁₂ : Type*) [CommRing S₁₂] [Algebra A S₁₂] [IsLocalization.Away (1 * f) S₁₂] :
    letI hden₁ := hasDenominatorPower_denom_one P ({f, 1} : Finset A) S₁
    letI hden₁₂ := hasDenominatorPower_mul P ({f, 1} : Finset A) ({1} : Finset A)
      ({f * f, f, 1} : Finset A) 1 f S₁ S₂ S₁₂
      (by simp) (by simp) hden₁ hden₂
    letI := locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
    letI := locUniformSpace P ({1} : Finset A) f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P ({1} : Finset A) f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P ({1} : Finset A) f S₂ hden₂
    letI := locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
    IsOpenQuotientMap
      ((restrictionRingHom P ({f, 1} : Finset A) 1 S₁ hden₁ ({f * f, f, 1} : Finset A) (1 * f) S₁₂
          hden₁₂ f rfl
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.fst (UniformSpace.Completion S₁) (UniformSpace.Completion S₂)) -
        (restrictionRingHom P ({1} : Finset A) f S₂ hden₂ ({f * f, f, 1} : Finset A) (1 * f) S₁₂
          hden₁₂ 1 (mul_comm 1 f)
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.snd (UniformSpace.Completion S₁) (UniformSpace.Completion S₂))) := by
  let hden₁ := hasDenominatorPower_denom_one P ({f, 1} : Finset A) S₁
  let hden₁₂ := hasDenominatorPower_mul P ({f, 1} : Finset A) ({1} : Finset A)
    ({f * f, f, 1} : Finset A) 1 f S₁ S₂ S₁₂
    (by simp) (by simp) hden₁ hden₂
  let _ := locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  let _ := locUniformSpace P ({1} : Finset A) f S₂ hden₂
  let _ := locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
  have _ := isUniformAddGroup_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ := continuousSMul_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₁
  have _ := isHuberRing_completion_locTopology P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ := continuousSMul_completion_locUniformSpace P ({f, 1} : Finset A) 1 S₁ hden₁
  have _ : (uniformity (Completion S₁)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  have _ := isUniformAddGroup_locUniformSpace P ({1} : Finset A) f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P ({1} : Finset A) f S₂ hden₂
  have _ := continuousSMul_locUniformSpace P ({1} : Finset A) f S₂ hden₂
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₂
  have _ := isHuberRing_completion_locTopology P ({1} : Finset A) f S₂ hden₂
  have _ := continuousSMul_completion_locUniformSpace P ({1} : Finset A) f S₂ hden₂
  have _ : (uniformity (Completion S₂)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  have _ := isUniformAddGroup_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
  have _ := continuousSMul_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₁₂
  have _ := continuousSMul_completion_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) S₁₂
    hden₁₂
  have _ := isHuberRing_completion_locTopology P ({f * f, f, 1} : Finset A) (1 * f) S₁₂ hden₁₂
  have _ : (uniformity (Completion S₁₂)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  -- The restriction maps are `A`-algebra maps; open mapping applies to their surjective difference.
  have key := AlgHom.isOpenQuotientMap_sub_of_surjective_of_isTateRing
    (restrictionAlgHom P ({f, 1} : Finset A) 1 S₁ hden₁ ({f * f, f, 1} : Finset A) (1 * f) S₁₂
      hden₁₂ f rfl (by simp))
    (restrictionAlgHom P ({1} : Finset A) f S₂ hden₂ ({f * f, f, 1} : Finset A) (1 * f) S₁₂
      hden₁₂ 1 (mul_comm 1 f) (by simp))
    (continuous_restrictionAlgHom P ({f, 1} : Finset A) 1 S₁ hden₁ ({f * f, f, 1} : Finset A)
      (1 * f) S₁₂ hden₁₂ f rfl (by simp))
    (continuous_restrictionAlgHom P ({1} : Finset A) f S₂ hden₂ ({f * f, f, 1} : Finset A)
      (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f) (by simp))
    (by simpa only [AlgHom.toRingHom_eq_coe, restrictionAlgHom_toRingHom] using
      laurentCover_surjective P f S₁ S₂ S₁₂ hden₂)
  simpa only [AlgHom.toRingHom_eq_coe, restrictionAlgHom_toRingHom] using key

end Differential

end TauCeti.ValuationSpectrum
