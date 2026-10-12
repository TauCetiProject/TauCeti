/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.LaurentCover.Basic

import TauCeti.RingTheory.Huber.OpenMapping

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
  (hden₂ : HasDenominatorPower P {1} f S₂)

/-- The augmentation for a Laurent cover is a closed embedding. In particular, the topology
on `A` is the subspace topology on the equalizer of the two restrictions to the overlap. -/
theorem isClosedEmbedding_laurentCover :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    IsClosedEmbedding
      (RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁) (toCompletionLoc P {1} f S₂ hden₂)) := by
  let hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  let S₁₂ := Localization.Away (1 * f)
  let hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
    (by simp) (by simp) hden₁ hden₂
  let _ := locUniformSpace P {f, 1} 1 S₁ hden₁
  let _ := locUniformSpace P {1} f S₂ hden₂
  let _ := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  -- Use the canonical scalar actions on the localizations and their completions.
  have _ : ContinuousSMul A S₁ := continuousSMul_of_algebraMap A S₁ (by
    rw [locUniformSpace_toTopologicalSpace]
    exact continuous_algebraMap_locTopology P {f, 1} 1 S₁ hden₁)
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₁
  have _ : ContinuousSMul A S₂ := continuousSMul_of_algebraMap A S₂ (by
    rw [locUniformSpace_toTopologicalSpace]
    exact continuous_algebraMap_locTopology P {1} f S₂ hden₂)
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₂
  have _ := isHuberRing_completion_locTopology P {f, 1} 1 S₁ hden₁
  have _ := isHuberRing_completion_locTopology P {1} f S₂ hden₂
  let ρ := RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁)
    (toCompletionLoc P {1} f S₂ hden₂)
  let l := Algebra.linearMap A (Completion S₁ × Completion S₂)
  have hρ : Continuous ρ := (continuous_toCompletionLoc P {f, 1} 1 S₁ hden₁).prodMk
    (continuous_toCompletionLoc P {1} f S₂ hden₂)
  have hρeq : ρ = algebraMap A (Completion S₁ × Completion S₂) := by
    ext a <;> simp [ρ, Completion.algebraMap_def]
  have hl : Continuous l := by simpa only [l, Algebra.coe_linearMap, ← hρeq] using hρ
  have _ : ContinuousSMul A (Completion S₁ × Completion S₂) :=
    continuousSMul_of_algebraMap A _ hl
  have _ := IsUniformAddGroup.uniformity_countably_generated (α := A)
  have _ := IsUniformAddGroup.uniformity_countably_generated (α := Completion S₁)
  have _ := IsUniformAddGroup.uniformity_countably_generated (α := Completion S₂)
  -- Exactness identifies the range with the closed equalizer of the overlap restrictions.
  have hrange : IsClosed (Set.range ρ) := by
    have he := laurentCover_exact P f S₁ S₂ S₁₂ hden₂
    have hc := (continuous_restrictionRingHom P {f, 1} 1 S₁ hden₁
      {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl (by simp)).comp
        (continuous_fst (X := Completion S₁) (Y := Completion S₂))
    have hd := (continuous_restrictionRingHom P {1} f S₂ hden₂
      {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f) (by simp)).comp
        (continuous_snd (X := Completion S₁) (Y := Completion S₂))
    convert isClosed_eq hc hd using 1
    ext x
    exact (he x).symm.trans sub_eq_zero
  have hinj : Function.Injective l := by
    simpa only [l, Algebra.coe_linearMap, ← hρeq] using
      (laurentCover_injective P f S₁ S₂ hden₂ : Function.Injective ρ)
  have hclosed : IsClosed (Set.range l) := by
    simpa only [l, Algebra.coe_linearMap, ← hρeq] using hrange
  -- Henkel makes the bijection onto this closed range a homeomorphism.
  have hemb := isEmbedding_iff_isStrictMap_injective.mpr
    ⟨IsTateRing.isStrictMap_of_isClosed_range l hl.continuousAt hclosed, hinj⟩
  simpa only [l, Algebra.coe_linearMap, ← hρeq] using (⟨hemb, hclosed⟩ : IsClosedEmbedding l)

end Augmentation

section Differential

variable (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  (S₂ : Type*) [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (hden₂ : HasDenominatorPower P {1} f S₂)

/-- The difference of the two restrictions in a Laurent cover is an open quotient map.
Thus the topology on the overlap ring agrees with the quotient topology from the product
of the two coordinate rings. -/
theorem isOpenQuotientMap_laurentCover
    (S₁₂ : Type*) [CommRing S₁₂] [Algebra A S₁₂] [IsLocalization.Away (1 * f) S₁₂] :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
      (by simp) (by simp) hden₁ hden₂
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    IsOpenQuotientMap
      ((restrictionRingHom P {f, 1} 1 S₁ hden₁ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.fst (UniformSpace.Completion S₁) (UniformSpace.Completion S₂)) -
        (restrictionRingHom P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f)
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.snd (UniformSpace.Completion S₁) (UniformSpace.Completion S₂))) := by
  let hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  let hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
    (by simp) (by simp) hden₁ hden₂
  let _ := locUniformSpace P {f, 1} 1 S₁ hden₁
  let _ := locUniformSpace P {1} f S₂ hden₂
  let _ := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  -- Use the canonical scalar actions on the localizations and their completions.
  have _ : ContinuousSMul A S₁ := continuousSMul_of_algebraMap A S₁ (by
    rw [locUniformSpace_toTopologicalSpace]
    exact continuous_algebraMap_locTopology P {f, 1} 1 S₁ hden₁)
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₁
  have _ : ContinuousSMul A S₂ := continuousSMul_of_algebraMap A S₂ (by
    rw [locUniformSpace_toTopologicalSpace]
    exact continuous_algebraMap_locTopology P {1} f S₂ hden₂)
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₂
  have _ : ContinuousSMul A S₁₂ := continuousSMul_of_algebraMap A S₁₂ (by
    rw [locUniformSpace_toTopologicalSpace]
    exact continuous_algebraMap_locTopology P {f * f, f, 1} (1 * f) S₁₂ hden₁₂)
  have _ := uniformContinuousConstSMul_of_continuousConstSMul A S₁₂
  have _ := isHuberRing_completion_locTopology P {f, 1} 1 S₁ hden₁
  have _ := isHuberRing_completion_locTopology P {1} f S₂ hden₂
  have _ := isHuberRing_completion_locTopology P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ : ContinuousSMul A (Completion S₁) :=
    continuousSMul_of_algebraMap A (Completion S₁) <|
      (continuous_toCompletionLoc P {f, 1} 1 S₁ hden₁).congr fun a ↦
        (toCompletionLoc_apply P {f, 1} 1 S₁ hden₁ a).trans
          (Completion.algebraMap_def S₁ A a).symm
  have _ : ContinuousSMul A (Completion S₂) :=
    continuousSMul_of_algebraMap A (Completion S₂) <|
      (continuous_toCompletionLoc P {1} f S₂ hden₂).congr fun a ↦
        (toCompletionLoc_apply P {1} f S₂ hden₂ a).trans
          (Completion.algebraMap_def S₂ A a).symm
  have _ : ContinuousSMul A (Completion S₁₂) :=
    continuousSMul_of_algebraMap A (Completion S₁₂) <|
      (continuous_toCompletionLoc P {f * f, f, 1} (1 * f) S₁₂ hden₁₂).congr fun a ↦
        (toCompletionLoc_apply P {f * f, f, 1} (1 * f) S₁₂ hden₁₂ a).trans
          (Completion.algebraMap_def S₁₂ A a).symm
  have _ := IsUniformAddGroup.uniformity_countably_generated (α := Completion S₁)
  have _ := IsUniformAddGroup.uniformity_countably_generated (α := Completion S₂)
  have _ := IsUniformAddGroup.uniformity_countably_generated (α := Completion S₁₂)
  -- The restriction maps commute with the structure maps, hence are A-linear.
  let r₁ : Completion S₁ →ₐ[A] Completion S₁₂ :=
    { toRingHom := restrictionRingHom P {f, 1} 1 S₁ hden₁
        {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl (by simp)
      commutes' := fun a ↦ by
        simpa only [RingHom.comp_apply, toCompletionLoc_apply, Completion.algebraMap_def,
          RingHom.toFun_eq_coe] using
          RingHom.congr_fun
            (restrictionRingHom_comp_toCompletionLoc P {f, 1} 1 S₁ hden₁
              {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl (by simp)) a }
  let r₂ : Completion S₂ →ₐ[A] Completion S₁₂ :=
    { toRingHom := restrictionRingHom P {1} f S₂ hden₂
        {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f) (by simp)
      commutes' := fun a ↦ by
        simpa only [RingHom.comp_apply, toCompletionLoc_apply, Completion.algebraMap_def,
          RingHom.toFun_eq_coe] using
          RingHom.congr_fun
            (restrictionRingHom_comp_toCompletionLoc P {1} f S₂ hden₂
              {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f) (by simp)) a }
  let d := r₁.toLinearMap.comp (LinearMap.fst A (Completion S₁) (Completion S₂)) -
    r₂.toLinearMap.comp (LinearMap.snd A (Completion S₁) (Completion S₂))
  have hd : Continuous d :=
    ((continuous_restrictionRingHom P {f, 1} 1 S₁ hden₁
      {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl (by simp)).comp continuous_fst).sub
      ((continuous_restrictionRingHom P {1} f S₂ hden₂
        {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f) (by simp)).comp continuous_snd)
  -- Identify the additive differential with its A-linear presentation.
  have hdiff : ⇑(r₁.toRingHom.toAddMonoidHom.comp
      (AddMonoidHom.fst (Completion S₁) (Completion S₂)) -
    r₂.toRingHom.toAddMonoidHom.comp
      (AddMonoidHom.snd (Completion S₁) (Completion S₂))) = d := by
    funext x
    simp only [d, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.coe_fst,
      AddMonoidHom.coe_snd, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      AlgHom.toLinearMap_apply]
  have hsurj : Function.Surjective d := by
    simpa only [← hdiff] using laurentCover_surjective P f S₁ S₂ S₁₂ hden₂
  -- Apply open mapping to the surjective difference of restrictions.
  simpa only [← hdiff] using
    (⟨hsurj, hd, IsTateRing.isOpenMap d hsurj hd.continuousAt⟩ : IsOpenQuotientMap d)

end Differential

end TauCeti.ValuationSpectrum
