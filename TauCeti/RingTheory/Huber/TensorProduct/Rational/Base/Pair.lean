/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pair
public import TauCeti.RingTheory.Huber.TensorProduct.Rational.Base.Basic
import TauCeti.RingTheory.Subring.Basic

/-!
# Invariance of completed tensor Huber pairs under localising the base ring

Let `A → B` and `A → C` be adic homomorphisms of Huber rings, `(B, B⁺)` and `(C, C⁺)` Huber pairs,
and `A → A⟨T₀/s₀⟩` a completed rational localisation of `A`. Building on the topological ring
equivalence `TauCeti.Huber.CompletedTensor.completionLocBaseEquiv` (from `Rational.Base.Basic`),
this file identifies the completed tensor plus rings of `(B, B⁺) ⊗̂_{A⟨T₀/s₀⟩} (C, C⁺)` and
`(B, B⁺) ⊗̂_A (C, C⁺)` (`Pair.completedTensor.map_plus_completionLocBaseEquiv`) and packages the
comparison as mutually inverse Huber-pair morphisms `ofBaseLocalization` and `toBaseLocalization`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensor.ofBaseLocalization`,
  `TauCeti.Huber.Pair.completedTensor.toBaseLocalization`: mutually inverse morphisms of Huber
  pairs for `completionLocBaseEquiv`.

## Main results

* `TauCeti.Huber.Pair.completedTensor.map_plus_completionLocBaseEquiv`:
  `completionLocBaseEquiv` preserves the completed tensor plus ring.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §3, proof of Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.5 and §8.1.
-/

public section

open TensorProduct UniformSpace

namespace TauCeti.Huber.Pair.completedTensor

open CompletedTensor PairOfDefinition

local macro "withCompletionLocBase " A:term:max B:term:max C:term:max
    P:term:max T:term:max s:term:max S:term:max hden:term:max
    α:ident β:ident hαc:ident hβc:ident hα:ident hβ:ident " in " t:term : term =>
  `(letI := locUniformSpace $P $T $s $S $hden
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $hden
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $hden
    ∀ ($α : UniformSpace.Completion $S →+* $B) ($β : UniformSpace.Completion $S →+* $C)
      ($hαc : Continuous $α) ($hβc : Continuous $β)
      ($hα : ($α).comp (PairOfDefinition.toCompletionLoc $P $T $s $S $hden) = algebraMap $A $B)
      ($hβ : ($β).comp (PairOfDefinition.toCompletionLoc $P $T $s $S $hden) = algebraMap $A $C),
      letI : Algebra (UniformSpace.Completion $S) $B := ($α).toAlgebra
      letI : Algebra (UniformSpace.Completion $S) $C := ($β).toAlgebra
      haveI : IsAdicHom (algebraMap (UniformSpace.Completion $S) $B) :=
        PairOfDefinition.isAdicHom_of_comp_toCompletionLoc $P $T $s $S $hden $hαc
          (($hα).symm ▸ inferInstanceAs (IsAdicHom (algebraMap $A $B)))
      haveI : IsAdicHom (algebraMap (UniformSpace.Completion $S) $C) :=
        PairOfDefinition.isAdicHom_of_comp_toCompletionLoc $P $T $s $S $hden $hβc
          (($hβ).symm ▸ inferInstanceAs (IsAdicHom (algebraMap $A $C)))
      $t)

local macro "funCompletionLocBase " A:term:max B:term:max C:term:max
    P:term:max T:term:max s:term:max S:term:max hden:term:max
    α:ident β:ident hαc:ident hβc:ident hα:ident hβ:ident " => " t:term : term =>
  `(letI := locUniformSpace $P $T $s $S $hden
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $hden
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $hden
    fun ($α : UniformSpace.Completion $S →+* $B) ($β : UniformSpace.Completion $S →+* $C)
      ($hαc : Continuous $α) ($hβc : Continuous $β)
      ($hα : ($α).comp (PairOfDefinition.toCompletionLoc $P $T $s $S $hden) = algebraMap $A $B)
      ($hβ : ($β).comp (PairOfDefinition.toCompletionLoc $P $T $s $S $hden) = algebraMap $A $C) ↦
      letI : Algebra (UniformSpace.Completion $S) $B := ($α).toAlgebra
      letI : Algebra (UniformSpace.Completion $S) $C := ($β).toAlgebra
      haveI : IsAdicHom (algebraMap (UniformSpace.Completion $S) $B) :=
        PairOfDefinition.isAdicHom_of_comp_toCompletionLoc $P $T $s $S $hden $hαc
          (($hα).symm ▸ inferInstanceAs (IsAdicHom (algebraMap $A $B)))
      haveI : IsAdicHom (algebraMap (UniformSpace.Completion $S) $C) :=
        PairOfDefinition.isAdicHom_of_comp_toCompletionLoc $P $T $s $S $hden $hβc
          (($hβ).symm ▸ inferInstanceAs (IsAdicHom (algebraMap $A $C)))
      $t)

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  (P₀ : PairOfDefinition A) (T₀ : Set A) (s₀ : A) (S₀ : Type*) [CommRing S₀] [Algebra A S₀]
  [IsLocalization.Away s₀ S₀] (hden₀ : HasDenominatorPower P₀ T₀ s₀ S₀) (UB : Pair B) (UC : Pair C)

/-- `completionLocBaseEquiv` identifies the completed tensor plus ring over `A⟨T₀/s₀⟩` with that
over `A`, for any Huber pairs on `B` and `C`. -/
theorem map_plus_completionLocBaseEquiv :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    ((UB.completedTensor (Completion S₀) UC).plus.map
        (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toRingHom) =
      (UB.completedTensor A UC).plus :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => by
    let e := completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
    let W₀ := UB.completedTensor (Completion S₀) UC
    let W := UB.completedTensor A UC
    have _ := W₀.isRingOfIntegralElements.isIntegrallyClosedIn
    have _ := W.isRingOfIntegralElements.isIntegrallyClosedIn
    refine Subring.map_equiv_eq_of_le_comap e ?_ ?_
    · exact UB.completedTensor_plus_le_comap (A := Completion S₀) UC
        (W.plus.toAddSubgroup.isClosed_of_isOpen W.isRingOfIntegralElements.isOpen)
        (continuous_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ)
        (fun b hb ↦ by
          simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
            completionLocBaseEquiv_inl] using UB.inl_mem_completedTensor_plus (A := A) UC hb)
        (fun c hc ↦ by
          simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
            completionLocBaseEquiv_inr] using UB.inr_mem_completedTensor_plus (A := A) UC hc)
    · exact UB.completedTensor_plus_le_comap (A := A) UC
        (W₀.plus.toAddSubgroup.isClosed_of_isOpen W₀.isRingOfIntegralElements.isOpen)
        (continuous_completionLocBaseEquiv_symm P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ)
        (fun b hb ↦ by
          simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
            completionLocBaseEquiv_symm_inl] using
              UB.inl_mem_completedTensor_plus (A := Completion S₀) UC hb)
        (fun c hc ↦ by
          simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
            completionLocBaseEquiv_symm_inr] using
              UB.inr_mem_completedTensor_plus (A := Completion S₀) UC hc)

/-- Membership in the completed tensor plus ring is preserved and reflected by
`completionLocBaseEquiv`. -/
theorem mem_completedTensor_plus_iff_completionLocBaseEquiv :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    ∀ x : CompletedTensor (Completion S₀) B C,
      x ∈ (UB.completedTensor (Completion S₀) UC).plus ↔
        completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ x ∈
          (UB.completedTensor A UC).plus :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => fun x ↦ by
    rw [← map_plus_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ,
      RingEquiv.toRingHom_eq_coe, Subring.mem_map_equiv, RingEquiv.symm_apply_apply]

/-- The forward Huber-pair morphism `(B, B⁺) ⊗̂_{A⟨T₀/s₀⟩} (C, C⁺) → (B, B⁺) ⊗̂_A (C, C⁺)` out of
the localised base. -/
noncomputable def ofBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    Hom (UB.completedTensor (Completion S₀) UC) (UB.completedTensor A UC) :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ =>
    { toRingHom := (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toRingHom
      continuous_toRingHom :=
        continuous_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
      map_mem_plus := fun x hx ↦
        (mem_completedTensor_plus_iff_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ UB UC
          α β hαc hβc hα hβ x).mp hx }

/-- The inverse Huber-pair morphism `(B, B⁺) ⊗̂_A (C, C⁺) → (B, B⁺) ⊗̂_{A⟨T₀/s₀⟩} (C, C⁺)` into the
localised base. -/
noncomputable def toBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    Hom (UB.completedTensor A UC) (UB.completedTensor (Completion S₀) UC) :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ =>
    { toRingHom := (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm.toRingHom
      continuous_toRingHom :=
        continuous_completionLocBaseEquiv_symm P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
      map_mem_plus := fun _ hy ↦
        (mem_completedTensor_plus_iff_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ UB UC
          α β hαc hβc hα hβ _).mpr (by simpa using hy) }

/-- The underlying ring homomorphism of `ofBaseLocalization`. -/
@[simp] theorem toRingHom_ofBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).toRingHom =
      (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toRingHom :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => (rfl)

/-- The underlying ring homomorphism of `toBaseLocalization`. -/
@[simp] theorem toRingHom_toBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).toRingHom =
      (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm.toRingHom :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => (rfl)

/-- `toBaseLocalization` is a left inverse to `ofBaseLocalization`. -/
@[simp] theorem toBaseLocalization_comp_ofBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).comp
        (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ) = Hom.id _ :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => by
    ext x; simp

/-- `ofBaseLocalization` is a left inverse to `toBaseLocalization`. -/
@[simp] theorem ofBaseLocalization_comp_toBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).comp
        (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ) = Hom.id _ :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => by
    ext x; simp

end TauCeti.Huber.Pair.completedTensor
