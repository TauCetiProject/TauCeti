/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.AdicHom.Localization
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Invariance of completed tensor products under localising the base ring

Let `A → B` and `A → C` be adic homomorphisms of topological rings and let `A → A⟨T₀/s₀⟩` be a
completed rational localisation of `A`. Because continuous homomorphisms out of `A⟨T₀/s₀⟩` into
Hausdorff rings are determined by their restriction to `A`
(`TauCeti.Huber.PairOfDefinition.completion_locTopology_ringHom_ext_of_continuous`), any continuous
extensions `α : A⟨T₀/s₀⟩ →+* B` and `β : A⟨T₀/s₀⟩ →+* C` of the `A`-algebra structures on `B` and
`C` are automatically adic (`TauCeti.Huber.PairOfDefinition.isAdicHom_of_comp_toCompletionLoc`),
and the universal property of completed tensor products identifies `B ⊗̂_{A⟨T₀/s₀⟩} C` with
`B ⊗̂_A C` both as a topological ring (`CompletedTensor.completionLocBaseEquiv`) and on rings of
integral elements (`Pair.completedTensor.map_plus_completionLocBaseEquiv`, `toBaseLocalization`,
`ofBaseLocalization`).

## Main definitions

* `TauCeti.Huber.CompletedTensor.completionLocBaseEquiv`: topological ring equivalence
  `B ⊗̂_{A⟨T₀/s₀⟩} C ≃+* B ⊗̂_A C` for continuous extensions `α`, `β` of the `A`-algebra actions.
* `TauCeti.Huber.Pair.completedTensor.toBaseLocalization`,
  `TauCeti.Huber.Pair.completedTensor.ofBaseLocalization`: mutually inverse morphisms of Huber
  pairs for `completionLocBaseEquiv`.

## Main results

* `TauCeti.Huber.CompletedTensor.isHomeomorph_completionLocBaseEquiv`:
  `completionLocBaseEquiv` is a homeomorphism.
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

open TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "withCompletionLocBase " A:term:max B:term:max C:term:max
    P:term:max T:term:max s:term:max S:term:max hden:term:max
    α:ident β:ident hαc:ident hβc:ident hα:ident hβ:ident " in " t:term : term =>
  `(letI := locUniformSpace $P $T $s $S $hden
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $hden
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $hden
    ∀ ($α : Completion $S →+* $B) ($β : Completion $S →+* $C)
      ($hαc : Continuous $α) ($hβc : Continuous $β)
      ($hα : ($α).comp (toCompletionLoc $P $T $s $S $hden) = algebraMap $A $B)
      ($hβ : ($β).comp (toCompletionLoc $P $T $s $S $hden) = algebraMap $A $C),
      letI : Algebra (Completion $S) $B := ($α).toAlgebra
      letI : Algebra (Completion $S) $C := ($β).toAlgebra
      haveI : IsAdicHom (algebraMap (Completion $S) $B) :=
        isAdicHom_of_comp_toCompletionLoc $P $T $s $S $hden $hαc
          (($hα).symm ▸ inferInstanceAs (IsAdicHom (algebraMap $A $B)))
      haveI : IsAdicHom (algebraMap (Completion $S) $C) :=
        isAdicHom_of_comp_toCompletionLoc $P $T $s $S $hden $hβc
          (($hβ).symm ▸ inferInstanceAs (IsAdicHom (algebraMap $A $C)))
      $t)

open TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "funCompletionLocBase " A:term:max B:term:max C:term:max
    P:term:max T:term:max s:term:max S:term:max hden:term:max
    α:ident β:ident hαc:ident hβc:ident hα:ident hβ:ident " => " t:term : term =>
  `(letI := locUniformSpace $P $T $s $S $hden
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $hden
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $hden
    fun ($α : Completion $S →+* $B) ($β : Completion $S →+* $C)
      ($hαc : Continuous $α) ($hβc : Continuous $β)
      ($hα : ($α).comp (toCompletionLoc $P $T $s $S $hden) = algebraMap $A $B)
      ($hβ : ($β).comp (toCompletionLoc $P $T $s $S $hden) = algebraMap $A $C) ↦
      letI : Algebra (Completion $S) $B := ($α).toAlgebra
      letI : Algebra (Completion $S) $C := ($β).toAlgebra
      haveI : IsAdicHom (algebraMap (Completion $S) $B) :=
        isAdicHom_of_comp_toCompletionLoc $P $T $s $S $hden $hαc
          (($hα).symm ▸ inferInstanceAs (IsAdicHom (algebraMap $A $B)))
      haveI : IsAdicHom (algebraMap (Completion $S) $C) :=
        isAdicHom_of_comp_toCompletionLoc $P $T $s $S $hden $hβc
          (($hβ).symm ▸ inferInstanceAs (IsAdicHom (algebraMap $A $C)))
      $t)

namespace TauCeti.Huber.CompletedTensor

open PairOfDefinition

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  (P₀ : PairOfDefinition A) (T₀ : Set A) (s₀ : A) (S₀ : Type*) [CommRing S₀] [Algebra A S₀]
  [IsLocalization.Away s₀ S₀] (hden₀ : HasDenominatorPower P₀ T₀ s₀ S₀)

/-- **Base-ring localisation invariance for completed tensor products.** When the adic structure
maps `A → B` and `A → C` extend to continuous ring homomorphisms `α : A⟨T₀/s₀⟩ → B` and
`β : A⟨T₀/s₀⟩ → C`, `B ⊗̂_{A⟨T₀/s₀⟩} C` is canonically isomorphic to `B ⊗̂_A C`. -/
noncomputable def completionLocBaseEquiv :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    CompletedTensor (Completion S₀) B C ≃+* CompletedTensor A B C :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ =>
    let hcompat : (inl A B C).comp (algebraMap (Completion S₀) B) =
        (inr A B C).comp (algebraMap (Completion S₀) C) :=
      completion_locTopology_ringHom_ext_of_continuous P₀ T₀ s₀ S₀ hden₀ _ _
        ((continuous_inl A B C).comp hαc) ((continuous_inr A B C).comp hβc)
        (by rw [RingHom.comp_assoc, RingHom.comp_assoc, RingHom.algebraMap_toAlgebra,
          RingHom.algebraMap_toAlgebra, hα, hβ, inl_comp_algebraMap])
    let hcompat' : (inl (Completion S₀) B C).comp (algebraMap A B) =
        (inr (Completion S₀) B C).comp (algebraMap A C) := by
      rw [← hα, ← hβ, ← RingHom.comp_assoc, ← RingHom.comp_assoc,
        ← RingHom.algebraMap_toAlgebra α, ← RingHom.algebraMap_toAlgebra β, inl_comp_algebraMap]
    let fwd := lift (A := Completion S₀) (inl A B C) (inr A B C) hcompat
      (continuous_inl ..) (continuous_inr ..)
    let inv := lift (A := A) (inl (Completion S₀) B C) (inr (Completion S₀) B C) hcompat'
      (continuous_inl ..) (continuous_inr ..)
    RingEquiv.ofRingHom fwd inv
      (hom_ext ((continuous_lift ..).comp (continuous_lift ..)) continuous_id
        (by ext b; simp [fwd, inv]) (by ext c; simp [fwd, inv]))
      (hom_ext ((continuous_lift ..).comp (continuous_lift ..)) continuous_id
        (by ext b; simp [fwd, inv]) (by ext c; simp [fwd, inv]))

/-- `completionLocBaseEquiv` is continuous. -/
@[fun_prop] theorem continuous_completionLocBaseEquiv :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    Continuous (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ) :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ =>
    continuous_lift ..

/-- The inverse of `completionLocBaseEquiv` is continuous. -/
@[fun_prop] theorem continuous_completionLocBaseEquiv_symm :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    Continuous (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ =>
    continuous_lift ..

/-- `completionLocBaseEquiv` is a homeomorphism. -/
theorem isHomeomorph_completionLocBaseEquiv :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    IsHomeomorph (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ) :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ =>
    (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toEquiv.isHomeomorph_iff.mpr
      ⟨continuous_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ,
        continuous_completionLocBaseEquiv_symm P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ⟩

/-- `completionLocBaseEquiv` preserves the left coprojection. -/
@[simp] theorem completionLocBaseEquiv_inl :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    ∀ b : B, completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
        (inl (Completion S₀) B C b) = inl A B C b :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => fun b ↦ by
    simp [completionLocBaseEquiv]

/-- `completionLocBaseEquiv` preserves the right coprojection. -/
@[simp] theorem completionLocBaseEquiv_inr :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    ∀ c : C, completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
        (inr (Completion S₀) B C c) = inr A B C c :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => fun c ↦ by
    simp [completionLocBaseEquiv]

/-- The inverse of `completionLocBaseEquiv` preserves the left coprojection. -/
@[simp] theorem completionLocBaseEquiv_symm_inl :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    ∀ b : B, (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm
        (inl A B C b) = inl (Completion S₀) B C b :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => fun b ↦ by
    simp [completionLocBaseEquiv]

/-- The inverse of `completionLocBaseEquiv` preserves the right coprojection. -/
@[simp] theorem completionLocBaseEquiv_symm_inr :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    ∀ c : C, (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm
        (inr A B C c) = inr (Completion S₀) B C c :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => fun c ↦ by
    simp [completionLocBaseEquiv]

/-- `completionLocBaseEquiv` sends pure tensors `b ⊗ₜ c` over `A⟨T₀/s₀⟩` to `b ⊗ₜ c` over `A`. -/
theorem completionLocBaseEquiv_toCompletion_tmul :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    ∀ (b : B) (c : C), completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
        (toCompletion (Completion S₀) B C (b ⊗ₜ[Completion S₀] c)) =
      toCompletion A B C (b ⊗ₜ[A] c) :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => fun b c ↦ by
    simp [toCompletion_tmul]

end TauCeti.Huber.CompletedTensor

namespace TauCeti.Huber.Pair.completedTensor

open CompletedTensor PairOfDefinition

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
    have hf : W₀.plus ≤ W.plus.comap e.toRingHom :=
      UB.completedTensor_plus_le_comap (A := Completion S₀) UC
        (W.plus.toAddSubgroup.isClosed_of_isOpen W.isRingOfIntegralElements.isOpen)
        (continuous_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ)
        (fun b hb ↦ by
          simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
            completionLocBaseEquiv_inl] using UB.inl_mem_completedTensor_plus (A := A) UC hb)
        (fun c hc ↦ by
          simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
            completionLocBaseEquiv_inr] using UB.inr_mem_completedTensor_plus (A := A) UC hc)
    have hg : W.plus ≤ W₀.plus.comap e.symm.toRingHom :=
      UB.completedTensor_plus_le_comap (A := A) UC
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
    exact le_antisymm (Subring.map_le_iff_le_comap.mpr hf) fun x hx ↦
      ⟨e.symm x, hg hx, e.apply_symm_apply x⟩

/-- Membership in the completed tensor plus ring is preserved and reflected by
`completionLocBaseEquiv`. -/
@[simp] theorem mem_completedTensor_plus_iff_completionLocBaseEquiv :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    ∀ x : CompletedTensor (Completion S₀) B C,
      x ∈ (UB.completedTensor (Completion S₀) UC).plus ↔
        completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ x ∈
          (UB.completedTensor A UC).plus :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => fun x ↦ by
    rw [← map_plus_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ]
    exact (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).injective.mem_set_image.symm

/-- The forward Huber-pair morphism `(B, B⁺) ⊗̂_{A⟨T₀/s₀⟩} (C, C⁺) → (B, B⁺) ⊗̂_A (C, C⁺)`. -/
noncomputable def toBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    Hom (UB.completedTensor (Completion S₀) UC) (UB.completedTensor A UC) :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ =>
    { toRingHom := (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toRingHom
      continuous_toRingHom :=
        continuous_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
      map_mem_plus := fun x hx ↦
        (mem_completedTensor_plus_iff_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ UB UC
          α β hαc hβc hα hβ x).mp hx }

/-- The inverse Huber-pair morphism `(B, B⁺) ⊗̂_A (C, C⁺) → (B, B⁺) ⊗̂_{A⟨T₀/s₀⟩} (C, C⁺)`. -/
noncomputable def ofBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    Hom (UB.completedTensor A UC) (UB.completedTensor (Completion S₀) UC) :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ =>
    { toRingHom := (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm.toRingHom
      continuous_toRingHom :=
        continuous_completionLocBaseEquiv_symm P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
      map_mem_plus := fun _ hy ↦
        (mem_completedTensor_plus_iff_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ UB UC
          α β hαc hβc hα hβ _).mpr (by simpa using hy) }

/-- The underlying ring homomorphism of `toBaseLocalization`. -/
@[simp] theorem toRingHom_toBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).toRingHom =
      (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toRingHom :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => (rfl)

/-- The underlying ring homomorphism of `ofBaseLocalization`. -/
@[simp] theorem toRingHom_ofBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).toRingHom =
      (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm.toRingHom :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => (rfl)

/-- `ofBaseLocalization` is a left inverse to `toBaseLocalization`. -/
@[simp] theorem ofBaseLocalization_comp_toBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).comp
        (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ) = Hom.id _ :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => by
    ext x; simp

/-- `toBaseLocalization` is a left inverse to `ofBaseLocalization`. -/
@[simp] theorem toBaseLocalization_comp_ofBaseLocalization :
    withCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ in
    (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).comp
        (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ) = Hom.id _ :=
  funCompletionLocBase A B C P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ => by
    ext x; simp

end TauCeti.Huber.Pair.completedTensor
