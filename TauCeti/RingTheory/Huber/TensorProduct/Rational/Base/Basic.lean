/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.AdicHom.Localization
public import TauCeti.RingTheory.Huber.TensorProduct.Completion

/-!
# Invariance of completed tensor rings under localising the base ring

Let `A → B` and `A → C` be adic homomorphisms of topological rings and let `A → A⟨T₀/s₀⟩` be a
completed rational localisation of `A`. Given any continuous extensions `α : A⟨T₀/s₀⟩ →+* B` and
`β : A⟨T₀/s₀⟩ →+* C` of the `A`-algebra structures on `B` and `C`, `α` and `β` are automatically
adic because their composites with `A → A⟨T₀/s₀⟩` are adic
(`TauCeti.Huber.PairOfDefinition.isAdicHom_of_comp_toCompletionLoc`). Moreover, because continuous
homomorphisms out of `A⟨T₀/s₀⟩` into Hausdorff rings are determined by their restriction to `A`
(`TauCeti.Huber.PairOfDefinition.completion_locTopology_ringHom_ext_of_continuous`), `inl ∘ α` and
`inr ∘ β` agree in the Hausdorff ring `B ⊗̂_A C`, giving the universal-property lift that
identifies `B ⊗̂_{A⟨T₀/s₀⟩} C` with `B ⊗̂_A C` as a topological ring
(`CompletedTensor.completionLocBaseEquiv`). Only the topological rings are compared here; the
Huber-pair upgrade on rings of integral elements is in
`TauCeti.RingTheory.Huber.TensorProduct.Rational.Base.Pair`.

## Main definitions

* `TauCeti.Huber.CompletedTensor.completionLocBaseEquiv`: topological ring equivalence
  `B ⊗̂_{A⟨T₀/s₀⟩} C ≃+* B ⊗̂_A C` for continuous extensions `α`, `β` of the `A`-algebra actions.

## Main results

* `TauCeti.Huber.CompletedTensor.isHomeomorph_completionLocBaseEquiv`:
  `completionLocBaseEquiv` is a homeomorphism.
* `TauCeti.Huber.CompletedTensor.completionLocBaseEquiv_inl`,
  `completionLocBaseEquiv_inr`, `completionLocBaseEquiv_toCompletion_tmul`: compatibility with
  coprojections and pure tensors.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §3, proof of Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.5 and §8.1.
-/

public section

open TensorProduct UniformSpace

namespace TauCeti.Huber.CompletedTensor

open PairOfDefinition

/-- Bring the localisation topology and extended base-algebra/adic instances for
`completionLocBaseEquiv` into scope under a universal quantifier. -/
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

/-- Bring the localisation topology and extended base-algebra/adic instances for
`completionLocBaseEquiv` into scope under a lambda binder. -/
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
