/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.AdicHom.Localization
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Invariance of completed tensor products under localising the base ring

Let `A → B` and `A → C` be adic homomorphisms of topological rings and `A → A⟨T₀/s₀⟩` a completed
rational localisation of `A`. Because `A → A⟨T₀/s₀⟩` is adic and continuous homomorphisms out of
`A⟨T₀/s₀⟩` into Hausdorff rings are determined by their restriction to `A`
(`TauCeti.Huber.PairOfDefinition.completion_locTopology_ringHom_ext_of_continuous`), any continuous
extensions `α : A⟨T₀/s₀⟩ →+* B` and `β : A⟨T₀/s₀⟩ →+* C` of the `A`-algebra structures on `B` and
`C` are automatically adic (`TauCeti.Huber.PairOfDefinition.isAdicHom_of_comp_toCompletionLoc`),
and the completed tensor product `B ⊗̂_{A⟨T₀/s₀⟩} C` agrees with `B ⊗̂_A C` both as a topological
ring and, when `B` and `C` carry Huber pairs, on rings of integral elements.

## Main definitions

* `TauCeti.Huber.CompletedTensor.completionLocBaseEquiv`: the topological ring equivalence
  `B ⊗̂_{A⟨T₀/s₀⟩} C ≃+* B ⊗̂_A C` when `A → B` and `A → C` factor continuously through `A⟨T₀/s₀⟩`.
* `TauCeti.Huber.Pair.completedTensor.toBaseLocalization`,
  `TauCeti.Huber.Pair.completedTensor.ofBaseLocalization`: mutually inverse morphisms of Huber
  pairs between `(B, B⁺) ⊗̂_{A⟨T₀/s₀⟩} (C, C⁺)` and `(B, B⁺) ⊗̂_A (C, C⁺)`.

## Main results

* `TauCeti.Huber.PairOfDefinition.isAdicHom_of_comp_toCompletionLoc`: a continuous homomorphism out
  of `A⟨T₀/s₀⟩` whose composite with `A → A⟨T₀/s₀⟩` is adic is itself adic.
* `TauCeti.Huber.CompletedTensor.isHomeomorph_completionLocBaseEquiv`: `completionLocBaseEquiv` is
  a homeomorphism.
* `TauCeti.Huber.Pair.completedTensor.map_plus_completionLocBaseEquiv`: `completionLocBaseEquiv`
  maps the completed tensor plus ring over `A⟨T₀/s₀⟩` onto that over `A`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §3, proof of Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.5 and §8.1.
-/

public section

open TensorProduct UniformSpace

namespace TauCeti.Huber.PairOfDefinition

/-- A continuous ring homomorphism out of a completed localisation `A⟨T₀/s₀⟩` whose composite with
the structure map `A → A⟨T₀/s₀⟩` is adic is itself adic. -/
theorem isAdicHom_of_comp_toCompletionLoc {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P₀ : PairOfDefinition A) (T₀ : Set A) (s₀ : A) (S₀ : Type*)
    [CommRing S₀] [Algebra A S₀] [IsLocalization.Away s₀ S₀]
    (hden₀ : HasDenominatorPower P₀ T₀ s₀ S₀) {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ {φ : Completion S₀ →+* B}, Continuous φ →
      IsAdicHom (φ.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀)) → IsAdicHom φ := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isHuberRing_completion_locTopology P₀ T₀ s₀ S₀ hden₀
  intro φ hφ hadic
  exact IsAdicHom.of_comp hadic (continuous_toCompletionLoc P₀ T₀ s₀ S₀ hden₀) hφ

end TauCeti.Huber.PairOfDefinition

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
`β : A⟨T₀/s₀⟩ → C`, the completed tensor product `B ⊗̂_{A⟨T₀/s₀⟩} C` is canonically isomorphic to
`B ⊗̂_A C`, because `A → A⟨T₀/s₀⟩` is epimorphic for continuous maps into Hausdorff rings. -/
noncomputable def completionLocBaseEquiv :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      CompletedTensor (Completion S₀) B C ≃+* CompletedTensor A B C := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  have hcompat : (inl A B C).comp (algebraMap (Completion S₀) B) =
      (inr A B C).comp (algebraMap (Completion S₀) C) := by
    refine completion_locTopology_ringHom_ext_of_continuous P₀ T₀ s₀ S₀ hden₀ _ _
      ((continuous_inl A B C).comp hαc) ((continuous_inr A B C).comp hβc) ?_
    rw [RingHom.comp_assoc, RingHom.comp_assoc, RingHom.algebraMap_toAlgebra,
      RingHom.algebraMap_toAlgebra, hα, hβ, inl_comp_algebraMap]
  have hcompat' : (inl (Completion S₀) B C).comp (algebraMap A B) =
      (inr (Completion S₀) B C).comp (algebraMap A C) := by
    rw [← hα, ← hβ, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
    exact congrArg (·.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀))
      (inl_comp_algebraMap (A := Completion S₀) (B := B) (C := C))
  let fwd := lift (A := Completion S₀) (inl A B C) (inr A B C) hcompat
    (continuous_inl A B C) (continuous_inr A B C)
  let inv := lift (A := A) (inl (Completion S₀) B C) (inr (Completion S₀) B C) hcompat'
    (continuous_inl _ B C) (continuous_inr _ B C)
  refine RingEquiv.ofRingHom fwd inv ?_ ?_
  · refine hom_ext ((continuous_lift ..).comp (continuous_lift ..)) continuous_id
      (by ext b; simp [fwd, inv]) (by ext c; simp [fwd, inv])
  · refine hom_ext ((continuous_lift ..).comp (continuous_lift ..)) continuous_id
      (by ext b; simp [fwd, inv]) (by ext c; simp [fwd, inv])

/-- `completionLocBaseEquiv` is continuous. -/
@[fun_prop] theorem continuous_completionLocBaseEquiv :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      Continuous (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ) := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  exact continuous_lift ..

/-- The inverse of `completionLocBaseEquiv` is continuous. -/
@[fun_prop] theorem continuous_completionLocBaseEquiv_symm :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      Continuous (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  exact continuous_lift ..

/-- `completionLocBaseEquiv` is a homeomorphism. -/
theorem isHomeomorph_completionLocBaseEquiv :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      IsHomeomorph (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ) := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  exact (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ,
      continuous_completionLocBaseEquiv_symm P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ⟩

/-- `completionLocBaseEquiv` preserves the left coprojection. -/
@[simp] theorem completionLocBaseEquiv_inl :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C) (b : B),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
          (inl (Completion S₀) B C b) = inl A B C b := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ b
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  simp [completionLocBaseEquiv]

/-- `completionLocBaseEquiv` preserves the right coprojection. -/
@[simp] theorem completionLocBaseEquiv_inr :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C) (c : C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
          (inr (Completion S₀) B C c) = inr A B C c := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ c
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  simp [completionLocBaseEquiv]

/-- The inverse of `completionLocBaseEquiv` preserves the left coprojection. -/
@[simp] theorem completionLocBaseEquiv_symm_inl :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C) (b : B),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm (inl A B C b) =
        inl (Completion S₀) B C b := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ b
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  simp [completionLocBaseEquiv]

/-- The inverse of `completionLocBaseEquiv` preserves the right coprojection. -/
@[simp] theorem completionLocBaseEquiv_symm_inr :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C) (c : C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm (inr A B C c) =
        inr (Completion S₀) B C c := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ c
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  simp [completionLocBaseEquiv]

/-- `completionLocBaseEquiv` sends pure tensors `b ⊗ₜ c` over `A⟨T₀/s₀⟩` to `b ⊗ₜ c` over `A`. -/
theorem completionLocBaseEquiv_toCompletion_tmul :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C) (b : B) (c : C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
          (toCompletion (Completion S₀) B C (b ⊗ₜ[Completion S₀] c)) =
        toCompletion A B C (b ⊗ₜ[A] c) := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ b c
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
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
  [IsLocalization.Away s₀ S₀] (hden₀ : HasDenominatorPower P₀ T₀ s₀ S₀)

/-- `completionLocBaseEquiv` identifies the completed tensor plus ring over `A⟨T₀/s₀⟩` with that
over `A`, for any Huber pairs on `B` and `C`. -/
theorem map_plus_completionLocBaseEquiv (UB : Pair B) (UC : Pair C) :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      ((UB.completedTensor (Completion S₀) UC).plus.map
        (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toRingHom) =
        (UB.completedTensor A UC).plus := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  let e := completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
  let W₀ := UB.completedTensor (Completion S₀) UC
  let W := UB.completedTensor A UC
  have _ := W₀.isRingOfIntegralElements.isIntegrallyClosedIn
  have _ := W.isRingOfIntegralElements.isIntegrallyClosedIn
  have hf : W₀.plus ≤ W.plus.comap e.toRingHom :=
    UB.completedTensor_plus_le_comap (A := Completion S₀) UC
      (W.plus.toAddSubgroup.isClosed_of_isOpen W.isRingOfIntegralElements.isOpen)
      (f := e.toRingHom)
      (continuous_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ)
      (fun b hb ↦ by
        simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
          completionLocBaseEquiv_inl]
        exact UB.inl_mem_completedTensor_plus (A := A) UC hb)
      (fun c hc ↦ by
        simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
          completionLocBaseEquiv_inr]
        exact UB.inr_mem_completedTensor_plus (A := A) UC hc)
  have hg : W.plus ≤ W₀.plus.comap e.symm.toRingHom :=
    UB.completedTensor_plus_le_comap (A := A) UC
      (W₀.plus.toAddSubgroup.isClosed_of_isOpen W₀.isRingOfIntegralElements.isOpen)
      (f := e.symm.toRingHom)
      (continuous_completionLocBaseEquiv_symm P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ)
      (fun b hb ↦ by
        simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
          completionLocBaseEquiv_symm_inl]
        exact UB.inl_mem_completedTensor_plus (A := Completion S₀) UC hb)
      (fun c hc ↦ by
        simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
          completionLocBaseEquiv_symm_inr]
        exact UB.inr_mem_completedTensor_plus (A := Completion S₀) UC hc)
  exact le_antisymm (Subring.map_le_iff_le_comap.mpr hf) fun x hx ↦
    ⟨e.symm x, hg hx, e.apply_symm_apply x⟩

/-- Membership in the completed tensor plus ring is preserved and reflected by
`completionLocBaseEquiv`. -/
@[simp] theorem mem_completedTensor_plus_iff_completionLocBaseEquiv (UB : Pair B) (UC : Pair C) :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      ∀ x : CompletedTensor (Completion S₀) B C,
        x ∈ (UB.completedTensor (Completion S₀) UC).plus ↔
          completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ x ∈
            (UB.completedTensor A UC).plus := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ x
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  rw [← map_plus_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ]
  exact (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).injective.mem_set_image.symm

/-- The forward Huber-pair morphism `(B, B⁺) ⊗̂_{A⟨T₀/s₀⟩} (C, C⁺) → (B, B⁺) ⊗̂_A (C, C⁺)`. -/
noncomputable def toBaseLocalization (UB : Pair B) (UC : Pair C) :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      Hom (UB.completedTensor (Completion S₀) UC) (UB.completedTensor A UC) := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  exact
    { toRingHom := (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toRingHom
      continuous_toRingHom := continuous_completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
      map_mem_plus := fun x hx ↦
        (mem_completedTensor_plus_iff_completionLocBaseEquiv
          P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ x).mp hx }

/-- The inverse Huber-pair morphism `(B, B⁺) ⊗̂_A (C, C⁺) → (B, B⁺) ⊗̂_{A⟨T₀/s₀⟩} (C, C⁺)`. -/
noncomputable def ofBaseLocalization (UB : Pair B) (UC : Pair C) :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      Hom (UB.completedTensor A UC) (UB.completedTensor (Completion S₀) UC) := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  exact
    { toRingHom := (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm.toRingHom
      continuous_toRingHom :=
        continuous_completionLocBaseEquiv_symm P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ
      map_mem_plus := fun y hy ↦
        (mem_completedTensor_plus_iff_completionLocBaseEquiv
          P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ _).mpr (by simpa using hy) }

/-- The underlying ring homomorphism of `toBaseLocalization`. -/
@[simp] theorem toRingHom_toBaseLocalization (UB : Pair B) (UC : Pair C) :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).toRingHom =
        (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).toRingHom := by
  intro α β hαc hβc hα hβ; rfl

/-- The underlying ring homomorphism of `ofBaseLocalization`. -/
@[simp] theorem toRingHom_ofBaseLocalization (UB : Pair B) (UC : Pair C) :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).toRingHom =
        (completionLocBaseEquiv P₀ T₀ s₀ S₀ hden₀ α β hαc hβc hα hβ).symm.toRingHom := by
  intro α β hαc hβc hα hβ; rfl

/-- `ofBaseLocalization` is a left inverse to `toBaseLocalization`. -/
@[simp] theorem ofBaseLocalization_comp_toBaseLocalization (UB : Pair B) (UC : Pair C) :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).comp
          (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ) = Hom.id _ := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  ext x; simp

/-- `toBaseLocalization` is a left inverse to `ofBaseLocalization`. -/
@[simp] theorem toBaseLocalization_comp_ofBaseLocalization (UB : Pair B) (UC : Pair C) :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    ∀ (α : Completion S₀ →+* B) (β : Completion S₀ →+* C)
      (hαc : Continuous α) (hβc : Continuous β)
      (hα : α.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A B)
      (hβ : β.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) = algebraMap A C),
      letI : Algebra (Completion S₀) B := α.toAlgebra
      letI : Algebra (Completion S₀) C := β.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) B) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
          (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
      haveI : IsAdicHom (algebraMap (Completion S₀) C) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
          (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
      (toBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ).comp
          (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀ UB UC α β hαc hβc hα hβ) = Hom.id _ := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  intro α β hαc hβc hα hβ
  let _ : Algebra (Completion S₀) B := α.toAlgebra
  let _ : Algebra (Completion S₀) C := β.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) B) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hαc
      (hα.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap (Completion S₀) C) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ hβc
      (hβ.symm ▸ inferInstanceAs (IsAdicHom (algebraMap A C)))
  ext x; simp

end TauCeti.Huber.Pair.completedTensor
