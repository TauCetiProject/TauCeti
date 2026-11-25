/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Unit
public import TauCeti.RingTheory.Huber.Pair.Finite.Basic

/-!
# Finiteness of the coprojection and the plus ring of the other factor

Finiteness of the coprojection `(C, C⁺) → (C, C⁺) ⊗̂_A (B, B⁺)` as a morphism of Huber pairs
constrains the plus ring `B⁺` of the other factor. The completed tensor plus ring contains the
image of `B⁺`, and a finite morphism makes it integral over the image of `C⁺`. When the
coprojection is injective, every element of `A` landing in `B⁺` therefore lands in the integrally
closed `C⁺` (`Pair.completedTensor.algebraMap_mem_plus_of_isFinite_inl`).

Over the base itself, with `B = C = A` complete and Hausdorff, the coprojection
`(A, A⁺₁) → (A, A⁺₁) ⊗̂_A (A, A⁺₂)` is finite only if `A⁺₂ ≤ A⁺₁`
(`Pair.completedTensor.plus_le_of_isFinite_inl_self`), and when `A⁺₁ ≤ A⁺₂` the right unit
carries the completed tensor plus ring onto `A⁺₂`
(`Pair.completedTensor.rightUnitor_mem_plus_self_iff`). So for `A⁺₁ ⊊ A⁺₂` the completed tensor
product is `(A, A⁺₂)` and the coprojection is the identity ring map `(A, A⁺₁) → (A, A⁺₂)`, which is
not finite. This is why finite étale base change of Huber pairs uses the integral-closure plus
ring on the finite étale factor (`Pair.completedTensor.isFiniteEtale_inl`).

## Main results

* `TauCeti.Huber.Pair.completedTensor.algebraMap_mem_plus_of_isFinite_inl`: if the coprojection
  from `(C, C⁺)` is finite and injective, then `a ∈ A` with image in `B⁺` has image in `C⁺`.
* `TauCeti.Huber.Pair.completedTensor.plus_le_of_isFinite_inl_self`: over the base, a finite
  coprojection forces `A⁺₂ ≤ A⁺₁`.
* `TauCeti.Huber.Pair.completedTensor.rightUnitor_mem_plus_self_iff`: for `A⁺₁ ≤ A⁺₂`, the plus
  ring of `(A, A⁺₁) ⊗̂_A (A, A⁺₂)` is `A⁺₂` under the right unit.
-/

public section

namespace TauCeti.Huber.Pair.completedTensor

section General

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  {T : Pair C} {U : Pair B}

/-- **A finite injective coprojection pulls the other factor's plus ring back into its own.** If
`(C, C⁺) → (C, C⁺) ⊗̂_A (B, B⁺)` is a finite morphism of Huber pairs with injective ring map, then
every `a : A` whose image lies in `B⁺` has image in `C⁺`: its image in the completed tensor plus
ring is integral over the image of `C⁺`, and `C⁺` is integrally closed in `C`. -/
theorem algebraMap_mem_plus_of_isFinite_inl (h : (inl A T U).IsFinite)
    (hinj : Function.Injective (CompletedTensor.inl A C B)) {a : A}
    (ha : algebraMap A B a ∈ U.plus) : algebraMap A C a ∈ T.plus := by
  have hmem : CompletedTensor.inl A C B (algebraMap A C a) ∈ (T.completedTensor A U).plus := by
    rw [CompletedTensor.inl_algebraMap, ← CompletedTensor.inr_algebraMap]
    exact T.inr_mem_completedTensor_plus U ha
  obtain ⟨q, hqm, hq⟩ := h.isIntegral_restrict ⟨_, hmem⟩
  refine Subring.isIntegrallyClosedIn_iff.mp T.isRingOfIntegralElements.isIntegrallyClosedIn
    ⟨q, hqm, hinj ?_⟩
  have hcomp : (T.completedTensor A U).plus.subtype.comp
      ((inl A T U).toRingHom.restrict T.plus _ (inl A T U).map_mem_plus) =
      (CompletedTensor.inl A C B).comp T.plus.subtype := by
    ext; simp
  have := congrArg Subtype.val hq
  rw [← Subring.coe_subtype, Polynomial.hom_eval₂, hcomp] at this
  simp only [Subring.coe_subtype, ZeroMemClass.coe_zero] at this
  rw [Polynomial.hom_eval₂, map_zero]
  exact this

end General

section Self

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] [T2Space A] {S T : Pair A}

/-- **Over the base, a finite coprojection does not enlarge the plus ring.** For two Huber pairs
`(A, A⁺₁)` and `(A, A⁺₂)` on the same complete Hausdorff ring, if the coprojection
`(A, A⁺₁) → (A, A⁺₁) ⊗̂_A (A, A⁺₂)` is finite then `A⁺₂ ≤ A⁺₁`. -/
theorem plus_le_of_isFinite_inl_self (h : (inl A S T).IsFinite) : T.plus ≤ S.plus := fun _ ha ↦
  algebraMap_mem_plus_of_isFinite_inl h
    (Function.LeftInverse.injective (CompletedTensor.rightUnitor_inl A A)) ha

/-- **The completed tensor plus ring over the base is the larger plus ring.** For
`A⁺₁ ≤ A⁺₂` on the same complete Hausdorff ring, an element of `A ⊗̂_A A` lies in the plus ring of
`(A, A⁺₁) ⊗̂_A (A, A⁺₂)` exactly when its image under the right unit lies in `A⁺₂`. -/
theorem rightUnitor_mem_plus_self_iff (hST : S.plus ≤ T.plus) (x : CompletedTensor A A A) :
    x ∈ (S.completedTensor A T).plus ↔ CompletedTensor.rightUnitor A A x ∈ T.plus := by
  have := T.isRingOfIntegralElements.isIntegrallyClosedIn
  constructor
  · intro hx
    exact S.completedTensor_plus_le_comap T
      (f := (CompletedTensor.rightUnitor A A).toRingHom)
      (T.plus.toAddSubgroup.isClosed_of_isOpen T.isRingOfIntegralElements.isOpen)
      (CompletedTensor.continuous_rightUnitor A A)
      (fun b hb ↦ by simpa using hST hb) (fun c hc ↦ by simpa using hc) hx
  · intro hx
    have hx' := S.inr_mem_completedTensor_plus (A := A) T hx
    rwa [← Algebra.algebraMap_self_apply (CompletedTensor.rightUnitor A A x),
      CompletedTensor.inr_algebraMap, ← CompletedTensor.inl_algebraMap,
      Algebra.algebraMap_self_apply, ← CompletedTensor.rightUnitor_symm_apply,
      RingEquiv.symm_apply_apply] at hx'

end Self

end TauCeti.Huber.Pair.completedTensor
