/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.CompletedScalars
public import TauCeti.RingTheory.Huber.Adic

/-!
# Checks for completed scalar actions on finite modules

For the integers with the `(p)`-adic topology, the constructed action on their completion
agrees with multiplication, including when `p = 0` (discrete) or `p = 1` (indiscrete).
The general checks exercise the scalar tower, the completed-linear comparison and its inverse
without unfolding their constructions.
-/

public section

noncomputable section

open TensorProduct UniformSpace
open TauCeti.Huber

namespace TauCeti.Examples

section General

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
  [UniformSpace M] [IsUniformAddGroup M] [IsModuleTopology A M]
  [UniformContinuousConstSMul A M]
  (P : PairOfDefinition A) [IsNoetherianRing P.ringOfDefinition]

variable [TopologicalSpace (Completion A ⊗[A] M)]
  [IsModuleTopology (Completion A) (Completion A ⊗[A] M)]

-- Both scalar rings act compatibly on the entire completion, not just its dense submodule.
example (a : A) (b : Completion A) (x : Completion M) :
    letI := P.completionModule (M := M)
    (a • b) • x = a • (b • x) := by
  let := P.completionModule (M := M)
  have := P.isScalarTower_completionModule (M := M)
  exact smul_assoc a b x

-- The completed-linear comparison fixes the tensor determined by a finite linear combination.
example (a b : A) (m n : M) :
    letI := P.completionModule (M := M)
    P.completionTensorHomeomorph ((a : Completion A) ⊗ₜ m + (b : Completion A) ⊗ₜ n) =
      (a • m + b • n : M) := by
  let := P.completionModule (M := M)
  simp [Completion.coe_add]

-- Its inverse recovers the same canonical tensor, including the zero-module case.
example (m : M) :
    letI := P.completionModule (M := M)
    (P.completionTensorHomeomorph (M := M)).symm (m : Completion M) =
      (1 : Completion A) ⊗ₜ[A] m := by
  simp

end General

-- No completeness or Hausdorffness is required of the uncompleted ring or module.
example (p : ℤ) :
    letI : TopologicalSpace ℤ := (Ideal.span {p}).adicTopology
    letI : UniformSpace ℤ := IsTopologicalAddGroup.rightUniformSpace ℤ
    haveI : IsUniformAddGroup ℤ := isUniformAddGroup_of_addCommGroup
    let P := PairOfDefinition.adic (Ideal.span {p}) (by rfl) (Submodule.fg_span_singleton p)
    haveI : IsNoetherianRing P.ringOfDefinition :=
      (PairOfDefinition.adic_ringOfDefinition (Ideal.span {p}) (by rfl)
        (Submodule.fg_span_singleton p)).symm ▸
          isNoetherianRing_of_ringEquiv ℤ Subring.topEquiv.symm
    ∀ a b : Completion ℤ,
      @SMul.smul _ _ (P.completionModule (M := ℤ)).toSMul a b = a * b := by
  let := (Ideal.span {p}).adicTopology
  let := IsTopologicalAddGroup.rightUniformSpace ℤ
  have := isUniformAddGroup_of_addCommGroup (G := ℤ)
  let P := PairOfDefinition.adic (Ideal.span {p}) (by rfl) (Submodule.fg_span_singleton p)
  have : IsNoetherianRing P.ringOfDefinition :=
    (PairOfDefinition.adic_ringOfDefinition (Ideal.span {p}) (by rfl)
      (Submodule.fg_span_singleton p)).symm ▸
        isNoetherianRing_of_ringEquiv ℤ Subring.topEquiv.symm
  have h := P.completionModule_unique (M := ℤ) (Semiring.toModule) inferInstance
    fun x y ↦ (Completion.coe_mul x y).symm
  refine fun a b ↦ ?_
  rw [← h]
  rfl

end TauCeti.Examples
