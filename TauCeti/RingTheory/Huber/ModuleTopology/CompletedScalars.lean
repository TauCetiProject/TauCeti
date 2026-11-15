/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Completion
import Mathlib.Algebra.Module.TransferInstance

/-!
# Completed scalars on the completion of a finite module

Let `A` be a Huber ring with a noetherian ring of definition and `M` a finite `A`-module
with its natural topology. The canonical comparison `Â ⊗[A] M → M̂` is already known to be
an `A`-linear homeomorphism. Transporting the `Â`-action through this comparison makes
`M̂` a topological `Â`-module and upgrades the comparison to an `Â`-linear homeomorphism.
Neither the ring nor the original module needs to be Hausdorff or complete.

The action extends the original scalar action and is uniquely characterized by continuity
and its values on the images of `A` and `M`. The module structure is explicit data
(`PairOfDefinition.completionModule`), rather than a global instance depending on a choice
of ring of definition. After installing it locally, `completionTensorHomeomorph` gives the
completed-scalar comparison and `isModuleTopology_completionModule` identifies the natural
topology. This is the completed-module comparison used for finite-module Čech complexes.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Lemma 2.3(iii).
-/

public section

open Topology TensorProduct UniformSpace

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
  [UniformSpace M] [IsUniformAddGroup M] [IsModuleTopology A M]
  [UniformContinuousConstSMul A M]

/-- The action of `Â` on `M̂`, transported along the canonical finite-module comparison.
Install this structure locally to use `completionTensorHomeomorph`. -/
@[instance_reducible]
noncomputable def completionModule (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] : Module (Completion A) (Completion M) :=
  P.ofTensorProductEquiv.symm.toAddEquiv.module (Completion A)

variable (P : PairOfDefinition A) [IsNoetherianRing P.ringOfDefinition]

/-- The finite-module comparison is linear over the completed coefficient ring. -/
noncomputable def completionTensorLinearEquiv :
    letI := P.completionModule (M := M)
    Completion A ⊗[A] M ≃ₗ[Completion A] Completion M :=
  (P.ofTensorProductEquiv.symm.toAddEquiv.linearEquiv (Completion A)).symm

/-- Upgrading the scalars does not change the canonical comparison map. -/
@[simp]
theorem completionTensorLinearEquiv_apply (t : Completion A ⊗[A] M) :
    P.completionTensorLinearEquiv t = Completion.ofTensorProduct A M t :=
  P.ofTensorProductEquiv_apply t

/-- The inverse completed-scalar comparison sends the image of `m` to `1 ⊗ m`. -/
@[simp]
theorem completionTensorLinearEquiv_symm_coe (m : M) :
    P.completionTensorLinearEquiv.symm (m : Completion M) = 1 ⊗ₜ m :=
  P.ofTensorProductEquiv_symm_coe m

/-- The action of a completed scalar on an original module element is the canonical
comparison applied to its elementary tensor. -/
theorem smul_coe_eq_ofTensorProduct (a : Completion A) (m : M) :
    letI := P.completionModule (M := M)
    a • (m : Completion M) = Completion.ofTensorProduct A M (a ⊗ₜ m) := by
  let := P.completionModule (M := M)
  apply P.completionTensorLinearEquiv.symm.injective
  rw [map_smul, P.completionTensorLinearEquiv_symm_coe,
    ← P.completionTensorLinearEquiv_apply, LinearEquiv.symm_apply_apply]
  simp [smul_tmul']

/-- Restricting the completed action along `A → Â` agrees with the existing `A`-action
on `M̂`. -/
@[simp]
theorem coe_smul_completion (a : A) (x : Completion M) :
    letI := P.completionModule (M := M)
    (a : Completion A) • x = a • x := by
  let := P.completionModule (M := M)
  apply P.ofTensorProductEquiv.symm.injective
  -- The transported action is defined through this inverse; the old comparison is `A`-linear.
  exact (P.ofTensorProductEquiv.symm.toAddEquiv.linearEquiv (Completion A)).map_smul
    (a : Completion A) x |>.trans (by
      rw [P.ofTensorProductEquiv.symm.map_smul]
      exact IsScalarTower.algebraMap_smul (Completion A) a (P.ofTensorProductEquiv.symm x))

/-- The old and completed scalar actions form a scalar tower. -/
theorem isScalarTower_completionModule :
    letI := P.completionModule (M := M)
    IsScalarTower A (Completion A) (Completion M) :=
  P.ofTensorProductEquiv.symm.isScalarTower (Completion A)

section TensorTopology

variable [TopologicalSpace (Completion A ⊗[A] M)]
  [IsModuleTopology (Completion A) (Completion A ⊗[A] M)]

/-- **Completion of a finite module is completed scalar extension**, as a topological
`Â`-module (Huber, Lemma 2.3(iii)). The tensor product has its natural `Â`-module topology. -/
noncomputable def completionTensorHomeomorph :
    letI := P.completionModule (M := M)
    Completion A ⊗[A] M ≃L[Completion A] Completion M := by
  letI := P.completionModule (M := M)
  have he : (P.completionTensorLinearEquiv : Completion A ⊗[A] M → Completion M) =
      Completion.ofTensorProduct A M := funext P.completionTensorLinearEquiv_apply
  have h := P.isHomeomorph_ofTensorProduct (M := M)
  rw [← he] at h
  exact { P.completionTensorLinearEquiv with
    continuous_toFun := h.continuous
    continuous_invFun :=
      (P.completionTensorLinearEquiv.toEquiv.toHomeomorphOfContinuousOpen
        h.continuous h.isOpenMap).symm.continuous }

/-- The topological completed-scalar comparison is the canonical map. -/
@[simp]
theorem completionTensorHomeomorph_apply (t : Completion A ⊗[A] M) :
    P.completionTensorHomeomorph t = Completion.ofTensorProduct A M t :=
  P.completionTensorLinearEquiv_apply t

/-- The inverse topological comparison sends the image of `m` to `1 ⊗ m`. -/
@[simp]
theorem completionTensorHomeomorph_symm_coe (m : M) :
    letI := P.completionModule (M := M)
    P.completionTensorHomeomorph.symm (m : Completion M) = 1 ⊗ₜ m :=
  P.completionTensorLinearEquiv_symm_coe m

end TensorTopology

/-- The completion has its natural module topology over the completed coefficient ring. -/
theorem isModuleTopology_completionModule :
    letI := P.completionModule (M := M)
    IsModuleTopology (Completion A) (Completion M) := by
  let := P.completionModule (M := M)
  let := moduleTopology (Completion A) (Completion A ⊗[A] M)
  exact IsModuleTopology.iso P.completionTensorHomeomorph

/-- The extended scalar action is jointly continuous. -/
theorem continuousSMul_completionModule :
    letI := P.completionModule (M := M)
    ContinuousSMul (Completion A) (Completion M) := by
  let := P.completionModule (M := M)
  have := P.isModuleTopology_completionModule (M := M)
  infer_instance

/-- A jointly continuous scalar action extending the action on original scalars and
original module elements is the completed module structure. -/
theorem completionModule_unique (S : Module (Completion A) (Completion M))
    (hcont : letI := S; ContinuousSMul (Completion A) (Completion M))
    (hcoe : letI := S; ∀ (a : A) (m : M),
      (a : Completion A) • (m : Completion M) = (↑(a • m) : Completion M)) :
    S = P.completionModule := by
  apply Module.ext'
  intro a x
  let μ : Completion A × Completion M → Completion M := fun p ↦ letI := S; p.1 • p.2
  let ν : Completion A × Completion M → Completion M :=
    fun p ↦ letI := P.completionModule (M := M); p.1 • p.2
  have hμ : Continuous μ := by
    let := S
    have := hcont
    exact continuous_smul
  have hν : Continuous ν := by
    let := P.completionModule (M := M)
    have := P.continuousSMul_completionModule (M := M)
    exact continuous_smul
  exact Completion.induction_on₂ a x (isClosed_eq hμ hν) fun a m ↦
    (hcoe a m).trans ((P.coe_smul_completion a (m : Completion M)).trans
      (Completion.coe_smul a m).symm).symm

/-- The completed scalar action does not depend on the noetherian ring of definition. -/
theorem completionModule_eq (Q : PairOfDefinition A) [IsNoetherianRing Q.ringOfDefinition] :
    P.completionModule (M := M) = Q.completionModule := by
  symm
  apply P.completionModule_unique Q.completionModule Q.continuousSMul_completionModule
  intro a m
  exact (Q.coe_smul_completion a (m : Completion M)).trans (Completion.coe_smul a m).symm

end TauCeti.Huber.PairOfDefinition
