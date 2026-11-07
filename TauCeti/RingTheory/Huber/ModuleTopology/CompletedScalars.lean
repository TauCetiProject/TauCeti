/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Completion
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Completed scalars on the completion of a finite module

Let `A` have a noetherian ring of definition and let `M` be a finite `A`-module with its
natural topology. The canonical comparison `Â ⊗[A] M → M̂` is already known to be an
`A`-linear homeomorphism. Here we extend the scalar action to `Â`, prove that the action
is continuous and compatible with the original `A`-action, and upgrade the comparison to
an `Â`-linear homeomorphism. In particular `M̂` has its natural topology as an `Â`-module.
This is the completed-scalar form of the finite-module comparison used to identify
completed localization complexes with complexes of base-changed finite modules.

The action is transported along `PairOfDefinition.ofTensorProductEquiv` using Mathlib's
`AddEquiv.module`, not assumed. It is provided as a local instance constructor, so no choice of
a pair of definition is made by global typeclass search. Its values on original scalars and
module elements characterize it uniquely among continuous actions.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Lemma 2.3(iii).
-/

public section

noncomputable section

open Topology TensorProduct UniformSpace

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
  [UniformSpace M] [IsUniformAddGroup M] [IsModuleTopology A M]
  [UniformContinuousConstSMul A M]
  (P : PairOfDefinition A) [IsNoetherianRing P.ringOfDefinition]

/-- The action of the completed ring on the completion of a finite module, transported
through the canonical base-change comparison. Use this as a local instance. -/
@[instance_reducible]
noncomputable def completionModule : Module (Completion A) (Completion M) :=
  P.ofTensorProductEquiv.symm.toAddEquiv.module (Completion A)

/-- Completed scalar multiplication, expressed through the base-change comparison. -/
private theorem completionModule_smul (a : Completion A) (x : Completion M) :
    letI := P.completionModule (M := M)
    a • x = Completion.ofTensorProduct A M (a • P.ofTensorProductEquiv.symm x) := by
  calc
    _ = P.ofTensorProductEquiv (a • P.ofTensorProductEquiv.symm x) := rfl
    _ = _ := P.ofTensorProductEquiv_apply _

/-- A completed scalar acting on an original module element is the image of a pure tensor. -/
@[simp]
theorem completionModule_smul_coe (a : Completion A) (m : M) :
    letI := P.completionModule (M := M)
    a • (m : Completion M) = Completion.ofTensorProduct A M (a ⊗ₜ m) := by
  let := P.completionModule (M := M)
  rw [completionModule_smul, ofTensorProductEquiv_symm_coe]
  simp [TensorProduct.smul_tmul']

/-- The completed scalar action restricts to the existing `A`-module structure on `M̂`. -/
@[simp]
theorem completionModule_coe_smul (a : A) (x : Completion M) :
    letI := P.completionModule (M := M)
    (a : Completion A) • x = a • x := by
  let := P.completionModule (M := M)
  rw [completionModule_smul]
  have ht : (a : Completion A) • P.ofTensorProductEquiv.symm x =
      a • P.ofTensorProductEquiv.symm x :=
    IsScalarTower.algebraMap_smul (A := Completion A) a _
  rw [ht, map_smul]
  simpa only [ofTensorProductEquiv_apply] using
    congrArg (a • ·) (P.ofTensorProductEquiv.apply_symm_apply x)

/-- The original and completed scalar actions form a scalar tower. -/
theorem isScalarTower_completionModule :
    letI := P.completionModule (M := M)
    IsScalarTower A (Completion A) (Completion M) :=
  P.ofTensorProductEquiv.symm.isScalarTower (Completion A)

section Topology

-- Use the natural topology on the scalar extension, rather than choosing any extra topology
-- on the completion itself.
/-- The natural completed-ring module topology on the scalar extension. -/
local instance tensorModuleTopology : TopologicalSpace (Completion A ⊗[A] M) :=
  moduleTopology (Completion A) (Completion A ⊗[A] M)

/-- The upgraded comparison is a homeomorphism for the natural completed-scalar topology. -/
noncomputable def completionTensorHomeomorph :
    letI := P.completionModule (M := M)
    Completion A ⊗[A] M ≃L[Completion A] Completion M := by
  letI := P.completionModule (M := M)
  have hmap : (P.ofTensorProductEquiv (M := M) : _ → _) = Completion.ofTensorProduct A M :=
    funext (P.ofTensorProductEquiv_apply (M := M))
  have hhome : IsHomeomorph (P.ofTensorProductEquiv (M := M)) := by
    rw [hmap]
    exact P.isHomeomorph_ofTensorProduct
  exact { (P.ofTensorProductEquiv.symm.toAddEquiv.linearEquiv (Completion A)).symm with
    continuous_toFun := hhome.continuous
    continuous_invFun := P.ofTensorProductEquiv.toEquiv.continuous_symm_iff.mpr hhome.isOpenMap }

/-- The linear homeomorphism is the canonical base-change map. -/
@[simp]
theorem completionTensorHomeomorph_apply (t : Completion A ⊗[A] M) :
    letI := P.completionModule (M := M)
    P.completionTensorHomeomorph t = Completion.ofTensorProduct A M t :=
  P.ofTensorProductEquiv_apply t

/-- The inverse homeomorphism sends the dense image of `m` to `1 ⊗ m`. -/
@[simp]
theorem completionTensorHomeomorph_symm_coe (m : M) :
    letI := P.completionModule (M := M)
    P.completionTensorHomeomorph.symm (m : Completion M) = 1 ⊗ₜ m :=
  P.ofTensorProductEquiv_symm_coe m

/-- Scalar multiplication by the completed ring is jointly continuous. -/
theorem continuousSMul_completionModule :
    letI := P.completionModule (M := M)
    ContinuousSMul (Completion A) (Completion M) := by
  let := P.completionModule (M := M)
  let e := P.completionTensorHomeomorph (M := M)
  refine ⟨?_⟩
  have h := e.continuous.comp
    ((continuous_fst : Continuous (Prod.fst : Completion A × Completion M → Completion A)).smul
      (e.symm.continuous.comp continuous_snd))
  simpa only [Function.comp_def, Pi.smul_apply', map_smul, e.apply_symm_apply] using h

/-- Any jointly continuous operation agreeing with scalar multiplication on the dense
original ring and module equals the completed scalar action. -/
theorem eq_completionModule_smul (μ : Completion A → Completion M → Completion M)
    (hμ : Continuous (Function.uncurry μ))
    (hcoe : ∀ (a : A) (m : M), μ a m = (a • m : M))
    (a : Completion A) (x : Completion M) :
    letI := P.completionModule (M := M)
    μ a x = a • x := by
  let := P.completionModule (M := M)
  have := P.continuousSMul_completionModule (M := M)
  exact Completion.induction_on₂ a x (isClosed_eq hμ continuous_smul)
    fun b m ↦ (hcoe b m).trans (by rw [completionModule_coe_smul, ← Completion.coe_smul])

/-- The topology on the completed module is its natural topology over the completed ring. -/
theorem isModuleTopology_completionModule :
    letI := P.completionModule (M := M)
    IsModuleTopology (Completion A) (Completion M) := by
  let := P.completionModule (M := M)
  exact IsModuleTopology.iso P.completionTensorHomeomorph

end Topology

end TauCeti.Huber.PairOfDefinition
