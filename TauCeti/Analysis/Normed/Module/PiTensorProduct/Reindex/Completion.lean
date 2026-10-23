/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.PiTensorProduct.Reindex.Basic
public import TauCeti.Analysis.Normed.Module.PiTensorProduct.Projective.Completion

/-!
# Symmetry of completed projective tensor products

Relabeling a finite family of factors and their defining seminorms gives a continuous linear
equivalence of their separated completed projective tensor products. In particular, exchanging
two factors gives the completed tensor flip. The equivalence is characterized on the dense
image of algebraic tensors, commutes with tensor products of seminorm-bounded linear maps, and
respects identity relabelings and composition.

No topology, separation, or completeness assumption on the factors is needed: the projective
topology is specified by the seminorm families, and the separated completion is taken after
forming the tensor product. The construction extends `ProjectiveTensorProduct.reindex` and
its inverse using Mathlib's `ContinuousLinearMap.completion`.
-/

public section

open scoped TensorProduct
open UniformSpace

namespace TauCeti.CompletedProjectiveTensorProduct

variable {ι κ υ 𝕜 : Type*} [Fintype ι] [Fintype κ] [Fintype υ] [NormedField 𝕜]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
variable {σ : ι → Type*} (p : ∀ i, SeminormFamily 𝕜 (E i) (σ i))

noncomputable section

/-- Relabel the factors and their seminorms in a separated completed projective tensor product.
For two factors, the transposition gives the completed tensor flip. -/
def reindex (e : ι ≃ κ) :
    CompletedProjectiveTensorProduct p ≃L[𝕜]
      CompletedProjectiveTensorProduct (fun j => p (e.symm j)) := by
  let f := (ProjectiveTensorProduct.reindex p e).toContinuousLinearMap.completion
  let g := (ProjectiveTensorProduct.reindex p e).symm.toContinuousLinearMap.completion
  refine
    { f.toLinearMap with
      invFun := g
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  · exact congr_fun (Completion.ext (g.continuous.comp f.continuous) continuous_id
      (fun x => by simp [f, g]))
  · exact congr_fun (Completion.ext (f.continuous.comp g.continuous) continuous_id
      (fun x => by simp [f, g]))

/-- Completed reindexing extends the reindexing of algebraic projective tensors. -/
@[simp]
theorem reindex_coe (e : ι ≃ κ) (x : ProjectiveTensorProduct p) :
    reindex p e (x : CompletedProjectiveTensorProduct p) =
      (ProjectiveTensorProduct.reindex p e x :
        CompletedProjectiveTensorProduct (fun j => p (e.symm j))) := by
  simp [reindex]

/-- The inverse completed equivalence extends the inverse algebraic reindexing. -/
@[simp]
theorem reindex_symm_coe (e : ι ≃ κ)
    (x : ProjectiveTensorProduct (fun j => p (e.symm j))) :
    (reindex p e).symm (x : CompletedProjectiveTensorProduct (fun j => p (e.symm j))) =
      ((ProjectiveTensorProduct.reindex p e).symm x : CompletedProjectiveTensorProduct p) := by
  apply (reindex p e).injective
  simp

/-- Reindexing a pure tensor relabels its factors. -/
theorem reindex_tprod (e : ι ≃ κ) (x : ∀ i, E i) :
    reindex p e (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct p) =
      (⟨⨂ₜ[𝕜] j, x (e.symm j)⟩ : ProjectiveTensorProduct (fun j => p (e.symm j))) := by
  simp

/-- The inverse equivalence recovers the original pure tensor. -/
theorem reindex_symm_tprod (e : ι ≃ κ) (x : ∀ i, E i) :
    (reindex p e).symm
        (⟨⨂ₜ[𝕜] j, x (e.symm j)⟩ : ProjectiveTensorProduct (fun j => p (e.symm j))) =
      (⟨⨂ₜ[𝕜] i, x i⟩ : ProjectiveTensorProduct p) := by
  simp

/-- The identity relabeling induces the identity equivalence. -/
@[simp]
theorem reindex_refl : reindex p (Equiv.refl ι) = ContinuousLinearEquiv.refl 𝕜 _ := by
  apply ContinuousLinearEquiv.coe_injective
  apply continuousLinearMap_ext p
  intro x
  exact reindex_tprod p (Equiv.refl ι) x

/-- Successive relabelings agree with their composite. -/
theorem reindex_trans (e : ι ≃ κ) (e' : κ ≃ υ) :
    (reindex p e).trans (reindex (fun j => p (e.symm j)) e') =
      reindex p (e.trans e') := by
  apply ContinuousLinearEquiv.coe_injective
  apply continuousLinearMap_ext p
  intro x
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
    reindex_tprod]
  exact (reindex_tprod p (e.trans e') x).symm

variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module 𝕜 (G i)]
variable {τ : ι → Type*} (q : ∀ i, SeminormFamily 𝕜 (G i) (τ i))

/-- Relabeling completed tensor factors commutes with tensoring seminorm-bounded maps. -/
theorem map_comp_reindex (e : ι ≃ κ) (f : ∀ i, E i →ₗ[𝕜] G i)
    (hf : ∀ i, Seminorm.IsBounded (p i) (q i) (f i)) :
    (map (fun j => p (e.symm j)) (fun j => q (e.symm j))
      (fun j => f (e.symm j)) (fun j => hf (e.symm j))).comp
        (reindex p e).toContinuousLinearMap =
      (reindex q e).toContinuousLinearMap.comp (map p q f hf) := by
  apply continuousLinearMap_ext p
  intro x
  simp

end

end TauCeti.CompletedProjectiveTensorProduct
