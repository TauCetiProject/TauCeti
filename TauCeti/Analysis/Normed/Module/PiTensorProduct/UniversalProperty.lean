/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.PiTensorProduct.ProjectiveTopology
public import TauCeti.Analysis.LocallyConvex.Multilinear

/-!
# The continuous universal property of the projective tensor topology

The algebraic tensor lift is continuous if and only if its multilinear map is continuous,
when the factors and target carry topologies defined by seminorm families. Thus continuous
multilinear maps correspond linearly to continuous linear maps out of the projective tensor
product. This statement concerns the algebraic tensor product with its projective topology;
no completeness or Hausdorffness is required.

The missing continuity-to-bound implication is supplied by
`exists_multilinearMap_seminorm_bound`. The algebraic construction and uniqueness are those
of `ProjectiveTensorProduct.lift`.
-/

public section

namespace TauCeti.ProjectiveTensorProduct

open scoped TensorProduct

variable {ι 𝕜 : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
variable {σ : ι → Type*} (p : ∀ i, SeminormFamily 𝕜 (E i) (σ i))
variable [∀ i, TopologicalSpace (E i)] (hp : ∀ i, WithSeminorms (p i))

/-- The pure-tensor map, bundled as a continuous multilinear map for the projective topology. -/
def continuousTprod : ContinuousMultilinearMap 𝕜 E (ProjectiveTensorProduct p) :=
  ⟨tprod p, continuous_tprod p hp⟩

@[simp] theorem continuousTprod_apply (x : ∀ i, E i) :
    continuousTprod p hp x = tprod p x := (rfl)

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable {τ : Type*} (q : SeminormFamily 𝕜 F τ) (hq : WithSeminorms q)

include hp hq in
/-- The tensor lift is continuous exactly when the original multilinear map is continuous. -/
theorem continuous_lift_iff (f : MultilinearMap 𝕜 E F) :
    Continuous (lift p f) ↔ Continuous f := by
  constructor
  · intro hf
    have hcomp : (lift p f) ∘ tprod p = f := by
      funext x
      simp
    exact hcomp ▸ hf.comp (continuous_tprod p hp)
  · intro hf
    exact continuous_lift p q hq f (fun j =>
      exists_multilinearMap_seminorm_bound p hp (q j) (hq.continuous_seminorm j) f hf)

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]

/-- Continuous multilinear maps correspond linearly to continuous linear maps from the
projective tensor product. The inverse is restriction to pure tensors. -/
noncomputable def liftEquiv :
    ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (ProjectiveTensorProduct p →L[𝕜] F) where
  toFun f := ⟨lift p f.toMultilinearMap,
    (continuous_lift_iff p hp q hq f.toMultilinearMap).mpr f.cont⟩
  invFun g := g.compContinuousMultilinearMap (continuousTprod p hp)
  left_inv f := by
    ext x
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    simp
  right_inv g := by
    apply ContinuousLinearMap.coe_injective
    apply linearMap_ext p
    intro x
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe]
  map_add' f g := by
    apply ContinuousLinearMap.coe_injective
    apply linearMap_ext p
    intro x
    simp
  map_smul' c f := by
    apply ContinuousLinearMap.coe_injective
    apply linearMap_ext p
    intro x
    simp

/-- The continuous lift agrees with its multilinear map on pure tensors. -/
@[simp] theorem liftEquiv_tprod (f : ContinuousMultilinearMap 𝕜 E F) (x : ∀ i, E i) :
    liftEquiv p hp q hq f ⟨⨂ₜ[𝕜] i, x i⟩ = f x := by
  simp [liftEquiv]

/-- The inverse of the continuous tensor-lift equivalence evaluates a linear map on pure
tensors. -/
@[simp] theorem liftEquiv_symm_apply (g : ProjectiveTensorProduct p →L[𝕜] F)
    (x : ∀ i, E i) : (liftEquiv p hp q hq).symm g x = g (tprod p x) := by
  simp [liftEquiv, ContinuousLinearMap.compContinuousMultilinearMap_coe]

end TauCeti.ProjectiveTensorProduct
