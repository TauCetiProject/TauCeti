/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TensorProduct.Associator
public import TauCeti.Topology.VectorBundle.Dual
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# Categorical operations and dual-tensor-hom isomorphism for tensor-product bundles

For finite-rank topological vector bundles over a complete nontrivially normed field `𝕜`, equipped
with the tensor-product bundle structure from `TauCeti.Topology.VectorBundle.TensorProduct.Basic`,
this file constructs the universal property, functoriality, monoidal coherence homeomorphisms, and
the canonical identification `E₁* ⊗ E₂ ≃ E₁ →L E₂`:

* `TauCeti.bundleTensorLift` and `TauCeti.continuous_bundleTensorLift_iff`: the fibrewise universal
  property lifting continuous bilinear bundle maps `E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x` to continuous
  linear maps `E₁ x ⊗[𝕜] E₂ x →L[𝕜] E₃ x`, with no finite-dimensionality assumption on the target
  model fibre `F₃`.
* `TauCeti.bundleTensorMap`, `TauCeti.continuousWithinAt_bundleTensorMap`,
  `TauCeti.continuous_bundleTensorMap`, `TauCeti.bundleTensorCongr`, and
  `TauCeti.bundleTensorCongrHomeomorph`: functoriality on morphisms and bundle homeomorphisms.
* `TauCeti.bundleTensorCommEquiv`, `TauCeti.bundleTensorCommHomeomorph`,
  `TauCeti.bundleTensorAssocEquiv`, and `TauCeti.bundleTensorAssocHomeomorph`: symmetry and
  associativity total-space homeomorphisms.
* `TauCeti.bundleDualTensorHom`, `TauCeti.bundleDualTensorHomEquiv`, and
  `TauCeti.bundleDualTensorHomHomeomorph`: the canonical bundle isomorphism between
  `StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x` and `E₁ x →L[𝕜] E₂ x`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 10.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
-/

public section

noncomputable section

open Bundle FiberBundle Set Topology
open scoped TensorProduct

namespace TauCeti

/-! ### Universal property on bundle homomorphisms -/

section LiftFiber

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

/-- Fibrewise universal property of the tensor product: a family of continuous bilinear maps
`Φ x : E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x` lifts to continuous linear maps `E₁ x ⊗[𝕜] E₂ x →L[𝕜] E₃ x`. -/
def bundleTensorLift (Φ : ∀ x, E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x) (x : B) :
    E₁ x ⊗[𝕜] E₂ x →L[𝕜] E₃ x :=
  let f : E₁ x ⊗[𝕜] E₂ x →ₗ[𝕜] E₃ x := _root_.TensorProduct.lift (Φ x).toLinearMap₁₂
  ⟨f, IsModuleTopology.continuous_of_linearMap f⟩

@[simp]
theorem bundleTensorLift_tmul (Φ : ∀ x, E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x) (x : B)
    (v : E₁ x) (w : E₂ x) :
    bundleTensorLift Φ x (v ⊗ₜ[𝕜] w) = Φ x v w := by
  simp [bundleTensorLift]

end LiftFiber

section LiftBundle

variable {𝕜 B F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₁ E₂ E₃ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]

/-- In the preferred frames at `a`, `bundleTensorLift Φ` corresponds to `Φ` through
`ProjectiveTensor.liftIsometry 𝕜 F₁ F₂ F₃`. The target model fibre `F₃` need not have finite
dimension. -/
theorem bundleTensorLift_inCoordinates (Φ : ∀ x, E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x) (a x : B)
    (hx₁ : x ∈ (trivializationAt F₁ E₁ a).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ a).baseSet)
    (hx₃ : x ∈ (trivializationAt F₃ E₃ a).baseSet) :
    ContinuousLinearMap.inCoordinates (ProjectiveTensor 𝕜 F₁ F₂) (fun y ↦ E₁ y ⊗[𝕜] E₂ y)
      F₃ E₃ a x a x (bundleTensorLift Φ x) =
      ProjectiveTensor.liftIsometry 𝕜 F₁ F₂ F₃
        (ContinuousLinearMap.inCoordinates F₁ E₁ (F₂ →L[𝕜] F₃) (fun y ↦ E₂ y →L[𝕜] E₃ y)
          a x a x (Φ x)) := by
  refine ProjectiveTensor.continuousLinearMap_ext fun v w ↦ ?_
  have hx₁₂ : x ∈ (trivializationAt (ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ E₁ y ⊗[𝕜] E₂ y) a).baseSet := by
    rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₁, hx₂⟩
  rw [ProjectiveTensor.liftIsometry_apply_tmul, inCoordinates_apply_eq₂ hx₁ hx₂ hx₃]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_apply (R := 𝕜) _ hx₁₂,
    tensorProduct_trivializationAt_symm_apply_tmul hx₁ hx₂,
    bundleTensorLift_tmul]
  rfl

/-- Universal property of the tensor-product bundle on continuous Hom-bundle sections:
`bundleTensorLift Φ` is a continuous section of `(E₁ ⊗ E₂) →L E₃` if and only if `Φ` is a
continuous section of `E₁ →L E₂ →L E₃`. The target model fibre `F₃` need not have finite
dimension. -/
theorem continuous_bundleTensorLift_iff (Φ : ∀ x, E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x) :
    Continuous (fun x ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] F₃)
      (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₃ y) x (bundleTensorLift Φ x)) ↔
      Continuous (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (E := fun y ↦ E₁ y →L[𝕜] E₂ y →L[𝕜] E₃ y) x (Φ x)) := by
  simp only [continuous_iff_continuousAt, continuousAt_hom_bundle]
  refine forall_congr' fun a ↦ and_congr_right fun _ ↦ ?_
  let L := ProjectiveTensor.liftIsometry 𝕜 F₁ F₂ F₃
  have hev : (fun x ↦ ContinuousLinearMap.inCoordinates (ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ E₁ y ⊗[𝕜] E₂ y) F₃ E₃ a x a x (bundleTensorLift Φ x)) =ᶠ[𝓝 a]
      (L ∘ fun x ↦
        ContinuousLinearMap.inCoordinates F₁ E₁ (F₂ →L[𝕜] F₃)
          (fun y ↦ E₂ y →L[𝕜] E₃ y) a x a x (Φ x)) := by
    filter_upwards [(trivializationAt F₁ E₁ a).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₁ E₁ a),
      (trivializationAt F₂ E₂ a).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₂ E₂ a),
      (trivializationAt F₃ E₃ a).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F₃ E₃ a)] with x hx₁ hx₂ hx₃
    exact bundleTensorLift_inCoordinates Φ a x hx₁ hx₂ hx₃
  refine ⟨fun h ↦ ?_, fun h ↦ (L.continuous.continuousAt.comp h).congr hev.symm⟩
  exact (L.symm.continuous.continuousAt.comp (h.congr hev)).congr
    (Filter.Eventually.of_forall fun _ ↦ L.symm_apply_apply _)

end LiftBundle

/-! ### Functoriality on morphisms and equivalences -/

section MapFiber

variable {𝕜 B : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
  {E₁ E₁' E₂ E₂' : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₁' x)] [∀ x, Module 𝕜 (E₁' x)] [∀ x, TopologicalSpace (E₁' x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, AddCommGroup (E₂' x)] [∀ x, Module 𝕜 (E₂' x)] [∀ x, TopologicalSpace (E₂' x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₁' x ⊗[𝕜] E₂' x)] [∀ x, IsModuleTopology 𝕜 (E₁' x ⊗[𝕜] E₂' x)]

/-- Fibrewise tensor product of two families of continuous linear maps. -/
def bundleTensorMap (f : ∀ x, E₁ x →L[𝕜] E₁' x) (g : ∀ x, E₂ x →L[𝕜] E₂' x) (x : B) :
    E₁ x ⊗[𝕜] E₂ x →L[𝕜] E₁' x ⊗[𝕜] E₂' x :=
  let m : E₁ x ⊗[𝕜] E₂ x →ₗ[𝕜] E₁' x ⊗[𝕜] E₂' x :=
    _root_.TensorProduct.map (f x).toLinearMap (g x).toLinearMap
  ⟨m, IsModuleTopology.continuous_of_linearMap m⟩

@[simp]
theorem bundleTensorMap_tmul (f : ∀ x, E₁ x →L[𝕜] E₁' x) (g : ∀ x, E₂ x →L[𝕜] E₂' x)
    (x : B) (v : E₁ x) (w : E₂ x) :
    bundleTensorMap f g x (v ⊗ₜ[𝕜] w) = f x v ⊗ₜ[𝕜] g x w := by
  simp [bundleTensorMap]

/-- Fibrewise continuous linear equivalence of tensor products induced by two families of
continuous linear equivalences. -/
def bundleTensorCongr (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x) (x : B) :
    (E₁ x ⊗[𝕜] E₂ x) ≃L[𝕜] (E₁' x ⊗[𝕜] E₂' x) :=
  let eqv : (E₁ x ⊗[𝕜] E₂ x) ≃ₗ[𝕜] (E₁' x ⊗[𝕜] E₂' x) :=
    _root_.TensorProduct.congr (e₁ x).toLinearEquiv (e₂ x).toLinearEquiv
  { eqv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap eqv.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap eqv.symm.toLinearMap }

@[simp]
theorem bundleTensorCongr_toContinuousLinearMap
    (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x) (x : B) :
    (bundleTensorCongr e₁ e₂ x).toContinuousLinearMap =
      bundleTensorMap (fun y ↦ (e₁ y).toContinuousLinearMap)
        (fun y ↦ (e₂ y).toContinuousLinearMap) x := by
  ext u
  induction u using _root_.TensorProduct.inductionOn with
  | tmul v w => simp [bundleTensorCongr, bundleTensorMap]
  | add p q hp hq =>
      simp only [ContinuousLinearEquiv.coe_coe] at hp hq
      simp [hp, hq]

@[simp]
theorem bundleTensorCongr_tmul (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (x : B) (v : E₁ x) (w : E₂ x) :
    bundleTensorCongr e₁ e₂ x (v ⊗ₜ[𝕜] w) = e₁ x v ⊗ₜ[𝕜] e₂ x w := by
  simp [bundleTensorCongr]

@[simp]
theorem bundleTensorCongr_symm (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (x : B) :
    (bundleTensorCongr e₁ e₂ x).symm =
      bundleTensorCongr (fun y ↦ (e₁ y).symm) (fun y ↦ (e₂ y).symm) x := by
  ext u
  refine (bundleTensorCongr e₁ e₂ x).symm_apply_eq.2 ?_
  induction u using _root_.TensorProduct.inductionOn with
  | tmul v w => simp
  | add p q hp hq => rw [map_add, map_add, ← hp, ← hq]

end MapFiber

section MapBundle

variable {𝕜 B M F₁ F₁' F₂ F₂' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] [TopologicalSpace M]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] [FiniteDimensional 𝕜 F₁']
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  [NormedAddCommGroup F₂'] [NormedSpace 𝕜 F₂'] [FiniteDimensional 𝕜 F₂']
  {E₁ E₁' E₂ E₂' : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₁' x)] [∀ x, Module 𝕜 (E₁' x)] [∀ x, TopologicalSpace (E₁' x)]
  [TopologicalSpace (TotalSpace F₁' E₁')] [FiberBundle F₁' E₁'] [VectorBundle 𝕜 F₁' E₁']
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, AddCommGroup (E₂' x)] [∀ x, Module 𝕜 (E₂' x)] [∀ x, TopologicalSpace (E₂' x)]
  [TopologicalSpace (TotalSpace F₂' E₂')] [FiberBundle F₂' E₂'] [VectorBundle 𝕜 F₂' E₂']
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₁' x ⊗[𝕜] E₂' x)] [∀ x, IsModuleTopology 𝕜 (E₁' x ⊗[𝕜] E₂' x)]

/-- In the preferred frames at `a`, `bundleTensorMap f g` is `ProjectiveTensor.mapL` of the
coordinate expressions of `f` and `g`. -/
theorem bundleTensorMap_inCoordinates
    (f : ∀ x, E₁ x →L[𝕜] E₁' x) (g : ∀ x, E₂ x →L[𝕜] E₂' x) (a x : B)
    (hx₁ : x ∈ (trivializationAt F₁ E₁ a).baseSet)
    (hx₁' : x ∈ (trivializationAt F₁' E₁' a).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ a).baseSet)
    (hx₂' : x ∈ (trivializationAt F₂' E₂' a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (ProjectiveTensor 𝕜 F₁ F₂) (fun y ↦ E₁ y ⊗[𝕜] E₂ y)
      (ProjectiveTensor 𝕜 F₁' F₂') (fun y ↦ E₁' y ⊗[𝕜] E₂' y)
      a x a x (bundleTensorMap f g x) =
      ProjectiveTensor.mapL
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₁' E₁' a x a x (f x))
        (ContinuousLinearMap.inCoordinates F₂ E₂ F₂' E₂' a x a x (g x)) := by
  refine ProjectiveTensor.continuousLinearMap_ext fun v w ↦ ?_
  have hx₁₂ : x ∈ (trivializationAt (ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ E₁ y ⊗[𝕜] E₂ y) a).baseSet := by
    rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₁, hx₂⟩
  have hx₁₂' : x ∈ (trivializationAt (ProjectiveTensor 𝕜 F₁' F₂')
      (fun y ↦ E₁' y ⊗[𝕜] E₂' y) a).baseSet := by
    rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₁', hx₂'⟩
  simp only [ProjectiveTensor.mapL_tmul, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_apply (R := 𝕜) _ hx₁₂,
    tensorProduct_trivializationAt_symm_apply_tmul hx₁ hx₂]
  simp [bundleTensorMap_tmul, Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx₁₂',
    tensorProduct_trivializationAt_apply, hx₁, hx₁', hx₂, hx₂']

variable [∀ x, IsTopologicalAddGroup (E₁' x)] [∀ x, ContinuousSMul 𝕜 (E₁' x)]
  [∀ x, IsTopologicalAddGroup (E₂' x)] [∀ x, ContinuousSMul 𝕜 (E₂' x)]

/-- Functoriality of `bundleTensorMap` preserves `ContinuousWithinAt` along a base map `b`. -/
theorem continuousWithinAt_bundleTensorMap {b : M → B}
    {f : ∀ x, E₁ x →L[𝕜] E₁' x} {g : ∀ x, E₂ x →L[𝕜] E₂' x} {s : Set M} {x₀ : M}
    (hf : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁') (E := fun y ↦ E₁ y →L[𝕜] E₁' y) (b m) (f (b m)))
      s x₀)
    (hg : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₂') (E := fun y ↦ E₂ y →L[𝕜] E₂' y) (b m) (g (b m)))
      s x₀) :
    ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁' F₂')
        (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₁' y ⊗[𝕜] E₂' y) (b m)
        (bundleTensorMap f g (b m))) s x₀ := by
  simp only [continuousWithinAt_hom_bundle] at hf hg ⊢
  refine ⟨hf.1, ?_⟩
  have h₁ := mem_baseSet_trivializationAt F₁ E₁ (b x₀)
  have h₁' := mem_baseSet_trivializationAt F₁' E₁' (b x₀)
  have h₂ := mem_baseSet_trivializationAt F₂ E₂ (b x₀)
  have h₂' := mem_baseSet_trivializationAt F₂' E₂' (b x₀)
  have hcomp : ContinuousWithinAt
      (fun m ↦ ProjectiveTensor.mapCLM 𝕜 F₁ F₁' F₂ F₂'
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₁' E₁' (b x₀) (b m) (b x₀) (b m) (f (b m)))
        (ContinuousLinearMap.inCoordinates F₂ E₂ F₂' E₂' (b x₀) (b m) (b x₀) (b m) (g (b m))))
      s x₀ :=
    ((ProjectiveTensor.mapCLM 𝕜 F₁ F₁' F₂ F₂').continuous.continuousAt.comp_continuousWithinAt
      hf.2).clm_apply hg.2
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hf.1.preimage_mem_nhdsWithin <| Filter.inter_mem
        (Filter.inter_mem ((trivializationAt F₁ E₁ (b x₀)).open_baseSet.mem_nhds h₁)
          ((trivializationAt F₁' E₁' (b x₀)).open_baseSet.mem_nhds h₁'))
        (Filter.inter_mem ((trivializationAt F₂ E₂ (b x₀)).open_baseSet.mem_nhds h₂)
          ((trivializationAt F₂' E₂' (b x₀)).open_baseSet.mem_nhds h₂'))] with m hm
    exact (bundleTensorMap_inCoordinates f g (b x₀) (b m) hm.1.1 hm.1.2 hm.2.1 hm.2.2).trans
      (ProjectiveTensor.mapCLM_apply _ _).symm
  · exact (bundleTensorMap_inCoordinates f g (b x₀) (b x₀) h₁ h₁' h₂ h₂').trans
      (ProjectiveTensor.mapCLM_apply _ _).symm

/-- Functoriality of `bundleTensorMap` on globally continuous Hom-bundle sections. -/
theorem continuous_bundleTensorMap
    {f : ∀ x, E₁ x →L[𝕜] E₁' x} {g : ∀ x, E₂ x →L[𝕜] E₂' x}
    (hf : Continuous (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁')
      (E := fun y ↦ E₁ y →L[𝕜] E₁' y) x (f x)))
    (hg : Continuous (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₂')
      (E := fun y ↦ E₂ y →L[𝕜] E₂' y) x (g x))) :
    Continuous (fun x ↦ TotalSpace.mk'
      (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₁' F₂')
      (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₁' y ⊗[𝕜] E₂' y) x (bundleTensorMap f g x)) :=
  continuous_iff_continuousAt.2 fun x ↦ by
    rw [← continuousWithinAt_univ]
    exact continuousWithinAt_bundleTensorMap (b := id)
      hf.continuousAt.continuousWithinAt hg.continuousAt.continuousWithinAt

/-- Homeomorphism of tensor-product total spaces induced by two continuous families of fibrewise
linear equivalences. Continuity of the inverse follows automatically from finite rank. -/
def bundleTensorCongrHomeomorph
    (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (he₁ : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₁' p.proj (e₁ p.proj p.2)))
    (he₂ : Continuous (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂' p.proj (e₂ p.proj p.2))) :
    TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) ≃ₜ
      TotalSpace (ProjectiveTensor 𝕜 F₁' F₂') (fun x ↦ E₁' x ⊗[𝕜] E₂' x) :=
  bundleHomeomorph (bundleTensorCongr e₁ e₂) <|
    ((continuous_hom_bundle_iff (fun x ↦ (bundleTensorCongr e₁ e₂ x).toContinuousLinearMap)).1 <| by
      simpa only [bundleTensorCongr_toContinuousLinearMap] using
        continuous_bundleTensorMap
          ((continuous_hom_bundle_iff (fun x ↦ (e₁ x).toContinuousLinearMap)).2 he₁)
          ((continuous_hom_bundle_iff (fun x ↦ (e₂ x).toContinuousLinearMap)).2 he₂)).congr
      fun _ ↦ rfl

@[simp]
theorem bundleTensorCongrHomeomorph_apply
    (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (he₁ : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₁' p.proj (e₁ p.proj p.2)))
    (he₂ : Continuous (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂' p.proj (e₂ p.proj p.2)))
    (p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    bundleTensorCongrHomeomorph e₁ e₂ he₁ he₂ p =
      ⟨p.proj, bundleTensorCongr e₁ e₂ p.proj p.2⟩ := by
  rw [bundleTensorCongrHomeomorph, bundleHomeomorph_apply]

@[simp]
theorem bundleTensorCongrHomeomorph_symm_apply
    (e₁ : ∀ x, E₁ x ≃L[𝕜] E₁' x) (e₂ : ∀ x, E₂ x ≃L[𝕜] E₂' x)
    (he₁ : Continuous (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₁' p.proj (e₁ p.proj p.2)))
    (he₂ : Continuous (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₂' p.proj (e₂ p.proj p.2)))
    (p : TotalSpace (ProjectiveTensor 𝕜 F₁' F₂') (fun x ↦ E₁' x ⊗[𝕜] E₂' x)) :
    (bundleTensorCongrHomeomorph e₁ e₂ he₁ he₂).symm p =
      ⟨p.proj, (bundleTensorCongr e₁ e₂ p.proj).symm p.2⟩ := by
  rw [bundleTensorCongrHomeomorph, bundleHomeomorph_symm_apply]

end MapBundle

/-! ### Symmetry and associativity bundle homeomorphisms -/

section CommFiber

variable {𝕜 B : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₂ x ⊗[𝕜] E₁ x)] [∀ x, IsModuleTopology 𝕜 (E₂ x ⊗[𝕜] E₁ x)]

/-- Fibrewise symmetry `(E₁ x ⊗[𝕜] E₂ x) ≃L[𝕜] (E₂ x ⊗[𝕜] E₁ x)` under the module topology. -/
def bundleTensorCommEquiv (x : B) : (E₁ x ⊗[𝕜] E₂ x) ≃L[𝕜] (E₂ x ⊗[𝕜] E₁ x) :=
  let eqv := _root_.TensorProduct.comm 𝕜 (E₁ x) (E₂ x)
  { eqv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap eqv.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap eqv.symm.toLinearMap }

@[simp]
theorem bundleTensorCommEquiv_tmul (x : B) (v : E₁ x) (w : E₂ x) :
    bundleTensorCommEquiv (E₁ := E₁) (E₂ := E₂) x (v ⊗ₜ[𝕜] w) = w ⊗ₜ[𝕜] v := by
  simp [bundleTensorCommEquiv]

@[simp]
theorem bundleTensorCommEquiv_symm (x : B) :
    (bundleTensorCommEquiv (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂) x).symm =
      bundleTensorCommEquiv (𝕜 := 𝕜) (E₁ := E₂) (E₂ := E₁) x := by
  ext u
  refine (bundleTensorCommEquiv x).symm_apply_eq.2 ?_
  induction u using _root_.TensorProduct.inductionOn with
  | tmul v w => simp
  | add p q hp hq => rw [map_add, map_add, ← hp, ← hq]

end CommFiber

section CommBundle

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₂ x ⊗[𝕜] E₁ x)] [∀ x, IsModuleTopology 𝕜 (E₂ x ⊗[𝕜] E₁ x)]

/-- In the preferred frames at `a`, `bundleTensorCommEquiv` is the constant symmetry
`(ProjectiveTensor.comm 𝕜 F₁ F₂).toLinearIsometry.toContinuousLinearMap`. -/
theorem bundleTensorCommEquiv_inCoordinates (a x : B)
    (hx₁ : x ∈ (trivializationAt F₁ E₁ a).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (ProjectiveTensor 𝕜 F₁ F₂) (fun y ↦ E₁ y ⊗[𝕜] E₂ y)
      (ProjectiveTensor 𝕜 F₂ F₁) (fun y ↦ E₂ y ⊗[𝕜] E₁ y)
      a x a x (bundleTensorCommEquiv x).toContinuousLinearMap =
      (ProjectiveTensor.comm 𝕜 F₁ F₂).toLinearIsometry.toContinuousLinearMap := by
  refine ProjectiveTensor.continuousLinearMap_ext fun v w ↦ ?_
  have hx₁₂ : x ∈ (trivializationAt (ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ E₁ y ⊗[𝕜] E₂ y) a).baseSet := by
    rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₁, hx₂⟩
  have hx₂₁ : x ∈ (trivializationAt (ProjectiveTensor 𝕜 F₂ F₁)
      (fun y ↦ E₂ y ⊗[𝕜] E₁ y) a).baseSet := by
    rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₂, hx₁⟩
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    ProjectiveTensor.comm_tmul, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_apply (R := 𝕜) _ hx₁₂,
    tensorProduct_trivializationAt_symm_apply_tmul hx₁ hx₂]
  simp [ContinuousLinearEquiv.coe_coe, bundleTensorCommEquiv_tmul,
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx₂₁,
    tensorProduct_trivializationAt_apply, Trivialization.linearMapAt_symm _ hx₁,
    Trivialization.linearMapAt_symm _ hx₂]

/-- `bundleTensorCommEquiv` defines a continuous section of the Hom bundle
`(E₁ ⊗ E₂) →L (E₂ ⊗ E₁)`. -/
theorem continuous_bundleTensorComm :
    Continuous (fun x ↦ TotalSpace.mk'
      (ProjectiveTensor 𝕜 F₁ F₂ →L[𝕜] ProjectiveTensor 𝕜 F₂ F₁)
      (E := fun y ↦ E₁ y ⊗[𝕜] E₂ y →L[𝕜] E₂ y ⊗[𝕜] E₁ y)
      x (bundleTensorCommEquiv x).toContinuousLinearMap) := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  rw [continuousAt_hom_bundle]
  let c := (ProjectiveTensor.comm 𝕜 F₁ F₂).toLinearIsometry.toContinuousLinearMap
  refine ⟨continuousAt_id, (continuous_const (y := c)).continuousAt.congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F₁ E₁ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₁ E₁ a),
    (trivializationAt F₂ E₂ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₂ E₂ a)] with x hx₁ hx₂
  exact bundleTensorCommEquiv_inCoordinates a x hx₁ hx₂

variable (F₁ E₁ F₂ E₂) in
/-- Canonical symmetry homeomorphism between the total spaces of `E₁ ⊗ E₂` and `E₂ ⊗ E₁`. -/
def bundleTensorCommHomeomorph :
    TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) ≃ₜ
      TotalSpace (ProjectiveTensor 𝕜 F₂ F₁) (fun x ↦ E₂ x ⊗[𝕜] E₁ x) :=
  bundleHomeomorph bundleTensorCommEquiv <|
    ((continuous_hom_bundle_iff (fun x ↦ (bundleTensorCommEquiv x).toContinuousLinearMap)).1
      continuous_bundleTensorComm).congr fun _ ↦ rfl

@[simp]
theorem bundleTensorCommHomeomorph_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    bundleTensorCommHomeomorph F₁ E₁ F₂ E₂ p = ⟨p.proj, bundleTensorCommEquiv p.proj p.2⟩ := by
  rw [bundleTensorCommHomeomorph, bundleHomeomorph_apply]

@[simp]
theorem bundleTensorCommHomeomorph_symm_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 F₂ F₁) (fun x ↦ E₂ x ⊗[𝕜] E₁ x)) :
    (bundleTensorCommHomeomorph F₁ E₁ F₂ E₂).symm p =
      ⟨p.proj, (bundleTensorCommEquiv p.proj).symm p.2⟩ := by
  rw [bundleTensorCommHomeomorph, bundleHomeomorph_symm_apply]

end CommBundle

section AssocFiber

variable {𝕜 B : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
  {E₁ E₂ E₃ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [∀ x, TopologicalSpace ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)]
  [∀ x, IsModuleTopology 𝕜 ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))]
  [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))]

/-- Fibrewise associativity `((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) ≃L[𝕜] (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))`
under the module topology. -/
def bundleTensorAssocEquiv (x : B) :
    ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) ≃L[𝕜] (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
  let eqv := _root_.TensorProduct.assoc 𝕜 (E₁ x) (E₂ x) (E₃ x)
  { eqv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap eqv.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap eqv.symm.toLinearMap }

@[simp]
theorem bundleTensorAssocEquiv_tmul (x : B) (u : E₁ x) (v : E₂ x) (w : E₃ x) :
    bundleTensorAssocEquiv (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) x ((u ⊗ₜ[𝕜] v) ⊗ₜ[𝕜] w) =
      u ⊗ₜ[𝕜] (v ⊗ₜ[𝕜] w) := by
  simp [bundleTensorAssocEquiv]

@[simp]
theorem bundleTensorAssocEquiv_symm_tmul (x : B) (u : E₁ x) (v : E₂ x) (w : E₃ x) :
    (bundleTensorAssocEquiv (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) x).symm (u ⊗ₜ[𝕜] (v ⊗ₜ[𝕜] w)) =
      (u ⊗ₜ[𝕜] v) ⊗ₜ[𝕜] w :=
  (bundleTensorAssocEquiv x).symm_apply_eq.2 (bundleTensorAssocEquiv_tmul x u v w).symm

end AssocFiber

section AssocBundle

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [FiniteDimensional 𝕜 F₃]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)] [∀ x, TopologicalSpace (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ x, TopologicalSpace (E₂ x ⊗[𝕜] E₃ x)] [∀ x, IsModuleTopology 𝕜 (E₂ x ⊗[𝕜] E₃ x)]
  [∀ x, TopologicalSpace ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)]
  [∀ x, IsModuleTopology 𝕜 ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))]
  [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))]

/-- In the preferred frames at `a`, `bundleTensorAssocEquiv` is the constant associativity isometry
`(ProjectiveTensor.assoc 𝕜 F₁ F₂ F₃).toLinearIsometry.toContinuousLinearMap`. -/
theorem bundleTensorAssocEquiv_inCoordinates (a x : B)
    (hx₁ : x ∈ (trivializationAt F₁ E₁ a).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ a).baseSet)
    (hx₃ : x ∈ (trivializationAt F₃ E₃ a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃)
      (fun y ↦ (E₁ y ⊗[𝕜] E₂ y) ⊗[𝕜] E₃ y)
      (ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
      (fun y ↦ E₁ y ⊗[𝕜] (E₂ y ⊗[𝕜] E₃ y))
      a x a x (bundleTensorAssocEquiv x).toContinuousLinearMap =
      (ProjectiveTensor.assoc 𝕜 F₁ F₂ F₃).toLinearIsometry.toContinuousLinearMap := by
  refine ProjectiveTensor.continuousLinearMap_ext fun uv w ↦ ?_
  rcases uv with ⟨uv⟩
  induction uv using _root_.TensorProduct.inductionOn with
  | tmul u v =>
      have hx₁₂ : x ∈ (trivializationAt (ProjectiveTensor 𝕜 F₁ F₂)
          (fun y ↦ E₁ y ⊗[𝕜] E₂ y) a).baseSet := by
        rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₁, hx₂⟩
      have hx₂₃ : x ∈ (trivializationAt (ProjectiveTensor 𝕜 F₂ F₃)
          (fun y ↦ E₂ y ⊗[𝕜] E₃ y) a).baseSet := by
        rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₂, hx₃⟩
      have hx_left : x ∈ (trivializationAt
          (ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃)
          (fun y ↦ (E₁ y ⊗[𝕜] E₂ y) ⊗[𝕜] E₃ y) a).baseSet := by
        rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₁₂, hx₃⟩
      have hx_right : x ∈ (trivializationAt
          (ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
          (fun y ↦ E₁ y ⊗[𝕜] (E₂ y ⊗[𝕜] E₃ y)) a).baseSet := by
        rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx₁, hx₂₃⟩
      simp only [LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, ProjectiveTensor.assoc_tmul,
        ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
      rw [Trivialization.symmL_apply _ hx_left,
        tensorProduct_trivializationAt_symm_apply_tmul hx₁₂ hx₃,
        tensorProduct_trivializationAt_symm_apply_tmul hx₁ hx₂]
      simp [ContinuousLinearEquiv.coe_coe, bundleTensorAssocEquiv_tmul,
        Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hx_right,
        tensorProduct_trivializationAt_apply, Trivialization.linearMapAt_def_of_mem _ hx₂₃,
        Trivialization.linearMapAt_symm _ hx₁, Trivialization.linearMapAt_symm _ hx₂,
        Trivialization.linearMapAt_symm _ hx₃]
  | add p q hp hq =>
      have hsplit : (⟨(⟨p + q⟩ : ProjectiveTensor 𝕜 F₁ F₂) ⊗ₜ[𝕜] w⟩ :
          ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃) =
          ⟨(⟨p⟩ : ProjectiveTensor 𝕜 F₁ F₂) ⊗ₜ[𝕜] w⟩ +
            ⟨(⟨q⟩ : ProjectiveTensor 𝕜 F₁ F₂) ⊗ₜ[𝕜] w⟩ := by
        rw [ProjectiveTensor.mk_add, TensorProduct.add_tmul, ProjectiveTensor.mk_add]
      rw [hsplit, map_add, map_add, hp, hq]

/-- `bundleTensorAssocEquiv` defines a continuous section of the Hom bundle
`((E₁ ⊗ E₂) ⊗ E₃) →L (E₁ ⊗ (E₂ ⊗ E₃))`. -/
theorem continuous_bundleTensorAssoc :
    Continuous (fun x ↦ TotalSpace.mk'
      (ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃ →L[𝕜]
        ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
      (E := fun y ↦ ((E₁ y ⊗[𝕜] E₂ y) ⊗[𝕜] E₃ y) →L[𝕜] (E₁ y ⊗[𝕜] (E₂ y ⊗[𝕜] E₃ y)))
      x (bundleTensorAssocEquiv x).toContinuousLinearMap) := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  rw [continuousAt_hom_bundle]
  let c := (ProjectiveTensor.assoc 𝕜 F₁ F₂ F₃).toLinearIsometry.toContinuousLinearMap
  refine ⟨continuousAt_id, (continuous_const (y := c)).continuousAt.congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F₁ E₁ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₁ E₁ a),
    (trivializationAt F₂ E₂ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₂ E₂ a),
    (trivializationAt F₃ E₃ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₃ E₃ a)] with x hx₁ hx₂ hx₃
  exact bundleTensorAssocEquiv_inCoordinates a x hx₁ hx₂ hx₃

variable (F₁ E₁ F₂ E₂ F₃ E₃) in
/-- Canonical associativity homeomorphism between the total spaces of `(E₁ ⊗ E₂) ⊗ E₃` and
`E₁ ⊗ (E₂ ⊗ E₃)`. -/
def bundleTensorAssocHomeomorph :
    TotalSpace (ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃)
        (fun x ↦ (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) ≃ₜ
      TotalSpace (ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
        (fun x ↦ E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
  bundleHomeomorph bundleTensorAssocEquiv <|
    ((continuous_hom_bundle_iff (fun x ↦ (bundleTensorAssocEquiv x).toContinuousLinearMap)).1
      continuous_bundleTensorAssoc).congr fun _ ↦ rfl

@[simp]
theorem bundleTensorAssocHomeomorph_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 (ProjectiveTensor 𝕜 F₁ F₂) F₃)
      (fun x ↦ (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)) :
    bundleTensorAssocHomeomorph F₁ E₁ F₂ E₂ F₃ E₃ p =
      ⟨p.proj, bundleTensorAssocEquiv p.proj p.2⟩ := by
  rw [bundleTensorAssocHomeomorph, bundleHomeomorph_apply]

@[simp]
theorem bundleTensorAssocHomeomorph_symm_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 F₁ (ProjectiveTensor 𝕜 F₂ F₃))
      (fun x ↦ E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x))) :
    (bundleTensorAssocHomeomorph F₁ E₁ F₂ E₂ F₃ E₃).symm p =
      ⟨p.proj, (bundleTensorAssocEquiv p.proj).symm p.2⟩ := by
  rw [bundleTensorAssocHomeomorph, bundleHomeomorph_symm_apply]

end AssocBundle

/-! ### Canonical isomorphism `E₁* ⊗ E₂ ≃ E₁ →L E₂` -/

section DualTensorHomFiber

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]
  [∀ x, IsModuleTopology 𝕜 (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]

/-- Canonical fibrewise contraction `StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x →L[𝕜] (E₁ x →L[𝕜] E₂ x)`,
sending `φ ⊗ₜ w` to `v ↦ φ v • w`. -/
def bundleDualTensorHom (x : B) :
    StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x →L[𝕜] (E₁ x →L[𝕜] E₂ x) :=
  let f : StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x →ₗ[𝕜] (E₁ x →L[𝕜] E₂ x) :=
    _root_.TensorProduct.lift
      { toFun φ :=
          { toFun w := φ.smulRight w
            map_add' u v := by ext; simp
            map_smul' c v := by
              ext y
              simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply]
              exact smul_comm _ _ _ }
        map_add' φ ψ := by ext w v; simp [add_smul]
        map_smul' c φ := by ext w v; simp [mul_smul] }
  ⟨f, IsModuleTopology.continuous_of_linearMap f⟩

@[simp]
theorem bundleDualTensorHom_tmul (x : B) (φ : StrongDual 𝕜 (E₁ x)) (w : E₂ x) :
    bundleDualTensorHom (E₁ := E₁) (E₂ := E₂) x (φ ⊗ₜ[𝕜] w) = φ.smulRight w := by
  simp [bundleDualTensorHom]

theorem bundleDualTensorHom_tmul_apply (x : B) (φ : StrongDual 𝕜 (E₁ x)) (w : E₂ x)
    (v : E₁ x) :
    bundleDualTensorHom (E₁ := E₁) (E₂ := E₂) x (φ ⊗ₜ[𝕜] w) v = φ v • w := by
  simp

end DualTensorHomFiber

section DualTensorHomBundle

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, TopologicalSpace (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]
  [∀ x, IsModuleTopology 𝕜 (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)]

/-- In the preferred frames at `a`, `bundleDualTensorHom` is the constant operator
`ProjectiveTensor.toOperator 𝕜 F₁ F₂`. -/
theorem bundleDualTensorHom_inCoordinates (a x : B)
    (hx₁ : x ∈ (trivializationAt F₁ E₁ a).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ a).baseSet) :
    ContinuousLinearMap.inCoordinates
      (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
      (fun y ↦ StrongDual 𝕜 (E₁ y) ⊗[𝕜] E₂ y)
      (F₁ →L[𝕜] F₂) (fun y ↦ E₁ y →L[𝕜] E₂ y)
      a x a x (bundleDualTensorHom x) = ProjectiveTensor.toOperator 𝕜 F₁ F₂ := by
  have hx_dual : x ∈ (trivializationAt (StrongDual 𝕜 F₁)
      (fun y ↦ StrongDual 𝕜 (E₁ y)) a).baseSet := by
    simpa [hom_trivializationAt_baseSet, Trivial.eq_trivialization] using hx₁
  have hx_tp : x ∈ (trivializationAt (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
      (fun y ↦ StrongDual 𝕜 (E₁ y) ⊗[𝕜] E₂ y) a).baseSet := by
    rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx_dual, hx₂⟩
  have hx_hom : x ∈ (trivializationAt (F₁ →L[𝕜] F₂)
      (fun y ↦ E₁ y →L[𝕜] E₂ y) a).baseSet := by
    rw [hom_trivializationAt_baseSet]; exact ⟨hx₁, hx₂⟩
  rw [ContinuousLinearMap.inCoordinates_eq hx_tp hx_hom]
  refine ProjectiveTensor.continuousLinearMap_ext fun φ w ↦ ?_
  ext v
  simp only [ProjectiveTensor.toOperator_tmul, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_symm_apply,
    Trivialization.continuousLinearEquivAt_apply]
  rw [tensorProduct_trivializationAt_symm_apply_tmul hx_dual hx₂,
    hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates_eq hx₁ hx₂]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_symm_apply, bundleDualTensorHom_tmul_apply, map_smul,
    dual_trivializationAt_symm_apply E₁ a hx₁ φ v,
    Trivialization.continuousLinearEquivAt_apply, (trivializationAt F₂ E₂ a).apply_mk_symm hx₂]

/-- `bundleDualTensorHom` induces a continuous map on total spaces from `StrongDual 𝕜 E₁ ⊗ E₂`
to `E₁ →L E₂`. -/
theorem continuous_bundleDualTensorHom :
    Continuous (fun p : TotalSpace (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
        (fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) ↦
      TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x)
        p.proj (bundleDualTensorHom p.proj p.2)) := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  refine (continuous_hom_bundle_iff
    (F₁ := ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂) (F₂ := F₁ →L[𝕜] F₂)
    (E₁ := fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) (E₂ := fun x ↦ E₁ x →L[𝕜] E₂ x)
    (bundleDualTensorHom (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂))).1 ?_
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id,
    (continuous_const
      (y := ProjectiveTensor.toOperator 𝕜 F₁ F₂)).continuousAt.congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F₁ E₁ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₁ E₁ a),
    (trivializationAt F₂ E₂ a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₂ E₂ a)] with x hx₁ hx₂
  exact bundleDualTensorHom_inCoordinates a x hx₁ hx₂

variable (𝕜 F₁ F₂) in
/-- Fibrewise continuous linear equivalence
`(StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) ≃L[𝕜] (E₁ x →L[𝕜] E₂ x)` for finite-rank vector bundles. -/
def bundleDualTensorHomEquiv (x : B) :
    (StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) ≃L[𝕜] (E₁ x →L[𝕜] E₂ x) :=
  have hinv : (bundleDualTensorHom (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂) x).IsInvertible := by
    have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
    have hx₂ := mem_baseSet_trivializationAt F₂ E₂ x
    have hx_dual : x ∈ (trivializationAt (StrongDual 𝕜 F₁)
        (fun y ↦ StrongDual 𝕜 (E₁ y)) x).baseSet := by
      simpa [hom_trivializationAt_baseSet, Trivial.eq_trivialization] using hx₁
    have hx_tp : x ∈ (trivializationAt (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
        (fun y ↦ StrongDual 𝕜 (E₁ y) ⊗[𝕜] E₂ y) x).baseSet := by
      rw [tensorProduct_trivializationAt_baseSet]; exact ⟨hx_dual, hx₂⟩
    have hx_hom : x ∈ (trivializationAt (F₁ →L[𝕜] F₂)
        (fun y ↦ E₁ y →L[𝕜] E₂ y) x).baseSet := by
      rw [hom_trivializationAt_baseSet]; exact ⟨hx₁, hx₂⟩
    refine (ContinuousLinearMap.isInvertible_inCoordinates_iff hx_tp hx_hom).1 ?_
    rw [bundleDualTensorHom_inCoordinates x x hx₁ hx₂,
      ← ProjectiveTensor.toOperatorEquiv_toContinuousLinearMap]
    exact ContinuousLinearMap.isInvertible_equiv
  ContinuousLinearEquiv.equivOfInverse
    (bundleDualTensorHom x) (bundleDualTensorHom x).inverse
    (fun _ ↦ hinv.inverse_apply_eq.2 rfl)
    (fun _ ↦ (hinv.inverse_apply_eq.1 rfl).symm)

@[simp]
theorem bundleDualTensorHomEquiv_toContinuousLinearMap (x : B) :
    (bundleDualTensorHomEquiv 𝕜 F₁ F₂ (E₁ := E₁) (E₂ := E₂) x).toContinuousLinearMap =
      bundleDualTensorHom (𝕜 := 𝕜) x :=
  (rfl)

@[simp]
theorem bundleDualTensorHomEquiv_symm_toContinuousLinearMap (x : B) :
    (bundleDualTensorHomEquiv 𝕜 F₁ F₂ (E₁ := E₁) (E₂ := E₂) x).symm.toContinuousLinearMap =
      (bundleDualTensorHom (𝕜 := 𝕜) x).inverse :=
  (rfl)

@[simp]
theorem bundleDualTensorHomEquiv_tmul (x : B) (φ : StrongDual 𝕜 (E₁ x)) (w : E₂ x) :
    bundleDualTensorHomEquiv 𝕜 F₁ F₂ (E₁ := E₁) (E₂ := E₂) x (φ ⊗ₜ[𝕜] w) = φ.smulRight w :=
  bundleDualTensorHom_tmul x φ w

@[simp]
theorem bundleDualTensorHomEquiv_symm_smulRight (x : B) (φ : StrongDual 𝕜 (E₁ x)) (w : E₂ x) :
    (bundleDualTensorHomEquiv 𝕜 F₁ F₂ (E₁ := E₁) (E₂ := E₂) x).symm (φ.smulRight w) =
      φ ⊗ₜ[𝕜] w :=
  (bundleDualTensorHomEquiv 𝕜 F₁ F₂ x).symm_apply_eq.2
    (bundleDualTensorHomEquiv_tmul x φ w).symm

variable (F₁ E₁ F₂ E₂) in
/-- Canonical homeomorphism between the total space of `StrongDual 𝕜 E₁ ⊗ E₂` and the total space
of the Hom bundle `E₁ →L E₂`. -/
def bundleDualTensorHomHomeomorph :
    TotalSpace (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
        (fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x) ≃ₜ
      TotalSpace (F₁ →L[𝕜] F₂) (fun x ↦ E₁ x →L[𝕜] E₂ x) :=
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  bundleHomeomorph (bundleDualTensorHomEquiv 𝕜 F₁ F₂)
    (continuous_bundleDualTensorHom.congr fun _ ↦ rfl)

@[simp]
theorem bundleDualTensorHomHomeomorph_apply
    (p : TotalSpace (ProjectiveTensor 𝕜 (StrongDual 𝕜 F₁) F₂)
      (fun x ↦ StrongDual 𝕜 (E₁ x) ⊗[𝕜] E₂ x)) :
    bundleDualTensorHomHomeomorph F₁ E₁ F₂ E₂ p =
      ⟨p.proj, bundleDualTensorHomEquiv 𝕜 F₁ F₂ p.proj p.2⟩ := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  rw [bundleDualTensorHomHomeomorph, bundleHomeomorph_apply]

@[simp]
theorem bundleDualTensorHomHomeomorph_symm_apply
    (p : TotalSpace (F₁ →L[𝕜] F₂) (fun x ↦ E₁ x →L[𝕜] E₂ x)) :
    (bundleDualTensorHomHomeomorph F₁ E₁ F₂ E₂).symm p =
      ⟨p.proj, (bundleDualTensorHomEquiv 𝕜 F₁ F₂ p.proj).symm p.2⟩ := by
  have : ∀ x, ContinuousAdd (E₁ x →L[𝕜] E₂ x) := fun _ ↦ inferInstance
  rw [bundleDualTensorHomHomeomorph, bundleHomeomorph_symm_apply]

end DualTensorHomBundle

end TauCeti

end
