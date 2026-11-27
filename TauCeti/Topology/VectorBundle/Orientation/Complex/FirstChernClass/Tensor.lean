/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
public import TauCeti.Topology.VectorBundle.TensorProduct.Line
public import TauCeti.Topology.VectorBundle.TensorProduct.Pullback

/-!
# Naturality of the first Chern class of a tensor product

Let `E₁` and `E₂` be complex vector bundles over `B`, with tensor product `E₁ ⊗ E₂`. This file
records how `c₁(E₁ ⊗ E₂)` behaves under the bundle maps that compare a tensor product of line
bundles with its universal value on a product of classifying spaces.

* It is natural under pairs of bundle maps covering a continuous map `g : B' → B`: for fibrewise
  complex-linear isomorphisms `E₁' ≃ g^*E₁` and `E₂' ≃ g^*E₂`, continuous on total spaces,
  `c₁(E₁' ⊗ E₂') = g^* c₁(E₁ ⊗ E₂)`
  (`TauCeti.firstChernClass_tensorProduct_eq_singularCohomologyMap_of_fiberwise`); in particular
  `c₁(g^*E₁ ⊗ g^*E₂) = g^* c₁(E₁ ⊗ E₂)` (`TauCeti.firstChernClass_tensorProduct_pullback`).
* It is symmetric, `c₁(E₁ ⊗ E₂) = c₁(E₂ ⊗ E₁)` (`TauCeti.firstChernClass_tensorProduct_comm`).
* Tensoring with a line bundle `L` that has a nowhere-zero continuous section does not change it:
  `c₁(E ⊗ L) = c₁(E)` (`TauCeti.firstChernClass_tensorProduct_eq_of_forall_ne_zero`) and
  `c₁(L ⊗ E) = c₁(E)` (`TauCeti.firstChernClass_tensorProduct_eq_of_forall_ne_zero_left`), through
  the isomorphism `v ↦ v ⊗ s b` (`TauCeti.tensorEquivOfNeZero`).

The tensor fibres carry the `ℂ`-module topology, as in
`TauCeti.Topology.VectorBundle.TensorProduct.Basic`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (naturality of Chern classes).
* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer (1982), §20 (the first Chern class of a tensor product of line bundles).
-/

public section

noncomputable section

open Bundle Module
open scoped TensorProduct

namespace TauCeti

variable {B : Type} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  {E₁ : B → Type} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁]
  [VectorBundle ℂ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  {E₂ : B → Type} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂]
  [VectorBundle ℂ F₂ E₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[ℂ] E₂ x)] [∀ x, IsModuleTopology ℂ (E₁ x ⊗[ℂ] E₂ x)]

section Naturality

variable {B' : Type} [TopologicalSpace B']
  {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℂ F₁'] [FiniteDimensional ℂ F₁']
  {E₁' : B' → Type} [∀ y, AddCommGroup (E₁' y)] [∀ y, Module ℂ (E₁' y)]
  [∀ y, TopologicalSpace (E₁' y)] [TopologicalSpace (TotalSpace F₁' E₁')] [FiberBundle F₁' E₁']
  [VectorBundle ℂ F₁' E₁']
  {F₂' : Type*} [NormedAddCommGroup F₂'] [NormedSpace ℂ F₂'] [FiniteDimensional ℂ F₂']
  {E₂' : B' → Type} [∀ y, AddCommGroup (E₂' y)] [∀ y, Module ℂ (E₂' y)]
  [∀ y, TopologicalSpace (E₂' y)] [TopologicalSpace (TotalSpace F₂' E₂')] [FiberBundle F₂' E₂']
  [VectorBundle ℂ F₂' E₂']
  [∀ y, TopologicalSpace (E₁' y ⊗[ℂ] E₂' y)] [∀ y, IsModuleTopology ℂ (E₁' y ⊗[ℂ] E₂' y)]

/-- **Naturality of `c₁` of a tensor product under pairs of bundle maps.** For fibrewise
complex-linear isomorphisms `φ₁ y : E₁' y ≃ E₁ (g y)` and `φ₂ y : E₂' y ≃ E₂ (g y)` over a
continuous map `g : B' → B`, continuous on total spaces,
`c₁(E₁' ⊗ E₂') = g^* c₁(E₁ ⊗ E₂)`. -/
theorem firstChernClass_tensorProduct_eq_singularCohomologyMap_of_fiberwise {g : C(B', B)}
    {φ₁ : ∀ y, E₁' y ≃L[ℂ] E₁ (g y)} {φ₂ : ∀ y, E₂' y ≃L[ℂ] E₂ (g y)}
    (hφ₁ : Continuous fun p : TotalSpace F₁' E₁' ↦ TotalSpace.mk' F₁ (g p.proj) (φ₁ p.proj p.snd))
    (hφ₂ : Continuous fun p : TotalSpace F₂' E₂' ↦ TotalSpace.mk' F₂ (g p.proj) (φ₂ p.proj p.snd)) :
    firstChernClass (ProjectiveTensor ℂ F₁' F₂') (fun y ↦ E₁' y ⊗[ℂ] E₂' y) =
      TopCat.singularCohomologyMap (TopCat.ofHom g) 2
        (firstChernClass (ProjectiveTensor ℂ F₁ F₂) (fun x ↦ E₁ x ⊗[ℂ] E₂ x)) :=
  firstChernClass_eq_singularCohomologyMap_of_fiberwise
    (φ := fun y ↦ (_root_.TensorProduct.congr (φ₁ y).toLinearEquiv
      (φ₂ y).toLinearEquiv).toContinuousLinearEquivOfIsModuleTopology)
    ((continuous_tensorProduct_map_covering (φ₁ := fun y ↦ (φ₁ y : E₁' y →L[ℂ] E₁ (g y)))
      (φ₂ := fun y ↦ (φ₂ y : E₂' y →L[ℂ] E₂ (g y))) hφ₁ hφ₂).congr fun p ↦ by
      rw [LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
        ← LinearEquiv.coe_toLinearMap, _root_.TensorProduct.toLinearMap_congr]
      -- The linear maps underlying `φᵢ` as continuous linear maps and as linear equivalences
      -- agree as functions.
      refine congrArg (TotalSpace.mk' _ (g p.proj))
        (LinearMap.congr_fun (congrArg₂ _root_.TensorProduct.map ?_ ?_) p.snd) <;>
      exact LinearMap.coe_injective (by simp))

/-- **Naturality of `c₁` of a tensor product under pullback**: for a continuous map
`g : B' → B`, `c₁(g^*E₁ ⊗ g^*E₂) = g^* c₁(E₁ ⊗ E₂)`. -/
theorem firstChernClass_tensorProduct_pullback (g : C(B', B))
    [∀ y, TopologicalSpace ((⇑g *ᵖ E₁) y ⊗[ℂ] (⇑g *ᵖ E₂) y)]
    [∀ y, IsModuleTopology ℂ ((⇑g *ᵖ E₁) y ⊗[ℂ] (⇑g *ᵖ E₂) y)] :
    firstChernClass (ProjectiveTensor ℂ F₁ F₂) (fun y ↦ (⇑g *ᵖ E₁) y ⊗[ℂ] (⇑g *ᵖ E₂) y) =
      TopCat.singularCohomologyMap (TopCat.ofHom g) 2
        (firstChernClass (ProjectiveTensor ℂ F₁ F₂) (fun x ↦ E₁ x ⊗[ℂ] E₂ x)) :=
  firstChernClass_tensorProduct_eq_singularCohomologyMap_of_fiberwise
    (φ₁ := fun _ ↦ ContinuousLinearEquiv.refl ℂ _) (φ₂ := fun _ ↦ ContinuousLinearEquiv.refl ℂ _)
    (Pullback.continuous_lift F₁ E₁ g) (Pullback.continuous_lift F₂ E₂ g)

end Naturality

variable [∀ x, TopologicalSpace (E₂ x ⊗[ℂ] E₁ x)] [∀ x, IsModuleTopology ℂ (E₂ x ⊗[ℂ] E₁ x)] in
/-- **`c₁` of a tensor product is symmetric**: `c₁(E₁ ⊗ E₂) = c₁(E₂ ⊗ E₁)`, through the fibrewise
symmetry `v ⊗ w ↦ w ⊗ v`. -/
theorem firstChernClass_tensorProduct_comm :
    firstChernClass (ProjectiveTensor ℂ F₁ F₂) (fun x ↦ E₁ x ⊗[ℂ] E₂ x) =
      firstChernClass (ProjectiveTensor ℂ F₂ F₁) (fun x ↦ E₂ x ⊗[ℂ] E₁ x) :=
  firstChernClass_eq_of_fiberwise (φ := bundleTensorCommEquiv)
    ((bundleTensorCommHomeomorph F₁ E₁ F₂ E₂).continuous.congr
      (bundleTensorCommHomeomorph_apply (F₁ := F₁) (F₂ := F₂)))

/-- **A line with a nowhere-zero section does not change `c₁`**: if the line bundle `E₂` has a
continuous section `s` with no zeros, then `c₁(E₁ ⊗ E₂) = c₁(E₁)`, through the isomorphism
`v ↦ v ⊗ s b`. -/
theorem firstChernClass_tensorProduct_eq_of_forall_ne_zero (hF₂ : finrank ℂ F₂ = 1)
    {s : ∀ x, E₂ x} (hsc : Continuous fun x ↦ TotalSpace.mk' F₂ x (s x)) (hs : ∀ x, s x ≠ 0) :
    firstChernClass (ProjectiveTensor ℂ F₁ F₂) (fun x ↦ E₁ x ⊗[ℂ] E₂ x) = firstChernClass F₁ E₁ :=
  (firstChernClass_eq_of_fiberwise (continuous_tensorEquivOfNeZero hF₂ hs hsc)).symm

variable [∀ x, TopologicalSpace (E₂ x ⊗[ℂ] E₁ x)] [∀ x, IsModuleTopology ℂ (E₂ x ⊗[ℂ] E₁ x)] in
/-- **A line with a nowhere-zero section does not change `c₁`, on the left**: if the line bundle
`E₁` has a continuous section `s` with no zeros, then `c₁(E₁ ⊗ E₂) = c₁(E₂)`. -/
theorem firstChernClass_tensorProduct_eq_of_forall_ne_zero_left (hF₁ : finrank ℂ F₁ = 1)
    {s : ∀ x, E₁ x} (hsc : Continuous fun x ↦ TotalSpace.mk' F₁ x (s x)) (hs : ∀ x, s x ≠ 0) :
    firstChernClass (ProjectiveTensor ℂ F₁ F₂) (fun x ↦ E₁ x ⊗[ℂ] E₂ x) = firstChernClass F₂ E₂ :=
  firstChernClass_tensorProduct_comm.trans
    (firstChernClass_tensorProduct_eq_of_forall_ne_zero hF₁ hsc hs)

end TauCeti
