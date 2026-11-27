/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.TensorProduct.Operations
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Tensor products of maps of vector bundles covering a base map

Let `E₁` and `E₂` be finite-rank vector bundles over `B`, and let `g : B' → B` be continuous. The
fibres of the tensor product `g^*E₁ ⊗ g^*E₂` over `B'` are those of `E₁ ⊗ E₂` over the image
points, and in the pulled-back charts the two bundles have the same coordinates
(`TensorProduct.inCoordinates_pullback`). So the fibrewise identity, covering `g`, is continuous
on total spaces (`TauCeti.continuous_tensorProduct_pullback`).

More generally, let `φ₁ y : E₁' y →L E₁ (g y)` and `φ₂ y : E₂' y →L E₂ (g y)` be fibrewise linear
maps of finite-rank bundles over `B'` into `E₁` and `E₂`, covering `g` and continuous on total
spaces. Then their fibrewise tensor product `φ₁ y ⊗ φ₂ y` is continuous on the total spaces of the
tensor products (`TauCeti.continuous_tensorProduct_map_covering`): it is the tensor product of the
maps `E₁' → g^*E₁` and `E₂' → g^*E₂` over `B'` followed by the identity above.

These are the bundle maps along which the first Chern class of a tensor product of line bundles
is compared with its universal value on a product of classifying spaces.

## Main results

* `TensorProduct.inCoordinates_pullback`: the coordinates of `g^*E₁ ⊗ g^*E₂` are those of
  `E₁ ⊗ E₂` at the image points.
* `TauCeti.continuous_tensorProduct_pullback`: `g^*E₁ ⊗ g^*E₂ → E₁ ⊗ E₂`, covering `g`, is
  continuous.
* `TauCeti.continuous_tensorProduct_map_covering`: the tensor product of two bundle maps covering
  `g` is continuous.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 5, §6 (tensor products of vector bundles and their naturality under pullback).
-/

public section

noncomputable section

open Bundle FiberBundle Topology
open scoped TensorProduct

section Pullback

variable {𝕜 B B' : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] [TopologicalSpace B']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  (g : C(B', B))

/-- In the pulled-back charts, the coordinates of a tensor of `g^*E₁ ⊗ g^*E₂` at `y` centred at
`y₀` are its coordinates in `E₁ ⊗ E₂` at `g y` centred at `g y₀`. -/
theorem TensorProduct.inCoordinates_pullback (y₀ y : B') (t : (⇑g *ᵖ E₁) y ⊗[𝕜] (⇑g *ᵖ E₂) y) :
    TensorProduct.inCoordinates F₁ ((⇑g) *ᵖ E₁) F₂ ((⇑g) *ᵖ E₂) y₀ y y₀ y t =
      TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (g y₀) (g y) (g y₀) (g y) t := by
  -- The two sides are read at the types `(g^*E₁) y ⊗ (g^*E₂) y` and `E₁ (g y) ⊗ E₂ (g y)`,
  -- equal only after unfolding the pullback, so the right side is rewritten by `Eq.trans` at its
  -- own type.
  induction t using _root_.TensorProduct.inductionOn with
  | tmul v w =>
    refine (TensorProduct.inCoordinates_tmul _ _ _ _ v w).trans (Eq.trans ?_
      (TensorProduct.inCoordinates_tmul (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂)
        (g y₀) (g y) (g y₀) (g y) v w).symm)
    -- The preferred charts of the pullbacks are the pulled-back preferred charts.
    simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
      Trivialization.linearMapAt_pullback]
    -- Both sides now agree up to unfolding the pullback fibres.
    rfl
  | add t t' ht ht' =>
    exact (map_add _ t t').trans ((congrArg₂ (· + ·) ht ht').trans
      (map_add (TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (g y₀) (g y) (g y₀) (g y)) t t').symm)

namespace TauCeti

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ y, TopologicalSpace ((⇑g *ᵖ E₁) y ⊗[𝕜] (⇑g *ᵖ E₂) y)]
  [∀ y, IsModuleTopology 𝕜 ((⇑g *ᵖ E₁) y ⊗[𝕜] (⇑g *ᵖ E₂) y)]

variable (F₁ E₁ F₂ E₂) in
/-- **The tensor product of pullbacks maps to the tensor product.** The fibre of
`g^*E₁ ⊗ g^*E₂` over `y` is the fibre of `E₁ ⊗ E₂` over `g y`, and the fibrewise identity, covering
`g`, is continuous on total spaces. -/
theorem continuous_tensorProduct_pullback :
    Continuous fun p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂)
        (fun y ↦ (⇑g *ᵖ E₁) y ⊗[𝕜] (⇑g *ᵖ E₂) y) ↦
      TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂) (E := fun x ↦ E₁ x ⊗[𝕜] E₂ x) (g p.proj) p.snd := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  have hid := (continuousAt_tensorProduct_bundle (F₁ := F₁) (F₂ := F₂)
    (fun p : TotalSpace (ProjectiveTensor 𝕜 F₁ F₂)
      (fun y ↦ (⇑g *ᵖ E₁) y ⊗[𝕜] (⇑g *ᵖ E₂) y) ↦ p) (x₀ := p₀)).1 continuousAt_id
  refine (continuousAt_tensorProduct_bundle (F₁ := F₁) (F₂ := F₂) _).2
    ⟨(g.continuous.comp (continuous_proj _ _)).continuousAt, hid.2.congr ?_⟩
  filter_upwards with p
  exact TensorProduct.inCoordinates_pullback g p₀.proj p.proj p.snd

end TauCeti

end Pullback

section Covering

namespace TauCeti

variable {𝕜 B B' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] [TopologicalSpace B']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁]
  [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂]
  [VectorBundle 𝕜 F₂ E₂]
  {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] [FiniteDimensional 𝕜 F₁']
  {E₁' : B' → Type*} [∀ y, AddCommGroup (E₁' y)] [∀ y, Module 𝕜 (E₁' y)]
  [∀ y, TopologicalSpace (E₁' y)] [TopologicalSpace (TotalSpace F₁' E₁')] [FiberBundle F₁' E₁']
  [VectorBundle 𝕜 F₁' E₁']
  {F₂' : Type*} [NormedAddCommGroup F₂'] [NormedSpace 𝕜 F₂'] [FiniteDimensional 𝕜 F₂']
  {E₂' : B' → Type*} [∀ y, AddCommGroup (E₂' y)] [∀ y, Module 𝕜 (E₂' y)]
  [∀ y, TopologicalSpace (E₂' y)] [TopologicalSpace (TotalSpace F₂' E₂')] [FiberBundle F₂' E₂']
  [VectorBundle 𝕜 F₂' E₂']
  [∀ x, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x)] [∀ x, IsModuleTopology 𝕜 (E₁ x ⊗[𝕜] E₂ x)]
  [∀ y, TopologicalSpace (E₁' y ⊗[𝕜] E₂' y)] [∀ y, IsModuleTopology 𝕜 (E₁' y ⊗[𝕜] E₂' y)]

/-- **Tensor products of bundle maps covering a base map are continuous.** For fibrewise linear
maps `φ₁ y : E₁' y →L E₁ (g y)` and `φ₂ y : E₂' y →L E₂ (g y)` covering a continuous map `g`,
continuous on total spaces, the fibrewise tensor product `φ₁ y ⊗ φ₂ y` is continuous on the total
spaces of `E₁' ⊗ E₂'` and `E₁ ⊗ E₂`. -/
theorem continuous_tensorProduct_map_covering {g : C(B', B)}
    {φ₁ : ∀ y, E₁' y →L[𝕜] E₁ (g y)} {φ₂ : ∀ y, E₂' y →L[𝕜] E₂ (g y)}
    (hφ₁ : Continuous fun p : TotalSpace F₁' E₁' ↦ TotalSpace.mk' F₁ (g p.proj) (φ₁ p.proj p.snd))
    (hφ₂ : Continuous fun p : TotalSpace F₂' E₂' ↦ TotalSpace.mk' F₂ (g p.proj) (φ₂ p.proj p.snd)) :
    Continuous fun p : TotalSpace (ProjectiveTensor 𝕜 F₁' F₂') (fun y ↦ E₁' y ⊗[𝕜] E₂' y) ↦
      TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂) (E := fun x ↦ E₁ x ⊗[𝕜] E₂ x) (g p.proj)
        (_root_.TensorProduct.map (φ₁ p.proj).toLinearMap (φ₂ p.proj).toLinearMap p.snd) := by
  open TauCeti.ModuleTopology in
  have := VectorBundle.isTopologicalAddGroup 𝕜 F₁ E₁
  have := VectorBundle.continuousSMul 𝕜 F₁ E₁
  have := VectorBundle.isTopologicalAddGroup 𝕜 F₂ E₂
  have := VectorBundle.continuousSMul 𝕜 F₂ E₂
  -- Read `φ₁` and `φ₂` as bundle maps over `B'` into the pullbacks `g^*E₁` and `g^*E₂`.
  let ψ₁ : ∀ y, E₁' y →L[𝕜] (⇑g *ᵖ E₁) y := φ₁
  let ψ₂ : ∀ y, E₂' y →L[𝕜] (⇑g *ᵖ E₂) y := φ₂
  have hψ₁ : Continuous fun p : TotalSpace F₁' E₁' ↦
      TotalSpace.mk' F₁ (E := ⇑g *ᵖ E₁) p.proj (ψ₁ p.proj p.snd) :=
    (inducing_pullbackTotalSpaceEmbedding F₁ E₁ g).continuous_iff.2
      ((continuous_proj F₁' E₁').prodMk hφ₁)
  have hψ₂ : Continuous fun p : TotalSpace F₂' E₂' ↦
      TotalSpace.mk' F₂ (E := ⇑g *ᵖ E₂) p.proj (ψ₂ p.proj p.snd) :=
    (inducing_pullbackTotalSpaceEmbedding F₂ E₂ g).continuous_iff.2
      ((continuous_proj F₂' E₂').prodMk hφ₂)
  have hψ := (continuous_hom_bundle_iff (bundleTensorMap ψ₁ ψ₂)).1
    (continuous_bundleTensorMap ((continuous_hom_bundle_iff ψ₁).2 hψ₁)
      ((continuous_hom_bundle_iff ψ₂).2 hψ₂))
  -- On each fibre `bundleTensorMap ψ₁ ψ₂` is `φ₁ y ⊗ φ₂ y`, read in the pullback fibres.
  have hmap (y : B') (t : E₁' y ⊗[𝕜] E₂' y) : bundleTensorMap ψ₁ ψ₂ y t =
      _root_.TensorProduct.map (φ₁ y).toLinearMap (φ₂ y).toLinearMap t := by
    induction t using _root_.TensorProduct.inductionOn with
    | tmul v w =>
      exact (bundleTensorMap_tmul ψ₁ ψ₂ y v w).trans (_root_.TensorProduct.map_tmul _ _ v w).symm
    | add t t' ht ht' =>
      exact (map_add _ t t').trans ((congrArg₂ (· + ·) ht ht').trans (map_add _ t t').symm)
  exact ((continuous_tensorProduct_pullback F₁ E₁ F₂ E₂ g).comp hψ).congr fun p ↦
    congrArg (TotalSpace.mk' (ProjectiveTensor 𝕜 F₁ F₂) (E := fun x ↦ E₁ x ⊗[𝕜] E₂ x) (g p.proj))
      (hmap p.proj p.snd)

end TauCeti

end Covering
