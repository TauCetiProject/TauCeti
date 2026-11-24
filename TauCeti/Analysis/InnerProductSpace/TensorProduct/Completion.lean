/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Basic
public import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Completed tensor products of Hilbert spaces and amplified operators

For inner product spaces `E` and `F` over `𝕜` (`ℝ` or `ℂ`), Mathlib puts on the algebraic tensor
product `E ⊗[𝕜] F` the inner product with `⟪x ⊗ₜ y, x' ⊗ₜ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`. Its completion
`UniformSpace.Completion (E ⊗[𝕜] F)` is the *completed Hilbert tensor product* `E ⊗̂ F`, a Hilbert
space, whether or not `E` and `F` are complete. This file develops the operators on it.

* The pure tensors `x ⊗ₜ y` span a dense subspace (`TensorProduct.dense_span_coe_tmul`), so a
  bounded operator out of `E ⊗̂ F` is determined by its values on them
  (`TensorProduct.completion_ext`), a vector orthogonal to all of them vanishes
  (`TensorProduct.eq_zero_of_forall_inner_coe_tmul`), and a bounded operator maps `E ⊗̂ F` into a
  closed submodule if it maps every pure tensor there
  (`TensorProduct.apply_mem_of_forall_apply_coe_tmul_mem`).
* A bounded operator `f : E →L[𝕜] E'` induces the bounded operator `f ⊗ 1` on `E ⊗̂ F`, the
  *amplification* `f.rTensorCompletion F`, which extends `ContinuousLinearMap.rTensor` and sends
  `x ⊗ₜ y` to `f x ⊗ₜ y`. It is the only bounded operator doing so
  (`ContinuousLinearMap.eq_rTensorCompletion_iff`). Symmetrically `g.lTensorCompletion E` is
  `1 ⊗ g`. Operators on both factors commute
  (`ContinuousLinearMap.rTensorCompletion_comp_lTensorCompletion`), and their product is the
  extension `TensorProduct.mapLCompletion f g` of `TensorProduct.mapL f g`, the tensor product
  `f ⊗ g` of the operators, which is likewise unique on pure tensors, has norm `‖f‖ * ‖g‖`
  (`TensorProduct.norm_mapLCompletion`, from `TensorProduct.norm_mapL`) and satisfies
  `(f ⊗ g)† = f† ⊗ g†` (`TensorProduct.adjoint_mapLCompletion`): if `f'` and `g'` are formal
  adjoints of `f` and `g` then `mapL f' g'` is a formal adjoint of `mapL f g`
  (`TensorProduct.inner_mapL_left`), so `ContinuousLinearMap.adjoint_completion` applies.
* Amplification preserves the operator norm when the other factor is nonzero
  (`ContinuousLinearMap.norm_rTensorCompletion`), composition and the identity, and it commutes
  with adjoints (`ContinuousLinearMap.adjoint_rTensorCompletion`), since `f ⊗ 1` is `f ⊗ id`
  (`ContinuousLinearMap.rTensorCompletion_eq_mapLCompletion`) and `id` is its own formal adjoint.
  When `E` is complete, `f ↦ f ⊗ 1` is therefore a unital star algebra homomorphism
  `B(E) →⋆ₐ[𝕜] B(E ⊗̂ F)` (`ContinuousLinearMap.rTensorCompletionStarAlgHom`), injective and
  isometric when `F ≠ 0`. When `F = 0` the completed tensor product is `0`, so every amplification
  is `0`.
* The flip `E ⊗ F ≃ F ⊗ E` extends to a unitary `E ⊗̂ F ≃ F ⊗̂ E`, which exchanges the two
  amplifications (`ContinuousLinearMap.lTensorCompletion_commIsometry_completion`,
  `ContinuousLinearMap.rTensorCompletion_commIsometry_completion`) and the factors of `f ⊗ g`
  (`TensorProduct.mapLCompletion_commIsometry_completion`).
* Completing a factor first does not change the completed tensor product: `E ⊗[𝕜] F` is dense in
  `Ê ⊗[𝕜] F` (`TensorProduct.denseRange_rTensor_toComplₗᵢ`, an instance of
  `ContinuousLinearMap.denseRange_rTensor`), which gives the unitaries
  `E ⊗̂ F ≃ Ê ⊗̂ F` and `E ⊗̂ F ≃ E ⊗̂ F̂` (`TensorProduct.completionLeftIsometry`,
  `TensorProduct.completionRightIsometry`). Through them the associator of the algebraic tensor
  product extends to the unitary `(E ⊗̂ F) ⊗̂ G ≃ E ⊗̂ (F ⊗̂ G)`
  (`TensorProduct.assocIsometryCompletion`). Bounded operators out of `(E ⊗̂ F) ⊗̂ G` are
  determined by their values on `(x ⊗ₜ y) ⊗ₜ z` (`TensorProduct.completion_ext₃`), so the
  associator is the only one sending it to `x ⊗ₜ (y ⊗ₜ z)`
  (`TensorProduct.eq_assocIsometryCompletion_iff`). It is natural in each factor:
  `(f ⊗ (g ⊗ h)) ∘ assoc = assoc ∘ ((f ⊗ g) ⊗ h)`
  (`TensorProduct.mapLCompletion_mapLCompletion_assocIsometryCompletion`).

These are the bounded operators `A ⊗ 1` and `1 ⊗ B` on tensor products of Hilbert spaces from which
spatial tensor products of operator algebras are built, and they act on tensor products of `L²`
spaces of sections, for instance in the block operators of products of elliptic operators.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras, Volume I*,
  Academic Press, 1983, §2.6 (tensor products of Hilbert spaces and of operators).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press, 1980, §II.4 and §VIII.10.
-/

public section

noncomputable section

open UniformSpace TensorProduct
open scoped InnerProductSpace

variable {𝕜 E E' E'' F F' F'' G G' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup E''] [InnerProductSpace 𝕜 E''] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
  [NormedAddCommGroup F''] [InnerProductSpace 𝕜 F''] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G']

namespace TensorProduct

variable (𝕜 E F) in
/-- The pure tensors span a dense subspace of the completed tensor product of `E` and `F`. -/
theorem dense_span_coe_tmul :
    (Submodule.span 𝕜 (Set.range fun p : E × F ↦
      ((p.1 ⊗ₜ[𝕜] p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)))).topologicalClosure = ⊤ := by
  have h : Submodule.span 𝕜 (Set.range fun p : E × F ↦
      ((p.1 ⊗ₜ[𝕜] p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) =
      (⊤ : Submodule 𝕜 (E ⊗[𝕜] F)).map
        ((Completion.toComplL : E ⊗[𝕜] F →L[𝕜] Completion (E ⊗[𝕜] F)) :
          E ⊗[𝕜] F →ₗ[𝕜] Completion (E ⊗[𝕜] F)) := by
    rw [← span_tmul_eq_top, Submodule.map_span]
    congr 1
    ext u
    simp
  exact h ▸ Completion.denseRange_coe.topologicalClosure_map_submodule
    (top_unique (Submodule.le_topologicalClosure _))

/-- Two bounded operators from the completed tensor product of `E` and `F` to a Hausdorff space
agree when they agree on pure tensors. -/
theorem completion_ext {M : Type*} [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M] [T2Space M]
    {l l' : Completion (E ⊗[𝕜] F) →L[𝕜] M}
    (h : ∀ x y, l (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = l' (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)) : l = l' := by
  have h' : l ∘L Completion.toComplL = l' ∘L Completion.toComplL :=
    ContinuousLinearMap.coe_inj.1 <| TensorProduct.ext' fun x y ↦ by simpa using h x y
  exact DFunLike.coe_injective <|
    Completion.ext l.continuous l'.continuous fun u ↦ by simpa using congr($h' u)

/-- A vector of the completed tensor product that is orthogonal to every pure tensor vanishes. -/
theorem eq_zero_of_forall_inner_coe_tmul {w : Completion (E ⊗[𝕜] F)}
    (h : ∀ x y, ⟪((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)), w⟫_𝕜 = 0) : w = 0 := by
  have hw : innerSL 𝕜 w = 0 := completion_ext fun x y ↦ by
    rw [innerSL_apply_apply, ← inner_conj_symm, h, map_zero, zero_apply]
  simpa using congr($hw w)

/-- A bounded operator out of the completed tensor product maps into a closed submodule as soon as
it maps every pure tensor into it. -/
theorem apply_mem_of_forall_apply_coe_tmul_mem {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [TopologicalSpace M] {T : Completion (E ⊗[𝕜] F) →L[𝕜] M} {S : Submodule 𝕜 M}
    (hS : IsClosed (S : Set M))
    (h : ∀ x y, T ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ∈ S)
    (w : Completion (E ⊗[𝕜] F)) : T w ∈ S := by
  have hle : Submodule.span 𝕜 (Set.range fun p : E × F ↦
      ((p.1 ⊗ₜ[𝕜] p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) ≤ S.comap (T : _ →ₗ[𝕜] M) :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun p ↦ h p.1 p.2
  have htop := Submodule.topologicalClosure_minimal _ hle (hS.preimage T.continuous)
  rw [dense_span_coe_tmul] at htop
  exact htop Submodule.mem_top

section Associator

variable (𝕜 E F) in
/-- The pure tensors `x ⊗ₜ y` with `x` in `E` have dense span in `Completion E ⊗[𝕜] F`, so the
algebraic tensor product `E ⊗[𝕜] F` is dense there. -/
theorem denseRange_rTensor_toComplₗᵢ :
    DenseRange ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E)).rTensor F) := by
  have := ContinuousLinearMap.denseRange_rTensor F
    (f := (Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E)).toContinuousLinearMap) Completion.denseRange_coe
  rwa [← LinearIsometry.toContinuousLinearMap_rTensor,
    LinearIsometry.coe_toContinuousLinearMap] at this

variable (𝕜 E F) in
/-- Completing the left factor does not change the completed tensor product:
`E ⊗̂ F ≃ Ê ⊗̂ F`, sending `x ⊗ₜ y` to `x ⊗ₜ y`. -/
def completionLeftIsometry :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (Completion E ⊗[𝕜] F) :=
  LinearIsometry.completionEquivOfDenseRange _ (denseRange_rTensor_toComplₗᵢ 𝕜 E F)

variable (𝕜 E F) in
/-- Completing the right factor does not change the completed tensor product:
`E ⊗̂ F ≃ E ⊗̂ F̂`, sending `x ⊗ₜ y` to `x ⊗ₜ y`. -/
def completionRightIsometry :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] Completion F) :=
  (commIsometry 𝕜 E F).completion.trans <| (completionLeftIsometry 𝕜 F E).trans
    (commIsometry 𝕜 (Completion F) E).completion

/-- On the algebraic tensor product, completing the left factor is
`LinearIsometry.rTensor` of the inclusion `E → Ê`. -/
@[simp]
theorem completionLeftIsometry_coe (u : E ⊗[𝕜] F) :
    completionLeftIsometry 𝕜 E F u =
      ((Completion.toComplₗᵢ.rTensor F u : Completion E ⊗[𝕜] F) :
        Completion (Completion E ⊗[𝕜] F)) :=
  LinearIsometry.completionEquivOfDenseRange_coe _ _ u

theorem completionLeftIsometry_coe_tmul (x : E) (y : F) :
    completionLeftIsometry 𝕜 E F (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) =
      ((x : Completion E) ⊗ₜ[𝕜] y : Completion E ⊗[𝕜] F) := by
  simp

theorem completionRightIsometry_coe_tmul (x : E) (y : F) :
    completionRightIsometry 𝕜 E F (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) =
      (x ⊗ₜ[𝕜] (y : Completion F) : E ⊗[𝕜] Completion F) := by
  simp [completionRightIsometry]

/-- On the algebraic tensor product, completing the right factor is
`LinearIsometry.lTensor` of the inclusion `F → F̂`. -/
@[simp]
theorem completionRightIsometry_coe (u : E ⊗[𝕜] F) :
    completionRightIsometry 𝕜 E F u =
      ((Completion.toComplₗᵢ.lTensor E u : E ⊗[𝕜] Completion F) :
        Completion (E ⊗[𝕜] Completion F)) := by
  induction u using TensorProduct.inductionOn with
  | tmul x y => simpa using completionRightIsometry_coe_tmul x y
  | add u v hu hv => simp only [Completion.coe_add, map_add, hu, hv]

@[simp]
theorem completionLeftIsometry_symm_coe_tmul (x : E) (y : F) :
    (completionLeftIsometry 𝕜 E F).symm ((x : Completion E) ⊗ₜ[𝕜] y : Completion E ⊗[𝕜] F) =
      (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) :=
  (LinearIsometryEquiv.symm_apply_eq _).2 (completionLeftIsometry_coe_tmul x y).symm

@[simp]
theorem completionRightIsometry_symm_coe_tmul (x : E) (y : F) :
    (completionRightIsometry 𝕜 E F).symm (x ⊗ₜ[𝕜] (y : Completion F) : E ⊗[𝕜] Completion F) =
      (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) :=
  (LinearIsometryEquiv.symm_apply_eq _).2 (completionRightIsometry_coe_tmul x y).symm

variable (𝕜 E F G) in
/-- The associator `(E ⊗̂ F) ⊗̂ G ≃ E ⊗̂ (F ⊗̂ G)` of completed tensor products, extending
`TensorProduct.assocIsometry`. -/
def assocIsometryCompletion :
    Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G)) :=
  (completionLeftIsometry 𝕜 (E ⊗[𝕜] F) G).symm.trans <|
    (assocIsometry 𝕜 E F G).completion.trans (completionRightIsometry 𝕜 E (F ⊗[𝕜] G))

/-- The associator sends `(x ⊗ₜ y) ⊗ₜ z` to `x ⊗ₜ (y ⊗ₜ z)`. -/
@[simp]
theorem assocIsometryCompletion_coe_tmul (x : E) (y : F) (z : G) :
    assocIsometryCompletion 𝕜 E F G
        (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
          Completion (E ⊗[𝕜] F) ⊗[𝕜] G) =
      (x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : Completion (F ⊗[𝕜] G)) :
        E ⊗[𝕜] Completion (F ⊗[𝕜] G)) := by
  simp [assocIsometryCompletion]

/-- The inverse associator sends `x ⊗ₜ (y ⊗ₜ z)` to `(x ⊗ₜ y) ⊗ₜ z`. -/
@[simp]
theorem assocIsometryCompletion_symm_coe_tmul (x : E) (y : F) (z : G) :
    (assocIsometryCompletion 𝕜 E F G).symm
        (x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : Completion (F ⊗[𝕜] G)) :
          E ⊗[𝕜] Completion (F ⊗[𝕜] G)) =
      (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G) :=
  (LinearIsometryEquiv.symm_apply_eq _).2 (assocIsometryCompletion_coe_tmul x y z).symm

/-- Two bounded operators from the completed tensor product of `E ⊗̂ F` and `G` to a Hausdorff
space agree when they agree on the triple pure tensors `(x ⊗ₜ y) ⊗ₜ z`. -/
theorem completion_ext₃ {M : Type*} [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
    [T2Space M] {l l' : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜] M}
    (h : ∀ x y z, l (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G) =
      l' (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G)) :
    l = l' :=
  completion_ext fun c z ↦ by
    -- For fixed `z`, both sides are bounded operators in `c`, agreeing on pure tensors `x ⊗ₜ y`.
    have hz : l ∘L Completion.toComplL ∘L (mkL 𝕜 (Completion (E ⊗[𝕜] F)) G).flip z =
        l' ∘L Completion.toComplL ∘L (mkL 𝕜 (Completion (E ⊗[𝕜] F)) G).flip z :=
      completion_ext fun x y ↦ by simpa using h x y z
    simpa using congr($hz c)

/-- The associator is the only bounded operator sending `(x ⊗ₜ y) ⊗ₜ z` to `x ⊗ₜ (y ⊗ₜ z)`. -/
theorem eq_assocIsometryCompletion_iff
    {T : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
      Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))} :
    T = (assocIsometryCompletion 𝕜 E F G : _ →L[𝕜] _) ↔
      ∀ x y z, T (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
          Completion (E ⊗[𝕜] F) ⊗[𝕜] G) =
        (x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : Completion (F ⊗[𝕜] G)) :
          E ⊗[𝕜] Completion (F ⊗[𝕜] G)) :=
  ⟨fun h x y z ↦ by simp [h], fun h ↦ completion_ext₃ fun x y z ↦ by simp [h]⟩

end Associator

section mapL

/-- The tensor product `f ⊗ g : E ⊗̂ F →L[𝕜] E' ⊗̂ F'` of bounded operators `f : E →L[𝕜] E'` and
`g : F →L[𝕜] F'` on the completed tensor products: the extension of `TensorProduct.mapL` to the
completions, sending `x ⊗ₜ y` to `f x ⊗ₜ g y`. -/
def mapLCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F') :=
  (mapL f g).completion

/-- On the algebraic tensor product, `f ⊗ g` is `TensorProduct.mapL f g`. -/
@[simp]
theorem mapLCompletion_coe (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : E ⊗[𝕜] F) :
    mapLCompletion f g u = (mapL f g u : Completion (E' ⊗[𝕜] F')) :=
  ContinuousLinearMap.completion_apply_coe _ u

/-- The tensor product `f ⊗ g` sends `x ⊗ₜ y` to `f x ⊗ₜ g y`. -/
theorem mapLCompletion_tmul (f : E →L[𝕜] E') (g : F →L[𝕜] F') (x : E) (y : F) :
    mapLCompletion f g (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (f x ⊗ₜ[𝕜] g y : E' ⊗[𝕜] F') := by
  simp

/-- The tensor product `f ⊗ g` is the only bounded operator sending `x ⊗ₜ y` to `f x ⊗ₜ g y`. -/
theorem eq_mapLCompletion_iff {f : E →L[𝕜] E'} {g : F →L[𝕜] F'}
    {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F')} :
    T = mapLCompletion f g ↔
      ∀ x y, T (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (f x ⊗ₜ[𝕜] g y : E' ⊗[𝕜] F') :=
  ⟨fun h x y ↦ h ▸ mapLCompletion_tmul f g x y,
    fun h ↦ completion_ext fun x y ↦ by rw [h, mapLCompletion_tmul]⟩

@[simp]
theorem mapLCompletion_add_left (f₁ f₂ : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion (f₁ + f₂) g = mapLCompletion f₁ g + mapLCompletion f₂ g :=
  completion_ext fun _ _ ↦ by simp [add_tmul, Completion.coe_add]

@[simp]
theorem mapLCompletion_add_right (f : E →L[𝕜] E') (g₁ g₂ : F →L[𝕜] F') :
    mapLCompletion f (g₁ + g₂) = mapLCompletion f g₁ + mapLCompletion f g₂ :=
  completion_ext fun _ _ ↦ by simp [tmul_add, Completion.coe_add]

@[simp]
theorem mapLCompletion_smul_left (c : 𝕜) (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion (c • f) g = c • mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp [← smul_tmul', Completion.coe_smul]

@[simp]
theorem mapLCompletion_smul_right (c : 𝕜) (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion f (c • g) = c • mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp [tmul_smul, Completion.coe_smul]

@[simp]
theorem mapLCompletion_neg_left (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion (-f) g = -mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp [neg_tmul, Completion.coe_neg]

@[simp]
theorem mapLCompletion_neg_right (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion f (-g) = -mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp [tmul_neg, Completion.coe_neg]

@[simp]
theorem mapLCompletion_sub_left (f₁ f₂ : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion (f₁ - f₂) g = mapLCompletion f₁ g - mapLCompletion f₂ g :=
  completion_ext fun _ _ ↦ by simp [sub_tmul, Completion.coe_sub]

@[simp]
theorem mapLCompletion_sub_right (f : E →L[𝕜] E') (g₁ g₂ : F →L[𝕜] F') :
    mapLCompletion f (g₁ - g₂) = mapLCompletion f g₁ - mapLCompletion f g₂ :=
  completion_ext fun _ _ ↦ by simp [tmul_sub, Completion.coe_sub]

@[simp]
theorem mapLCompletion_zero_left (g : F →L[𝕜] F') :
    mapLCompletion (0 : E →L[𝕜] E') g = 0 :=
  completion_ext fun _ _ ↦ by simp

@[simp]
theorem mapLCompletion_zero_right (f : E →L[𝕜] E') :
    mapLCompletion f (0 : F →L[𝕜] F') = 0 :=
  completion_ext fun _ _ ↦ by simp

/-- The tensor product `f ⊗ g` has norm at most `‖f‖ * ‖g‖`. -/
theorem norm_mapLCompletion_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    ‖mapLCompletion f g‖ ≤ ‖f‖ * ‖g‖ :=
  (ContinuousLinearMap.norm_completion _).trans_le (norm_mapL_le f g)

/-- The tensor product `f ⊗ g` has norm `‖f‖ * ‖g‖`. -/
@[simp]
theorem norm_mapLCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    ‖mapLCompletion f g‖ = ‖f‖ * ‖g‖ :=
  (ContinuousLinearMap.norm_completion _).trans (norm_mapL f g)

/-- The tensor product of the identities is the identity: `1 ⊗ 1 = 1`. -/
@[simp]
theorem mapLCompletion_id :
    mapLCompletion (.id 𝕜 E) (.id 𝕜 F) = .id 𝕜 (Completion (E ⊗[𝕜] F)) :=
  completion_ext fun _ _ ↦ by simp

/-- The tensor product of operators respects composition:
`(f₂ ∘ f₁) ⊗ (g₂ ∘ g₁) = (f₂ ⊗ g₂) ∘ (f₁ ⊗ g₁)`. -/
theorem mapLCompletion_comp (f₂ : E' →L[𝕜] E'') (f₁ : E →L[𝕜] E') (g₂ : F' →L[𝕜] F'')
    (g₁ : F →L[𝕜] F') :
    mapLCompletion (f₂ ∘L f₁) (g₂ ∘L g₁) = mapLCompletion f₂ g₂ ∘L mapLCompletion f₁ g₁ :=
  completion_ext fun _ _ ↦ by simp

/-- The tensor product `f† ⊗ g†` is the adjoint of `f ⊗ g`. -/
@[simp]
theorem adjoint_mapLCompletion [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    [CompleteSpace F'] (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    (mapLCompletion f g).adjoint = mapLCompletion f.adjoint g.adjoint :=
  ContinuousLinearMap.adjoint_completion <| inner_mapL_left
    (fun x y ↦ (f.adjoint_inner_right x y).symm) fun x y ↦ (g.adjoint_inner_right x y).symm

/-- The extension of the flip `E ⊗ F ≃ F ⊗ E` to the completions exchanges the factors of a
tensor product of operators: `(g ⊗ f) ∘ flip = flip ∘ (f ⊗ g)`. -/
theorem mapLCompletion_commIsometry_completion (f : E →L[𝕜] E')
    (g : F →L[𝕜] F') (u : Completion (E ⊗[𝕜] F)) :
    mapLCompletion g f ((commIsometry 𝕜 E F).completion u) =
      (commIsometry 𝕜 E' F').completion (mapLCompletion f g u) := by
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    simp only [LinearIsometryEquiv.completion_apply_coe, mapLCompletion_coe]
    exact congr(($(mapL_comp_commIsometry g f) u : Completion (F' ⊗[𝕜] E')))

/-- The associator of completed tensor products is natural in each factor:
`(f ⊗ (g ⊗ h)) ∘ assoc = assoc ∘ ((f ⊗ g) ⊗ h)`. -/
theorem mapLCompletion_mapLCompletion_assocIsometryCompletion (f : E →L[𝕜] E')
    (g : F →L[𝕜] F') (h : G →L[𝕜] G') (u : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G)) :
    mapLCompletion f (mapLCompletion g h) (assocIsometryCompletion 𝕜 E F G u) =
      assocIsometryCompletion 𝕜 E' F' G' (mapLCompletion (mapLCompletion f g) h u) := by
  have key : mapLCompletion f (mapLCompletion g h) ∘L
      (assocIsometryCompletion 𝕜 E F G : _ →L[𝕜] _) =
        (assocIsometryCompletion 𝕜 E' F' G' : _ →L[𝕜] _) ∘L
          mapLCompletion (mapLCompletion f g) h :=
    completion_ext₃ fun x y z ↦ by simp
  exact congr($key u)

end mapL

end TensorProduct

namespace ContinuousLinearMap

section rTensor

variable (F) in
/-- The amplification `f ⊗ 1 : E ⊗̂ F →L[𝕜] E' ⊗̂ F` of a bounded operator `f : E →L[𝕜] E'` to the
completed tensor products with `F`: the extension of `ContinuousLinearMap.rTensor` to the
completions, sending `x ⊗ₜ y` to `f x ⊗ₜ y`. -/
def rTensorCompletion (f : E →L[𝕜] E') :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F) :=
  (f.rTensor F).completion

/-- On the algebraic tensor product, the amplification is `ContinuousLinearMap.rTensor`. -/
@[simp]
theorem rTensorCompletion_coe (f : E →L[𝕜] E') (u : E ⊗[𝕜] F) :
    f.rTensorCompletion F u = (f.rTensor F u : Completion (E' ⊗[𝕜] F)) :=
  completion_apply_coe _ u

/-- The amplification `f ⊗ 1` sends `x ⊗ₜ y` to `f x ⊗ₜ y`. -/
theorem rTensorCompletion_tmul (f : E →L[𝕜] E') (x : E) (y : F) :
    f.rTensorCompletion F (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (f x ⊗ₜ[𝕜] y : E' ⊗[𝕜] F) := by
  simp

variable (F) in
/-- The amplification `f ⊗ 1` is the tensor product of `f` with the identity. -/
theorem rTensorCompletion_eq_mapLCompletion (f : E →L[𝕜] E') :
    f.rTensorCompletion F = mapLCompletion f (.id 𝕜 F) :=
  congrArg completion (f.rTensor_eq_mapL F)

/-- The amplification `f ⊗ 1` is the only bounded operator sending `x ⊗ₜ y` to `f x ⊗ₜ y`. -/
theorem eq_rTensorCompletion_iff {f : E →L[𝕜] E'}
    {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)} :
    T = f.rTensorCompletion F ↔
      ∀ x y, T (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (f x ⊗ₜ[𝕜] y : E' ⊗[𝕜] F) :=
  ⟨fun h x y ↦ h ▸ f.rTensorCompletion_tmul x y,
    fun h ↦ completion_ext fun x y ↦ by rw [h, rTensorCompletion_tmul]⟩

/-- The amplification `f ⊗ 1` has norm at most `‖f‖`. -/
theorem norm_rTensorCompletion_le (f : E →L[𝕜] E') : ‖f.rTensorCompletion F‖ ≤ ‖f‖ :=
  (norm_completion _).trans_le (norm_rTensor_le _ _)

/-- The amplification `f ⊗ 1` to a nonzero space `F` has the same norm as `f`. -/
@[simp]
theorem norm_rTensorCompletion [Nontrivial F] (f : E →L[𝕜] E') :
    ‖f.rTensorCompletion F‖ = ‖f‖ :=
  (norm_completion _).trans (norm_rTensor _)

@[simp]
theorem rTensorCompletion_id :
    (ContinuousLinearMap.id 𝕜 E).rTensorCompletion F =
      ContinuousLinearMap.id 𝕜 (Completion (E ⊗[𝕜] F)) :=
  completion_ext fun _ _ ↦ by simp

@[simp]
theorem rTensorCompletion_one :
    (1 : E →L[𝕜] E).rTensorCompletion F = 1 :=
  rTensorCompletion_id

/-- Amplification respects composition: `(f₂ ∘ f₁) ⊗ 1 = (f₂ ⊗ 1) ∘ (f₁ ⊗ 1)`. -/
theorem rTensorCompletion_comp (f₂ : E' →L[𝕜] E'') (f₁ : E →L[𝕜] E') :
    (f₂ ∘L f₁).rTensorCompletion F = f₂.rTensorCompletion F ∘L f₁.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp

theorem rTensorCompletion_mul (f₁ f₂ : E →L[𝕜] E) :
    (f₁ * f₂).rTensorCompletion F = f₁.rTensorCompletion F * f₂.rTensorCompletion F :=
  rTensorCompletion_comp f₁ f₂

@[simp]
theorem rTensorCompletion_add (f₁ f₂ : E →L[𝕜] E') :
    (f₁ + f₂).rTensorCompletion F = f₁.rTensorCompletion F + f₂.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_add]

@[simp]
theorem rTensorCompletion_smul (c : 𝕜) (f : E →L[𝕜] E') :
    (c • f).rTensorCompletion F = c • f.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_smul]

@[simp]
theorem rTensorCompletion_neg (f : E →L[𝕜] E') :
    (-f).rTensorCompletion F = -f.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_neg]

@[simp]
theorem rTensorCompletion_sub (f₁ f₂ : E →L[𝕜] E') :
    (f₁ - f₂).rTensorCompletion F = f₁.rTensorCompletion F - f₂.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_sub]

@[simp]
theorem rTensorCompletion_zero : (0 : E →L[𝕜] E').rTensorCompletion F = 0 :=
  completion_ext fun _ _ ↦ by simp

/-- The amplifications of the orthogonal projections onto a subspace and onto its orthogonal
complement add up to the identity: `Π ⊗ 1 + Πᗮ ⊗ 1 = 1`. -/
theorem rTensorCompletion_starProjection_add_rTensorCompletion_starProjection_orthogonal
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K.starProjection.rTensorCompletion F + Kᗮ.starProjection.rTensorCompletion F =
      ContinuousLinearMap.id 𝕜 (Completion (E ⊗[𝕜] F)) := by
  rw [← rTensorCompletion_add, ← K.id_eq_sum_starProjection_self_orthogonalComplement,
    rTensorCompletion_id]

/-- Every amplification to the zero space is zero. -/
theorem rTensorCompletion_of_subsingleton [Subsingleton F] (f : E →L[𝕜] E') :
    f.rTensorCompletion F = 0 :=
  completion_ext fun x y ↦ by simp [Subsingleton.elim y 0]

variable (F) in
/-- The amplification `f† ⊗ 1` is the adjoint of `f ⊗ 1`. -/
@[simp]
theorem adjoint_rTensorCompletion [CompleteSpace E] [CompleteSpace E'] (f : E →L[𝕜] E') :
    adjoint (f.rTensorCompletion F) = (adjoint f).rTensorCompletion F := by
  rw [rTensorCompletion_eq_mapLCompletion, rTensorCompletion_eq_mapLCompletion]
  exact adjoint_completion <|
    inner_mapL_left (fun x y ↦ (f.adjoint_inner_right x y).symm) fun _ _ ↦ rfl

end rTensor

section lTensor

variable (E) in
/-- The amplification `1 ⊗ g : E ⊗̂ F →L[𝕜] E ⊗̂ F'` of a bounded operator `g : F →L[𝕜] F'` to the
completed tensor products with `E`: the extension of `ContinuousLinearMap.lTensor` to the
completions, sending `x ⊗ₜ y` to `x ⊗ₜ g y`. -/
def lTensorCompletion (g : F →L[𝕜] F') :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F') :=
  (g.lTensor E).completion

/-- On the algebraic tensor product, the amplification is `ContinuousLinearMap.lTensor`. -/
@[simp]
theorem lTensorCompletion_coe (g : F →L[𝕜] F') (u : E ⊗[𝕜] F) :
    g.lTensorCompletion E u = (g.lTensor E u : Completion (E ⊗[𝕜] F')) :=
  completion_apply_coe _ u

/-- The amplification `1 ⊗ g` sends `x ⊗ₜ y` to `x ⊗ₜ g y`. -/
theorem lTensorCompletion_tmul (g : F →L[𝕜] F') (x : E) (y : F) :
    g.lTensorCompletion E (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (x ⊗ₜ[𝕜] g y : E ⊗[𝕜] F') := by
  simp

variable (E) in
/-- The amplification `1 ⊗ g` is the tensor product of the identity with `g`. -/
theorem lTensorCompletion_eq_mapLCompletion (g : F →L[𝕜] F') :
    g.lTensorCompletion E = mapLCompletion (.id 𝕜 E) g :=
  congrArg completion (g.lTensor_eq_mapL E)

/-- The amplification `1 ⊗ g` is the only bounded operator sending `x ⊗ₜ y` to `x ⊗ₜ g y`. -/
theorem eq_lTensorCompletion_iff {g : F →L[𝕜] F'}
    {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')} :
    T = g.lTensorCompletion E ↔
      ∀ x y, T (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (x ⊗ₜ[𝕜] g y : E ⊗[𝕜] F') :=
  ⟨fun h x y ↦ h ▸ g.lTensorCompletion_tmul x y,
    fun h ↦ completion_ext fun x y ↦ by rw [h, lTensorCompletion_tmul]⟩

/-- The amplification `1 ⊗ g` has norm at most `‖g‖`. -/
theorem norm_lTensorCompletion_le (g : F →L[𝕜] F') : ‖g.lTensorCompletion E‖ ≤ ‖g‖ :=
  (norm_completion _).trans_le (norm_lTensor_le _ _)

/-- The amplification `1 ⊗ g` from a nonzero space `E` has the same norm as `g`. -/
@[simp]
theorem norm_lTensorCompletion [Nontrivial E] (g : F →L[𝕜] F') :
    ‖g.lTensorCompletion E‖ = ‖g‖ :=
  (norm_completion _).trans (norm_lTensor _)

@[simp]
theorem lTensorCompletion_id :
    (ContinuousLinearMap.id 𝕜 F).lTensorCompletion E =
      ContinuousLinearMap.id 𝕜 (Completion (E ⊗[𝕜] F)) :=
  completion_ext fun _ _ ↦ by simp

@[simp]
theorem lTensorCompletion_one :
    (1 : F →L[𝕜] F).lTensorCompletion E = 1 :=
  lTensorCompletion_id

/-- Amplification respects composition: `1 ⊗ (g₂ ∘ g₁) = (1 ⊗ g₂) ∘ (1 ⊗ g₁)`. -/
theorem lTensorCompletion_comp (g₂ : F' →L[𝕜] F'') (g₁ : F →L[𝕜] F') :
    (g₂ ∘L g₁).lTensorCompletion E = g₂.lTensorCompletion E ∘L g₁.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp

theorem lTensorCompletion_mul (g₁ g₂ : F →L[𝕜] F) :
    (g₁ * g₂).lTensorCompletion E = g₁.lTensorCompletion E * g₂.lTensorCompletion E :=
  lTensorCompletion_comp g₁ g₂

@[simp]
theorem lTensorCompletion_add (g₁ g₂ : F →L[𝕜] F') :
    (g₁ + g₂).lTensorCompletion E = g₁.lTensorCompletion E + g₂.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_add]

@[simp]
theorem lTensorCompletion_smul (c : 𝕜) (g : F →L[𝕜] F') :
    (c • g).lTensorCompletion E = c • g.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_smul]

@[simp]
theorem lTensorCompletion_neg (g : F →L[𝕜] F') :
    (-g).lTensorCompletion E = -g.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_neg]

@[simp]
theorem lTensorCompletion_sub (g₁ g₂ : F →L[𝕜] F') :
    (g₁ - g₂).lTensorCompletion E = g₁.lTensorCompletion E - g₂.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_sub]

@[simp]
theorem lTensorCompletion_zero : (0 : F →L[𝕜] F').lTensorCompletion E = 0 :=
  completion_ext fun _ _ ↦ by simp

/-- The amplifications of the orthogonal projections onto a subspace and onto its orthogonal
complement add up to the identity: `1 ⊗ Π + 1 ⊗ Πᗮ = 1`. -/
theorem lTensorCompletion_starProjection_add_lTensorCompletion_starProjection_orthogonal
    (K : Submodule 𝕜 F) [K.HasOrthogonalProjection] :
    K.starProjection.lTensorCompletion E + Kᗮ.starProjection.lTensorCompletion E =
      ContinuousLinearMap.id 𝕜 (Completion (E ⊗[𝕜] F)) := by
  rw [← lTensorCompletion_add, ← K.id_eq_sum_starProjection_self_orthogonalComplement,
    lTensorCompletion_id]

/-- Every amplification from the zero space is zero. -/
theorem lTensorCompletion_of_subsingleton [Subsingleton E] (g : F →L[𝕜] F') :
    g.lTensorCompletion E = 0 :=
  completion_ext fun x y ↦ by simp [Subsingleton.elim x 0]

variable (E) in
/-- The amplification `1 ⊗ g†` is the adjoint of `1 ⊗ g`. -/
@[simp]
theorem adjoint_lTensorCompletion [CompleteSpace F] [CompleteSpace F'] (g : F →L[𝕜] F') :
    adjoint (g.lTensorCompletion E) = (adjoint g).lTensorCompletion E := by
  rw [lTensorCompletion_eq_mapLCompletion, lTensorCompletion_eq_mapLCompletion]
  exact adjoint_completion <|
    inner_mapL_left (fun _ _ ↦ rfl) fun x y ↦ (g.adjoint_inner_right x y).symm

end lTensor

/-- Amplifications on the two factors commute, with product the tensor product of the operators:
`(f ⊗ 1) ∘ (1 ⊗ g) = f ⊗ g`. -/
theorem rTensorCompletion_comp_lTensorCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    f.rTensorCompletion F' ∘L g.lTensorCompletion E = mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp

/-- Amplifications on the two factors commute, with product the tensor product of the operators:
`(1 ⊗ g) ∘ (f ⊗ 1) = f ⊗ g`. -/
theorem lTensorCompletion_comp_rTensorCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    g.lTensorCompletion E' ∘L f.rTensorCompletion F = mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp

/-- The amplifications `f ⊗ 1` and `1 ⊗ g` of endomorphisms commute. -/
theorem commute_rTensorCompletion_lTensorCompletion (f : E →L[𝕜] E) (g : F →L[𝕜] F) :
    Commute (f.rTensorCompletion F) (g.lTensorCompletion E) :=
  (rTensorCompletion_comp_lTensorCompletion f g).trans
    (lTensorCompletion_comp_rTensorCompletion f g).symm

/-- The extension of the flip `E ⊗ F ≃ F ⊗ E` to the completions exchanges the two
amplifications: `(1 ⊗ f) ∘ flip = flip ∘ (f ⊗ 1)`. -/
theorem lTensorCompletion_commIsometry_completion (f : E →L[𝕜] E') (u : Completion (E ⊗[𝕜] F)) :
    f.lTensorCompletion F ((commIsometry 𝕜 E F).completion u) =
      (commIsometry 𝕜 E' F).completion (f.rTensorCompletion F u) := by
  rw [lTensorCompletion_eq_mapLCompletion, rTensorCompletion_eq_mapLCompletion]
  exact mapLCompletion_commIsometry_completion f (.id 𝕜 F) u

/-- The extension of the flip `E ⊗ F ≃ F ⊗ E` to the completions exchanges the two
amplifications: `(g ⊗ 1) ∘ flip = flip ∘ (1 ⊗ g)`. -/
theorem rTensorCompletion_commIsometry_completion (g : F →L[𝕜] F') (u : Completion (E ⊗[𝕜] F)) :
    g.rTensorCompletion E ((commIsometry 𝕜 E F).completion u) =
      (commIsometry 𝕜 E F').completion (g.lTensorCompletion E u) := by
  rw [rTensorCompletion_eq_mapLCompletion, lTensorCompletion_eq_mapLCompletion]
  exact mapLCompletion_commIsometry_completion (.id 𝕜 E) g u

section StarAlgHom

variable (𝕜 E F)

/-- The amplification `f ↦ f ⊗ 1` from the bounded operators on a Hilbert space `E` to the bounded
operators on the completed tensor product `E ⊗̂ F`, as a unital star algebra homomorphism. -/
def rTensorCompletionStarAlgHom [CompleteSpace E] :
    (E →L[𝕜] E) →⋆ₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) where
  toFun f := f.rTensorCompletion F
  map_one' := rTensorCompletion_one
  map_mul' := rTensorCompletion_mul
  map_zero' := rTensorCompletion_zero
  map_add' := rTensorCompletion_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, rTensorCompletion_smul,
      rTensorCompletion_one]
  map_star' f := by
    rw [star_eq_adjoint, star_eq_adjoint, adjoint_rTensorCompletion]

/-- The amplification `g ↦ 1 ⊗ g` from the bounded operators on a Hilbert space `F` to the bounded
operators on the completed tensor product `E ⊗̂ F`, as a unital star algebra homomorphism. -/
def lTensorCompletionStarAlgHom [CompleteSpace F] :
    (F →L[𝕜] F) →⋆ₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) where
  toFun g := g.lTensorCompletion E
  map_one' := lTensorCompletion_one
  map_mul' := lTensorCompletion_mul
  map_zero' := lTensorCompletion_zero
  map_add' := lTensorCompletion_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, lTensorCompletion_smul,
      lTensorCompletion_one]
  map_star' g := by
    rw [star_eq_adjoint, star_eq_adjoint, adjoint_lTensorCompletion]

variable {𝕜 E F}

@[simp]
theorem rTensorCompletionStarAlgHom_apply [CompleteSpace E] (f : E →L[𝕜] E) :
    rTensorCompletionStarAlgHom 𝕜 E F f = f.rTensorCompletion F :=
  (rfl)

@[simp]
theorem lTensorCompletionStarAlgHom_apply [CompleteSpace F] (g : F →L[𝕜] F) :
    lTensorCompletionStarAlgHom 𝕜 E F g = g.lTensorCompletion E :=
  (rfl)

/-- The amplification `f ↦ f ⊗ 1` to a nonzero space `F` is injective. -/
theorem rTensorCompletionStarAlgHom_injective [CompleteSpace E] [Nontrivial F] :
    Function.Injective (rTensorCompletionStarAlgHom 𝕜 E F) :=
  (injective_iff_map_eq_zero _).2 fun f hf ↦ by
    rw [← norm_eq_zero, ← norm_rTensorCompletion (F := F), ← rTensorCompletionStarAlgHom_apply, hf,
      norm_zero]

/-- The amplification `g ↦ 1 ⊗ g` from a nonzero space `E` is injective. -/
theorem lTensorCompletionStarAlgHom_injective [CompleteSpace F] [Nontrivial E] :
    Function.Injective (lTensorCompletionStarAlgHom 𝕜 E F) :=
  (injective_iff_map_eq_zero _).2 fun g hg ↦ by
    rw [← norm_eq_zero, ← norm_lTensorCompletion (E := E), ← lTensorCompletionStarAlgHom_apply, hg,
      norm_zero]

end StarAlgHom

end ContinuousLinearMap
