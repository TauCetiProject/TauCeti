/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExternalProductBlock.Completion
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.RepresentationTheory.Continuous.WithLpProd
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# External tensor products of representations on completed tensor products

Let `π` be a continuous representation of a monoid `G` on an inner product space `V`, and `ρ` one
of a monoid `H` on an inner product space `W`. The product `G × H` acts on the completed Hilbert
tensor product `V ⊗̂ W = UniformSpace.Completion (V ⊗[𝕜] W)` by

`(g, h) ↦ π g ⊗ ρ h`,

the extension `TensorProduct.mapLCompletion (π g) (ρ h)` of `v ⊗ w ↦ π g v ⊗ ρ h w` to the
completion. This is the *external tensor product* `π ⊠̂ ρ`
(`ContRepresentation.externalTensorCompletion`). When `π` and `ρ` are unitary so is `π ⊠̂ ρ`
(`ContRepresentation.IsUnitary.externalTensorCompletion`), and when they are strongly continuous
with uniformly bounded operators, so is `π ⊠̂ ρ`
(`ContRepresentation.continuous_externalTensorCompletion_apply`). Strong continuity is not
inherited for free: the orbits of the pure tensors are continuous, the pure tensors span a dense
subspace, and the operators `π g ⊗ ρ h` are uniformly bounded
(`ContinuousLinearMap.continuous_apply_of_dense_span`).

For compact groups `G` and `H` acting on Hermitian bundles over closed manifolds `X` and `Y`, the
`L²` sections of the external product bundle over `X × Y` are identified, by a unitary, with the
completed tensor product of the two `L²` section spaces, and `G × H` acts on it in this way.

Intertwining maps of the factors give intertwining maps of the completed tensor products
(`ContIntertwiningMap.externalTensorCompletion`). In particular, for intertwining maps
`A : π₀ →ⁱL π₁` and `B : ρ₀ →ⁱL ρ₁` between unitary representations of groups `G` and `H` on
Hilbert spaces, the external product block

`D = [[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]] : (V₀ ⊗̂ W₀) ⊕ (V₁ ⊗̂ W₁) → (V₁ ⊗̂ W₀) ⊕ (V₀ ⊗̂ W₁)`

of `ContinuousLinearMap.externalProductBlockCompletion` intertwines the Hilbert direct sums
`(π₀ ⊠̂ ρ₀) ⊕ (π₁ ⊠̂ ρ₁)` and `(π₁ ⊠̂ ρ₀) ⊕ (π₀ ⊠̂ ρ₁)` of representations of `G × H`
(`ContIntertwiningMap.externalProductBlockCompletion`). This is the operator whose index is the
product of the indices of `A` and `B` (`ContinuousLinearMap.index_externalProductBlockCompletion`).
When `A` and `B` are Fredholm and the representations are strongly continuous, its equivariant
index (`ContIntertwiningMap.equivariantIndex`) in the representation ring of `G × H` is defined.

## Main definitions

* `ContRepresentation.externalTensorCompletion`: the external tensor product `π ⊠̂ ρ` on the
  completed tensor product.
* `ContIntertwiningMap.externalTensorCompletion`: the tensor product `A ⊗ B` of two intertwining
  maps, an intertwining map of the external tensor products.
* `ContIntertwiningMap.externalProductBlockCompletion`: the external product block of two
  intertwining maps between unitary representations, as an intertwining map of representations of
  `G × H`.

## Main statements

* `ContRepresentation.IsUnitary.externalTensorCompletion`: the external tensor product of unitary
  representations is unitary.
* `ContRepresentation.continuous_externalTensorCompletion_apply`: the external tensor product of
  strongly continuous representations with uniformly bounded operators is strongly continuous.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §9, for the product of a `G`-equivariant and an `H`-equivariant elliptic operator,
  equivariant for `G × H`.
-/

public section

noncomputable section

open Filter UniformSpace TensorProduct
open scoped Topology InnerProductSpace ContRepresentation

namespace ContRepresentation

variable {𝕜 G H V W : Type*} [RCLike 𝕜] [Monoid G] [Monoid H]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- **The external tensor product `π ⊠̂ ρ` on the completed tensor product.** The pair `(g, h)` acts
on `V ⊗̂ W = UniformSpace.Completion (V ⊗[𝕜] W)` by the extension `π g ⊗ ρ h` of
`v ⊗ w ↦ π g v ⊗ ρ h w` (`TensorProduct.mapLCompletion`). -/
def externalTensorCompletion (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 H W) :
    ContRepresentation 𝕜 (G × H) (Completion (V ⊗[𝕜] W)) :=
  .ofMonoidHom
    { toFun g := mapLCompletion (π g.1) (ρ g.2)
      map_one' := by
        simpa only [Prod.fst_one, Prod.snd_one, map_one, ContinuousLinearMap.one_def] using
          mapLCompletion_id
      map_mul' g h := by
        simpa only [Prod.fst_mul, Prod.snd_mul, map_mul, ContinuousLinearMap.mul_def] using
          mapLCompletion_comp (π g.1) (π h.1) (ρ g.2) (ρ h.2) }

variable {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 H W}

/-- The pair `(g, h)` acts on the completed tensor product by `π g ⊗ ρ h`. -/
@[simp]
theorem externalTensorCompletion_apply (g : G × H) :
    π.externalTensorCompletion ρ g = mapLCompletion (π g.1) (ρ g.2) :=
  (rfl)

/-- On a pure tensor the pair `(g, h)` acts by `v ⊗ w ↦ π g v ⊗ ρ h w`. -/
theorem externalTensorCompletion_apply_coe_tmul (g : G × H) (v : V) (w : W) :
    π.externalTensorCompletion ρ g (v ⊗ₜ[𝕜] w : V ⊗[𝕜] W) =
      (π g.1 v ⊗ₜ[𝕜] ρ g.2 w : V ⊗[𝕜] W) := by
  simp

/-- **The external tensor product of unitary representations is unitary**: the extension to the
completion of the tensor product of two isometries is an isometry. -/
theorem IsUnitary.externalTensorCompletion (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) :
    (π.externalTensorCompletion ρ).IsUnitary := by
  refine (isUnitary_iff_norm_map _).mpr fun g u ↦ ?_
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq ((π.externalTensorCompletion ρ g).continuous.norm) continuous_norm
  | ih a =>
    rw [externalTensorCompletion_apply, mapLCompletion_coe, Completion.norm_coe,
      Completion.norm_coe]
    simpa using TensorProduct.norm_map
      (((π g.1) : V →ₗ[𝕜] V).isometryOfInner (hπ.inner_map_map g.1))
      (((ρ g.2) : W →ₗ[𝕜] W).isometryOfInner (hρ.inner_map_map g.2)) a

/-- **The external tensor product of strongly continuous representations is strongly continuous**,
when the operators of both factors are uniformly bounded, for instance for unitary
representations (`ContRepresentation.IsUnitary.exists_norm_le`). -/
theorem continuous_externalTensorCompletion_apply [TopologicalSpace G] [TopologicalSpace H]
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun h ↦ ρ h w)
    (hπb : ∃ C, ∀ g, ‖π g‖ ≤ C) (hρb : ∃ C, ∀ h, ‖ρ h‖ ≤ C) (u : Completion (V ⊗[𝕜] W)) :
    Continuous fun p ↦ π.externalTensorCompletion ρ p u := by
  obtain ⟨C, hC⟩ := hπb
  obtain ⟨D, hD⟩ := hρb
  refine ContinuousLinearMap.continuous_apply_of_dense_span
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (dense_span_coe_tmul 𝕜 V W))
    (fun p ↦ (norm_mapLCompletion_le _ _).trans
      (mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC p.1))))
    ?_ u
  rintro _ ⟨⟨v, w⟩, rfl⟩
  exact (((Completion.continuous_coe (V ⊗[𝕜] W)).comp continuous_tmul).comp
    (((hπ v).comp continuous_fst).prodMk ((hρ w).comp continuous_snd))).congr
    fun p ↦ (externalTensorCompletion_apply_coe_tmul p v w).symm

end ContRepresentation

namespace ContIntertwiningMap

open ContRepresentation

section Monoid

variable {𝕜 G H V₀ V₁ W₀ W₁ : Type*} [RCLike 𝕜] [Monoid G] [Monoid H]
  [NormedAddCommGroup V₀] [InnerProductSpace 𝕜 V₀] [NormedAddCommGroup V₁] [InnerProductSpace 𝕜 V₁]
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁]
  {π₀ : ContRepresentation 𝕜 G V₀} {π₁ : ContRepresentation 𝕜 G V₁}
  {ρ₀ : ContRepresentation 𝕜 H W₀} {ρ₁ : ContRepresentation 𝕜 H W₁}

/-- **The tensor product of two intertwining maps** `A : π₀ →ⁱL π₁` and `B : ρ₀ →ⁱL ρ₁`, the
operator `A ⊗ B` of `TensorProduct.mapLCompletion` on the completed tensor products, intertwines
the external tensor products `π₀ ⊠̂ ρ₀` and `π₁ ⊠̂ ρ₁`. -/
def externalTensorCompletion (A : π₀ →ⁱL π₁) (B : ρ₀ →ⁱL ρ₁) :
    π₀.externalTensorCompletion ρ₀ →ⁱL π₁.externalTensorCompletion ρ₁ where
  toContinuousLinearMap :=
    TensorProduct.mapLCompletion A.toContinuousLinearMap B.toContinuousLinearMap
  isIntertwining' g := by
    simp only [ContRepresentation.externalTensorCompletion_apply, ← mapLCompletion_comp,
      A.isIntertwining', B.isIntertwining']

/-- The underlying operator of `A ⊗ B` is the tensor product of the underlying operators. -/
@[simp]
theorem toContinuousLinearMap_externalTensorCompletion (A : π₀ →ⁱL π₁) (B : ρ₀ →ⁱL ρ₁) :
    (A.externalTensorCompletion B).toContinuousLinearMap =
      TensorProduct.mapLCompletion A.toContinuousLinearMap B.toContinuousLinearMap :=
  (rfl)

/-- The intertwining map `A ⊗ B` applies as the tensor product of the underlying operators. -/
@[simp]
theorem externalTensorCompletion_apply (A : π₀ →ⁱL π₁) (B : ρ₀ →ⁱL ρ₁)
    (u : Completion (V₀ ⊗[𝕜] W₀)) :
    A.externalTensorCompletion B u =
      TensorProduct.mapLCompletion A.toContinuousLinearMap B.toContinuousLinearMap u :=
  (rfl)

/-- The amplification `A ⊗ 1` of an intertwining map `A : π₀ →ⁱL π₁` intertwines `π₀ ⊠̂ ρ` and
`π₁ ⊠̂ ρ`. -/
theorem rTensorCompletion_comp_externalTensorCompletion (A : π₀ →ⁱL π₁)
    (ρ : ContRepresentation 𝕜 H W₀) (g : G × H) :
    A.toContinuousLinearMap.rTensorCompletion W₀ ∘L π₀.externalTensorCompletion ρ g =
      π₁.externalTensorCompletion ρ g ∘L A.toContinuousLinearMap.rTensorCompletion W₀ := by
  simpa only [toContinuousLinearMap_externalTensorCompletion, toContinuousLinearMap_id,
    ← ContinuousLinearMap.rTensorCompletion_eq_mapLCompletion] using
    (A.externalTensorCompletion (ContIntertwiningMap.id : ρ →ⁱL ρ)).isIntertwining' g

/-- The amplification `1 ⊗ B` of an intertwining map `B : ρ₀ →ⁱL ρ₁` intertwines `π ⊠̂ ρ₀` and
`π ⊠̂ ρ₁`. -/
theorem lTensorCompletion_comp_externalTensorCompletion (B : ρ₀ →ⁱL ρ₁)
    (π : ContRepresentation 𝕜 G V₀) (g : G × H) :
    B.toContinuousLinearMap.lTensorCompletion V₀ ∘L π.externalTensorCompletion ρ₀ g =
      π.externalTensorCompletion ρ₁ g ∘L B.toContinuousLinearMap.lTensorCompletion V₀ := by
  simpa only [toContinuousLinearMap_externalTensorCompletion, toContinuousLinearMap_id,
    ← ContinuousLinearMap.lTensorCompletion_eq_mapLCompletion] using
    ((ContIntertwiningMap.id : π →ⁱL π).externalTensorCompletion B).isIntertwining' g

end Monoid

section Group

variable {𝕜 G H V₀ V₁ W₀ W₁ : Type*} [RCLike 𝕜] [Group G] [Group H]
  [NormedAddCommGroup V₀] [InnerProductSpace 𝕜 V₀] [CompleteSpace V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace 𝕜 V₁] [CompleteSpace V₁]
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  {π₀ : ContRepresentation 𝕜 G V₀} {π₁ : ContRepresentation 𝕜 G V₁}
  {ρ₀ : ContRepresentation 𝕜 H W₀} {ρ₁ : ContRepresentation 𝕜 H W₁}

/-- **The external product block is equivariant.** For intertwining maps `A : π₀ →ⁱL π₁` and
`B : ρ₀ →ⁱL ρ₁` between unitary representations of the groups `G` and `H`, the external product
block

`D = [[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]] : (V₀ ⊗̂ W₀) ⊕ (V₁ ⊗̂ W₁) → (V₁ ⊗̂ W₀) ⊕ (V₀ ⊗̂ W₁)`

of `ContinuousLinearMap.externalProductBlockCompletion` intertwines the Hilbert direct sums
`(π₀ ⊠̂ ρ₀) ⊕ (π₁ ⊠̂ ρ₁)` and `(π₁ ⊠̂ ρ₀) ⊕ (π₀ ⊠̂ ρ₁)` of representations of `G × H`. Unitarity
makes the adjoints `A†` and `B†` intertwining maps (`ContIntertwiningMap.adjoint`). -/
def externalProductBlockCompletion (A : π₀ →ⁱL π₁) (B : ρ₀ →ⁱL ρ₁) (hπ₀ : π₀.IsUnitary)
    (hπ₁ : π₁.IsUnitary) (hρ₀ : ρ₀.IsUnitary) (hρ₁ : ρ₁.IsUnitary) :
    (π₀.externalTensorCompletion ρ₀).withLpProd 2 (π₁.externalTensorCompletion ρ₁) →ⁱL
      (π₁.externalTensorCompletion ρ₀).withLpProd 2 (π₀.externalTensorCompletion ρ₁) where
  toContinuousLinearMap :=
    ContinuousLinearMap.externalProductBlockCompletion A.toContinuousLinearMap
      B.toContinuousLinearMap
  isIntertwining' g := by
    have hA := DFunLike.congr_fun (A.rTensorCompletion_comp_externalTensorCompletion ρ₀ g)
    have hA' := DFunLike.congr_fun
      ((A.adjoint hπ₀ hπ₁).rTensorCompletion_comp_externalTensorCompletion ρ₁ g)
    have hB := DFunLike.congr_fun (B.lTensorCompletion_comp_externalTensorCompletion π₀ g)
    have hB' := DFunLike.congr_fun
      ((B.adjoint hρ₀ hρ₁).lTensorCompletion_comp_externalTensorCompletion π₁ g)
    simp only [ContinuousLinearMap.comp_apply, toContinuousLinearMap_adjoint] at hA hA' hB hB'
    ext w : 1
    simp [ContinuousLinearMap.externalProductBlockCompletion_apply, hA, hA', hB, hB',
      -ContRepresentation.externalTensorCompletion_apply]

/-- The underlying operator of the equivariant external product block is
`ContinuousLinearMap.externalProductBlockCompletion`. -/
@[simp]
theorem toContinuousLinearMap_externalProductBlockCompletion (A : π₀ →ⁱL π₁) (B : ρ₀ →ⁱL ρ₁)
    (hπ₀ : π₀.IsUnitary) (hπ₁ : π₁.IsUnitary) (hρ₀ : ρ₀.IsUnitary) (hρ₁ : ρ₁.IsUnitary) :
    (A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).toContinuousLinearMap =
      ContinuousLinearMap.externalProductBlockCompletion A.toContinuousLinearMap
        B.toContinuousLinearMap :=
  (rfl)

/-- The equivariant external product block applies as
`ContinuousLinearMap.externalProductBlockCompletion`. -/
@[simp]
theorem externalProductBlockCompletion_apply (A : π₀ →ⁱL π₁) (B : ρ₀ →ⁱL ρ₁)
    (hπ₀ : π₀.IsUnitary) (hπ₁ : π₁.IsUnitary) (hρ₀ : ρ₀.IsUnitary) (hρ₁ : ρ₁.IsUnitary)
    (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) :
    A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁ w =
      ContinuousLinearMap.externalProductBlockCompletion A.toContinuousLinearMap
        B.toContinuousLinearMap w :=
  (rfl)

end Group

end ContIntertwiningMap
