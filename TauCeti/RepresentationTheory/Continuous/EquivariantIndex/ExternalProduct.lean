/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.EquivariantIndex
public import TauCeti.RepresentationTheory.Continuous.TensorProduct
public import TauCeti.RepresentationTheory.Continuous.TensorProduct.Completion
public import TauCeti.RepresentationTheory.Continuous.Unitary.HilbertSum
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous.External
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous.Prod
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The equivariant index of an external product

Let `A : π₀ →ⁱL π₁` be an intertwining map between unitary representations of a group `G` on Hilbert
spaces `V₀`, `V₁`, and `B : ρ₀ →ⁱL ρ₁` one between unitary representations of a group `H` on
Hilbert spaces `W₀`, `W₁`. Their *external product block*

`D = [[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]] : (V₀ ⊗̂ W₀) ⊕ (V₁ ⊗̂ W₁) → (V₁ ⊗̂ W₀) ⊕ (V₀ ⊗̂ W₁)`

(`ContIntertwiningMap.externalProductBlockCompletion`) intertwines the actions of `G × H`. It is the
even-to-odd part of the graded tensor product `D_A ⊗ 1 + Γ ⊗ D_B`, the operator by which Atiyah and
Singer multiply a `G`-equivariant elliptic operator and an `H`-equivariant one. This file proves
that **the equivariant index is multiplicative**: when `A` and `B` are Fredholm and the four
representations strongly continuous,

`ind_{G × H} D = ind_G A ⊠ ind_H B`

in the representation ring of continuous finite-dimensional representations of `G × H`
(`ContIntertwiningMap.equivariantIndex_externalProductBlockCompletion`). This refines the
multiplicativity of the Fredholm index (`ContinuousLinearMap.index_externalProductBlockCompletion`),
which is its character at the identity.

The proof makes the kernel computations of
`ContinuousLinearMap.kerExternalProductBlockCompletionEquiv` and
`ContinuousLinearMap.kerAdjointExternalProductBlockCompletionEquiv` equivariant:

`ker D ≅ (ker A ⊠ ker B) ⊕ (ker A† ⊠ ker B†)` and
`ker D† ≅ (ker A† ⊠ ker B) ⊕ (ker A ⊠ ker B†)`

as representations of `G × H`
(`ContIntertwiningMap.kerExternalProductBlockCompletionEquiv_kerRepresentation_apply`,
`ContIntertwiningMap.kerAdjointExternalProductBlockCompletionEquiv_kerRepresentation_apply`). Since
`ind T = [ker T] - [ker T†]` for unitary representations
(`ContIntertwiningMap.equivariantIndex_eq_sub_ker_adjoint`), and the class of the external tensor
product `σ ⊠ τ` of two continuous finite-dimensional representations is the external product of
their classes (`ContRepresentation.contRepRingExternalTensor_of_ofContRepresentation`), both sides
expand to

`[ker A ⊠ ker B] + [ker A† ⊠ ker B†] - [ker A† ⊠ ker B] - [ker A ⊠ ker B†]`.

## Main definitions

* `ContIntertwiningMap.kerExternalProductBlockCompletionEquiv` and
  `ContIntertwiningMap.kerAdjointExternalProductBlockCompletionEquiv`: the kernels of `D` and of its
  adjoint as products of tensor products of kernels.

## Main statements

* `ContRepresentation.contRepRingExternalTensor_of_ofContRepresentation`: the class of `σ ⊠ τ` is
  the external product of the classes of `σ` and `τ`.
* `ContIntertwiningMap.kerExternalProductBlockCompletionEquiv_kerRepresentation_apply` and
  `ContIntertwiningMap.kerAdjointExternalProductBlockCompletionEquiv_kerRepresentation_apply`: these
  identifications are equivariant for `G × H`.
* `ContIntertwiningMap.equivariantIndex_externalProductBlockCompletion`: the equivariant index of
  the external product block is the external product of the equivariant indices.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §9, for the product of a `G`-equivariant and an `H`-equivariant elliptic operator and
  the multiplicativity of its index in `R(G × H)`.
-/

public section

noncomputable section

open CategoryTheory UniformSpace TensorProduct TauCeti

namespace ContRepresentation

variable {𝕜 G H X Y : Type*} [RCLike 𝕜] [Monoid G] [Monoid H]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

variable (σ : ContRepresentation 𝕜 G X) (τ : ContRepresentation 𝕜 H Y)

/-- **The class of an external tensor product.** For continuous representations `σ` of `G` and `τ`
of `H` on finite-dimensional inner product spaces, the class of the external tensor product
`σ ⊠ τ` in the representation ring of `G × H` is the external product of the classes of `σ` and
`τ`. -/
theorem contRepRingExternalTensor_of_ofContRepresentation [TopologicalSpace G]
    [TopologicalSpace H] [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y] (hσ : Continuous σ)
    (hτ : Continuous τ) :
    contRepRingExternalTensor 𝕜 G H (SplitK0.of (ContFDRep.ofContRepresentation σ hσ))
        (SplitK0.of (ContFDRep.ofContRepresentation τ hτ)) =
      SplitK0.of (ContFDRep.ofContRepresentation (σ.externalTensor τ)
        (continuous_externalTensor σ τ hσ hτ)) := by
  rw [contRepRingExternalTensor_of_of]
  refine SplitK0.of_congr (ObjectProperty.isoMk _ ?_)
  let E₁ := (ContFDRep.ofContRepresentationEquiv hσ).externalTensor
    (ContFDRep.ofContRepresentationEquiv hτ)
  let E₂ : Representation.Equiv (σ.toRepresentation.externalTensor τ.toRepresentation)
      (σ.externalTensor τ).toRepresentation :=
    .mk (LinearEquiv.refl 𝕜 _) fun g ↦ TensorProduct.ext' fun x y ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply,
        Representation.externalTensor_apply_tmul, toRepresentation_apply, externalTensor_apply,
        TensorProduct.mapL_tmul]
  let E := (E₁.trans E₂).trans
    (ContFDRep.ofContRepresentationEquiv (continuous_externalTensor σ τ hσ hτ)).symm
  exact E.toLinearEquiv.toFDRepIso fun g x ↦
    Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g x

end ContRepresentation

namespace ContIntertwiningMap

open ContRepresentation

section Monoid

variable {𝕜 G H V V' W W' : Type*} [RCLike 𝕜] [Monoid G] [Monoid H]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup V'] [InnerProductSpace 𝕜 V']
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
  {π : ContRepresentation 𝕜 G V} {π' : ContRepresentation 𝕜 G V'}
  {ρ : ContRepresentation 𝕜 H W} {ρ' : ContRepresentation 𝕜 H W'}

/-- The inclusion `ker T ⊗ ker S → V ⊗ W` intertwines the external tensor product of the kernel
representations with that of `π` and `ρ`. -/
theorem mapIncl_externalTensor_kerRepresentation_apply (T : π →ⁱL π') (S : ρ →ⁱL ρ')
    (g : G × H) (x : T.toContinuousLinearMap.ker ⊗[𝕜] S.toContinuousLinearMap.ker) :
    mapIncl T.toContinuousLinearMap.ker S.toContinuousLinearMap.ker
        (T.kerRepresentation.externalTensor S.kerRepresentation g x) =
      π.externalTensor ρ g (mapIncl _ _ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Monoid

/-- Linear equivalences `p ≃ p'` and `q ≃ q'` of submodules that preserve the underlying vectors,
such as the transports along equalities of submodules, do not change the inclusion of `p ⊗ q`
into `V ⊗ W`. -/
private theorem mapIncl_congr {𝕜 V W : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] {p p' : Submodule 𝕜 V} {q q' : Submodule 𝕜 W} (e₁ : p ≃ₗ[𝕜] p')
    (e₂ : q ≃ₗ[𝕜] q') (h₁ : ∀ v, (e₁ v : V) = v) (h₂ : ∀ w, (e₂ w : W) = w) (x : p ⊗[𝕜] q) :
    mapIncl p' q' (TensorProduct.congr e₁ e₂ x) = mapIncl p q x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [h₁, h₂]
  | add x y hx hy => simp only [map_add, hx, hy]

section Group

variable {𝕜 G H V₀ V₁ W₀ W₁ : Type*} [RCLike 𝕜] [Group G] [Group H]
  [NormedAddCommGroup V₀] [InnerProductSpace 𝕜 V₀] [CompleteSpace V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace 𝕜 V₁] [CompleteSpace V₁]
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  {π₀ : ContRepresentation 𝕜 G V₀} {π₁ : ContRepresentation 𝕜 G V₁}
  {ρ₀ : ContRepresentation 𝕜 H W₀} {ρ₁ : ContRepresentation 𝕜 H W₁}
  (A : π₀ →ⁱL π₁) (B : ρ₀ →ⁱL ρ₁) (hπ₀ : π₀.IsUnitary) (hπ₁ : π₁.IsUnitary)
  (hρ₀ : ρ₀.IsUnitary) (hρ₁ : ρ₁.IsUnitary)
  [FiniteDimensional 𝕜 A.toContinuousLinearMap.ker]
  [FiniteDimensional 𝕜 B.toContinuousLinearMap.ker]
  [FiniteDimensional 𝕜 A.toContinuousLinearMap.adjoint.ker]
  [FiniteDimensional 𝕜 B.toContinuousLinearMap.adjoint.ker]

/-- The kernel of the equivariant external product block, identified with
`(ker A ⊗ ker B) × (ker A† ⊗ ker B†)` by
`ContinuousLinearMap.kerExternalProductBlockCompletionEquiv`.
This identification is equivariant
(`ContIntertwiningMap.kerExternalProductBlockCompletionEquiv_kerRepresentation_apply`). -/
def kerExternalProductBlockCompletionEquiv :
    (A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).toContinuousLinearMap.ker ≃ₗ[𝕜]
      (A.toContinuousLinearMap.ker ⊗[𝕜] B.toContinuousLinearMap.ker) ×
        ((A.adjoint hπ₀ hπ₁).toContinuousLinearMap.ker ⊗[𝕜]
          (B.adjoint hρ₀ hρ₁).toContinuousLinearMap.ker) :=
  (LinearEquiv.ofEq _ _ (by rw [toContinuousLinearMap_externalProductBlockCompletion])).trans <|
    (ContinuousLinearMap.kerExternalProductBlockCompletionEquiv A.toContinuousLinearMap
      B.toContinuousLinearMap).trans <|
    (LinearEquiv.refl 𝕜 _).prodCongr <|
      TensorProduct.congr (.ofEq _ _ (by rw [toContinuousLinearMap_adjoint]))
        (.ofEq _ _ (by rw [toContinuousLinearMap_adjoint]))

/-- The identification of the kernel of the external product block sends a pair of tensors of
kernel vectors to the pair of the corresponding tensors. -/
@[simp]
theorem coe_kerExternalProductBlockCompletionEquiv_symm_apply
    (p : (A.toContinuousLinearMap.ker ⊗[𝕜] B.toContinuousLinearMap.ker) ×
      ((A.adjoint hπ₀ hπ₁).toContinuousLinearMap.ker ⊗[𝕜]
        (B.adjoint hρ₀ hρ₁).toContinuousLinearMap.ker)) :
    ((kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁).symm p :
        WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))) =
      WithLp.toLp 2
        (((mapIncl _ _ p.1 : V₀ ⊗[𝕜] W₀) : Completion (V₀ ⊗[𝕜] W₀)),
          ((mapIncl _ _ p.2 : V₁ ⊗[𝕜] W₁) : Completion (V₁ ⊗[𝕜] W₁))) := by
  simp only [kerExternalProductBlockCompletionEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, TensorProduct.congr_symm, LinearEquiv.ofEq_symm,
    ContinuousLinearMap.coe_kerExternalProductBlockCompletionEquiv_symm_apply,
    LinearEquiv.coe_ofEq_apply]
  rw [mapIncl_congr _ _ (fun _ ↦ by rfl) (fun _ ↦ by rfl)]

/-- The identification of the kernel of the external product block sends a kernel vector to the
tensor of kernel vectors whose inclusion is its first component. -/
@[simp]
theorem coe_mapIncl_kerExternalProductBlockCompletionEquiv_apply_fst
    (w : (A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).toContinuousLinearMap.ker) :
    ((mapIncl _ _ (kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁ w).1 :
        V₀ ⊗[𝕜] W₀) : Completion (V₀ ⊗[𝕜] W₀)) =
      (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))).fst := by
  conv_rhs => rw [← (kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁).symm_apply_apply w]
  simp only [coe_kerExternalProductBlockCompletionEquiv_symm_apply, WithLp.toLp_fst]

/-- The identification of the kernel of the external product block sends a kernel vector to the
tensor of kernel vectors whose inclusion is its second component. -/
@[simp]
theorem coe_mapIncl_kerExternalProductBlockCompletionEquiv_apply_snd
    (w : (A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).toContinuousLinearMap.ker) :
    ((mapIncl _ _ (kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁ w).2 :
        V₁ ⊗[𝕜] W₁) : Completion (V₁ ⊗[𝕜] W₁)) =
      (w : WithLp 2 (Completion (V₀ ⊗[𝕜] W₀) × Completion (V₁ ⊗[𝕜] W₁))).snd := by
  conv_rhs => rw [← (kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁).symm_apply_apply w]
  simp only [coe_kerExternalProductBlockCompletionEquiv_symm_apply, WithLp.toLp_snd]

/-- **The kernel of the external product block, equivariantly**: the identification of the kernel
of `D` with `(ker A ⊗ ker B) × (ker A† ⊗ ker B†)` intertwines the action of `G × H` on the kernel
with the external tensor products of the kernel representations of `A`, `B`, `A†` and `B†`. -/
theorem kerExternalProductBlockCompletionEquiv_kerRepresentation_apply (g : G × H)
    (w : (A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).toContinuousLinearMap.ker) :
    kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁
        ((A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).kerRepresentation g w) =
      (A.kerRepresentation.externalTensor B.kerRepresentation).prod
        ((A.adjoint hπ₀ hπ₁).kerRepresentation.externalTensor
          (B.adjoint hρ₀ hρ₁).kerRepresentation) g
        (kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁ w) := by
  set e := kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁
  set Φ := (A.kerRepresentation.externalTensor B.kerRepresentation).prod
    ((A.adjoint hπ₀ hπ₁).kerRepresentation.externalTensor (B.adjoint hρ₀ hρ₁).kerRepresentation)
  rw [← e.apply_symm_apply (Φ g (e w)), e.injective.eq_iff]
  refine Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext ?_ ?_))
  · rw [coe_kerExternalProductBlockCompletionEquiv_symm_apply, WithLp.ofLp_toLp,
      show (Φ g (e w)).1 =
        A.kerRepresentation.externalTensor B.kerRepresentation g (e w).1 by simp [Φ],
      mapIncl_externalTensor_kerRepresentation_apply, externalTensor_apply, ← mapLCompletion_coe,
      coe_mapIncl_kerExternalProductBlockCompletionEquiv_apply_fst]
    simp
  · rw [coe_kerExternalProductBlockCompletionEquiv_symm_apply, WithLp.ofLp_toLp,
      show (Φ g (e w)).2 = (A.adjoint hπ₀ hπ₁).kerRepresentation.externalTensor
        (B.adjoint hρ₀ hρ₁).kerRepresentation g (e w).2 by simp [Φ],
      mapIncl_externalTensor_kerRepresentation_apply, externalTensor_apply, ← mapLCompletion_coe,
      coe_mapIncl_kerExternalProductBlockCompletionEquiv_apply_snd]
    simp

/-- The kernel of the adjoint of the equivariant external product block, identified with
`(ker A† ⊗ ker B) × (ker A ⊗ ker B†)` by
`ContinuousLinearMap.kerAdjointExternalProductBlockCompletionEquiv`. This identification is
equivariant
(`ContIntertwiningMap.kerAdjointExternalProductBlockCompletionEquiv_kerRepresentation_apply`). -/
def kerAdjointExternalProductBlockCompletionEquiv :
    ((A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).adjoint
        ((hπ₀.externalTensorCompletion hρ₀).withLpProd (hπ₁.externalTensorCompletion hρ₁))
        ((hπ₁.externalTensorCompletion hρ₀).withLpProd
          (hπ₀.externalTensorCompletion hρ₁))).toContinuousLinearMap.ker ≃ₗ[𝕜]
      ((A.adjoint hπ₀ hπ₁).toContinuousLinearMap.ker ⊗[𝕜] B.toContinuousLinearMap.ker) ×
        (A.toContinuousLinearMap.ker ⊗[𝕜] (B.adjoint hρ₀ hρ₁).toContinuousLinearMap.ker) :=
  (LinearEquiv.ofEq _ _ (by
      rw [toContinuousLinearMap_adjoint,
        toContinuousLinearMap_externalProductBlockCompletion])).trans <|
    (ContinuousLinearMap.kerAdjointExternalProductBlockCompletionEquiv A.toContinuousLinearMap
      B.toContinuousLinearMap).trans <|
    (TensorProduct.congr (.ofEq _ _ (by rw [toContinuousLinearMap_adjoint]))
        (LinearEquiv.refl 𝕜 _)).prodCongr
      (TensorProduct.congr (LinearEquiv.refl 𝕜 _)
        (.ofEq _ _ (by rw [toContinuousLinearMap_adjoint])))

/-- The identification of the kernel of the adjoint of the external product block sends a pair of
tensors of kernel vectors to the pair of the corresponding tensors. -/
@[simp]
theorem coe_kerAdjointExternalProductBlockCompletionEquiv_symm_apply
    (p : ((A.adjoint hπ₀ hπ₁).toContinuousLinearMap.ker ⊗[𝕜] B.toContinuousLinearMap.ker) ×
      (A.toContinuousLinearMap.ker ⊗[𝕜] (B.adjoint hρ₀ hρ₁).toContinuousLinearMap.ker)) :
    ((kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁).symm p :
        WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁))) =
      WithLp.toLp 2
        (((mapIncl _ _ p.1 : V₁ ⊗[𝕜] W₀) : Completion (V₁ ⊗[𝕜] W₀)),
          ((mapIncl _ _ p.2 : V₀ ⊗[𝕜] W₁) : Completion (V₀ ⊗[𝕜] W₁))) := by
  simp only [kerAdjointExternalProductBlockCompletionEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, LinearEquiv.refl_symm,
    TensorProduct.congr_symm, LinearEquiv.ofEq_symm,
    ContinuousLinearMap.coe_kerAdjointExternalProductBlockCompletionEquiv_symm_apply,
    LinearEquiv.coe_ofEq_apply]
  rw [mapIncl_congr _ _ (fun _ ↦ by rfl) (fun _ ↦ by rfl),
    mapIncl_congr _ _ (fun _ ↦ by rfl) (fun _ ↦ by rfl)]

/-- The identification of the kernel of the adjoint of the external product block sends a kernel
vector to the tensor of kernel vectors whose inclusion is its first component. -/
@[simp]
theorem coe_mapIncl_kerAdjointExternalProductBlockCompletionEquiv_apply_fst
    (w : ((A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).adjoint
        ((hπ₀.externalTensorCompletion hρ₀).withLpProd (hπ₁.externalTensorCompletion hρ₁))
        ((hπ₁.externalTensorCompletion hρ₀).withLpProd
          (hπ₀.externalTensorCompletion hρ₁))).toContinuousLinearMap.ker) :
    ((mapIncl _ _ (kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁ w).1 :
        V₁ ⊗[𝕜] W₀) : Completion (V₁ ⊗[𝕜] W₀)) =
      (w : WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁))).fst := by
  conv_rhs =>
    rw [← (kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁).symm_apply_apply w]
  simp only [coe_kerAdjointExternalProductBlockCompletionEquiv_symm_apply, WithLp.toLp_fst]

/-- The identification of the kernel of the adjoint of the external product block sends a kernel
vector to the tensor of kernel vectors whose inclusion is its second component. -/
@[simp]
theorem coe_mapIncl_kerAdjointExternalProductBlockCompletionEquiv_apply_snd
    (w : ((A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).adjoint
        ((hπ₀.externalTensorCompletion hρ₀).withLpProd (hπ₁.externalTensorCompletion hρ₁))
        ((hπ₁.externalTensorCompletion hρ₀).withLpProd
          (hπ₀.externalTensorCompletion hρ₁))).toContinuousLinearMap.ker) :
    ((mapIncl _ _ (kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁ w).2 :
        V₀ ⊗[𝕜] W₁) : Completion (V₀ ⊗[𝕜] W₁)) =
      (w : WithLp 2 (Completion (V₁ ⊗[𝕜] W₀) × Completion (V₀ ⊗[𝕜] W₁))).snd := by
  conv_rhs =>
    rw [← (kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁).symm_apply_apply w]
  simp only [coe_kerAdjointExternalProductBlockCompletionEquiv_symm_apply, WithLp.toLp_snd]

/-- **The kernel of the adjoint of the external product block, equivariantly**: the identification
of the kernel of `D†` with `(ker A† ⊗ ker B) × (ker A ⊗ ker B†)` intertwines the action of `G × H`
on the kernel with the external tensor products of the kernel representations. -/
theorem kerAdjointExternalProductBlockCompletionEquiv_kerRepresentation_apply (g : G × H)
    (w : ((A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).adjoint
        ((hπ₀.externalTensorCompletion hρ₀).withLpProd (hπ₁.externalTensorCompletion hρ₁))
        ((hπ₁.externalTensorCompletion hρ₀).withLpProd
          (hπ₀.externalTensorCompletion hρ₁))).toContinuousLinearMap.ker) :
    kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁
        (((A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).adjoint
          ((hπ₀.externalTensorCompletion hρ₀).withLpProd (hπ₁.externalTensorCompletion hρ₁))
          ((hπ₁.externalTensorCompletion hρ₀).withLpProd
            (hπ₀.externalTensorCompletion hρ₁))).kerRepresentation g w) =
      ((A.adjoint hπ₀ hπ₁).kerRepresentation.externalTensor B.kerRepresentation).prod
        (A.kerRepresentation.externalTensor (B.adjoint hρ₀ hρ₁).kerRepresentation) g
        (kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁ w) := by
  set e := kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁
  set Φ := ((A.adjoint hπ₀ hπ₁).kerRepresentation.externalTensor B.kerRepresentation).prod
    (A.kerRepresentation.externalTensor (B.adjoint hρ₀ hρ₁).kerRepresentation)
  rw [← e.apply_symm_apply (Φ g (e w)), e.injective.eq_iff]
  refine Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext ?_ ?_))
  · rw [coe_kerAdjointExternalProductBlockCompletionEquiv_symm_apply, WithLp.ofLp_toLp,
      show (Φ g (e w)).1 = (A.adjoint hπ₀ hπ₁).kerRepresentation.externalTensor
        B.kerRepresentation g (e w).1 by simp [Φ],
      mapIncl_externalTensor_kerRepresentation_apply, externalTensor_apply, ← mapLCompletion_coe,
      coe_mapIncl_kerAdjointExternalProductBlockCompletionEquiv_apply_fst]
    simp
  · rw [coe_kerAdjointExternalProductBlockCompletionEquiv_symm_apply, WithLp.ofLp_toLp,
      show (Φ g (e w)).2 = A.kerRepresentation.externalTensor
        (B.adjoint hρ₀ hρ₁).kerRepresentation g (e w).2 by simp [Φ],
      mapIncl_externalTensor_kerRepresentation_apply, externalTensor_apply, ← mapLCompletion_coe,
      coe_mapIncl_kerAdjointExternalProductBlockCompletionEquiv_apply_snd]
    simp

end Group

section Index

variable {𝕜 G H V₀ V₁ W₀ W₁ : Type*} [RCLike 𝕜] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H]
  [NormedAddCommGroup V₀] [InnerProductSpace 𝕜 V₀] [CompleteSpace V₀]
  [NormedAddCommGroup V₁] [InnerProductSpace 𝕜 V₁] [CompleteSpace V₁]
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  {π₀ : ContRepresentation 𝕜 G V₀} {π₁ : ContRepresentation 𝕜 G V₁}
  {ρ₀ : ContRepresentation 𝕜 H W₀} {ρ₁ : ContRepresentation 𝕜 H W₁}

/-- **The equivariant index is multiplicative.** Let `A : π₀ →ⁱL π₁` and `B : ρ₀ →ⁱL ρ₁` be
Fredholm intertwining maps between strongly continuous unitary representations of groups `G` and
`H` on Hilbert spaces. The equivariant index of their external product block
`D = [[A ⊗ 1, -(1 ⊗ B†)], [1 ⊗ B, A† ⊗ 1]]`, an intertwining map of representations of `G × H`, is
the external product `ind_G A ⊠ ind_H B` of their equivariant indices. This refines
`ContinuousLinearMap.index_externalProductBlockCompletion`. -/
theorem equivariantIndex_externalProductBlockCompletion (A : π₀ →ⁱL π₁) (B : ρ₀ →ⁱL ρ₁)
    (hA : A.toContinuousLinearMap.IsFredholm) (hB : B.toContinuousLinearMap.IsFredholm)
    (hπ₀ : π₀.IsUnitary) (hπ₁ : π₁.IsUnitary) (hρ₀ : ρ₀.IsUnitary) (hρ₁ : ρ₁.IsUnitary)
    (hπ₀c : ∀ v, Continuous fun g ↦ π₀ g v) (hπ₁c : ∀ v, Continuous fun g ↦ π₁ g v)
    (hρ₀c : ∀ w, Continuous fun h ↦ ρ₀ h w) (hρ₁c : ∀ w, Continuous fun h ↦ ρ₁ h w) :
    (A.externalProductBlockCompletion B hπ₀ hπ₁ hρ₀ hρ₁).equivariantIndex
        (by
          rw [toContinuousLinearMap_externalProductBlockCompletion]
          exact hA.externalProductBlockCompletion hB)
        (continuous_withLpProd_apply
          (continuous_externalTensorCompletion_apply hπ₀c hρ₀c hπ₀.exists_norm_le
            hρ₀.exists_norm_le)
          (continuous_externalTensorCompletion_apply hπ₁c hρ₁c hπ₁.exists_norm_le
            hρ₁.exists_norm_le))
        (continuous_withLpProd_apply
          (continuous_externalTensorCompletion_apply hπ₁c hρ₀c hπ₁.exists_norm_le
            hρ₀.exists_norm_le)
          (continuous_externalTensorCompletion_apply hπ₀c hρ₁c hπ₀.exists_norm_le
            hρ₁.exists_norm_le)) =
      contRepRingExternalTensor 𝕜 G H (A.equivariantIndex hA hπ₀c hπ₁c)
        (B.equivariantIndex hB hρ₀c hρ₁c) := by
  have := hA.finite_ker
  have := hB.finite_ker
  have := hA.adjoint.finite_ker
  have := hB.adjoint.finite_ker
  have : FiniteDimensional 𝕜 (A.adjoint hπ₀ hπ₁).toContinuousLinearMap.ker := by
    rw [toContinuousLinearMap_adjoint]
    exact hA.adjoint.finite_ker
  have : FiniteDimensional 𝕜 (B.adjoint hρ₀ hρ₁).toContinuousLinearMap.ker := by
    rw [toContinuousLinearMap_adjoint]
    exact hB.adjoint.finite_ker
  have := (kerExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁).symm.finiteDimensional
  have := (kerAdjointExternalProductBlockCompletionEquiv A B hπ₀ hπ₁ hρ₀ hρ₁).symm.finiteDimensional
  have hkA := A.continuous_kerRepresentation hπ₀c
  have hkB := B.continuous_kerRepresentation hρ₀c
  have hkA' := (A.adjoint hπ₀ hπ₁).continuous_kerRepresentation hπ₁c
  have hkB' := (B.adjoint hρ₀ hρ₁).continuous_kerRepresentation hρ₁c
  rw [equivariantIndex_eq_sub_ker_adjoint _ _ _ _
      ((hπ₀.externalTensorCompletion hρ₀).withLpProd (hπ₁.externalTensorCompletion hρ₁))
      ((hπ₁.externalTensorCompletion hρ₀).withLpProd (hπ₀.externalTensorCompletion hρ₁)),
    A.equivariantIndex_eq_sub_ker_adjoint hA hπ₀c hπ₁c hπ₀ hπ₁,
    B.equivariantIndex_eq_sub_ker_adjoint hB hρ₀c hρ₁c hρ₀ hρ₁]
  simp only [map_sub, AddMonoidHom.sub_apply]
  rw [contRepRingExternalTensor_of_ofContRepresentation _ _ hkA hkB,
    contRepRingExternalTensor_of_ofContRepresentation _ _ hkA hkB',
    contRepRingExternalTensor_of_ofContRepresentation _ _ hkA' hkB,
    contRepRingExternalTensor_of_ofContRepresentation _ _ hkA' hkB',
    SplitK0.of_congr (ContFDRep.ofContRepresentationIso _
      (kerExternalProductBlockCompletionEquiv_kerRepresentation_apply A B hπ₀ hπ₁ hρ₀ hρ₁) _
      (continuous_prod _ _ (continuous_externalTensor _ _ hkA hkB)
        (continuous_externalTensor _ _ hkA' hkB'))),
    SplitK0.of_congr (ContFDRep.ofContRepresentationIso _
      (kerAdjointExternalProductBlockCompletionEquiv_kerRepresentation_apply A B hπ₀ hπ₁ hρ₀ hρ₁) _
      (continuous_prod _ _ (continuous_externalTensor _ _ hkA' hkB)
        (continuous_externalTensor _ _ hkA hkB'))),
    contRepRing_of_prod, contRepRing_of_prod]
  abel

end Index

end ContIntertwiningMap
