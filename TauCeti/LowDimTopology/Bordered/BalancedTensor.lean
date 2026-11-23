/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Pi
public import TauCeti.LowDimTopology.Bordered.InducedModule

/-!
# The box tensor product as a balanced tensor product

For a differential right module `(M, dM)` over a differential algebra `(A, d)` with idempotents
`ι` and a type `D` structure `N` over `A`, the box tensor product `M ⊠ N` of
`TauCeti.LowDimTopology.Bordered.TypeD` is the ordinary tensor product over `A` of `M` with the
differential left module `A ⊠ N` induced by `N` (`TauCeti.TypeDStructure.inducedModule`):

`M ⊠ N ≅ M ⊗_A (A ⊠ N)`, `m ⊗ (a ⊗ x) ↦ m * a ⊗ x`,

as complexes, where `M ⊗_A (A ⊠ N)` (`TauCeti.BalancedTensorProduct`) carries the tensor
differential `dM ⊗ 1 + 1 ⊗ ∂` (`TauCeti.BalancedTensorProduct.ungradedDifferential`). This compares
the box tensor product of Lipshitz, Ozsváth and Thurston with the ordinary tensor product of
differential modules: the box tensor product of `M` with `N` is the tensor product of `M` with a
module which is projective over `A`.

In the basis of generators `x : X` of `N`, `M ⊠ N` is the module `TauCeti.TypeDStructure.boxTensor`
of row vectors `φ : X → M` with `φ x * ι (idem x) = φ x`, and `A ⊠ N` the left module of such row
vectors with entries in `A`. When the `ι s` are idempotents, `A ⊠ N` is a direct summand of the
free module `X → A`: the projection `φ ↦ (x ↦ φ x * ι (idem x))`
(`TauCeti.TypeDStructure.inducedProj`) retracts the inclusion, so `A ⊠ N` is a projective left
`A`-module (`TauCeti.TypeDStructure.projective_inducedModule`). Tensoring this splitting with `M`
and using `M ⊗_A (X → A) ≅ (X → M)` (`TauCeti.BalancedTensorProduct.piRight`) identifies
`M ⊗_A (A ⊠ N)` with the row vectors fixed by the idempotents, which is `M ⊠ N`
(`TauCeti.TypeDStructure.balancedTensorEquiv`). Its inverse sends `φ` to `∑ x, φ x ⊗ (1 ⊗ x)`,
with `1 ⊗ x` the generator `TauCeti.TypeDStructure.generator`.

When moreover the `ι s` are cycles, the identification carries the tensor differential to the box
tensor differential `∂ φ = dM φ + φ ⬝ δ`
(`TauCeti.TypeDStructure.balancedTensorEquiv_ungradedDifferential`). It is natural in both
variables: an equivariant map `f : M → M'` acts on row vectors entrywise
(`TauCeti.TypeDStructure.coe_balancedTensorEquiv_map_id_right`), and a morphism `F` of type `D`
structures, acting on `A ⊠ N` by `TauCeti.TypeDStructure.inducedHom`, acts on row vectors by
`φ ↦ φ ⬝ F` (`TauCeti.TypeDStructure.coe_balancedTensorEquiv_map_inducedHom`).

## Main definitions

* `TauCeti.TypeDStructure.inducedProj`: the projection of the row vectors `X → A` onto `A ⊠ N`.
* `TauCeti.TypeDStructure.balancedTensorEquiv`: the identification `M ⊗_A (A ⊠ N) ≃ M ⊠ N`.

## Main results

* `TauCeti.TypeDStructure.projective_inducedModule`: `A ⊠ N` is a projective left `A`-module.
* `TauCeti.TypeDStructure.coe_balancedTensorEquiv_tmul`,
  `TauCeti.TypeDStructure.balancedTensorEquiv_symm_apply`: the identification and its inverse on
  pure tensors and on row vectors.
* `TauCeti.TypeDStructure.balancedTensorEquiv_ungradedDifferential`: it is an isomorphism of
  complexes.
* `TauCeti.TypeDStructure.coe_balancedTensorEquiv_map_id_right`,
  `TauCeti.TypeDStructure.coe_balancedTensorEquiv_map_inducedHom`: it is natural in the module
  and in the type `D` structure.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (the differential module `A ⊠ N` induced by a type `D` structure, and the box tensor
  product with a differential module as a tensor product over `A`).
-/

public section

open MulOpposite

namespace TauCeti

namespace TypeDStructure

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {d : A →ₗ[R] A} {S : Type*}
  {ι : S → A} {X X' : Type*} [Fintype X] [Fintype X']
  {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'}

/-! ### The induced module as a direct summand of a free module -/

variable (N) in
/-- The **projection onto the induced module** `A ⊠ N` of the free left module of row vectors,
`φ ↦ (x ↦ φ x * ι (idem x))`, when the `ι s` are idempotents. -/
def inducedProj (hι : ∀ s, IsIdempotentElem (ι s)) : (X → A) →ₗ[A] N.inducedModule where
  toFun φ := ⟨fun x => φ x * ι (N.idem x),
    mem_inducedModule_iff.mpr fun x => by rw [mul_assoc, (hι _).eq]⟩
  map_add' φ ψ := Subtype.ext <| funext fun x => add_mul _ _ _
  map_smul' b φ := Subtype.ext <| funext fun x => mul_assoc _ _ _

@[simp]
theorem coe_inducedProj_apply (hι : ∀ s, IsIdempotentElem (ι s)) (φ : X → A) :
    (N.inducedProj hι φ : X → A) = fun x => φ x * ι (N.idem x) :=
  (rfl)

/-- The projection restricts to the identity on `A ⊠ N`. -/
@[simp]
theorem inducedProj_coe (hι : ∀ s, IsIdempotentElem (ι s)) (φ : N.inducedModule) :
    N.inducedProj hι φ = φ :=
  Subtype.ext <| funext <| mem_inducedModule_iff.mp φ.property

/-- The projection retracts the inclusion of `A ⊠ N` into the row vectors. -/
theorem inducedProj_comp_subtype (hι : ∀ s, IsIdempotentElem (ι s)) :
    N.inducedProj hι ∘ₗ N.inducedModule.subtype = LinearMap.id :=
  LinearMap.ext (inducedProj_coe hι)

/-- The projection sends the coordinate row vector at `x` to the generator `1 ⊗ x`. -/
theorem inducedProj_single [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s)) (x : X) :
    N.inducedProj hι (Pi.single x 1) = N.generator hι x := by
  ext y
  rcases eq_or_ne y x with rfl | h
  · simp
  · simp [h]

variable (N) in
/-- **The induced module is projective**: when the `ι s` are idempotents, `A ⊠ N` is a direct
summand of the free left module `X → A`. -/
theorem projective_inducedModule (hι : ∀ s, IsIdempotentElem (ι s)) :
    Module.Projective A N.inducedModule :=
  .of_split N.inducedModule.subtype (N.inducedProj hι) (inducedProj_comp_subtype hι)

/-! ### The box tensor product as a balanced tensor product -/

section BalancedTensor

variable {M M' : Type*} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  [IsScalarTower R Aᵐᵒᵖ M] [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M']
  [SMulCommClass R Aᵐᵒᵖ M'] [IsScalarTower R Aᵐᵒᵖ M']

/-- Tensoring with `M` the inclusion of `A ⊠ N` into the row vectors, read in `X → M`:
`m ⊗ ψ ↦ (x ↦ m * ψ x)`. -/
private noncomputable def toRowVectors (N : TypeDStructure d ι X) (M : Type*) [AddCommGroup M]
    [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] :
    BalancedTensorProduct R A M N.inducedModule →ₗ[R] X → M :=
  (BalancedTensorProduct.piRight R A M X).toLinearMap ∘ₗ
    BalancedTensorProduct.lTensor R M N.inducedModule.subtype

private theorem toRowVectors_tmul (m : M) (ψ : N.inducedModule) :
    toRowVectors N M (BalancedTensorProduct.tmul R A m ψ) = fun x => op ((ψ : X → A) x) • m := by
  simp [toRowVectors]

private theorem toRowVectors_mem (z : BalancedTensorProduct R A M N.inducedModule) :
    toRowVectors N M z ∈ N.boxTensor M := by
  induction z using BalancedTensorProduct.induction_on with
  | ht m ψ =>
    refine mem_boxTensor_iff.mpr fun x => ?_
    rw [toRowVectors_tmul, smul_smul, ← op_mul, mem_inducedModule_iff.mp ψ.property x]
  | ha z z' hz hz' => exact map_add (toRowVectors N M) z z' ▸ add_mem hz hz'

/-- Tensoring with `M` the projection onto `A ⊠ N`, read on `X → M`. -/
private noncomputable def fromRowVectors (N : TypeDStructure d ι X) (M : Type*) [AddCommGroup M]
    [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
    (hι : ∀ s, IsIdempotentElem (ι s)) :
    (X → M) →ₗ[R] BalancedTensorProduct R A M N.inducedModule :=
  BalancedTensorProduct.lTensor R M (N.inducedProj hι) ∘ₗ
    (BalancedTensorProduct.piRight R A M X).symm.toLinearMap

private theorem fromRowVectors_toRowVectors (hι : ∀ s, IsIdempotentElem (ι s))
    (z : BalancedTensorProduct R A M N.inducedModule) :
    fromRowVectors N M hι (toRowVectors N M z) = z := by
  induction z using BalancedTensorProduct.induction_on with
  -- Cancel `piRight` against its inverse rather than evaluating it on the pure tensor.
  | ht m ψ => simp [fromRowVectors, toRowVectors, -BalancedTensorProduct.piRight_tmul]
  | ha z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- On row vectors, `fromRowVectors` is `φ ↦ ∑ x, φ x ⊗ (1 ⊗ x)`. -/
private theorem fromRowVectors_apply [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s))
    (φ : X → M) :
    fromRowVectors N M hι φ = ∑ x, BalancedTensorProduct.tmul R A (φ x) (N.generator hι x) := by
  simp [fromRowVectors, BalancedTensorProduct.piRight_symm_apply, inducedProj_single]

private theorem toRowVectors_fromRowVectors (hι : ∀ s, IsIdempotentElem (ι s)) {φ : X → M}
    (hφ : φ ∈ N.boxTensor M) : toRowVectors N M (fromRowVectors N M hι φ) = φ := by
  classical
  ext y
  simpa [fromRowVectors_apply, toRowVectors_tmul, Pi.single_apply, apply_ite op] using
    mem_boxTensor_iff.mp hφ y

variable (N M) in
/-- **The box tensor product is the balanced tensor product with the induced module**: when the
`ι s` are idempotents, `M ⊗_A (A ⊠ N) ≃ M ⊠ N` by `m ⊗ ψ ↦ (x ↦ m * ψ x)`, that is
`m ⊗ (a ⊗ x) ↦ m * a ⊗ x`. -/
noncomputable def balancedTensorEquiv (hι : ∀ s, IsIdempotentElem (ι s)) :
    BalancedTensorProduct R A M N.inducedModule ≃ₗ[R] N.boxTensor M where
  toFun z := ⟨toRowVectors N M z, toRowVectors_mem z⟩
  map_add' z z' := Subtype.ext (map_add _ z z')
  map_smul' r z := Subtype.ext (map_smul _ r z)
  invFun φ := fromRowVectors N M hι φ
  left_inv := fromRowVectors_toRowVectors hι
  right_inv φ := Subtype.ext (toRowVectors_fromRowVectors hι φ.property)

@[simp]
theorem coe_balancedTensorEquiv_tmul (hι : ∀ s, IsIdempotentElem (ι s)) (m : M)
    (ψ : N.inducedModule) :
    (balancedTensorEquiv N M hι (BalancedTensorProduct.tmul R A m ψ) : X → M) =
      fun x => op ((ψ : X → A) x) • m :=
  toRowVectors_tmul m ψ

/-- The inverse of `balancedTensorEquiv` sends a row vector `φ` to `∑ x, φ x ⊗ (1 ⊗ x)`. -/
theorem balancedTensorEquiv_symm_apply [DecidableEq X] (hι : ∀ s, IsIdempotentElem (ι s))
    (φ : N.boxTensor M) :
    (balancedTensorEquiv N M hι).symm φ =
      ∑ x, BalancedTensorProduct.tmul R A ((φ : X → M) x) (N.generator hι x) :=
  fromRowVectors_apply (N := N) hι (φ : X → M)

/-- **The identification is an isomorphism of complexes**: when the `ι s` are idempotent cycles,
it carries the tensor differential `dM ⊗ 1 + 1 ⊗ ∂` of `M ⊗_A (A ⊠ N)` to the box tensor
differential `∂ φ = dM φ + φ ⬝ δ` of `M ⊠ N`. -/
theorem balancedTensorEquiv_ungradedDifferential (hd : IsUngradedDGAlgebra d)
    (hidem : ∀ s, IsIdempotentElem (ι s)) (hι : ∀ s, d (ι s) = 0) {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (z : BalancedTensorProduct R A M N.inducedModule) :
    balancedTensorEquiv N M hidem
        (BalancedTensorProduct.ungradedDifferential hM.map_smul (inducedDifferential_smul hd hι)
          z) =
      N.boxTensorDifferential hι hM (balancedTensorEquiv N M hidem z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht m ψ =>
    ext x
    simp only [BalancedTensorProduct.ungradedDifferential_tmul, map_add, Submodule.coe_add,
      coe_balancedTensorEquiv_tmul, coe_inducedDifferential_apply, coe_boxTensorDifferential_apply,
      boxDifferential_apply, Pi.add_apply, hM.map_smul,
      continuationMap_apply (R := R) (M := A) N.coeff,
      continuationMap_apply (R := R) (M := M) N.coeff, op_smul_eq_mul, op_add,
      add_smul, Finset.op_sum, Finset.sum_smul, smul_smul, ← op_mul]
    abel
  | ha z z' hz hz' => simp only [map_add, hz, hz']

/-- **Naturality in the module**: an equivariant map `f : M → M'` acts on `M ⊗_A (A ⊠ N)` as
`f ⊗ 1` and on `M ⊠ N` entrywise. -/
theorem coe_balancedTensorEquiv_map_id_right (hι : ∀ s, IsIdempotentElem (ι s)) (f : M →ₗ[R] M')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (z : BalancedTensorProduct R A M N.inducedModule) :
    (balancedTensorEquiv N M' hι (BalancedTensorProduct.map f LinearMap.id hf (fun _ _ => rfl) z) :
        X → M') =
      fun x => f ((balancedTensorEquiv N M hι z : X → M) x) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht m ψ =>
    ext x
    simp [hf]
  | ha z z' hz hz' =>
    ext x
    simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']

/-- **Naturality in the type `D` structure**: a morphism `F` from `N` to `N'` acts on
`M ⊗_A (A ⊠ N)` as `1 ⊗ T_F`, through the map `T_F` of induced modules, and on `M ⊠ N` by
`φ ↦ φ ⬝ F`. -/
theorem coe_balancedTensorEquiv_map_inducedHom (hι : ∀ s, IsIdempotentElem (ι s))
    (F : morphisms N N') (z : BalancedTensorProduct R A M N.inducedModule) :
    (balancedTensorEquiv N' M hι (BalancedTensorProduct.lTensor R M (inducedHom N N' F) z) :
        X' → M) =
      continuationMap R M (F : Matrix X X' A) (balancedTensorEquiv N M hι z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht m ψ =>
    ext y
    simp only [BalancedTensorProduct.lTensor_tmul, coe_balancedTensorEquiv_tmul,
      coe_inducedHom_apply, continuationMap_apply (R := R) (M := A) (F : Matrix X X' A),
      continuationMap_apply (R := R) (M := M) (F : Matrix X X' A), op_smul_eq_mul, Finset.op_sum,
      Finset.sum_smul, smul_smul, ← op_mul]
  | ha z z' hz hz' => simp only [map_add, Submodule.coe_add, hz, hz']

end BalancedTensor

end TypeDStructure

end TauCeti
