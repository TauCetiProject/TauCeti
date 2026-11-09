/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Hom
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.SimpleModule.Basic
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Comodules as modules over the convolution dual

A right comodule over a coalgebra carries a left module structure over its convolution
dual. For a projective coalgebra over a commutative semiring, maps of comodules are
exactly the linear maps for the convolution dual. Over a commutative ring, its
subcomodules are exactly the submodules for this action. In particular these comparisons
apply to every coalgebra over a field.
No finiteness hypothesis on the coalgebra or the comodule is required.

The module structure is named, rather than a global instance: install
`Comodule.convolutionModule` locally when using the module-side API. The order
isomorphism `Subcomodule.convolutionSubmoduleOrderIso` transports simplicity to
`IsSimpleModule`. This lets module-theoretic results, such as the Jacobson density
theorem, apply to simple comodules and their matrix coefficients.
`Subcomodule.isSimpleModule_convolution_iff_isAtom` also compares an atom with
the convolution-dual module on its inherited comodule carrier.

This is a fully faithful passage to modules, not an equivalence with all modules over
the convolution dual of an infinite-dimensional coalgebra.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2, comodules and modules over the dual algebra.
-/

public noncomputable section

open scoped TensorProduct
open TauCeti

section Semiring

variable {R C M N : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]
  [AddCommMonoid N] [Module R N] [Comodule R C N]

namespace TauCeti.Comodule

/-- A right comodule as a left module over the convolution algebra of the coalgebra's
linear dual. This structure is not installed globally. -/
abbrev convolutionModule : Module (WithConv (C →ₗ[R] R)) M :=
  Module.compHom M (convolutionAction (R := R) (C := C) (M := M)).toRingHom

attribute [local instance] convolutionModule

/-- The convolution-dual scalar action contracts the coaction. -/
@[simp]
theorem convolutionModule_smul (f : WithConv (C →ₗ[R] R)) (m : M) :
    f • m = LinearMap.tensorComponent f.ofConv (coact (R := R) (C := C) m) :=
  convolutionAction_apply f m

/-- The convolution-dual module structure extends the original ground-ring action. -/
instance convolutionModule_isScalarTower : IsScalarTower R (WithConv (C →ₗ[R] R)) M :=
  IsScalarTower.of_algebraMap_smul fun r m ↦ by
    exact DFunLike.congr_fun ((convolutionAction (R := R) (C := C) (M := M)).commutes r) m

/-- Comodule morphisms are linear for the convolution-dual action. -/
def Hom.toConvolutionLinearMap (f : Hom R C M N) :
    M →ₗ[WithConv (C →ₗ[R] R)] N where
  toFun := f
  map_add' := f.map_add
  map_smul' g m := Hom.map_convolutionAction f g m

/-- Passing a comodule morphism to the convolution dual leaves its values unchanged. -/
@[simp]
theorem Hom.toConvolutionLinearMap_apply (f : Hom R C M N) (m : M) :
    f.toConvolutionLinearMap m = f m := (rfl)

end TauCeti.Comodule

attribute [local instance] Comodule.convolutionModule

namespace TauCeti.Subcomodule

/-- A subcomodule, regarded as a submodule for the convolution-dual action. -/
def toConvolutionSubmodule (S : Subcomodule R C M) :
    Submodule (WithConv (C →ₗ[R] R)) M where
  carrier := S
  zero_mem' := zero_mem S
  add_mem' := fun hx hy ↦ add_mem hx hy
  smul_mem' f m hm := by
    rw [Comodule.convolutionModule_smul, LinearMap.tensorComponent_def, LinearMap.comp_apply]
    exact S.rid_lTensor_coact_mem f.ofConv hm

/-- Restriction to the ground ring recovers the original submodule. -/
@[simp]
theorem toConvolutionSubmodule_restrictScalars (S : Subcomodule R C M) :
    S.toConvolutionSubmodule.restrictScalars R = S.toSubmodule := by
  ext; rfl

/-- Converting a subcomodule does not change membership. -/
@[simp]
theorem mem_toConvolutionSubmodule (S : Subcomodule R C M) (m : M) :
    m ∈ S.toConvolutionSubmodule ↔ m ∈ S := Iff.rfl

end TauCeti.Subcomodule

end Semiring

section Ring

variable {R C M N : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]
  [AddCommGroup N] [Module R N] [Comodule R C N]

attribute [local instance] Comodule.convolutionModule

namespace Submodule

/-- A submodule for the convolution-dual action is a subcomodule. -/
def toSubcomodule (S : Submodule (WithConv (C →ₗ[R] R)) M) : Subcomodule R C M :=
  Subcomodule.ofSubmodule (S.restrictScalars R) fun m hm ↦ by
    apply (tensor_mem_range_iff_forall_tensorComponent_mem _
      (Comodule.coact (R := R) (C := C) m)).mpr
    intro f
    simpa only [restrictScalars_mem, Comodule.convolutionModule_smul,
      WithConv.ofConv_toConv] using S.smul_mem (WithConv.toConv f) hm

/-- The reconstructed subcomodule has the given submodule restricted to the ground ring. -/
@[simp]
theorem toSubcomodule_toSubmodule (S : Submodule (WithConv (C →ₗ[R] R)) M) :
    S.toSubcomodule.toSubmodule = S.restrictScalars R := (rfl)

/-- Converting a convolution-dual submodule does not change membership. -/
@[simp]
theorem mem_toSubcomodule (S : Submodule (WithConv (C →ₗ[R] R)) M) (m : M) :
    m ∈ S.toSubcomodule ↔ m ∈ S := Iff.rfl

/-- Passing a reconstructed subcomodule back to the convolution dual is the identity. -/
@[simp]
theorem toSubcomodule_toConvolutionSubmodule (S : Submodule (WithConv (C →ₗ[R] R)) M) :
    S.toSubcomodule.toConvolutionSubmodule = S := by
  ext; rfl

end Submodule

namespace TauCeti.Subcomodule

/-- Reconstructing a subcomodule from its convolution-dual submodule is the identity. -/
@[simp]
theorem toConvolutionSubmodule_toSubcomodule (S : Subcomodule R C M) :
    S.toConvolutionSubmodule.toSubcomodule = S := by
  ext; rfl

/-- Subcomodules and convolution-dual submodules are the same ordered family of submodules.
The coalgebra need not be finitely generated. -/
def convolutionSubmoduleOrderIso :
    Subcomodule R C M ≃o Submodule (WithConv (C →ₗ[R] R)) M where
  toFun := toConvolutionSubmodule
  invFun := Submodule.toSubcomodule
  left_inv := toConvolutionSubmodule_toSubcomodule
  right_inv := Submodule.toSubcomodule_toConvolutionSubmodule
  map_rel_iff' := Iff.rfl

/-- The forward order isomorphism is the convolution-dual submodule construction. -/
@[simp]
theorem convolutionSubmoduleOrderIso_apply (S : Subcomodule R C M) :
    convolutionSubmoduleOrderIso S = S.toConvolutionSubmodule := (rfl)

/-- The inverse order isomorphism constructs a subcomodule from a convolution-dual submodule. -/
@[simp]
theorem convolutionSubmoduleOrderIso_symm_apply (S : Submodule (WithConv (C →ₗ[R] R)) M) :
    convolutionSubmoduleOrderIso.symm S = S.toSubcomodule := (rfl)

end TauCeti.Subcomodule

end Ring

section SemiringMorphisms

variable {R C M N : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]
  [AddCommMonoid N] [Module R N] [Comodule R C N]

attribute [local instance] Comodule.convolutionModule

namespace LinearMap

/-- A linear map intertwining the convolution-dual actions is a comodule morphism.
This converse uses separation by the full linear dual, not just by rational points. -/
def toComoduleHom (f : M →ₗ[WithConv (C →ₗ[R] R)] N) : Comodule.Hom R C M N where
  toLinearMap := f.restrictScalars R
  map_coact := by
    ext m
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro g
    simp only [comp_apply, tensorComponent_map, comp_id]
    simpa only [restrictScalars_apply, Comodule.convolutionModule_smul,
      WithConv.ofConv_toConv] using f.map_smul (WithConv.toConv g) m

/-- The reconstructed comodule morphism has the original values. -/
@[simp]
theorem toComoduleHom_apply (f : M →ₗ[WithConv (C →ₗ[R] R)] N) (m : M) :
    f.toComoduleHom m = f m := (rfl)

/-- Passing a reconstructed morphism back to the convolution dual is the identity. -/
@[simp]
theorem toComoduleHom_toConvolutionLinearMap (f : M →ₗ[WithConv (C →ₗ[R] R)] N) :
    f.toComoduleHom.toConvolutionLinearMap = f := by
  ext; rfl

end LinearMap

namespace TauCeti.Comodule

/-- Reconstructing a comodule morphism from its convolution-linear map is the identity. -/
@[simp]
theorem Hom.toConvolutionLinearMap_toComoduleHom (f : Hom R C M N) :
    f.toConvolutionLinearMap.toComoduleHom = f := by
  ext; rfl

/-- Comodule morphisms are exactly the linear maps for the convolution-dual modules. -/
def Hom.convolutionLinearEquiv :
    Hom R C M N ≃ₗ[R] (M →ₗ[WithConv (C →ₗ[R] R)] N) where
  toFun := Hom.toConvolutionLinearMap
  invFun := LinearMap.toComoduleHom
  left_inv := Hom.toConvolutionLinearMap_toComoduleHom
  right_inv := LinearMap.toComoduleHom_toConvolutionLinearMap
  map_add' f g := by ext; rfl
  map_smul' r f := by ext; rfl

/-- The forward comparison of morphisms is the convolution-linear map construction. -/
@[simp]
theorem Hom.convolutionLinearEquiv_apply (f : Hom R C M N) :
    Hom.convolutionLinearEquiv f = f.toConvolutionLinearMap := (rfl)

/-- The inverse comparison reconstructs the comodule morphism. -/
@[simp]
theorem Hom.convolutionLinearEquiv_symm_apply (f : M →ₗ[WithConv (C →ₗ[R] R)] N) :
    Hom.convolutionLinearEquiv.symm f = f.toComoduleHom := (rfl)

end TauCeti.Comodule

end SemiringMorphisms

section Ring

variable {R C M : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]

attribute [local instance] Comodule.convolutionModule

namespace TauCeti.Comodule

/-- A comodule is simple exactly when its convolution-dual module is simple. -/
theorem isSimpleModule_convolution_iff :
    IsSimpleModule (WithConv (C →ₗ[R] R)) M ↔ IsSimpleOrder (Subcomodule R C M) := by
  rw [isSimpleModule_iff]
  exact Subcomodule.convolutionSubmoduleOrderIso.symm.isSimpleOrder_iff

end TauCeti.Comodule

namespace TauCeti.Subcomodule

/-- A subcomodule is an atom exactly when its inherited convolution-dual module is simple. -/
theorem isSimpleModule_convolution_iff_isAtom (S : Subcomodule R C M) :
    IsSimpleModule (WithConv (C →ₗ[R] R)) S ↔ IsAtom S := by
  let f : S →ₗ[WithConv (C →ₗ[R] R)] M := S.subtype.toConvolutionLinearMap
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (by simpa [f] using h)
  have hr : LinearMap.range f = S.toConvolutionSubmodule := by
    ext m
    constructor
    · rintro ⟨x, rfl⟩
      simp [f]
    · intro hm
      exact ⟨⟨m, hm⟩, by simp [f]⟩
  rw [LinearEquiv.isSimpleModule_iff (R := WithConv (C →ₗ[R] R))
      (M := S) (N := LinearMap.range f) (LinearEquiv.ofInjective f hf),
    isSimpleModule_iff_isAtom, hr, ← convolutionSubmoduleOrderIso_apply,
    OrderIso.isAtom_iff]

end TauCeti.Subcomodule

end Ring
