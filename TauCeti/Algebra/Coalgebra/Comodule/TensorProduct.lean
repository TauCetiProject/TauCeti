/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule

/-!
# Tensor-product coactions

This file records the external tensor-product coaction attached to two right comodules.
If `M` is a right comodule over `C` and `N` is a right comodule over `D`, their tensor product
has the standard candidate coaction
`M ⊗ N → (M ⊗ N) ⊗ (C ⊗ D)`, obtained by coacting on both factors and then swapping the
middle two tensor factors.

This is the first bookkeeping step toward tensor products in the comodule representation
category from the reductive-groups roadmap. The later internal tensor product over a bialgebra
will compose this external coaction with multiplication on the coordinate bialgebra.

## Main declarations

* `TauCeti.Comodule.externalTensorCoact`: the external tensor-product coaction.
* `TauCeti.Comodule.externalTensorCoact_tmul`: its value on a simple tensor.
* `TauCeti.Comodule.externalTensorCoact_naturality`: compatibility with tensor products of
  comodule morphisms.

## References

This is the standard external tensor coaction for comodules; see Sweedler, *Hopf Algebras*,
Chapter 2. It supplies a prerequisite for `TauCetiRoadmap/ReductiveGroups/README.md`,
Layer 1, "Comodules over a coalgebra/Hopf algebra", specifically tensor products in the
finite-dimensional comodule category.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v v' w w'

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {D : Type v'} [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N : Type w'} [AddCommMonoid N] [Module R N] [Comodule R D N]

/-- The external tensor-product coaction attached to a pair of right comodules.

It coacts on both tensor factors and then rearranges
`(M ⊗ C) ⊗ (N ⊗ D)` as `(M ⊗ N) ⊗ (C ⊗ D)`. -/
@[expose] noncomputable def externalTensorCoact :
    M ⊗[R] N →ₗ[R] (M ⊗[R] N) ⊗[R] (C ⊗[R] D) :=
  (TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap ∘ₗ
    TensorProduct.map (coact (R := R) (C := C) (M := M))
      (coact (R := R) (C := D) (M := N))

/-- The external tensor coaction on a simple tensor. -/
@[simp]
theorem externalTensorCoact_tmul (m : M) (n : N) :
    externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N) (m ⊗ₜ[R] n) =
      (TensorProduct.tensorTensorTensorComm R M C N D)
        (coact (R := R) (C := C) (M := M) m ⊗ₜ[R]
          coact (R := R) (C := D) (M := N) n) := by
  rfl

/-- Naturality of the external tensor coaction under tensor products of comodule morphisms. -/
theorem externalTensorCoact_naturality
    {M' : Type*} [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    {N' : Type*} [AddCommMonoid N'] [Module R N'] [Comodule R D N']
    (f : Comodule.Hom R C M M') (g : Comodule.Hom R D N N') :
    TensorProduct.map (TensorProduct.map f.toLinearMap g.toLinearMap) LinearMap.id ∘ₗ
        externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N) =
      externalTensorCoact (R := R) (C := C) (D := D) (M := M') (N := N') ∘ₗ
        TensorProduct.map f.toLinearMap g.toLinearMap := by
  refine TensorProduct.ext' fun m n => ?_
  have hcomm := LinearMap.congr_fun
    (TensorProduct.tensorTensorTensorComm_comp_map
      (R := R) f.toLinearMap (LinearMap.id : C →ₗ[R] C) g.toLinearMap
        (LinearMap.id : D →ₗ[R] D))
    (coact (R := R) (C := C) (M := M) m ⊗ₜ[R]
      coact (R := R) (C := D) (M := N) n)
  simpa [externalTensorCoact, TensorProduct.map_map] using hcomm.symm

/-- Pointwise form of naturality of the external tensor coaction. -/
theorem externalTensorCoact_naturality_apply
    {M' : Type*} [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    {N' : Type*} [AddCommMonoid N'] [Module R N'] [Comodule R D N']
    (f : Comodule.Hom R C M M') (g : Comodule.Hom R D N N') (x : M ⊗[R] N) :
    TensorProduct.map (TensorProduct.map f.toLinearMap g.toLinearMap) LinearMap.id
        (externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N) x) =
      externalTensorCoact (R := R) (C := C) (D := D) (M := M') (N := N')
        (TensorProduct.map f.toLinearMap g.toLinearMap x) := by
  exact LinearMap.congr_fun (externalTensorCoact_naturality (R := R) (C := C) (D := D) f g) x

end Comodule

end TauCeti
