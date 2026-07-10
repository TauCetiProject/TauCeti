/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import TauCeti.Algebra.Coalgebra.Comodule

/-!
# The tensor-product coaction map for comodules over a bialgebra

This file constructs the diagonal coaction map used in the tensor product of two right
comodules over a bialgebra. If `M` and `N` are right comodules over `C`, the map on
`M ⊗ N` is the usual formula

`m ⊗ n ↦ m₀ ⊗ n₀ ⊗ m₁ n₁`.

This is the concrete linear-map prerequisite for the full tensor-product comodule structure:
the counit and coassociativity laws can be proved against this map, and the naturality lemma
here is the morphism-level compatibility needed for the later categorical tensor product.

## Main declarations

* `TauCeti.Comodule.tensorCombine`: combines two coacted tensor factors.
* `TauCeti.Comodule.tensorCoact`: the diagonal coaction on `M ⊗ N`.
* `TauCeti.Comodule.tensorCombine_natural`: naturality of the combining map in the two
  comodule carriers.
* `TauCeti.Comodule.tensorCoact_natural`: the diagonal coaction commutes with tensoring
  comodule morphisms.

## References

This is the standard diagonal map for the tensor product of right comodules over a bialgebra;
see Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct
open TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x y z

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Combine two coacted tensor factors by shuffling the middle factors together and multiplying
the two `C`-components.

On pure tensors it sends `(m ⊗ c) ⊗ (n ⊗ d)` to `(m ⊗ n) ⊗ cd`. -/
def tensorCombine :
    (M ⊗[R] C) ⊗[R] (N ⊗[R] C) →ₗ[R] (M ⊗[R] N) ⊗[R] C :=
  TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) (LinearMap.mul' R C) ∘ₗ
    (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap

/-- `tensorCombine` sends `(m ⊗ c) ⊗ (n ⊗ d)` to `(m ⊗ n) ⊗ cd`. -/
@[simp]
theorem tensorCombine_tmul_tmul (m : M) (c : C) (n : N) (d : C) :
    tensorCombine (R := R) (C := C) (M := M) (N := N)
        ((m ⊗ₜ[R] c) ⊗ₜ[R] (n ⊗ₜ[R] d)) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] (c * d) := by
  simp [tensorCombine]

variable {M' : Type y} {N' : Type z}
variable [AddCommMonoid M'] [Module R M']
variable [AddCommMonoid N'] [Module R N']

/-- The combining map is natural in the two comodule carriers. -/
theorem tensorCombine_natural (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    TensorProduct.map (TensorProduct.map f g) (LinearMap.id : C →ₗ[R] C) ∘ₗ
        tensorCombine (R := R) (C := C) (M := M) (N := N) =
      tensorCombine (R := R) (C := C) (M := M') (N := N') ∘ₗ
        TensorProduct.map (TensorProduct.map f (LinearMap.id : C →ₗ[R] C))
          (TensorProduct.map g (LinearMap.id : C →ₗ[R] C)) := by
  rw [tensorCombine, tensorCombine]
  have h := TensorProduct.tensorTensorTensorComm_comp_map (R := R) (M := M) (N := C)
    (P := N) (Q := C) (S := M') (T := C) (V := N') (W := C) f
    (LinearMap.id : C →ₗ[R] C) g (LinearMap.id : C →ₗ[R] C)
  calc
    TensorProduct.map (TensorProduct.map f g) (LinearMap.id : C →ₗ[R] C) ∘ₗ
        (TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N)
          (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap) =
        (TensorProduct.map (LinearMap.id : M' ⊗[R] N' →ₗ[R] M' ⊗[R] N')
            (LinearMap.mul' R C) ∘ₗ
          TensorProduct.map (TensorProduct.map f g)
            (TensorProduct.map (LinearMap.id : C →ₗ[R] C) LinearMap.id)) ∘ₗ
          (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap := by
      rw [LinearMap.comp_assoc]
      apply TensorProduct.ext'
      intro x y
      simp [TensorProduct.map_map]
    _ = TensorProduct.map (LinearMap.id : M' ⊗[R] N' →ₗ[R] M' ⊗[R] N')
          (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.map (TensorProduct.map f g)
            (TensorProduct.map (LinearMap.id : C →ₗ[R] C) LinearMap.id) ∘ₗ
          (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap) := by
      rw [LinearMap.comp_assoc]
    _ = TensorProduct.map (LinearMap.id : M' ⊗[R] N' →ₗ[R] M' ⊗[R] N')
          (LinearMap.mul' R C) ∘ₗ
        ((TensorProduct.tensorTensorTensorComm R M' C N' C).toLinearMap ∘ₗ
          TensorProduct.map (TensorProduct.map f (LinearMap.id : C →ₗ[R] C))
            (TensorProduct.map g (LinearMap.id : C →ₗ[R] C))) := by
      rw [← h]
    _ = (TensorProduct.map (LinearMap.id : M' ⊗[R] N' →ₗ[R] M' ⊗[R] N')
          (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M' C N' C).toLinearMap) ∘ₗ
          TensorProduct.map (TensorProduct.map f (LinearMap.id : C →ₗ[R] C))
            (TensorProduct.map g (LinearMap.id : C →ₗ[R] C)) := by
      rw [LinearMap.comp_assoc]

variable [Coalgebra R C] [Comodule R C M] [Comodule R C N]

/-- The diagonal coaction map on the tensor product of two right comodules over a bialgebra.

The later full tensor-product comodule structure uses this as its coaction. -/
def tensorCoact : M ⊗[R] N →ₗ[R] (M ⊗[R] N) ⊗[R] C :=
  tensorCombine (R := R) (C := C) (M := M) (N := N) ∘ₗ
    TensorProduct.map (coact (R := R) (C := C) (M := M))
      (coact (R := R) (C := C) (M := N))

/-- The tensor-product coaction, before expanding the two component coactions. -/
@[simp]
theorem tensorCoact_tmul (m : M) (n : N) :
    tensorCoact (R := R) (C := C) (M := M) (N := N) (m ⊗ₜ[R] n) =
      tensorCombine (R := R) (C := C) (M := M) (N := N)
        (coact (R := R) (C := C) (M := M) m ⊗ₜ[R]
          coact (R := R) (C := C) (M := N) n) := by
  simp [tensorCoact]

variable [Comodule R C M'] [Comodule R C N']

/-- The diagonal tensor coaction is natural under tensor products of comodule morphisms. -/
theorem tensorCoact_natural (f : Hom R C M M') (g : Hom R C N N') :
    TensorProduct.map (TensorProduct.map f.toLinearMap g.toLinearMap)
        (LinearMap.id : C →ₗ[R] C) ∘ₗ
        tensorCoact (R := R) (C := C) (M := M) (N := N) =
      tensorCoact (R := R) (C := C) (M := M') (N := N') ∘ₗ
        TensorProduct.map f.toLinearMap g.toLinearMap := by
  rw [tensorCoact, tensorCoact, ← LinearMap.comp_assoc, tensorCombine_natural,
    LinearMap.comp_assoc, LinearMap.comp_assoc]
  congr 1
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, Hom.map_coact_eq, Hom.map_coact_eq]

end Comodule

end TauCeti
