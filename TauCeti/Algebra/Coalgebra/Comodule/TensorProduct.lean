/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
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

section Combine

variable [NonUnitalNonAssocSemiring C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Combine two coacted tensor factors by shuffling the middle factors together and multiplying
the two `C`-components.

On pure tensors it sends `(m ⊗ c) ⊗ (n ⊗ d)` to `(m ⊗ n) ⊗ cd`.

The body is exposed through the `tensorCombine_def` equation lemma and the definition is then
marked `irreducible`, so downstream code depends only on `tensorCombine_def` and the
characteristic lemmas below rather than on the shuffle/multiplication body by reduction. -/
@[expose] noncomputable def tensorCombine :
    (M ⊗[R] C) ⊗[R] (N ⊗[R] C) →ₗ[R] (M ⊗[R] N) ⊗[R] C :=
  TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) (LinearMap.mul' R C) ∘ₗ
    (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap

/-- The defining equation of `tensorCombine`, kept as the sole handle on its opaque body. -/
theorem tensorCombine_def :
    tensorCombine (R := R) (C := C) (M := M) (N := N) =
      TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap :=
  rfl

attribute [irreducible] tensorCombine

/-- `tensorCombine` sends `(m ⊗ c) ⊗ (n ⊗ d)` to `(m ⊗ n) ⊗ cd`. -/
@[simp]
theorem tensorCombine_tmul_tmul (m : M) (c : C) (n : N) (d : C) :
    tensorCombine (R := R) (C := C) (M := M) (N := N)
        ((m ⊗ₜ[R] c) ⊗ₜ[R] (n ⊗ₜ[R] d)) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] (c * d) := by
  simp [tensorCombine_def]

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
  rw [tensorCombine_def, tensorCombine_def]
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

end Combine

section Coact

/-- The diagonal coaction map on the tensor product of two right comodules over a bialgebra.

The later full tensor-product comodule structure uses this as its coaction.

The body is exposed through the `tensorCoact_def` equation lemma and the definition is then
marked `irreducible`, so downstream code depends only on the characteristic coaction lemmas
`tensorCoact_tmul` and `tensorCoact_natural` rather than on this composition by reduction. -/
@[expose] noncomputable def tensorCoact [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    M ⊗[R] N →ₗ[R] (M ⊗[R] N) ⊗[R] C :=
  tensorCombine (R := R) (C := C) (M := M) (N := N) ∘ₗ
    TensorProduct.map (coact (R := R) (C := C) (M := M))
      (coact (R := R) (C := C) (M := N))

/-- The defining equation of `tensorCoact`, kept as the sole handle on its opaque body. -/
theorem tensorCoact_def [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    tensorCoact (R := R) (C := C) (M := M) (N := N) =
      tensorCombine (R := R) (C := C) (M := M) (N := N) ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M))
          (coact (R := R) (C := C) (M := N)) :=
  rfl

attribute [irreducible] tensorCoact

/-- The tensor-product coaction, before expanding the two component coactions. -/
@[simp]
theorem tensorCoact_tmul [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (m : M) (n : N) :
    tensorCoact (R := R) (C := C) (M := M) (N := N) (m ⊗ₜ[R] n) =
      tensorCombine (R := R) (C := C) (M := M) (N := N)
        (coact (R := R) (C := C) (M := M) m ⊗ₜ[R]
          coact (R := R) (C := C) (M := N) n) := by
  rw [tensorCoact_def (R := R) (C := C) (M := M) (N := N)]
  rfl

variable {M' : Type y} {N' : Type z}

/-- The diagonal tensor coaction is natural under tensor products of comodule morphisms. -/
theorem tensorCoact_natural [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    (f : Hom R C M M') (g : Hom R C N N') :
    TensorProduct.map (TensorProduct.map f.toLinearMap g.toLinearMap)
        (LinearMap.id : C →ₗ[R] C) ∘ₗ
        tensorCoact (R := R) (C := C) (M := M) (N := N) =
        tensorCoact (R := R) (C := C) (M := M') (N := N') ∘ₗ
        TensorProduct.map f.toLinearMap g.toLinearMap := by
  rw [tensorCoact_def (R := R) (C := C) (M := M) (N := N),
    tensorCoact_def (R := R) (C := C) (M := M') (N := N'), ← LinearMap.comp_assoc,
    tensorCombine_natural,
    LinearMap.comp_assoc, LinearMap.comp_assoc]
  rw [tensorCombine_def (R := R) (C := C) (M := M') (N := N')]
  rw [LinearMap.comp_assoc]
  rw [← TensorProduct.map_comp, Hom.map_coact_eq, Hom.map_coact_eq]
  rw [← TensorProduct.map_comp]
  rw [← LinearMap.comp_assoc]

end Coact

end Comodule

end TauCeti
