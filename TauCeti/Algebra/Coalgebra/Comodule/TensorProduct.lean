/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule

/-!
# Tensor products of comodules over a bialgebra

This file constructs the tensor product of two right comodules over a bialgebra. If `M` and
`N` are right comodules over `C`, the diagonal coaction on `M ⊗ N` is the usual formula

`m ⊗ n ↦ m₀ ⊗ n₀ ⊗ m₁ n₁`.

The candidate coaction is exposed as a linear map, its counit and coassociativity laws are
proved, and the resulting comodule structure is provided as an explicit named definition rather
than as a global instance. The file also tensors comodule morphisms, giving the morphism-level
compatibility needed for the later categorical tensor product.

## Main declarations

* `TauCeti.Comodule.tensorCombine`: combines two coacted tensor factors.
* `TauCeti.Comodule.tensorCoact`: the diagonal coaction on `M ⊗ N`.
* `TauCeti.Comodule.TensorProduct`: the tensor-product comodule structure.
* `TauCeti.Comodule.tensorCombine_natural`: naturality of the combining map in the two
  comodule carriers.
* `TauCeti.Comodule.tensorCoact_natural`: the diagonal coaction commutes with tensoring
  comodule morphisms.
* `TauCeti.Comodule.Hom.tensor`: the tensor product of two comodule morphisms.

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

On pure tensors it sends `(m ⊗ c) ⊗ (n ⊗ d)` to `(m ⊗ n) ⊗ cd`. -/
noncomputable def tensorCombine :
    (M ⊗[R] C) ⊗[R] (N ⊗[R] C) →ₗ[R] (M ⊗[R] N) ⊗[R] C :=
  TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) (LinearMap.mul' R C) ∘ₗ
    (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap

/-- Unfold `tensorCombine` to its defining composition. Kept `private`: the map's body is
deliberately not exposed to downstream modules (the module system hides non-`@[expose]`d
definition bodies), so this equation is an in-file helper for the lemmas below. -/
private theorem tensorCombine_def :
    tensorCombine (R := R) (C := C) (M := M) (N := N) =
      TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap :=
  rfl

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

The later full tensor-product comodule structure uses this map as its coaction. -/
noncomputable def tensorCoact [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    M ⊗[R] N →ₗ[R] (M ⊗[R] N) ⊗[R] C :=
  tensorCombine (R := R) (C := C) (M := M) (N := N) ∘ₗ
    TensorProduct.map (coact (R := R) (C := C) (M := M))
      (coact (R := R) (C := C) (M := N))

/-- Unfold `tensorCoact` to the combining map applied to the two component coactions. Kept
`private` for the same reason as `tensorCombine_def`: the coaction's body is not exposed
downstream, so this equation only serves the lemmas in this file. -/
private theorem tensorCoact_def [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    tensorCoact (R := R) (C := C) (M := M) (N := N) =
      tensorCombine (R := R) (C := C) (M := M) (N := N) ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M))
          (coact (R := R) (C := C) (M := N)) :=
  rfl

/-- The tensor-product coaction, before expanding the two component coactions. -/
@[simp]
theorem tensorCoact_tmul [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (m : M) (n : N) :
    tensorCoact (R := R) (C := C) (M := M) (N := N) (m ⊗ₜ[R] n) =
      tensorCombine (R := R) (C := C) (M := M) (N := N)
        (coact (R := R) (C := C) (M := M) m ⊗ₜ[R]
          coact (R := R) (C := C) (M := N) n) := by
  simp [tensorCoact_def (R := R) (C := C) (M := M) (N := N)]

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
  apply TensorProduct.ext'
  intro m n
  have hcombine := LinearMap.congr_fun
    (tensorCombine_natural (R := R) (C := C) (M := M) (N := N)
      (M' := M') (N' := N') f.toLinearMap g.toLinearMap)
    (coact (R := R) (C := C) (M := M) m ⊗ₜ[R] coact (R := R) (C := C) (M := N) n)
  simpa [tensorCoact_tmul, Hom.map_coact_apply] using hcombine

private theorem lTensor_counit_tensorCombine [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (x : M ⊗[R] C) (y : N ⊗[R] C) :
    Coalgebra.counit.lTensor (M ⊗[R] N)
        (tensorCombine (R := R) (C := C) (M := M) (N := N) (x ⊗ₜ[R] y)) =
      tensorCombine (R := R) (C := R) (M := M) (N := N)
        (Coalgebra.counit.lTensor M x ⊗ₜ[R] Coalgebra.counit.lTensor N y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m c =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul n d => simp [Bialgebra.counit_mul]
      | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂, TensorProduct.tmul_add]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂, TensorProduct.add_tmul]

/-- The diagonal tensor-product coaction satisfies the counit law. -/
theorem tensorCoact_counit [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    Coalgebra.counit.lTensor (M ⊗[R] N) ∘ₗ
        tensorCoact (R := R) (C := C) (M := M) (N := N) =
      (TensorProduct.mk R (M ⊗[R] N) R).flip 1 := by
  apply TensorProduct.ext'
  intro m n
  simp [tensorCoact_tmul, lTensor_counit_tensorCombine]

private theorem comul_lTensor_tensorCombine [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (x : M ⊗[R] C) (y : N ⊗[R] C) :
    Coalgebra.comul.lTensor (M ⊗[R] N)
        (tensorCombine (R := R) (C := C) (M := M) (N := N) (x ⊗ₜ[R] y)) =
      tensorCombine (R := R) (C := C ⊗[R] C) (M := M) (N := N)
        (Coalgebra.comul.lTensor M x ⊗ₜ[R] Coalgebra.comul.lTensor N y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m c =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul n d => simp [Bialgebra.comul_mul]
      | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂, TensorProduct.tmul_add]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂, TensorProduct.add_tmul]

private theorem tensorCoact_rTensor_tensorCombine_core [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (x : M ⊗[R] C) (y : N ⊗[R] C)
    (c d : C) :
    TensorProduct.assoc R (M ⊗[R] N) C C
        (tensorCombine (R := R) (C := C) (M := M) (N := N) (x ⊗ₜ[R] y) ⊗ₜ[R] (c * d)) =
      tensorCombine (R := R) (C := C ⊗[R] C) (M := M) (N := N)
        (TensorProduct.assoc R M C C (x ⊗ₜ[R] c) ⊗ₜ[R]
          TensorProduct.assoc R N C C (y ⊗ₜ[R] d)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m c' =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul n d' => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [TensorProduct.tmul_add, map_add, TensorProduct.add_tmul, map_add,
            TensorProduct.add_tmul, map_add, TensorProduct.tmul_add, map_add, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂, TensorProduct.add_tmul]

private theorem tensorCoact_rTensor_tensorCombine [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (x : M ⊗[R] C) (y : N ⊗[R] C) :
    TensorProduct.assoc R (M ⊗[R] N) C C
        ((tensorCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (tensorCombine (R := R) (C := C) (M := M) (N := N) (x ⊗ₜ[R] y))) =
      tensorCombine (R := R) (C := C ⊗[R] C) (M := M) (N := N)
        (TensorProduct.assoc R M C C
            ((coact (R := R) (C := C) (M := M)).rTensor C x) ⊗ₜ[R]
          TensorProduct.assoc R N C C
            ((coact (R := R) (C := C) (M := N)).rTensor C y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m c =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul n d =>
          simpa only [tensorCombine_tmul_tmul, LinearMap.rTensor_tmul, tensorCoact_tmul] using
            tensorCoact_rTensor_tensorCombine_core (R := R) (C := C) (M := M) (N := N)
              (coact (R := R) (C := C) (M := M) m)
              (coact (R := R) (C := C) (M := N) n) c d
      | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂, TensorProduct.tmul_add]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂, TensorProduct.add_tmul]

/-- The diagonal tensor-product coaction is coassociative. -/
theorem tensorCoact_coassoc [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    TensorProduct.assoc R (M ⊗[R] N) C C ∘ₗ
        (tensorCoact (R := R) (C := C) (M := M) (N := N)).rTensor C ∘ₗ
          tensorCoact (R := R) (C := C) (M := M) (N := N) =
      Coalgebra.comul.lTensor (M ⊗[R] N) ∘ₗ
        tensorCoact (R := R) (C := C) (M := M) (N := N) := by
  apply TensorProduct.ext'
  intro m n
  calc
    TensorProduct.assoc R (M ⊗[R] N) C C
        ((tensorCoact (R := R) (C := C) (M := M) (N := N)).rTensor C
          (tensorCoact (R := R) (C := C) (M := M) (N := N) (m ⊗ₜ[R] n))) =
        tensorCombine (R := R) (C := C ⊗[R] C) (M := M) (N := N)
          (TensorProduct.assoc R M C C
              ((coact (R := R) (C := C) (M := M)).rTensor C
                (coact (R := R) (C := C) (M := M) m)) ⊗ₜ[R]
            TensorProduct.assoc R N C C
              ((coact (R := R) (C := C) (M := N)).rTensor C
                (coact (R := R) (C := C) (M := N) n))) := by
          rw [tensorCoact_tmul]
          exact tensorCoact_rTensor_tensorCombine (R := R) (C := C) (M := M) (N := N)
            (coact (R := R) (C := C) (M := M) m)
            (coact (R := R) (C := C) (M := N) n)
    _ = tensorCombine (R := R) (C := C ⊗[R] C) (M := M) (N := N)
          (Coalgebra.comul.lTensor M (coact (R := R) (C := C) (M := M) m) ⊗ₜ[R]
            Coalgebra.comul.lTensor N (coact (R := R) (C := C) (M := N) n)) := by
          rw [coassoc_apply (R := R) (C := C) (M := M) m,
            coassoc_apply (R := R) (C := C) (M := N) n]
    _ = Coalgebra.comul.lTensor (M ⊗[R] N)
          (tensorCoact (R := R) (C := C) (M := M) (N := N) (m ⊗ₜ[R] n)) := by
          rw [tensorCoact_tmul]
          exact (comul_lTensor_tensorCombine (R := R) (C := C) (M := M) (N := N)
            (coact (R := R) (C := C) (M := M) m)
            (coact (R := R) (C := C) (M := N) n)).symm

/-- The tensor product of two right comodules over a bialgebra, with diagonal coaction. -/
@[implicit_reducible]
noncomputable def TensorProduct [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    Comodule R C (M ⊗[R] N) where
  coact := tensorCoact (R := R) (C := C) (M := M) (N := N)
  coassoc := tensorCoact_coassoc (R := R) (C := C) (M := M) (N := N)
  lTensor_counit_comp_coact := tensorCoact_counit (R := R) (C := C) (M := M) (N := N)

attribute [local instance] TensorProduct

private theorem TensorProduct_coact_aux [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    coact (R := R) (C := C) (M := M ⊗[R] N) =
      tensorCoact (R := R) (C := C) (M := M) (N := N) :=
  rfl

/-- The coaction in `Comodule.TensorProduct` is `Comodule.tensorCoact`. -/
@[simp]
theorem TensorProduct_coact [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    coact (R := R) (C := C) (M := M ⊗[R] N) =
      tensorCoact (R := R) (C := C) (M := M) (N := N) :=
  TensorProduct_coact_aux (R := R) (C := C) (M := M) (N := N)

namespace Hom

variable {M' : Type y} {N' : Type z}

/-- Tensor two right-comodule morphisms over a bialgebra. -/
noncomputable def tensor [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    (f : Hom R C M M') (g : Hom R C N N') :
    Hom R C (M ⊗[R] N) (M' ⊗[R] N') where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  map_coact := tensorCoact_natural (R := R) (C := C) (M := M) (N := N)
    (M' := M') (N' := N') f g

private theorem tensor_toLinearMap_aux [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    (f : Hom R C M M') (g : Hom R C N N') :
    (tensor (R := R) (C := C) f g).toLinearMap =
      TensorProduct.map f.toLinearMap g.toLinearMap :=
  rfl

/-- The underlying linear map of the tensor product of comodule morphisms is the tensor
product of the underlying linear maps. -/
@[simp]
theorem tensor_toLinearMap [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    (f : Hom R C M M') (g : Hom R C N N') :
    (tensor (R := R) (C := C) f g).toLinearMap =
      TensorProduct.map f.toLinearMap g.toLinearMap :=
  tensor_toLinearMap_aux (R := R) (C := C) f g

private theorem tensor_tmul_aux [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    (f : Hom R C M M') (g : Hom R C N N') (m : M) (n : N) :
    tensor (R := R) (C := C) f g (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n :=
  rfl

/-- The tensor product of comodule morphisms acts as the tensor product of the underlying
linear maps on pure tensors. -/
@[simp]
theorem tensor_tmul [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    (f : Hom R C M M') (g : Hom R C N N') (m : M) (n : N) :
    tensor (R := R) (C := C) f g (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n :=
  tensor_tmul_aux (R := R) (C := C) f g m n

private theorem tensor_id_aux [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    tensor (R := R) (C := C) (id R C M) (id R C N) =
      id R C (M ⊗[R] N) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rfl
  | add x₁ x₂ hx₁ hx₂ =>
      change ((tensor (R := R) (C := C) (id R C M) (id R C N)).toLinearMap (x₁ + x₂)) =
        (id R C (M ⊗[R] N)).toLinearMap (x₁ + x₂)
      rw [map_add, map_add]
      simpa only [coe_toLinearMap] using congrArg₂ (fun a b => a + b) hx₁ hx₂

/-- Tensoring identity comodule morphisms gives the identity on the tensor-product
comodule.

This is not a `simp` lemma: the ambient `ComoduleCat.ofHom_id` simp lemma rewrites the bare
`Hom.id R C M` on the left-hand side to `𝟙 (ComoduleCat.of R C M)`, so the statement is never
in `simp`-normal form. -/
theorem tensor_id [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    tensor (R := R) (C := C) (id R C M) (id R C N) =
      id R C (M ⊗[R] N) := by
  exact tensor_id_aux (R := R) (C := C) (M := M) (N := N)

variable {M'' N'' : Type*}

private theorem tensor_comp_aux [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    [AddCommMonoid M''] [Module R M''] [Comodule R C M'']
    [AddCommMonoid N''] [Module R N''] [Comodule R C N'']
    (f₂ : Hom R C M' M'') (f₁ : Hom R C M M')
    (g₂ : Hom R C N' N'') (g₁ : Hom R C N N') :
    tensor (R := R) (C := C) (comp f₂ f₁) (comp g₂ g₁) =
      comp (tensor (R := R) (C := C) f₂ g₂) (tensor (R := R) (C := C) f₁ g₁) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rfl
  | add x₁ x₂ hx₁ hx₂ =>
      change ((tensor (R := R) (C := C) (comp f₂ f₁) (comp g₂ g₁)).toLinearMap
          (x₁ + x₂)) =
        (comp (tensor (R := R) (C := C) f₂ g₂) (tensor (R := R) (C := C) f₁ g₁)).toLinearMap
          (x₁ + x₂)
      rw [map_add, map_add]
      simpa only [coe_toLinearMap] using congrArg₂ (fun a b => a + b) hx₁ hx₂

/-- Tensoring composite comodule morphisms gives the composite of the tensor products. -/
@[simp]
theorem tensor_comp [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    [AddCommMonoid M''] [Module R M''] [Comodule R C M'']
    [AddCommMonoid N''] [Module R N''] [Comodule R C N'']
    (f₂ : Hom R C M' M'') (f₁ : Hom R C M M')
    (g₂ : Hom R C N' N'') (g₁ : Hom R C N N') :
    tensor (R := R) (C := C) (comp f₂ f₁) (comp g₂ g₁) =
      comp (tensor (R := R) (C := C) f₂ g₂) (tensor (R := R) (C := C) f₁ g₁) := by
  exact tensor_comp_aux (R := R) (C := C) f₂ f₁ g₂ g₁

end Hom

end Coact

end Comodule

end TauCeti
