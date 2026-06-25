/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.TensorProduct
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
* `TauCeti.Comodule.tensorProduct`: the non-global tensor-product comodule structure.
* `TauCeti.Comodule.tensorProductHom`: the tensor product of comodule morphisms.
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
noncomputable def externalTensorCoact :
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

omit [Coalgebra R C] [Coalgebra R D] [Comodule R C M] [Comodule R D N] in
private theorem tensorTensorTensorComm_rTensor_assoc :
    TensorProduct.assoc R (M ⊗[R] N) (C ⊗[R] D) (C ⊗[R] D) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap.rTensor
          (C ⊗[R] D) =
      LinearMap.lTensor (M ⊗[R] N)
          (TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M (C ⊗[R] C) N (D ⊗[R] D)).toLinearMap ∘ₗ
        TensorProduct.map (TensorProduct.assoc R M C C) (TensorProduct.assoc R N D D) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R (M ⊗[R] C) (N ⊗[R] D) C D).toLinearMap := by
  ext m c n d c' d'
  simp

/-- Coherence for the tensor shuffle in the coassociativity proof of the external
tensor-product coaction. -/
theorem externalTensorCoact_coassoc_shuffle :
    TensorProduct.assoc R (M ⊗[R] N) (C ⊗[R] D) (C ⊗[R] D) ∘ₗ
        (externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N)).rTensor
          (C ⊗[R] D) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap =
      LinearMap.lTensor (M ⊗[R] N)
          (TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M (C ⊗[R] C) N (D ⊗[R] D)).toLinearMap ∘ₗ
        TensorProduct.map
          (TensorProduct.assoc R M C C ∘ₗ
            (coact (R := R) (C := C) (M := M)).rTensor C)
          (TensorProduct.assoc R N D D ∘ₗ
            (coact (R := R) (C := D) (M := N)).rTensor D) := by
  ext m c n d
  simpa [externalTensorCoact, LinearMap.comp_assoc] using LinearMap.congr_fun
    (tensorTensorTensorComm_rTensor_assoc (R := R) (C := C) (D := D) (M := M) (N := N))
    (coact (R := R) (C := C) (M := M) m ⊗ₜ[R]
      coact (R := R) (C := D) (M := N) n ⊗ₜ[R] (c ⊗ₜ[R] d))

/-- Coassociativity of the external tensor coaction. -/
@[simp]
theorem externalTensorCoact_coassoc :
    TensorProduct.assoc R (M ⊗[R] N) (C ⊗[R] D) (C ⊗[R] D) ∘ₗ
        (externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N)).rTensor
          (C ⊗[R] D) ∘ₗ
          externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N) =
      Coalgebra.comul.lTensor (M ⊗[R] N) ∘ₗ
        externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N) := by
  ext m n
  let F : (M ⊗[R] (C ⊗[R] C)) ⊗[R] (N ⊗[R] (D ⊗[R] D)) →ₗ[R]
      (M ⊗[R] N) ⊗[R] ((C ⊗[R] D) ⊗[R] (C ⊗[R] D)) :=
    LinearMap.lTensor (M ⊗[R] N)
        (TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap ∘ₗ
      (TensorProduct.tensorTensorTensorComm R M (C ⊗[R] C) N (D ⊗[R] D)).toLinearMap
  have hright :
      LinearMap.lTensor (M ⊗[R] N) (Coalgebra.comul (R := R) (A := C ⊗[R] D)) ∘ₗ
          (TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap =
        F ∘ₗ TensorProduct.map (LinearMap.lTensor M (Coalgebra.comul (R := R) (A := C)))
          (LinearMap.lTensor N (Coalgebra.comul (R := R) (A := D))) := by
    ext m' c n' d
    simp [F, TensorProduct.comul_def, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq]
  calc
    (TensorProduct.assoc R (M ⊗[R] N) (C ⊗[R] D) (C ⊗[R] D))
        ((LinearMap.rTensor (C ⊗[R] D)
            (externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N)))
          ((TensorProduct.tensorTensorTensorComm R M C N D) (coact m ⊗ₜ[R] coact n)))
        =
      F
        ((TensorProduct.assoc R M C C
            ((coact (R := R) (C := C) (M := M)).rTensor C (coact m))) ⊗ₜ[R]
          (TensorProduct.assoc R N D D
            ((coact (R := R) (C := D) (M := N)).rTensor D (coact n)))) := by
        simpa [F, externalTensorCoact] using LinearMap.congr_fun
          (externalTensorCoact_coassoc_shuffle (R := R) (C := C) (D := D) (M := M) (N := N))
          (coact (R := R) (C := C) (M := M) m ⊗ₜ[R]
            coact (R := R) (C := D) (M := N) n)
    _ =
      F
        ((Coalgebra.comul.lTensor M (coact (R := R) (C := C) (M := M) m)) ⊗ₜ[R]
          (Coalgebra.comul.lTensor N (coact (R := R) (C := D) (M := N) n))) := by
        simp
    _ =
      (LinearMap.lTensor (M ⊗[R] N) (Coalgebra.comul (R := R) (A := C ⊗[R] D)))
        ((TensorProduct.tensorTensorTensorComm R M C N D) (coact m ⊗ₜ[R] coact n)) := by
        simpa using (LinearMap.congr_fun hright (coact m ⊗ₜ[R] coact n)).symm

/-- The counit law for the external tensor coaction. -/
@[simp]
theorem externalTensorCoact_counit :
    Coalgebra.counit.lTensor (M ⊗[R] N) ∘ₗ
        externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N) =
      (TensorProduct.mk R (M ⊗[R] N) R).flip 1 := by
  ext m n
  let F : (M ⊗[R] R) ⊗[R] (N ⊗[R] R) →ₗ[R] (M ⊗[R] N) ⊗[R] R :=
    LinearMap.lTensor (M ⊗[R] N) (TensorProduct.rid R R).toLinearMap ∘ₗ
      (TensorProduct.tensorTensorTensorComm R M R N R).toLinearMap
  have hright :
      LinearMap.lTensor (M ⊗[R] N) (Coalgebra.counit (R := R) (A := C ⊗[R] D)) ∘ₗ
          (TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap =
        F ∘ₗ TensorProduct.map (LinearMap.lTensor M (Coalgebra.counit (R := R) (A := C)))
          (LinearMap.lTensor N (Coalgebra.counit (R := R) (A := D))) := by
    ext m' c n' d
    simp [F, TensorProduct.counit_def, mul_comm]
  calc
    (LinearMap.lTensor (M ⊗[R] N) (Coalgebra.counit (R := R) (A := C ⊗[R] D)))
        ((TensorProduct.tensorTensorTensorComm R M C N D) (coact m ⊗ₜ[R] coact n)) =
      F
        ((Coalgebra.counit.lTensor M (coact (R := R) (C := C) (M := M) m)) ⊗ₜ[R]
          (Coalgebra.counit.lTensor N (coact (R := R) (C := D) (M := N) n))) := by
        simpa using LinearMap.congr_fun hright (coact m ⊗ₜ[R] coact n)
    _ = F ((m ⊗ₜ[R] 1) ⊗ₜ[R] (n ⊗ₜ[R] 1)) := by
        simp
    _ = m ⊗ₜ[R] n ⊗ₜ[R] 1 := by
        simp [F]

variable (R C D M N) in
/-- The external tensor product of two right comodules, as a non-global comodule structure. -/
@[expose, reducible] noncomputable def tensorProduct : Comodule R (C ⊗[R] D) (M ⊗[R] N) where
  coact := externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N)
  coassoc := externalTensorCoact_coassoc (R := R) (C := C) (D := D) (M := M) (N := N)
  lTensor_counit_comp_coact :=
    externalTensorCoact_counit (R := R) (C := C) (D := D) (M := M) (N := N)

/-- The packaged tensor-product comodule has coaction `externalTensorCoact`. -/
@[simp]
theorem tensorProduct_coact :
    coact (self := tensorProduct R C D M N) =
      externalTensorCoact (R := R) (C := C) (D := D) (M := M) (N := N) :=
  rfl

/-- Naturality of the external tensor coaction under tensor products of comodule morphisms. -/
@[simp]
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

/-- The tensor product of two comodule morphisms, for the non-global tensor-product comodules. -/
@[expose] def tensorProductHom
    {M' : Type*} [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    {N' : Type*} [AddCommMonoid N'] [Module R N'] [Comodule R D N']
    (f : Comodule.Hom R C M M') (g : Comodule.Hom R D N N') :
    letI : Comodule R (C ⊗[R] D) (M ⊗[R] N) := tensorProduct R C D M N
    letI : Comodule R (C ⊗[R] D) (M' ⊗[R] N') := tensorProduct R C D M' N'
    Comodule.Hom R (C ⊗[R] D) (M ⊗[R] N) (M' ⊗[R] N') :=
  letI : Comodule R (C ⊗[R] D) (M ⊗[R] N) := tensorProduct R C D M N
  letI : Comodule R (C ⊗[R] D) (M' ⊗[R] N') := tensorProduct R C D M' N'
  { toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
    map_coact := by
      simp [tensorProduct_coact,
        externalTensorCoact_naturality (R := R) (C := C) (D := D) f g] }

/-- The underlying linear map of the tensor product of comodule morphisms. -/
@[simp]
theorem tensorProductHom_toLinearMap
    {M' : Type*} [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    {N' : Type*} [AddCommMonoid N'] [Module R N'] [Comodule R D N']
    (f : Comodule.Hom R C M M') (g : Comodule.Hom R D N N') :
    letI : Comodule R (C ⊗[R] D) (M ⊗[R] N) := tensorProduct R C D M N
    letI : Comodule R (C ⊗[R] D) (M' ⊗[R] N') := tensorProduct R C D M' N'
    (tensorProductHom (R := R) (C := C) (D := D) f g).toLinearMap =
      TensorProduct.map f.toLinearMap g.toLinearMap :=
  rfl

/-- The tensor product of comodule morphisms applies as the tensor product of the underlying
linear maps. -/
@[simp]
theorem tensorProductHom_apply
    {M' : Type*} [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    {N' : Type*} [AddCommMonoid N'] [Module R N'] [Comodule R D N']
    (f : Comodule.Hom R C M M') (g : Comodule.Hom R D N N') (x : M ⊗[R] N) :
    letI : Comodule R (C ⊗[R] D) (M ⊗[R] N) := tensorProduct R C D M N
    letI : Comodule R (C ⊗[R] D) (M' ⊗[R] N') := tensorProduct R C D M' N'
    tensorProductHom (R := R) (C := C) (D := D) f g x =
      TensorProduct.map f.toLinearMap g.toLinearMap x :=
  rfl

/-- Pointwise form of naturality of the external tensor coaction. -/
@[simp]
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
