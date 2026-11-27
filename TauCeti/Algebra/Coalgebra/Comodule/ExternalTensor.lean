/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# External tensor products of comodules

For a right `B`-comodule `M` and a right `C`-comodule `N`, the external tensor product is
a right `B ⊗[R] C`-comodule with coaction
`m ⊗ n ↦ (m₀ ⊗ n₀) ⊗ (m₁ ⊗ n₁)`.
No multiplication on either coefficient coalgebra is required. Tensor products of comodule
morphisms intertwine these coactions. Corestriction along a coalgebra map `B ⊗[R] C → D`
therefore gives `D`-coactions natural in both variables.

The comodule structure is not a global instance, since the tensor-product carrier can carry
other coactions.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.

The coassociativity proof adapts the tensor shuffle in Mathlib's tensor-product coalgebra
(`Mathlib.RingTheory.Coalgebra.TensorProduct`, Amelia Livingston and Andrew Yang).
-/

public section

open scoped TensorProduct
open TensorProduct

namespace TauCeti.Comodule

universe u v w x y

variable {R : Type u} [CommSemiring R]
variable {B : Type v} {C : Type w}
variable [AddCommMonoid B] [Module R B] [Coalgebra R B]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type x} {N : Type y}
variable [AddCommMonoid M] [Module R M] [Comodule R B M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The external coaction on the tensor product of comodules over two coalgebras. -/
noncomputable def externalCoact : M ⊗[R] N →ₗ[R] (M ⊗[R] N) ⊗[R] (B ⊗[R] C) :=
  (tensorTensorTensorComm R M B N C).toLinearMap ∘ₗ
    map (coact (R := R) (C := B) (M := M)) (coact (R := R) (C := C) (M := N))

/-- The external coaction applies each coaction and shuffles the middle two factors. -/
theorem externalCoact_def :
    externalCoact (R := R) (B := B) (C := C) (M := M) (N := N) =
      (tensorTensorTensorComm R M B N C).toLinearMap ∘ₗ
        map (coact (R := R) (C := B) (M := M)) (coact (R := R) (C := C) (M := N)) :=
  (rfl)

/-- The external coaction of a simple tensor. -/
@[simp]
theorem externalCoact_tmul (m : M) (n : N) :
    externalCoact (R := R) (B := B) (C := C) (m ⊗ₜ[R] n) =
      tensorTensorTensorComm R M B N C
        (coact (R := R) (C := B) m ⊗ₜ[R] coact (R := R) (C := C) n) :=
  (rfl)

/-- Coassociativity of the external coaction. -/
theorem externalCoact_coassoc :
    TensorProduct.assoc R (M ⊗[R] N) (B ⊗[R] C) (B ⊗[R] C) ∘ₗ
        (externalCoact (R := R) (B := B) (C := C) (M := M) (N := N)).rTensor
          (B ⊗[R] C) ∘ₗ externalCoact (R := R) (B := B) (C := C) =
      Coalgebra.comul.lTensor (M ⊗[R] N) ∘ₗ
        externalCoact (R := R) (B := B) (C := C) := by
  let f := coact (R := R) (C := B) (M := M)
  let g := coact (R := R) (C := C) (M := N)
  let S := (tensorTensorTensorComm R M B N C).toLinearMap
  let F := tensorTensorTensorComm R M (B ⊗[R] B) N (C ⊗[R] C) ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl R (M ⊗[R] N))
      (tensorTensorTensorComm R B B C C)
  -- Rebracketing before or after the two shuffles gives the same six-factor map.
  have hs : TensorProduct.assoc R (M ⊗[R] N) (B ⊗[R] C) (B ⊗[R] C) ∘ₗ
      S.rTensor (B ⊗[R] C) ∘ₗ
        (tensorTensorTensorComm R (M ⊗[R] B) B (N ⊗[R] C) C).toLinearMap =
      F.toLinearMap ∘ₗ map (TensorProduct.assoc R M B B).toLinearMap
        (TensorProduct.assoc R N C C).toLinearMap := by
    ext m b₁ b₂ n c₁ c₂
    simp [S, F]
  have hn : (map f g).rTensor (B ⊗[R] C) ∘ₗ S =
      (tensorTensorTensorComm R (M ⊗[R] B) B (N ⊗[R] C) C).toLinearMap ∘ₗ
        map (f.rTensor B) (g.rTensor C) := by
    simpa only [LinearMap.rTensor_def, map_id] using
      (tensorTensorTensorComm_comp_map R f (LinearMap.id : B →ₗ[R] B)
        g (LinearMap.id : C →ₗ[R] C)).symm
  have hc : Coalgebra.comul.lTensor (M ⊗[R] N) ∘ₗ S =
      F.toLinearMap ∘ₗ map (Coalgebra.comul.lTensor M) (Coalgebra.comul.lTensor N) := by
    simp only [TensorProduct.comul_def, AlgebraTensorModule.tensorTensorTensorComm_eq,
      AlgebraTensorModule.map_eq, LinearMap.lTensor_comp, LinearMap.comp_assoc]
    simp only [LinearMap.lTensor_def]
    have h := tensorTensorTensorComm_comp_map R (LinearMap.id : M →ₗ[R] M)
      (Coalgebra.comul (R := R) (A := B)) (LinearMap.id : N →ₗ[R] N)
      (Coalgebra.comul (R := R) (A := C))
    simp only [map_id] at h
    rw [← h]
    simp only [F, LinearEquiv.coe_trans, TensorProduct.toLinearMap_congr,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_assoc]
  -- Naturality moves the second coactions through the shuffle; the two comodule
  -- laws then identify the resulting map with comultiplication on the coefficients.
  simp only [externalCoact_def, LinearMap.rTensor_comp, LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc (map f g) S ((map f g).rTensor _), hn]
  simp only [← LinearMap.comp_assoc] at hs ⊢
  rw [hs]
  simp only [f, g, LinearMap.comp_assoc, ← map_comp, coact_coassoc]
  rw [map_comp, ← LinearMap.comp_assoc, ← hc]
  simp only [S, LinearMap.comp_assoc]

/-- Applying the tensor-product counit to the external coaction recovers the vector. -/
theorem externalCoact_counit :
    Coalgebra.counit.lTensor (M ⊗[R] N) ∘ₗ
        externalCoact (R := R) (B := B) (C := C) =
      (TensorProduct.mk R (M ⊗[R] N) R).flip 1 := by
  let F := map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N)
      (TensorProduct.rid R R).toLinearMap ∘ₗ
    (tensorTensorTensorComm R M R N R).toLinearMap
  refine TensorProduct.ext' fun m n ↦ ?_
  simp only [LinearMap.comp_apply, externalCoact_tmul, LinearMap.flip_apply,
    TensorProduct.mk_apply]
  calc
    _ = F (Coalgebra.counit.lTensor M (coact (R := R) (C := B) m) ⊗ₜ[R]
        Coalgebra.counit.lTensor N (coact (R := R) (C := C) n)) := by
      induction coact (R := R) (C := B) m using TensorProduct.inductionOn with
      | add p q hp hq => simp only [add_tmul, map_add, hp, hq]
      | tmul m b =>
        induction coact (R := R) (C := C) n using TensorProduct.inductionOn with
        | add p q hp hq => simp only [tmul_add, map_add, hp, hq]
        | tmul n c => simp [F]
    _ = _ := by simp [F]

/-- The external tensor product as a comodule over the tensor-product coalgebra. -/
@[instance_reducible]
noncomputable def externalTensor : Comodule R (B ⊗[R] C) (M ⊗[R] N) where
  coact := externalCoact
  coassoc := externalCoact_coassoc
  lTensor_counit_comp_coact := externalCoact_counit

/-- The coaction of the external tensor product. -/
@[simp]
theorem externalTensor_coact :
    (externalTensor (R := R) (B := B) (C := C) (M := M) (N := N)).coact =
      externalCoact (R := R) (B := B) (C := C) :=
  (rfl)

/-- The external product of two regular comodules is the regular tensor-product comodule. -/
@[simp]
theorem externalCoact_regular :
    externalCoact (R := R) (B := B) (C := C) (M := B) (N := C) =
      Coalgebra.comul := by
  simp only [externalCoact_def, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq, AlgebraTensorModule.map_eq, instSelf_coact]

variable {M' N' : Type*}
variable [AddCommMonoid M'] [Module R M'] [Comodule R B M']
variable [AddCommMonoid N'] [Module R N'] [Comodule R C N']

/-- External tensor coactions are natural in both comodule morphisms. -/
theorem externalCoact_natural (f : Hom R B M M') (g : Hom R C N N') :
    (map f.toLinearMap g.toLinearMap).rTensor (B ⊗[R] C) ∘ₗ
        externalCoact (R := R) (B := B) (C := C) =
      externalCoact (R := R) (B := B) (C := C) ∘ₗ map f.toLinearMap g.toLinearMap := by
  rw [externalCoact_def, externalCoact_def]
  have h := tensorTensorTensorComm_comp_map R f.toLinearMap
    (LinearMap.id : B →ₗ[R] B) g.toLinearMap (LinearMap.id : C →ₗ[R] C)
  simp only [TensorProduct.map_id] at h
  simp only [LinearMap.rTensor_def]
  rw [← LinearMap.comp_assoc, ← h, LinearMap.comp_assoc, ← map_comp,
    f.map_coact, g.map_coact, map_comp, LinearMap.comp_assoc]

attribute [local instance] externalTensor

/-- The tensor product of morphisms between external tensor products. -/
noncomputable def Hom.externalTensorMap (f : Hom R B M M') (g : Hom R C N N') :
    letI := externalTensor (R := R) (B := B) (C := C) (M := M) (N := N)
    letI := externalTensor (R := R) (B := B) (C := C) (M := M') (N := N')
    Hom R (B ⊗[R] C) (M ⊗[R] N) (M' ⊗[R] N') :=
  letI := externalTensor (R := R) (B := B) (C := C) (M := M) (N := N)
  letI := externalTensor (R := R) (B := B) (C := C) (M := M') (N := N')
  { toLinearMap := map f.toLinearMap g.toLinearMap
    map_coact := externalCoact_natural f g }

/-- The underlying linear map of the external tensor product of morphisms. -/
@[simp]
theorem Hom.externalTensorMap_toLinearMap (f : Hom R B M M') (g : Hom R C N N') :
    (f.externalTensorMap g).toLinearMap = map f.toLinearMap g.toLinearMap :=
  (rfl)

/-- The external tensor product of morphisms acts by the ordinary tensor-product map. -/
@[simp]
theorem Hom.externalTensorMap_apply (f : Hom R B M M') (g : Hom R C N N')
    (z : M ⊗[R] N) :
    f.externalTensorMap g z = map f.toLinearMap g.toLinearMap z :=
  LinearMap.congr_fun (Hom.externalTensorMap_toLinearMap f g) z

end TauCeti.Comodule
