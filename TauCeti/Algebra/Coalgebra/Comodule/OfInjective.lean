/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# Inheriting a comodule through an injective map

A linear coaction inherits the comodule laws from an ambient comodule if its inclusion
intertwines coactions and remains injective after tensoring with the double coalgebra.
This permits restriction to split homogeneous pieces without assuming the coalgebra flat.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable {R C M N : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]
  [AddCommMonoid N] [Module R N]

/-- Inherit the comodule laws from an equivariant inclusion. Injectivity after tensoring
with `C ⊗ C` suffices for coassociativity; injectivity of the inclusion suffices for the
counit law. In particular, a split inclusion requires no flatness hypothesis on `C`. -/
@[implicit_reducible]
def ofInjective (ρ : N →ₗ[R] N ⊗[R] C) (i : N →ₗ[R] M)
    (hi : Function.Injective i) (hiCC : Function.Injective (i.rTensor (C ⊗[R] C)))
    (hρ : i.rTensor C ∘ₗ ρ = coact (R := R) (C := C) ∘ₗ i) : Comodule R C N where
  coact := ρ
  coassoc := by
    ext n
    apply hiCC
    have hρn (n : N) : i.rTensor C (ρ n) = coact (R := R) (C := C) (i n) :=
      LinearMap.congr_fun hρ n
    have hmap (z : N ⊗[R] C) :
        (i.rTensor C).rTensor C (ρ.rTensor C z) =
          (coact (R := R) (C := C) (M := M)).rTensor C (i.rTensor C z) := by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hρ,
        LinearMap.rTensor_comp, LinearMap.comp_apply]
    have hcomul (z : N ⊗[R] C) :
        i.rTensor (C ⊗[R] C) (Coalgebra.comul.lTensor N z) =
          Coalgebra.comul.lTensor M (i.rTensor C z) := by
      simp only [LinearMap.rTensor_def, LinearMap.lTensor_def, TensorProduct.map_map,
        LinearMap.comp_id, LinearMap.id_comp]
    have hassoc (z : (N ⊗[R] C) ⊗[R] C) :
        i.rTensor (C ⊗[R] C) (TensorProduct.assoc R N C C z) =
          TensorProduct.assoc R M C C ((i.rTensor C).rTensor C z) := by
      simpa only [LinearMap.rTensor_def, TensorProduct.map_id] using
        TensorProduct.map_map_assoc i (LinearMap.id : C →ₗ[R] C)
          (LinearMap.id : C →ₗ[R] C) z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hassoc, hmap, hρn, coassoc_apply, hcomul, hρn]
  lTensor_counit_comp_coact := by
    ext n
    -- The right unitor identifies the counit law with an equality in `N`.
    apply (TensorProduct.rid R N).injective
    apply hi
    have hn := LinearMap.congr_fun hρ n
    have hc := congrArg (fun z ↦ TensorProduct.rid R M
      (Coalgebra.counit.lTensor M z)) hn
    have hnatural (z : N ⊗[R] C) :
        TensorProduct.rid R M (Coalgebra.counit.lTensor M (i.rTensor C z)) =
          i (TensorProduct.rid R N (Coalgebra.counit.lTensor N z)) := by
      induction z using TensorProduct.inductionOn with
      | tmul n c => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    simpa only [LinearMap.comp_apply, hnatural, lTensor_counit_coact,
      TensorProduct.rid_tmul, one_smul, LinearMap.flip_apply, TensorProduct.mk_apply] using hc

/-- The coaction inherited through an inclusion is the specified linear coaction. -/
@[simp]
theorem ofInjective_coact (ρ : N →ₗ[R] N ⊗[R] C) (i : N →ₗ[R] M)
    (hi : Function.Injective i) (hiCC : Function.Injective (i.rTensor (C ⊗[R] C)))
    (hρ : i.rTensor C ∘ₗ ρ = coact (R := R) (C := C) ∘ₗ i) :
    letI := ofInjective ρ i hi hiCC hρ
    coact (R := R) (C := C) (M := N) = ρ :=
  (rfl)

end TauCeti.Comodule
