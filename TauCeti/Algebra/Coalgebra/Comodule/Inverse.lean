/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import TauCeti.Algebra.Coalgebra.Comodule.Hom

/-!
# Inverses of comodule morphisms

Let `f` be an endomorphism of a right `C`-comodule `M`.  If the underlying linear map of `f` is
invertible, its inverse again commutes with the coaction: from `ρ ∘ f = (f ⊗ 1) ∘ ρ`, composing
with `f⁻¹` on both sides gives `ρ ∘ f⁻¹ = (f⁻¹ ⊗ 1) ∘ ρ`.  Using `Ring.inverse` in
`Module.End R M`, which is zero on non-units, this gives a comodule endomorphism
`TauCeti.Comodule.Hom.ringInverse f` for every `f`, with no invertibility hypothesis.

The same computation shows that the inverse of a bijective comodule morphism `f : M ⟶ N` between
two comodules is a comodule morphism `TauCeti.Comodule.Hom.inverse f`.

## Main definitions

* `TauCeti.Comodule.Hom.ringInverse`: the comodule endomorphism with underlying linear map
  `Ring.inverse f`.
* `TauCeti.Comodule.Hom.inverse`: the inverse of a bijective comodule morphism.

## Main results

* `TauCeti.Comodule.Hom.ringInverse_comp_self` and `TauCeti.Comodule.Hom.comp_ringInverse`: it is
  a two-sided inverse of `f` when the underlying linear map of `f` is invertible.
* `TauCeti.Comodule.Hom.ringInverse_of_not_isUnit`: it is zero otherwise.
* `TauCeti.Comodule.Hom.inverse_comp_self` and `TauCeti.Comodule.Hom.comp_inverse`: the inverse
  of a bijective comodule morphism is a two-sided inverse.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

namespace Hom

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The **inverse of a comodule endomorphism**: `Ring.inverse` of the underlying linear map is
again a comodule morphism.  It is the two-sided inverse of `f` when the underlying linear map of
`f` is invertible, and zero otherwise. -/
noncomputable def ringInverse (f : Hom R C M M) : Hom R C M M where
  toLinearMap := Ring.inverse f.toLinearMap
  map_coact := by
    set ρ := coact (R := R) (C := C) (M := M)
    set V := Ring.inverse f.toLinearMap
    rw [← LinearMap.rTensor_def]
    by_cases hf : IsUnit f.toLinearMap
    · have h : ρ ∘ₗ f.toLinearMap = f.toLinearMap.rTensor C ∘ₗ ρ := f.map_coact_eq.symm
      have hUV : f.toLinearMap ∘ₗ V = LinearMap.id := Ring.mul_inverse_cancel _ hf
      have hVU : V ∘ₗ f.toLinearMap = LinearMap.id := Ring.inverse_mul_cancel _ hf
      calc V.rTensor C ∘ₗ ρ = V.rTensor C ∘ₗ (ρ ∘ₗ f.toLinearMap) ∘ₗ V := by
            rw [LinearMap.comp_assoc, hUV, LinearMap.comp_id]
        _ = (V ∘ₗ f.toLinearMap).rTensor C ∘ₗ ρ ∘ₗ V := by
            rw [h, LinearMap.rTensor_comp]
            simp only [LinearMap.comp_assoc]
        _ = ρ ∘ₗ V := by
            rw [hVU, LinearMap.rTensor_id, LinearMap.id_comp]
    · have hV : V = 0 := Ring.inverse_non_unit _ hf
      rw [hV, LinearMap.rTensor_zero, LinearMap.zero_comp, LinearMap.comp_zero]

/-- The underlying linear map of `ringInverse f` is `Ring.inverse` of that of `f`. -/
@[simp]
theorem ringInverse_toLinearMap (f : Hom R C M M) :
    f.ringInverse.toLinearMap = Ring.inverse f.toLinearMap :=
  (rfl)

/-- If the underlying linear map of `f` is invertible, `ringInverse f` is a left inverse of `f`. -/
theorem ringInverse_comp_self {f : Hom R C M M} (hf : IsUnit f.toLinearMap) :
    f.ringInverse.comp f = id R C M :=
  toLinearMap_injective <| by
    rw [comp_toLinearMap, ringInverse_toLinearMap, id_toLinearMap]
    exact Ring.inverse_mul_cancel _ hf

/-- If the underlying linear map of `f` is invertible, `ringInverse f` is a right inverse of `f`.
-/
theorem comp_ringInverse {f : Hom R C M M} (hf : IsUnit f.toLinearMap) :
    f.comp f.ringInverse = id R C M :=
  toLinearMap_injective <| by
    rw [comp_toLinearMap, ringInverse_toLinearMap, id_toLinearMap]
    exact Ring.mul_inverse_cancel _ hf

/-- If the underlying linear map of `f` is not invertible, `ringInverse f` is zero. -/
@[simp]
theorem ringInverse_of_not_isUnit {f : Hom R C M M} (hf : ¬IsUnit f.toLinearMap) :
    f.ringInverse = 0 :=
  toLinearMap_injective <| by
    rw [ringInverse_toLinearMap, zero_toLinearMap]
    exact Ring.inverse_non_unit _ hf

section Inverse

variable {N : Type*} [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The **inverse of a bijective comodule morphism**: the inverse linear equivalence again
commutes with the coactions. -/
noncomputable def inverse (f : Hom R C M N) (hf : Function.Bijective f) : Hom R C N M where
  toLinearMap := (LinearEquiv.ofBijective f.toLinearMap hf).symm.toLinearMap
  map_coact := by
    refine LinearMap.ext fun n ↦ ?_
    obtain ⟨m, rfl⟩ := hf.2 n
    have hm : (LinearEquiv.ofBijective f.toLinearMap hf).symm.toLinearMap ∘ₗ f.toLinearMap =
        LinearMap.id :=
      LinearMap.ext fun m ↦ LinearEquiv.ofBijective_symm_apply_apply (h := hf) _ m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← f.map_coact_apply,
      ← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp, hm,
      LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
    exact congrArg _ (LinearEquiv.ofBijective_symm_apply_apply (h := hf) _ m).symm

/-- The underlying linear map of `inverse f hf` is the inverse linear equivalence. -/
@[simp]
theorem inverse_toLinearMap (f : Hom R C M N) (hf : Function.Bijective f) :
    (f.inverse hf).toLinearMap = (LinearEquiv.ofBijective f.toLinearMap hf).symm.toLinearMap :=
  (rfl)

/-- The inverse of a bijective comodule morphism is a left inverse. -/
@[simp]
theorem inverse_comp_self (f : Hom R C M N) (hf : Function.Bijective f) :
    (f.inverse hf).comp f = id R C M :=
  ext fun m ↦ LinearEquiv.ofBijective_symm_apply_apply (h := hf) _ m

/-- The inverse of a bijective comodule morphism is a right inverse. -/
@[simp]
theorem comp_inverse (f : Hom R C M N) (hf : Function.Bijective f) :
    f.comp (f.inverse hf) = id R C N :=
  ext fun n ↦ (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply n

end Inverse

end Hom

end Comodule

end TauCeti
