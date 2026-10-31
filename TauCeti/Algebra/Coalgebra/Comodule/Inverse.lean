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
# Inverses of comodule endomorphisms

Let `f` be an endomorphism of a right `C`-comodule `M`.  If the underlying linear map of `f` is
invertible, its inverse again commutes with the coaction: from `ρ ∘ f = (f ⊗ 1) ∘ ρ`, composing
with `f⁻¹` on both sides gives `ρ ∘ f⁻¹ = (f⁻¹ ⊗ 1) ∘ ρ`.  Using `Ring.inverse` in
`Module.End R M`, which is zero on non-units, this gives a comodule endomorphism
`TauCeti.Comodule.Hom.ringInverse f` for every `f`, with no invertibility hypothesis.

## Main definitions

* `TauCeti.Comodule.Hom.ringInverse`: the comodule endomorphism with underlying linear map
  `Ring.inverse f`.

## Main results

* `TauCeti.Comodule.Hom.ringInverse_comp_self` and `TauCeti.Comodule.Hom.comp_ringInverse`: it is
  a two-sided inverse of `f` when the underlying linear map of `f` is invertible.
* `TauCeti.Comodule.Hom.ringInverse_of_not_isUnit`: it is zero otherwise.
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

end Hom

end Comodule

end TauCeti
