/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import TauCeti.Algebra.Coalgebra.Comodule.Basic

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
@[expose] noncomputable def ringInverse (f : Hom R C M M) : Hom R C M M where
  toLinearMap := Ring.inverse f.toLinearMap
  map_coact := by
    set ρ := coact (R := R) (C := C) (M := M)
    set V := Ring.inverse f.toLinearMap
    change V.rTensor C ∘ₗ ρ = ρ ∘ₗ V
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
    · rw [show V = 0 from Ring.inverse_non_unit _ hf, LinearMap.rTensor_zero, LinearMap.zero_comp,
        LinearMap.comp_zero]

/-- The underlying linear map of `ringInverse f` is `Ring.inverse` of that of `f`. -/
@[simp]
theorem ringInverse_toLinearMap (f : Hom R C M M) :
    f.ringInverse.toLinearMap = Ring.inverse f.toLinearMap :=
  rfl

end Hom

end Comodule

end TauCeti
