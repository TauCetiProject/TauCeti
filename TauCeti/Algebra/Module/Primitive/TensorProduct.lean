/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Detecting scalars with primitive vectors after base change

An integral functional taking a primitive vector to one still recovers its coefficient
in a tensor product. Consequently an integral linear map with a primitive vector in its
image remains faithful as a vector in the space of operators after every scalar extension.
This criterion detects root operators in integral representations in arbitrary characteristic.
-/

public section

open TensorProduct

namespace TauCeti

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- A primitive integral vector detects its coefficient after tensoring with any abelian group. -/
theorem IsPrimitive.tmul_left_injective {w : M} (hw : IsPrimitive w)
    (N : Type*) [AddCommGroup N] [Module ℤ N] : Function.Injective (fun a : N => a ⊗ₜ[ℤ] w) := by
  obtain ⟨f, hf⟩ := isPrimitive_def.mp hw
  -- Primitivity uses the canonical integer action; tensor products may carry another
  -- instance of that same action. Rebuild the functional for the supplied module instance.
  let f' : M →ₗ[ℤ] ℤ :=
    { __ := f.toAddMonoidHom
      map_smul' := fun n x => by
        simpa using map_intCast_smul f.toAddMonoidHom ℤ ℤ n x }
  have hf' : f' w = 1 := hf
  intro a b hab
  have h := congrArg (fun z : N ⊗[ℤ] M =>
    TensorProduct.rid ℤ N (TensorProduct.map (LinearMap.id : N →ₗ[ℤ] N) f' z)) hab
  -- Select the scalar action stored in the tensor product rather than canonical zsmul.
  have hone := fun x : N =>
    @one_smul ℤ N _ (Module.toDistribMulAction (R := ℤ) (M := N)).toMulAction x
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, hf', TensorProduct.rid_tmul,
    hone] using h

end TauCeti

namespace LinearMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]

/-- If an integral linear map has a primitive vector in its image, its scalar extension has
no nonzero scalar annihilator, even over a ring with zero divisors. -/
theorem smul_baseChange_eq_zero_iff_of_isPrimitive (f : M →ₗ[ℤ] N) (v : M)
    (hv : TauCeti.IsPrimitive (f v)) (A : Type*) [CommRing A] (c : A) :
    c • f.baseChange A = 0 ↔ c = 0 := by
  constructor
  · intro hc
    apply hv.tmul_left_injective A
    have h := LinearMap.congr_fun hc ((1 : A) ⊗ₜ[ℤ] v)
    simpa only [LinearMap.smul_apply, LinearMap.baseChange_tmul, smul_tmul',
      smul_eq_mul, mul_one, LinearMap.zero_apply, zero_tmul] using h
  · rintro rfl
    exact zero_smul _ _

end LinearMap
