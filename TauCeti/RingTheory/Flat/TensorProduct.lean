/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flatness and kernels of tensor products of algebra maps

Mathlib's `TensorProduct.map_injective_of_flat_flat` shows that the tensor product of two
injective linear maps is injective when the codomain of the first and the domain of the second
are flat. This file records the same statement for `Algebra.TensorProduct.map` of algebra
homomorphisms, so that it applies without first passing to the underlying linear maps.
Scalar extension also preserves faithful flatness of algebra homomorphisms, via the same
pushout identification used by Mathlib's `RingHom.Flat.lTensor`.
It also identifies the kernel after tensoring an algebra map with a flat algebra, following
Mathlib's `Algebra.TensorProduct.lTensor_ker` with flatness in place of surjectivity.

## Main results

* `RingHom.FaithfullyFlat.lTensor`: scalar extension preserves faithful flatness.
* `Algebra.TensorProduct.lTensor_ker_of_flat`: tensoring with a flat algebra carries kernels
  to their images under the right tensor inclusion.
* `Algebra.TensorProduct.map_injective_of_flat_flat`: the tensor product of two injective algebra
  homomorphisms is injective under the flatness hypotheses of
  `TensorProduct.map_injective_of_flat_flat`.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B C D : Type*} [CommSemiring R]
variable [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-- The tensor product of two injective algebra homomorphisms is injective when the codomain of
the first and the domain of the second are flat. -/
theorem map_injective_of_flat_flat (f : A →ₐ[R] B) (g : C →ₐ[R] D)
    [Module.Flat R B] [Module.Flat R C]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (map f g) := by
  have h := _root_.TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg
  rwa [← TensorProduct.AlgebraTensorModule.map_eq, ← toLinearMap_map, AlgHom.coe_toLinearMap] at h

section Ring

variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Module.Flat R A]

/-- Tensoring an algebra map with a flat algebra carries its kernel to the ideal generated
by its image under the right tensor inclusion. -/
theorem lTensor_ker_of_flat (f : B →ₐ[R] C) :
    RingHom.ker (map (AlgHom.id R A) f) =
      (RingHom.ker f).map (includeRight : B →ₐ[R] A ⊗[R] B) := by
  have hmap : ⇑(map (AlgHom.id R A) f) =
      TensorProduct.AlgebraTensorModule.lTensor R A f.toLinearMap := by
    rw [← AlgHom.coe_toLinearMap, toLinearMap_map, AlgHom.toLinearMap_id,
      TensorProduct.AlgebraTensorModule.map_eq, TensorProduct.AlgebraTensorModule.coe_lTensor,
      LinearMap.lTensor_def]
  have hker : (RingHom.ker f).restrictScalars R = LinearMap.ker f.toLinearMap := by
    ext; simp
  have hrange : LinearMap.range
        (TensorProduct.AlgebraTensorModule.lTensor R A f.toLinearMap.ker.subtype) =
      LinearMap.range (LinearMap.lTensor A f.toLinearMap.ker.subtype) := by
    ext; simp
  rw [← Submodule.restrictScalars_inj R, Ideal.map_includeRight_eq, hker, ← hrange,
    ← Module.Flat.ker_lTensor_eq]
  ext
  simp [hmap]

end Ring

end Algebra.TensorProduct

/-- Tensoring an algebra homomorphism with an algebra preserves faithful flatness.

This follows the scalar-extension identification in Mathlib's `RingHom.Flat.lTensor`. -/
theorem RingHom.FaithfullyFlat.lTensor
    {R B D : Type*} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D] (A : Type*) [CommRing A] [Algebra R A]
    {f : B →ₐ[R] D} (hf : f.toRingHom.FaithfullyFlat) :
    (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom.FaithfullyFlat := by
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom]
  let e : A ⊗[R] D ≃ₐ[A ⊗[R] B] (A ⊗[R] B) ⊗[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv
