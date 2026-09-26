/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Descent for scalar extensions of algebra homomorphisms

A property of ring maps satisfying faithfully flat descent can be checked after faithfully
flat extension of the common scalar ring. The two tensor-product squares form a pushout
square for the scalar-extended algebra homomorphism, by `Algebra.IsPushout.comp_iff`.
-/

public section

open TensorProduct

namespace RingHom.CodescendsAlong

universe u

/-- A property of ring maps with faithfully flat descent is reflected by faithfully flat
extension of the common scalar ring of an algebra homomorphism. -/
theorem of_tensorProduct_map
    {P : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat)
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Module.FaithfullyFlat R S]
    (f : A →ₐ[R] B)
    (hf : P (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom) :
    P f.toRingHom := by
  -- Equip the scalar-extension square with the algebra structures of its four edges.
  let : Algebra A B := f.toAlgebra
  let : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra B (S ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra A (S ⊗[R] B) := ((Algebra.TensorProduct.includeRight :
    B →ₐ[R] S ⊗[R] B).comp f).toAlgebra
  let : Algebra (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algHom f
  have : IsScalarTower A B (S ⊗[R] B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower S (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun s ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R A (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by simp [RingHom.algebraMap_toAlgebra]
  -- Cancel the left tensor-product square from the outer tensor-product square.
  have : Algebra.IsPushout A B (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.IsPushout.comp_iff R A S (S ⊗[R] A)).mp inferInstance
  have : Module.FaithfullyFlat A (S ⊗[R] A) :=
    Module.FaithfullyFlat.of_linearEquiv A _
      (Algebra.TensorProduct.commRight R A S).symm.toLinearEquiv
  exact hP (RingHom.faithfullyFlat_algebraMap_iff.mpr this) hf

end RingHom.CodescendsAlong
