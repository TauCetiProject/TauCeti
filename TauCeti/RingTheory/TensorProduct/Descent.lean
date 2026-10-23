/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Descent for scalar extensions of algebra homomorphisms

A property stable under base change is preserved by extension of the common scalar ring,
as expressed by `RingHom.IsStableUnderBaseChange.tensorProduct_map`.

A property of ring maps satisfying faithfully flat descent is reflected by faithfully flat
extension of the common scalar ring. Use `RingHom.CodescendsAlong.of_tensorProduct_map`
to deduce such a property of an algebra homomorphism from the corresponding property
after extending scalars. In particular, it applies to finiteness and faithful flatness
once their faithfully flat descent properties are supplied.

The source and target algebras and the extending ring share a universe because
`RingHom.CodescendsAlong` concerns maps between rings in one fixed universe. The common
base may lie in a different universe, and preservation under base change only needs it
to be a commutative semiring.
-/

public section

open TensorProduct

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingHom.IsStableUnderBaseChange

/-- A property stable under base change is preserved by extension of the common scalar ring. -/
theorem tensorProduct_map
    {P : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange P)
    {R : Type v} {S A B : Type u} [CommSemiring R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (hf : P f.toRingHom) :
    P (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom := by
  -- Equip the scalar-extension square with its edge algebra structures.
  let : Algebra A B := f.toAlgebra
  let : Algebra A (S ⊗[R] B) := ((Algebra.TensorProduct.includeRight :
    B →ₐ[R] S ⊗[R] B).comp f).toAlgebra
  let : Algebra (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algHom f
  have : IsScalarTower A B (S ⊗[R] B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower S (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algHom (Algebra.TensorProduct.lTensor S f)
  have : IsScalarTower R (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algHom (Algebra.TensorProduct.map (AlgHom.id R S) f)
  -- Cancel the left tensor-product square from the outer tensor-product square.
  have : Algebra.IsPushout A B (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.IsPushout.comp_iff R A S (S ⊗[R] A)).mp inferInstance
  exact hP A B (S ⊗[R] A) (S ⊗[R] B) hf

end RingHom.IsStableUnderBaseChange

namespace RingHom.CodescendsAlong

/-- A property of ring maps with faithfully flat descent is reflected by faithfully flat
extension of the common scalar ring of an algebra homomorphism. -/
theorem of_tensorProduct_map
    {P : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat)
    {R : Type v} {S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Module.FaithfullyFlat R S]
    (f : A →ₐ[R] B)
    (hf : P (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom) :
    P f.toRingHom := by
  -- Equip the scalar-extension square with the algebra structures of its four edges.
  let : Algebra A B := f.toAlgebra
  let : Algebra A (S ⊗[R] B) := ((Algebra.TensorProduct.includeRight :
    B →ₐ[R] S ⊗[R] B).comp f).toAlgebra
  let : Algebra (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algHom f
  have : IsScalarTower A B (S ⊗[R] B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower S (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algHom (Algebra.TensorProduct.lTensor S f)
  have : IsScalarTower R (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algHom (Algebra.TensorProduct.map (AlgHom.id R S) f)
  -- Cancel the left tensor-product square from the outer tensor-product square.
  have : Algebra.IsPushout A B (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.IsPushout.comp_iff R A S (S ⊗[R] A)).mp inferInstance
  have : Module.FaithfullyFlat A (S ⊗[R] A) :=
    Module.FaithfullyFlat.of_linearEquiv A _
      (Algebra.TensorProduct.commRight R A S).symm.toLinearEquiv
  exact hP (RingHom.faithfullyFlat_algebraMap_iff.mpr this) hf

end RingHom.CodescendsAlong
