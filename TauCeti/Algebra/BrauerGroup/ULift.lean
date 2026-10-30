/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.BaseChange
public import TauCeti.Algebra.TensorProduct.ULift
public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Lifting central simple algebras and their Brauer classes

The lifted field `ULift K` and lifted algebra `ULift A` carry the transported operations.
`CSA.ulift` bundles this algebra as central simple, using its explicit identification with
scalar extension. Its Brauer class is the image under the tensor-defined `BrauerGroup.baseChange`.
This map is injective, so lifting universes preserves nontrivial Brauer classes.

The algebra identification is `TauCeti.Algebra.TensorProduct.uliftBaseChangeAlgEquiv`.
No cohomological comparison is used to define the transport.
-/

public noncomputable section

universe u v

open scoped TensorProduct

attribute [local instance 100] ULift.algebra'

namespace CSA

variable {K : Type u} [Field K]

/-- Lift both the base field and the carrier of a central simple algebra to a larger universe.
The carrier is `ULift A`, with its transported ring operations. The source carrier lives in
the field's universe, as in the tensor-defined Brauer group. -/
abbrev ulift (A : CSA.{u, u} K) : CSA.{max u v, max u v} (ULift.{v} K) := by
  let e := TauCeti.Algebra.TensorProduct.uliftBaseChangeAlgEquiv.{u, u, v} K A
  letI : Algebra.IsCentral (ULift.{v} K) (ULift.{v} A) :=
    Algebra.IsCentral.of_algEquiv (ULift.{v} K) _ _ e
  letI : IsSimpleRing (ULift.{v} A) := IsSimpleRing.of_ringEquiv e.toRingEquiv inferInstance
  letI : FiniteDimensional (ULift.{v} K) (ULift.{v} A) := Module.Finite.equiv e.toLinearEquiv
  exact TauCeti.CSA.of (ULift.{v} K) (ULift.{v} A)

end CSA

namespace TauCeti.BrauerGroup

variable (K : Type u) [Field K]

/-- The class of the lifted algebra is its scalar-extension class. -/
@[simp]
theorem mk_ulift (A : CSA.{u, u} K) :
    mk (A.ulift : CSA.{max u v, max u v} (ULift.{v} K)) =
      baseChange K (ULift.{v} K) (mk A) := by
  rw [baseChange_mk]
  exact mk_eq_mk_of_algEquiv (Algebra.TensorProduct.uliftBaseChangeAlgEquiv K A).symm

/-- Upward universe lifting is injective on the tensor-defined Brauer group. -/
theorem baseChange_ulift_injective : Function.Injective (baseChange K (ULift.{v} K)) :=
  baseChange_injective_of_surjective K (ULift.{v} K) fun x => ⟨x.down, rfl⟩

end TauCeti.BrauerGroup
