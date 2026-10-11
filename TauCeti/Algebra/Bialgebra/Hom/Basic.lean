/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Basic facts about bialgebra morphisms

`BialgHom.id_toRingHom` identifies the direct ring-homomorphism coercion of the identity.
It complements Mathlib's `BialgHom.id_toAlgHom`, which concerns the algebra-homomorphism
coercion.

The ordinary kernel of a bialgebra morphism is killed by the counit, and its comultiplication
lies in the kernel of the tensor-square map. These facts require only the algebra and coalgebra
structures used to define a bialgebra morphism, without an antipode.
-/

public section

namespace BialgHom

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [CoalgebraStruct R A]

/-- The ring homomorphism underlying the identity bialgebra morphism is the identity. -/
@[simp]
theorem id_toRingHom : (BialgHom.id R A : A →+* A) = RingHom.id A := rfl

variable {R A}
variable {B : Type*} [Semiring B] [Algebra R B] [CoalgebraStruct R B]

/-- The tensor-square map sends the comultiplication of an element in the kernel of a
bialgebra morphism to zero. -/
theorem comul_mem_ker_tensorProduct_map (f : A →ₐc[R] B) {x : A}
    (hx : x ∈ RingHom.ker f.toAlgHom) :
    Coalgebra.comul (R := R) x ∈
      RingHom.ker (Algebra.TensorProduct.map f.toAlgHom f.toAlgHom) := by
  simp only [RingHom.mem_ker, coe_toAlgHom] at hx
  rw [RingHom.mem_ker]
  calc
    Algebra.TensorProduct.map f.toAlgHom f.toAlgHom (Coalgebra.comul (R := R) x) =
        Coalgebra.comul (R := R) (f x) := CoalgHomClass.map_comp_comul_apply f x
    _ = 0 := by rw [hx, map_zero]

/-- The counit vanishes on the ordinary kernel of a bialgebra morphism. -/
theorem counit_eq_zero_of_mem_ker (f : A →ₐc[R] B) {x : A}
    (hx : x ∈ RingHom.ker f.toAlgHom) : Coalgebra.counit (R := R) x = 0 := by
  simp only [RingHom.mem_ker, coe_toAlgHom] at hx
  rw [← CoalgHomClass.counit_comp_apply f x, hx, map_zero]

end BialgHom
