/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Cocommutative coalgebras

Cocommutativity descends along surjective coalgebra homomorphisms. In particular, it
transfers across coalgebra equivalences without requiring compatible algebra structures.

## Main declarations

* `CoalgHom.isCocomm_of_surjective`: a surjective image of a cocommutative coalgebra is
  cocommutative.
-/

public section

namespace CoalgHom

variable {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] [Coalgebra R A] [Coalgebra R B]

/-- A surjective image of a cocommutative coalgebra is cocommutative. -/
theorem isCocomm_of_surjective (f : A →ₗc[R] B) (hf : Function.Surjective f)
    [hA : Coalgebra.IsCocomm R A] : Coalgebra.IsCocomm R B := by
  constructor
  ext b
  obtain ⟨a, rfl⟩ := hf b
  simpa only [CoalgHom.toLinearMap_eq_ofClass, CoalgHomClass.map_comp_comul_apply,
    Coalgebra.comm_comul, LinearMap.comp_apply, LinearEquiv.coe_coe] using
    (TensorProduct.map_comm f.toLinearMap f.toLinearMap (Coalgebra.comul a)).symm

end CoalgHom
