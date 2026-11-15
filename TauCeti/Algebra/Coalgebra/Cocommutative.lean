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

* `TauCeti.Coalgebra.IsCocomm.of_surjective`: a surjective image of a cocommutative coalgebra is
  cocommutative.
-/

public section

namespace TauCeti.Coalgebra.IsCocomm

variable {R A B F : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] [Coalgebra R A] [Coalgebra R B] [FunLike F A B]
  [CoalgHomClass F R A B]

/-- A surjective image of a cocommutative coalgebra is cocommutative. -/
theorem of_surjective [hA : _root_.Coalgebra.IsCocomm R A] (f : F)
    (hf : Function.Surjective f) : _root_.Coalgebra.IsCocomm R B := by
  refine ⟨LinearMap.ext fun b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hf b
  simp [← CoalgHomClass.map_comp_comul_apply, ← TensorProduct.map_comm]

end TauCeti.Coalgebra.IsCocomm
