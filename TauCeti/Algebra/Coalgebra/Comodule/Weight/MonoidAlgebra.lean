/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space

/-!
# Group-like weight spaces for monoid-algebra comodules

This file identifies the group-like weight space indexed by `single g 1` with the usual weight
space of a comodule over a monoid algebra.

## Main declaration

* `TauCeti.Comodule.groupLikeWeightSpace_single_one`: the group-like and monoid-algebra weight
  spaces agree.
-/

public section

namespace TauCeti.Comodule

universe u v w

variable {R : Type u} {G : Type v} {M : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Comodule R (MonoidAlgebra R G) M]

/-- The generic group-like weight space at `single g 1` is the usual monoid-algebra weight
space. -/
@[simp]
theorem groupLikeWeightSpace_single_one (g : G) :
    GroupLike.weightSpace (M := M)
        ⟨MonoidAlgebra.single g (1 : R),
          by
            constructor
            · simp
            · simp⟩ =
      weightSpace R G M g := by
  ext m
  rw [GroupLike.mem_weightSpace, mem_weightSpace]

end TauCeti.Comodule
