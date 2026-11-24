/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Star.Module

/-!
# The Lie subalgebra of skew-adjoint elements of a star algebra

In an associative `R`-algebra `A` with a star operation, for which `star` is trivial on `R`, the
skew-adjoint elements `star X = -X` are closed under the commutator bracket
`⁅X, Y⁆ = X Y - Y X`: `star ⁅X, Y⁆ = ⁅star Y, star X⁆ = ⁅Y, X⁆ = -⁅X, Y⁆`. So they form a Lie
subalgebra of `A`, `TauCeti.skewAdjoint.lieSubalgebra R A`, with underlying submodule
`skewAdjoint.submodule R A` (`TauCeti.skewAdjoint.toSubmodule_lieSubalgebra`). For
`A = Matrix ι ι ℂ` over `R = ℝ` this is the unitary Lie algebra of skew-Hermitian matrices.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.skewAdjoint

variable (R A : Type*) [CommRing R] [StarMul R] [TrivialStar R] [Ring A] [StarRing A]
  [Algebra R A] [StarModule R A]

/-- The **Lie subalgebra of skew-adjoint elements** `star X = -X` of a star algebra `A`, for the
commutator bracket. -/
def lieSubalgebra : LieSubalgebra R A :=
  { skewAdjoint.submodule R A with
    lie_mem' := fun {X Y} hX hY => skewAdjoint.mem_iff.mpr <| by
      simp [Ring.lie_def, skewAdjoint.mem_iff.mp hX, skewAdjoint.mem_iff.mp hY] }

@[simp]
theorem toSubmodule_lieSubalgebra :
    (lieSubalgebra R A).toSubmodule = skewAdjoint.submodule R A :=
  Submodule.ext fun _ => Iff.rfl

variable {R A}

@[simp]
theorem mem_lieSubalgebra {X : A} : X ∈ lieSubalgebra R A ↔ X ∈ skewAdjoint A :=
  Iff.rfl

end TauCeti.skewAdjoint
