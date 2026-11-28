/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Points of diagonalizable groups from characters

For a commutative semiring `R`, a commutative group `G`, and a commutative `R`-algebra `A`, every
character `χ : G →* Aˣ` extends by `MonoidAlgebra.lift` to an `R`-algebra homomorphism
`TauCeti.DiagonalizableGroup.point χ : R[G] →ₐ[R] A`.

Separating this lightweight construction from
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic` allows ordinary group-ring character
evaluation (`TauCeti.Algebra.MonoidAlgebra.CharEval.Basic`) to reuse `DiagonalizableGroup.point`
without importing Hopf algebra or Laurent polynomial machinery.

## Main definitions

* `TauCeti.DiagonalizableGroup.point`: the `R[G]`-point extending a character of `G`.

## Main results

* `TauCeti.DiagonalizableGroup.point_single` and `TauCeti.DiagonalizableGroup.point_single_one`:
  values of `point` on group-algebra basis elements.
-/

public section

namespace TauCeti

universe u v w

namespace DiagonalizableGroup

variable {R : Type u} {A : Type v} {G : Type w}
variable [CommSemiring R] [CommSemiring A] [Algebra R A] [CommGroup G]

/-- The `R[G]`-point of the diagonalizable group `D(G)` corresponding to a character of `G`.
It is the algebra map extending `χ` via the universal property of the group algebra; it sends
`single g r` to `r • χ g`. -/
@[expose] noncomputable def point (χ : G →* Aˣ) : MonoidAlgebra R G →ₐ[R] A :=
  MonoidAlgebra.lift R A G ((Units.coeHom A).comp χ)

/-- The point associated to a character sends `single g r` to `r • χ g`. -/
@[simp]
theorem point_single (χ : G →* Aˣ) (g : G) (r : R) :
    point (R := R) χ (MonoidAlgebra.single g r) = r • (χ g : A) := by
  rw [point, MonoidAlgebra.lift_single, MonoidHom.coe_comp, Function.comp_apply,
    Units.coeHom_apply]

/-- The point associated to a character sends the group-like `single g 1` to `χ g`. -/
theorem point_single_one (χ : G →* Aˣ) (g : G) :
    point (R := R) χ (MonoidAlgebra.single g 1) = (χ g : A) := by
  rw [point_single, one_smul]

end DiagonalizableGroup

end TauCeti
