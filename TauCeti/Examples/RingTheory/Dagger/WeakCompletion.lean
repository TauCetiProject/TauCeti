/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Dagger.WeakCompletion.Map

/-!
# Checks for maps of weak completions

Evaluation at zero and one, substitution of a square, and polynomial retraction test the
induced maps. The retraction and identity checks apply to arbitrary weakly completed
elements, not just polynomials in the original algebra. The base ring and parameter are
arbitrary, so the checks apply in positive characteristic and with nilpotents as well.
-/

namespace TauCeti.Dagger

variable {O S : Type*} [CommRing O] [CommRing S] [Algebra O S]
  [Algebra.FiniteType O S] (π : O)

open weakCompletion

-- Both evaluations retract inclusion, even on nonalgebraic weakly completed elements.
example (z : weakCompletion π S) :
    map π ((Polynomial.aeval (0 : S)).restrictScalars O)
      (map π (IsScalarTower.toAlgHom O S (Polynomial S)) z) = z :=
  leftInverse_map_aeval π 0 z

example (z : weakCompletion π S) :
    map π ((Polynomial.aeval (1 : S)).restrictScalars O)
      (map π (IsScalarTower.toAlgHom O S (Polynomial S)) z) = z :=
  leftInverse_map_aeval π 1 z

-- The constant inclusion is injective, without separatedness of the original algebra.
example : Function.Injective
    (map π (IsScalarTower.toAlgHom O S (Polynomial S))) :=
  (leftInverse_map_aeval π (0 : S)).injective

-- The weak coordinate has the correct values at zero and at one.
example : map π ((Polynomial.aeval (0 : S)).restrictScalars O)
    (of π (Polynomial S) Polynomial.X) = 0 := by
  simpa only [AlgHom.restrictScalars_apply, Polynomial.aeval_X, map_zero] using
    map_of π ((Polynomial.aeval (R := S) (0 : S)).restrictScalars O) Polynomial.X

example : map π ((Polynomial.aeval (1 : S)).restrictScalars O)
    (of π (Polynomial S) Polynomial.X) = 1 := by
  simpa only [AlgHom.restrictScalars_apply, Polynomial.aeval_X, map_one] using
    map_of π ((Polynomial.aeval (R := S) (1 : S)).restrictScalars O) Polynomial.X

-- A ramified substitution is permitted: weak-completion functoriality requires no étaleness.
example : map π ((Polynomial.aeval (Polynomial.X ^ 2 : Polynomial S)).restrictScalars O)
    (of π (Polynomial S) Polynomial.X) = of π (Polynomial S) (Polynomial.X ^ 2) := by
  simpa only [AlgHom.restrictScalars_apply, Polynomial.aeval_X] using
    map_of π ((Polynomial.aeval (R := S) (Polynomial.X ^ 2 : Polynomial S)).restrictScalars O)
      Polynomial.X

example (z : weakCompletion π S) : map π (AlgHom.id O S) z = z := by
  rw [map_id]
  rfl

end TauCeti.Dagger
