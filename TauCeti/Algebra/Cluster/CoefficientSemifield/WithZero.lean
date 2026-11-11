/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import Mathlib.Algebra.Ring.WithZero

/-!
# Adjoining zero to a coefficient semifield

Adjoining an absorbing zero to a coefficient semifield gives a semifield.
This allows ordinary polynomial evaluation to express auxiliary sums, including the
empty sum, without imposing an additive identity on the coefficient semifield itself.
Homomorphisms extend by sending the adjoined zero to zero.
-/

public section

namespace TauCeti.CoefficientSemifield

variable {P : Type*} [CoefficientSemifield P]

/-- Auxiliary addition extends by an additive identity, and every nonzero element is invertible. -/
instance : Semifield (WithZero P) where
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

end TauCeti.CoefficientSemifield

namespace TauCeti.CoefficientSemifieldHom

variable {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- Extend a coefficient homomorphism by zero. -/
def withZeroMap (f : CoefficientSemifieldHom P Q) : WithZero P →+* WithZero Q :=
  { WithZero.map' f.toMonoidHom with
    map_add' := by
      intro a b
      induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
      all_goals simp [← WithZero.coe_add, map_add] }

@[simp]
theorem withZeroMap_coe (f : CoefficientSemifieldHom P Q) (p : P) :
    f.withZeroMap (p : WithZero P) = (f p : WithZero Q) :=
  (rfl)

end TauCeti.CoefficientSemifieldHom
