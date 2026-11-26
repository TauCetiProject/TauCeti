/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Semisimplification
import TauCeti.RepresentationTheory.Augmentation.Semisimple
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Irreducible

/-!
# Examples: the semisimplification of a representation

* An irreducible representation is equivalent to its semisimplification, and the
  semisimplification of the zero representation is zero.
* In characteristic `p`, the regular representation of the cyclic group of order `p` (for `p = 2`
  the action of `ℤ/2` on `𝔽₂²` by `(1 1; 0 1)` in the basis `e₀ + e₁, e₁`) has the
  characteristic polynomials of its semisimplification but is not equivalent to it.
-/

open Representation

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

-- An irreducible representation is equivalent to its semisimplification.
example (ρ : Representation k G V) [ρ.IsIrreducible] : Nonempty (ρ.semisimplification.Equiv ρ) :=
  ρ.nonempty_equiv_semisimplification_iff.mpr inferInstance

-- The semisimplification of the zero representation is zero.
example (ρ : Representation k G PUnit) :
    Subsingleton (TauCeti.semisimplification k[G] ρ.asModule) := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton PUnit)
  infer_instance

section Cyclic

variable (p : ℕ) [Fact p.Prime]

-- The regular representation of `ℤ/p` over `𝔽_p` has the characteristic polynomials of its
-- semisimplification ...
example (g : Multiplicative (ZMod p)) :
    ((leftRegular (ZMod p) (Multiplicative (ZMod p))).semisimplification g).charpoly =
      (leftRegular (ZMod p) (Multiplicative (ZMod p)) g).charpoly :=
  charpoly_semisimplification_apply _ g

-- ... but is not equivalent to it, as it is not semisimple.
example : IsEmpty ((leftRegular (ZMod p) (Multiplicative (ZMod p))).semisimplification.Equiv
    (leftRegular (ZMod p) (Multiplicative (ZMod p)))) :=
  not_nonempty_iff.mp fun h ↦ not_isSemisimpleRepresentation_leftRegular (by simp)
    ((nonempty_equiv_semisimplification_iff _).mp h)

end Cyclic
