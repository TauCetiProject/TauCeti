/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Module.LinearMap.Finite

/-!
# Endomorphism rings of modules over Artin algebras

Let `A` be an algebra over a commutative Artinian ring `R`, and `M` an `A`-module that is finitely
generated over `R`. Then the endomorphism ring of `M` over `A` is again finitely generated over `R`,
hence an Artinian ring (`Module.End.isArtinianRing`). This applies to a finitely generated module
over an *Artin algebra*, an `R`-algebra that is finitely generated as an `R`-module; a
finite-dimensional algebra over a field is the basic example.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace Module.End

variable (R : Type*) {A M : Type*} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] [Module.Finite R M]

include R in
/-- Let `A` be an algebra over a commutative Artinian ring `R`, and `M` an `A`-module that is
finitely generated over `R`. Then `Module.End A M` is an Artinian ring. -/
theorem isArtinianRing : IsArtinianRing (Module.End A M) := by
  have : Module.Finite A M := .of_restrictScalars_finite R A M
  have : Module.Finite R (Module.End A M) := .linearMap_of_isNoetherian
  exact IsArtinianRing.of_finite R (Module.End A M)

end Module.End
