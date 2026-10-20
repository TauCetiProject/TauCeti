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

Let `A` be an algebra over a commutative Artinian ring `R` that is finitely generated as an
`R`-module, an *Artin algebra*. A finite-dimensional algebra over a field is the basic example.
The endomorphism ring of a finitely generated `A`-module is then again finitely generated over `R`,
hence an Artinian ring (`Module.End.isArtinianRing`).

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace Module.End

variable (R : Type*) {A M : Type*} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A] [AddCommGroup M] [Module A M] [Module.Finite A M]

include R in
/-- The endomorphism ring of a finitely generated module over an Artin algebra is Artinian. -/
theorem isArtinianRing : IsArtinianRing (Module.End A M) := by
  -- Let `R` act on `M` through `A`.
  let : Module R M := Module.compHom M (algebraMap R A)
  have : IsScalarTower R A M := .of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite R M := .trans A M
  have : Module.Finite R (Module.End A M) := .linearMap_of_isNoetherian
  exact IsArtinianRing.of_finite R (Module.End A M)

end Module.End
