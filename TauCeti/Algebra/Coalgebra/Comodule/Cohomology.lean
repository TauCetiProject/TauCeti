/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Invariants
public import TauCeti.Algebra.Coalgebra.Comodule.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Rational cohomology as derived invariants

For a flat bialgebra `H` over a commutative ring `R`, define rational cohomology on all
right `H`-comodules as the right derived functors of invariants. In particular this
applies to flat commutative coordinate Hopf algebras. The coefficient module need not
be flat or finitely generated. The natural degree-zero identification is with the
existing fixed subcomodule, not the vectors fixed only by field-valued points.

The construction uses Mathlib's right derived functors and the enough-injectives
instance for comodules. The invariants adjunction supplies left exactness. Computing
these functors by an explicit cofree complex is a separate comparison.

## References

* J. C. Jantzen, *Representations of Algebraic Groups I*, SFB/MPI 85-9 (1985),
  §§4.2 and 4.7.
-/

public section

open CategoryTheory

namespace TauCeti.ComoduleCat

universe u v w

variable (R : Type u) (H : Type v) [CommRing R] [Semiring H] [Bialgebra R H]
  [Module.Flat R H]

/-- Rational cohomology in degree `n`, as the right derived functor of comodule
invariants. Coefficients range over all comodules in the indicated universe. -/
noncomputable abbrev rationalCohomology (n : ℕ) :
    ComoduleCat.{u, v, max u v w} R H ⥤ ModuleCat.{max u v w} R :=
  (invariantsFunctor R H).rightDerived n

/-- Zeroth rational cohomology is naturally the invariant submodule. -/
noncomputable def rationalCohomologyZeroIso :
    rationalCohomology.{u, v, w} R H 0 ≅ invariantsFunctor R H :=
  (invariantsFunctor R H).rightDerivedZeroIsoSelf

end TauCeti.ComoduleCat
