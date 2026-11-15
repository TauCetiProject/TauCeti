/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Geometric
public import TauCeti.Algebra.AlgebraicGroup.Reductive.NormalSubgroup
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Normal

/-!
# Derived subgroups of reductive and semisimple groups

The derived closed subgroup of a reductive affine group over any field is reductive; that of a
semisimple group is semisimple. These statements use the scheme-theoretic derived subgroup,
formed from the universal commutator morphism, rather than just commutators of rational points.

The normal-subgroup theorems apply because the derived subgroup is smooth and geometrically
connected by `Derived.Geometric`. No perfectness or characteristic hypothesis is needed.
Reductivity of the derived subgroup is a step toward its semisimplicity; the reductive result
here does not assert triviality of its radical or equality with the ambient group.
Semisimplicity is `TauCeti.reductiveCommHopfAlgProperty.semisimple_derived` in
`TauCeti.Algebra.AlgebraicGroup.Derived.Semisimple`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 21.
* A. Borel, *Linear Algebraic Groups*, §14.

The structural inputs are `TauCeti.reductiveCommHopfAlgProperty.quotient_of_isNormal` and
`TauCeti.semisimpleCommHopfAlgProperty.quotient_of_isNormal`.
-/

public section

namespace TauCeti

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The scheme-theoretic derived subgroup of a reductive affine group is reductive. -/
theorem reductiveCommHopfAlgProperty.derived (hH : reductiveCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H (CommHopfAlgCat.derivedDefiningIdeal H.obj)) :=
  hH.quotient_of_isNormal _ (CommHopfAlgCat.isNormal_derivedDefiningIdeal H.obj)
    ((smoothCommHopfAlgProperty_iff _).mp
      ((smoothCommHopfAlgProperty_iff H.obj).mpr hH.smooth).derived)
    hH.geometricallyConnected.derived

/-- The scheme-theoretic derived subgroup of a semisimple affine group is semisimple. -/
theorem semisimpleCommHopfAlgProperty.derived (hH : semisimpleCommHopfAlgProperty k H) :
    semisimpleCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H (CommHopfAlgCat.derivedDefiningIdeal H.obj)) :=
  hH.quotient_of_isNormal _ (CommHopfAlgCat.isNormal_derivedDefiningIdeal H.obj)
    ((smoothCommHopfAlgProperty_iff _).mp
      ((smoothCommHopfAlgProperty_iff H.obj).mpr hH.smooth).derived)
    hH.geometricallyConnected.derived

end TauCeti
