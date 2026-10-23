/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.CenterQuotient
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Finite
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Reductive

/-!
# The represented center quotient of a semisimple group

This file proves that the represented center-quotient projection of a semisimple group is a
central isogeny and that its target is semisimple. The named quotient, its projection, their
universal property, and the fppf comparison are defined for reductive groups in
`Reductive.CenterQuotient`.

For a semisimple group, the center is finite. The represented center quotient is therefore the
target of a central isogeny and is again semisimple. Proving that its scheme-theoretic center is
trivial is a separate step toward identifying it as the adjoint form.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgProperty.isCentralIsogeny_centerQuotientι`: the named projection
  is a central isogeny.
* `TauCeti.semisimpleCommHopfAlgProperty.semisimple_centerQuotient`: the represented center
  quotient of a semisimple group is semisimple.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§5.c and 21.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15–16.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace semisimpleCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The represented center-quotient projection is a central isogeny. -/
theorem isCentralIsogeny_centerQuotientι (hH : semisimpleCommHopfAlgProperty k H) :
    CommHopfAlgCat.IsCentralIsogeny hH.reductive.centerQuotientι :=
  hH.reductive.isCentralIsogeny_centerQuotientι_of_moduleFinite hH.moduleFinite_centerCoordinate

/-- The represented quotient of a semisimple affine group by its scheme-theoretic center is
semisimple. -/
theorem semisimple_centerQuotient (hH : semisimpleCommHopfAlgProperty k H) :
    semisimpleCommHopfAlgProperty k hH.reductive.centerQuotient :=
  hH.of_isCentralIsogeny hH.reductive.centerQuotientι hH.isCentralIsogeny_centerQuotientι

end semisimpleCommHopfAlgProperty

end

end TauCeti
