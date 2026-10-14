/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Coinvariants
public import TauCeti.Algebra.AlgebraicGroup.Center.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Isogeny.Basic
public import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The represented quotient by the center

The fppf quotient of a geometrically reduced finite-type affine group by its scheme-theoretic
center is represented by the Hopf algebra of center-coinvariant functions. For a semisimple
group, this file gives that finite-type coordinate Hopf algebra and its projection canonical
names, records its scheme-theoretic kernel, and identifies its functor of points with the fppf
center quotient.

For a semisimple group, the center is finite. The represented center quotient is therefore the
target of a central isogeny and is again semisimple. Proving that its scheme-theoretic center is
trivial is a separate step toward identifying it as the adjoint form.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgProperty.centerQuotient`: the finite-type coordinate Hopf
  algebra of the quotient by the center.
* `TauCeti.semisimpleCommHopfAlgProperty.centerQuotientι`: the coordinate inclusion representing
  the center-quotient projection.
* `TauCeti.semisimpleCommHopfAlgProperty.centerQuotientFppfIso`: representability of the fppf
  center quotient by `centerQuotient`.
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

/-- The finite-type coordinate Hopf algebra of the quotient of a semisimple affine group by its
scheme-theoretic center. It consists of the functions invariant under the center. -/
@[expose] noncomputable def centerQuotient (hH : semisimpleCommHopfAlgProperty k H) :
    FiniteTypeCommHopfAlgCat.{u, u} k := by
  letI : Algebra.Smooth k H := hH.smooth
  letI : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  let hnormal := (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal
  exact ⟨CommHopfAlgCat.coinvariants hnormal, hnormal.finiteType_coinvariants⟩

/-- The inclusion of center-coinvariant functions. Contravariantly, this is the quotient
projection from a semisimple affine group to its represented center quotient. -/
@[expose] noncomputable def centerQuotientι (hH : semisimpleCommHopfAlgProperty k H) :
    (hH.centerQuotient).obj ⟶ H.obj := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.coinvariantsι
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal

/-- The represented center-quotient projection has the full scheme-theoretic center as its
kernel, including any nonreduced structure. -/
@[simp]
theorem kernelHopfIdeal_centerQuotientι_eq (hH : semisimpleCommHopfAlgProperty k H) :
    CommHopfAlgCat.kernelHopfIdeal hH.centerQuotientι =
      CommHopfAlgCat.centerDefiningIdeal H.obj := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal

/-- The fppf quotient of a semisimple affine group by its center is represented by
`centerQuotient`. -/
noncomputable def centerQuotientFppfIso (hH : semisimpleCommHopfAlgProperty k H) :
    CommHopfAlgCat.centerQuotientFppfSheaf H.obj ≅
      CommHopfAlgCat.pointsFppfGroupObject hH.centerQuotient.obj := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.coinvariantsFppfQuotientIso
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal

/-- Under representability, the fppf center-quotient projection is the affine group morphism
induced by the inclusion of center-coinvariant functions. -/
@[reassoc (attr := simp), simp]
theorem centerQuotientFppfProjection_comp_centerQuotientFppfIso_hom
    (hH : semisimpleCommHopfAlgProperty k H) :
    CommHopfAlgCat.centerQuotientFppfProjection H.obj ≫ (hH.centerQuotientFppfIso).hom =
      CommHopfAlgCat.pointsFppfGroupObjectMap hH.centerQuotientι := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  simpa only [CommHopfAlgCat.centerQuotientFppfProjection_def, centerQuotientFppfIso,
    centerQuotientι, centerQuotient] using
      (CommHopfAlgCat.fppfQuotientProjection_comp_coinvariantsFppfQuotientIso_hom
        (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal)

/-- The projection from a semisimple affine group to its represented center quotient is a
central isogeny. -/
theorem isCentralIsogeny_centerQuotientι (hH : semisimpleCommHopfAlgProperty k H) :
    CommHopfAlgCat.IsCentralIsogeny hH.centerQuotientι := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact hH.isCentralIsogeny_coinvariantsι_centerDefiningIdeal

/-- The represented quotient of a semisimple affine group by its scheme-theoretic center is
semisimple. -/
theorem semisimple_centerQuotient (hH : semisimpleCommHopfAlgProperty k H) :
    semisimpleCommHopfAlgProperty k hH.centerQuotient := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact hH.of_isCentralIsogeny hH.centerQuotientι hH.isCentralIsogeny_centerQuotientι

end semisimpleCommHopfAlgProperty

end

end TauCeti
