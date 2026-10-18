/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Center.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Coinvariants
public import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The represented center quotient of a reductive group

The quotient of a reductive affine group by its full scheme-theoretic center is represented
by the finite-type Hopf algebra of center-coinvariant functions. The coordinate inclusion is
faithfully flat and has the center as its scheme-theoretic kernel, including any nonreduced
structure.

This file names the quotient and projection and gives their universal property: a homomorphism
whose kernel contains the center factors uniquely through the quotient. A faithfully flat map
with kernel exactly the center identifies its target with the represented quotient.

The functor of points of the represented quotient is identified with the fppf center quotient,
compatibly with the quotient projections.

The construction uses smoothness of the reductive group and the general normal-coinvariant
quotient results. No semisimplicity or characteristic assumption is needed.

## Main declarations

* `TauCeti.reductiveCommHopfAlgProperty.centerQuotient`: the finite-type coordinate Hopf
  algebra of the quotient by the center.
* `TauCeti.reductiveCommHopfAlgProperty.centerQuotientι`: the coordinate inclusion representing
  the center-quotient projection.
* `TauCeti.reductiveCommHopfAlgProperty.liftCenterQuotient`: the universal factorization through
  the represented center quotient.
* `TauCeti.reductiveCommHopfAlgProperty.isIso_liftCenterQuotient_of_faithfullyFlat`: recognition
  of the quotient by its kernel and faithful flatness.

* `TauCeti.reductiveCommHopfAlgProperty.centerQuotientFppfIso`: representability of the fppf
  center quotient by `centerQuotient`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§5.c and 21.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15–16.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace reductiveCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The finite-type coordinate Hopf algebra of the quotient of a reductive affine group by its
scheme-theoretic center. It consists of the functions invariant under the center. -/
noncomputable def centerQuotient (hH : reductiveCommHopfAlgProperty k H) :
    FiniteTypeCommHopfAlgCat.{u, u} k := by
  letI : Algebra.Smooth k H := hH.smooth
  letI : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  let hnormal := (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal
  exact ⟨CommHopfAlgCat.coinvariants hnormal, hnormal.finiteType_coinvariants⟩

/-- The inclusion of center-coinvariant functions. Contravariantly, this is the quotient
projection from a reductive affine group to its represented center quotient. -/
noncomputable def centerQuotientι (hH : reductiveCommHopfAlgProperty k H) :
    (hH.centerQuotient).obj ⟶ H.obj := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.coinvariantsι
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal

/-- The represented center-quotient projection is faithfully flat. -/
theorem faithfullyFlat_centerQuotientι (hH : reductiveCommHopfAlgProperty k H) :
    hH.centerQuotientι.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.faithfullyFlat_coinvariantsι
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal

/-- The represented center-quotient projection has the full scheme-theoretic center as its
kernel, including any nonreduced structure. -/
@[simp]
theorem kernelHopfIdeal_centerQuotientι_eq (hH : reductiveCommHopfAlgProperty k H) :
    CommHopfAlgCat.kernelHopfIdeal hH.centerQuotientι =
      CommHopfAlgCat.centerDefiningIdeal H.obj := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal

/-- The represented center-quotient projection is a central isogeny when the scheme-theoretic
center is finite. -/
theorem isCentralIsogeny_centerQuotientι_of_moduleFinite
    (hH : reductiveCommHopfAlgProperty k H)
    (hfin : Module.Finite k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj)) :
    CommHopfAlgCat.IsCentralIsogeny hH.centerQuotientι := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.isCentralIsogeny_coinvariantsι
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj) hfin

/-- A homomorphism whose kernel contains the center factors through the represented center
quotient. -/
noncomputable def liftCenterQuotient (hH : reductiveCommHopfAlgProperty k H)
    {K : _root_.CommHopfAlgCat.{u} k} (f : K ⟶ H.obj)
    (hf : CommHopfAlgCat.kernelHopfIdeal f ≤ CommHopfAlgCat.centerDefiningIdeal H.obj) :
    K ⟶ hH.centerQuotient.obj := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.liftCoinvariants
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal f hf

/-- The factorization through the represented center quotient recovers the original
homomorphism. -/
@[reassoc (attr := simp)]
theorem liftCenterQuotient_comp_centerQuotientι (hH : reductiveCommHopfAlgProperty k H)
    {K : _root_.CommHopfAlgCat.{u} k} (f : K ⟶ H.obj)
    (hf : CommHopfAlgCat.kernelHopfIdeal f ≤ CommHopfAlgCat.centerDefiningIdeal H.obj) :
    hH.liftCenterQuotient f hf ≫ hH.centerQuotientι = f := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.liftCoinvariants_comp_coinvariantsι
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal f hf

/-- The factorization through the represented center quotient is unique. -/
theorem liftCenterQuotient_unique (hH : reductiveCommHopfAlgProperty k H)
    {K : _root_.CommHopfAlgCat.{u} k} (f : K ⟶ H.obj)
    (hf : CommHopfAlgCat.kernelHopfIdeal f ≤ CommHopfAlgCat.centerDefiningIdeal H.obj)
    (g : K ⟶ hH.centerQuotient.obj) (hg : g ≫ hH.centerQuotientι = f) :
    g = hH.liftCenterQuotient f hf := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.liftCoinvariants_unique
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal f hf g hg

/-- A homomorphism factors through the represented center quotient exactly when its kernel
contains the scheme-theoretic center. -/
theorem exists_comp_centerQuotientι_iff (hH : reductiveCommHopfAlgProperty k H)
    {K : _root_.CommHopfAlgCat.{u} k} (f : K ⟶ H.obj) :
    (∃ g : K ⟶ hH.centerQuotient.obj, g ≫ hH.centerQuotientι = f) ↔
      CommHopfAlgCat.kernelHopfIdeal f ≤ CommHopfAlgCat.centerDefiningIdeal H.obj := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.exists_comp_coinvariantsι_iff
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal f

/-- A faithfully flat map with kernel the source center identifies its target with the
represented center quotient on coordinate algebras. -/
theorem isIso_liftCenterQuotient_of_faithfullyFlat
    (hH : reductiveCommHopfAlgProperty k H)
    {K : _root_.CommHopfAlgCat.{u} k} (f : K ⟶ H.obj)
    (hf : (f.hom.toAlgHom : K →+* H).FaithfullyFlat)
    (hker : CommHopfAlgCat.kernelHopfIdeal f = CommHopfAlgCat.centerDefiningIdeal H.obj) :
    IsIso (hH.liftCenterQuotient f hker.le) := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  have hbij := CommHopfAlgCat.bijective_liftCoinvariants_of_faithfullyFlat
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal f hf hker
  exact (CommHopfAlgCat.isIsogeny_of_bijective _ hbij).isIso_iff_surjective.mpr hbij.2

/-- The fppf quotient of a reductive affine group by its center is represented by
`centerQuotient`. -/
noncomputable def centerQuotientFppfIso (hH : reductiveCommHopfAlgProperty k H) :
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
    (hH : reductiveCommHopfAlgProperty k H) :
    CommHopfAlgCat.centerQuotientFppfProjection H.obj ≫ (hH.centerQuotientFppfIso).hom =
      CommHopfAlgCat.pointsFppfGroupObjectMap hH.centerQuotientι := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  simpa only [CommHopfAlgCat.centerQuotientFppfProjection_def, centerQuotientFppfIso,
    centerQuotientι, centerQuotient] using
      (CommHopfAlgCat.fppfQuotientProjection_comp_coinvariantsFppfQuotientIso_hom
        (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal)

end reductiveCommHopfAlgProperty

end

end TauCeti
