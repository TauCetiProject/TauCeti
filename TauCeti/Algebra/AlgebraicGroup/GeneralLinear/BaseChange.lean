/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Coordinate

/-!
# Base change of the general linear group scheme

The scheme-theoretic base change of `GL_n` along a morphism of commutative rings is canonically
isomorphic to the general linear group scheme constructed directly over the target ring. This is
the scheme-side form of `GeneralLinear.coordinateHopfAlgebraBaseChangeIso`.

## Main declaration

* `TauCeti.GeneralLinear.groupSchemeBaseChangeIso`: the canonical base-change isomorphism for
  general linear group schemes.

## Roadmap

This supplies general infrastructure for the base-change target in Layer 9 of the
ReductiveGroups roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (n : ℕ)

/-- The canonical identification of the base change of `GL_n/R` with `GL_n/S`. -/
noncomputable def groupSchemeBaseChangeIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
        (groupScheme R n) ≅ groupScheme S n :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.mapIso
      (eqToIso (groupScheme_def R n)) ≪≫
    AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso
      (coordinateHopfAlgebra R n) ≪≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of S)).mapIso
      (coordinateHopfAlgebraBaseChangeIso R S n).symm.op ≪≫
    eqToIso (groupScheme_def S n).symm

/-- The forward base-change comparison is the composite of the scheme presentation, affine
Hopf-spectrum base change, and the general-linear coordinate comparison. -/
theorem groupSchemeBaseChangeIso_hom :
    (groupSchemeBaseChangeIso R S n).hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.map
          (eqToHom (groupScheme_def R n)) ≫
        (AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso
          (coordinateHopfAlgebra R n)).hom ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of S)).map
          (coordinateHopfAlgebraBaseChangeIso R S n).symm.hom.op ≫
        eqToHom (groupScheme_def S n).symm := by
  rfl

end TauCeti.GeneralLinear
