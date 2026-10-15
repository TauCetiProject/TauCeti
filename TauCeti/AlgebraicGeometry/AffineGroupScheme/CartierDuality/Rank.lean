/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.CartierDuality.FiniteLocallyFree
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Rank
public import TauCeti.LinearAlgebra.Dual.Rank

/-!
# Cartier duality preserves rank

For a finite locally free commutative affine group scheme over a commutative ring, the Cartier
dual has the same scheme-theoretic rank at every point of the base. Thus the statement also
applies when rank varies between components, and does not require the base to be reduced or
the rank to be invertible.

We compare the structural morphism with the spectrum of the coordinate Hopf algebra using the
existing Hopf-spectrum anti-equivalence. The coordinate algebra of the Cartier dual is the
finite linear dual, whose local rank equals that of the original finite projective module.
This rank identity is used when passing between finite subgroup schemes and their duals.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé VIIA, §3.3.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat

open finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

universe u

variable (R : Type u) [CommRing R]

/-- The scheme-theoretic rank of a finite locally free commutative affine group scheme is
the local rank of its coordinate Hopf algebra. -/
@[simp↓]
theorem finrank_eq_rankAtStalk_coordinateHopfAlgebra
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R))
    (x : PrimeSpectrum R) :
    G.obj.obj.X.hom.finrank x = Module.rankAtStalk (R := R) (coordinateHopfAlgebra R G) x := by
  let e := CommHopfAlgCat.ofIso ((rightOpInverseCompιIso R).app (op G))
  exact (AffineGroupSchemeCat.finrank_eq_rankAtStalk_coordinateHopfAlgebra R G.obj x).trans
    (congrFun (Module.rankAtStalk_eq_of_equiv e.toAlgEquiv.toLinearEquiv) x).symm

/-- Cartier duality preserves the entire locally constant rank function over the affine base. -/
@[simp]
theorem finrank_cartierDual
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    (cartierDual R G).obj.obj.X.hom.finrank = G.obj.obj.X.hom.finrank := by
  ext x
  let e := CommHopfAlgCat.ofIso
    ((forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat R) (CommHopfAlgCat R)).mapIso
      (coordinateHopfAlgebraCartierDualIso R G))
  calc
    _ = Module.rankAtStalk (R := R) (coordinateHopfAlgebra R (cartierDual R G)) x :=
      finrank_eq_rankAtStalk_coordinateHopfAlgebra R (cartierDual R G) x
    _ = Module.rankAtStalk (R := R)
        (FiniteLocallyFreeBicommutativeHopfAlgCat.dual (coordinateHopfAlgebra R G)) x :=
      congrFun (Module.rankAtStalk_eq_of_equiv e.toAlgEquiv.toLinearEquiv) x
    _ = Module.rankAtStalk (R := R) (Module.Dual R (coordinateHopfAlgebra R G)) x :=
      congrFun (Module.rankAtStalk_eq_of_equiv (WithConv.linearEquiv R _)) x
    _ = Module.rankAtStalk (R := R) (coordinateHopfAlgebra R G) x :=
      congrFun (Module.rankAtStalk_dual R (coordinateHopfAlgebra R G)) x
    _ = _ := (finrank_eq_rankAtStalk_coordinateHopfAlgebra R G x).symm

end TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat
