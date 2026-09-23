/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Reductive.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Reductive.LinearlyReductive

/-!
# Geometrically linearly reductive affine group schemes are reductive

This module transfers the implication from geometric linear reductivity to reductivity from
coordinate Hopf algebras to finite-type affine group schemes.  The hypothesis says that the
coordinate Hopf algebra after scalar extension to an algebraic closure has completely reducible
finite-dimensional comodules.  Together with smoothness and geometric connectedness, this rules
out nontrivial geometric unipotent normal subgroups, hence gives reductivity.

## Main declaration

* `TauCeti.reductiveAffineGroupSchemeProperty.
  of_smooth_of_geometricallyConnected_of_coordinateBaseChange_linearlyReductive`:
  a smooth geometrically connected finite-type affine group scheme is reductive when the
  coordinate Hopf algebra of its geometric fibre is linearly reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 12.45 and §22.42.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 3.2 and 8.3.

The argument is the scheme-side form of the comparison between reductivity and complete
reducibility in the theory of affine algebraic groups.
-/

public section

namespace TauCeti

open AlgebraicGeometry Opposite

universe u

namespace reductiveAffineGroupSchemeProperty

open reductiveCommHopfAlgProperty

/-- A smooth geometrically connected finite-type affine group scheme is reductive when the
coordinate Hopf algebra of its geometric fibre is linearly reductive. -/
theorem of_smooth_of_geometricallyConnected_of_coordinateBaseChange_linearlyReductive
    (k : Type u) [Field k] (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hsm : Smooth G.obj.obj.X.hom)
    (hconn : GeometricallyConnected G.obj.obj.X.hom)
    (hlr : linearlyReductiveCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
        ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj
          G).unop).obj) :
    reductiveAffineGroupSchemeProperty k G := by
  rw [reductiveAffineGroupSchemeProperty_iff]
  apply of_smooth_of_geometricallyConnected_of_baseChange_linearlyReductive
  · exact (smooth_iff_algebraSmooth_coordinate k G).mp hsm
  · exact (geometricallyConnected_iff_geometricallyConnected_coordinate k G).mp hconn
  · exact hlr

end reductiveAffineGroupSchemeProperty

end TauCeti
