/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Additivity
public import TauCeti.Algebra.Homology.ShortComplex.Limit
public import TauCeti.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Additivity of singular cohomology with local coefficients

For a local coefficient system `L` on a disjoint union, the twisted cochain complex is the
product of the cochain complexes of the summands, with the restricted systems. Products of
modules are exact, so this remains a product after taking cohomology, in every degree. The
projections in both statements are the maps induced by the inclusions of the summands.

Here twisted cochains take values in a module `M`: they are `Hom(C_*(-; L), M)`, so the local
cohomology coefficients are the dual of `L` with values in `M`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.1 and 3.H.

The proof follows the ordinary additivity construction in
`TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic`, using the twisted chain coproduct
and Mathlib's preservation of products by the contravariant linear Yoneda functor.
-/

public section

noncomputable section

open CategoryTheory Limits TopCat

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {ι : Type v} (X : ι → TopCat.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (Σ i, X i)))
  (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)]
  (M : ModuleCat.{max v w} R)

/-- Twisted singular cochains of a disjoint union are the product of the twisted cochains of
the summands. The projections restrict cochains along the inclusions of spaces. -/
def isLimitFanTwistedCochainComplex :
    IsLimit (Fan.mk (L.twistedCochainComplex k M)
      (fun i ↦ twistedCochainComplexMap k M (sigmaι X i) L) :
      Fan fun i ↦ ((pullback (sigmaι X i).hom).obj L).twistedCochainComplex k M) :=
  isLimitFanMkObjOfIsLimit (ChainComplex.linearYonedaFunctor (α := ℕ) k M) _ _
    (Cofan.IsColimit.op (isColimitCofanTwistedChainComplex X L))

/-- In every degree, twisted singular cohomology of a disjoint union is the product of the
twisted cohomologies of its summands, through the inclusion-induced restriction maps. -/
def isLimitFanTwistedCohomology (n : ℕ) :
    IsLimit (Fan.mk (L.twistedCohomology k M n)
      (fun i ↦ twistedCohomologyMap k M (sigmaι X i) L n) :
      Fan fun i ↦ ((pullback (sigmaι X i).hom).obj L).twistedCohomology k M n) :=
  have : HasLimitsOfShape (Discrete ι) (ModuleCat.{max v w} k) := ModuleCat.hasLimitsOfShape
  isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor
    (ModuleCat.{max v w} k) (ComplexShape.up ℕ) n) _ _
      (isLimitFanTwistedCochainComplex X L k M)

end TauCeti.LocalCoefficientSystem
