/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Additivity.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality

/-!
# Additivity of relative singular homology with local coefficients

The relative twisted chains of a disjoint union of pairs are the coproduct of the relative
chains of its summands, with the coefficient system restricted along each ambient inclusion.
The coproduct legs are induced by the actual pair inclusions. Exactness of coproducts of
modules then gives additivity of relative twisted homology in every degree.

The restriction of a coefficient system to a subspace commutes with pullback only up to its
canonical comparison isomorphism. The subspace cofan below retains this comparison, so that
the coproduct calculation applies to the short exact chain sequences of the pairs themselves.

The construction follows the cokernel argument for ordinary relative additivity in
`TauCeti.AlgebraicTopology.Singular.Additivity`, using `TopPair.subspaceSystemPullbackIso`
for the coefficient comparison and `TauCeti.isColimitCofanMkCokernelCofork` for the passage to
relative chains.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I–III.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti.LocalCoefficientSystem

universe u v w

namespace TopPair

variable {R : Type u} [Ring R] {ι : Type v} (P : ι → TopPair.{v})
  (L : TauCeti.LocalCoefficientSystem.{u, v, max v w} R (sigma P).fst)

/-- The twisted chains of the subspaces in a disjoint union of pairs form a coproduct.
The legs include the canonical restriction-pullback comparison. -/
def isColimitCofanTwistedSubspaceChainComplex :
    IsColimit (Cofan.mk ((sigma P).subspaceSystem L).twistedChainComplex
      (fun i ↦ twistedSubspaceChainComplexMap (sigmaι P i) L)) := by
  let e :
      Discrete.functor (fun i ↦ ((P i).subspaceSystem
        ((TauCeti.LocalCoefficientSystem.pullback
          (Hom.fst (sigmaι P i)).hom).obj L)).twistedChainComplex) ≅
      Discrete.functor (fun i ↦ ((TauCeti.LocalCoefficientSystem.pullback
        (TopCat.sigmaι (fun i ↦ (P i).snd) i).hom).obj
          ((sigma P).subspaceSystem L)).twistedChainComplex) :=
    Discrete.natIso fun i ↦ TauCeti.LocalCoefficientSystem.twistedChainComplexCoefficientIso
      (subspaceSystemPullbackIso (sigmaι P i.as) L)
  refine ((IsColimit.precomposeHomEquiv e _).symm
    (isColimitCofanTwistedChainComplex (fun i ↦ (P i).snd)
      ((sigma P).subspaceSystem L))).ofIsoColimit (Cocone.ext (Iso.refl _) ?_)
  intro i
  -- The subspace of `sigma P` and the subspace component of `sigmaι P i` use the
  -- absolute sigma carrier and inclusion, so the general leg formula applies directly.
  refine (Category.comp_id _).trans ?_
  dsimp [e]
  simp only [← Iso.app_hom, Discrete.natIso_app]
  erw [TauCeti.LocalCoefficientSystem.twistedChainComplexCoefficientIso_hom]
  exact (twistedSubspaceChainComplexMap_def (sigmaι P i.as) L).symm

/-- Relative twisted singular chains of a disjoint union of pairs are the coproduct of the
relative twisted chains of the summands, with their restricted coefficient systems. -/
def isColimitCofanTwistedChainComplex :
    IsColimit (Cofan.mk ((sigma P).twistedChainComplex L)
      (fun i ↦ twistedChainComplexMap (sigmaι P i) L)) := by
  -- State the cokernel cocones through their quotient maps, using their public characterization.
  have hc (Q : TopPair.{v}) (K : TauCeti.LocalCoefficientSystem.{u, v, max v w} R Q.fst) :
      IsColimit (CokernelCofork.ofπ (Q.twistedChainComplexπ K)
        (Q.twistedChainComplexMap_comp_twistedChainComplexπ K)) := by
    rw [← cokernelCoforkTwistedChainComplex_def]
    exact Q.isColimitCokernelCoforkTwistedChainComplex K
  exact TauCeti.isColimitCofanMkCokernelCofork
    (fun i ↦ hc (P i) ((TauCeti.LocalCoefficientSystem.pullback (Hom.fst (sigmaι P i)).hom).obj L))
    (isColimitCofanTwistedSubspaceChainComplex P L)
    (TauCeti.LocalCoefficientSystem.isColimitCofanTwistedChainComplex
      (fun i ↦ (P i).fst) L)
    (fun i ↦ (twistedChainComplexMap_naturality_pair (sigmaι P i) L).symm)
    (hc (sigma P) L) _
    (fun i ↦ twistedChainComplexπ_comp_twistedChainComplexMap (sigmaι P i) L)

/-- Relative twisted homology of a disjoint union of pairs is the coproduct of their relative
twisted homologies. This holds for arbitrary rings and local systems in every degree. -/
def isColimitCofanTwistedHomology (k : ℕ) :
    IsColimit (Cofan.mk ((sigma P).twistedHomology L k)
      (fun i ↦ twistedHomologyMap (sigmaι P i) L k)) := by
  have : AB4OfSize.{v} (ModuleCat.{max v w} R) := AB4OfSize_shrink.{v, w} _
  exact isColimitCofanMkObjOfIsColimit (HomologicalComplex.homologyFunctor _ _ k) _ _
    (isColimitCofanTwistedChainComplex P L)

end TopPair
