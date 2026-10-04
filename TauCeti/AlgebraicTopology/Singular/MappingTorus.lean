/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingTorus
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Singular chains of a mapping torus

The fibre of the mapping torus of `φ : F ≃ₜ F` has a canonical inclusion at height zero.
Traversing the cylinder from height zero to height one gives a homotopy from this inclusion after
`φ` to the inclusion itself.  This file transfers that homotopy to singular chains and homology.

Thus the inclusion coequalizes the identity and monodromy maps, first up to chain homotopy and
then on homology.  This is the elementary chain-level relation behind the endomorphism
`id - φ_*` in the Wang sequence of a mapping torus.

## Main declarations

* `TauCeti.MappingTorus.singularChainHomotopy`: the composite of the monodromy chain map with
  the fibre-inclusion chain map is chain-homotopic to the fibre-inclusion map.
* `TauCeti.MappingTorus.homologyMap_monodromy_comp_incl`: the corresponding equality on singular
  homology.

The construction follows the mapping-torus derivation of the Wang sequence; see A. Hatcher,
*Algebraic Topology*, Section 2.2.  The chain homotopy itself is obtained from Mathlib's
homotopy invariance of singular chains, `TopCat.Homotopy.singularChainComplexFunctorObjMap`.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The singular-chain map induced by monodromy followed by fibre inclusion is chain-homotopic
to the fibre-inclusion chain map. -/
def singularChainHomotopy :
    _root_.Homotopy
      (((singularChainComplexFunctor C).obj R).map
          (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))) ≫
        ((singularChainComplexFunctor C).obj R).map
          (TopCat.ofHom (TauCeti.MappingTorus.incl φ)))
      (((singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom (TauCeti.MappingTorus.incl φ))) := by
  let f : TopCat.of F ⟶ TopCat.of F := TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))
  let i : TopCat.of F ⟶ TopCat.of (TauCeti.MappingTorus φ) :=
    TopCat.ofHom (TauCeti.MappingTorus.incl φ)
  refine (_root_.Homotopy.ofEq
    (((singularChainComplexFunctor C).obj R).map_comp f i).symm).trans ?_
  -- `TopCat.Homotopy (f ≫ i) i` unfolds to a homotopy between the underlying continuous maps,
  -- whose composite `(incl φ).comp φ` is exactly the source of `monodromyHomotopy φ`.
  exact (show TopCat.Homotopy (f ≫ i) i from
    TauCeti.MappingTorus.monodromyHomotopy φ).singularChainComplexFunctorObjMap R

/-- On singular homology, the map induced by the fibre inclusion is unchanged after
precomposition with the monodromy map. -/
@[simp]
lemma homologyMap_monodromy_comp_incl [CategoryWithHomology C] (n : ℕ) :
    HomologicalComplex.homologyMap
          (((singularChainComplexFunctor C).obj R).map
            (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))) n ≫
        HomologicalComplex.homologyMap
          (((singularChainComplexFunctor C).obj R).map
            (TopCat.ofHom (TauCeti.MappingTorus.incl φ))) n =
      HomologicalComplex.homologyMap
        (((singularChainComplexFunctor C).obj R).map
          (TopCat.ofHom (TauCeti.MappingTorus.incl φ))) n := by
  rw [← HomologicalComplex.homologyMap_comp]
  exact (singularChainHomotopy φ R).homologyMap_eq n

end TauCeti.MappingTorus
