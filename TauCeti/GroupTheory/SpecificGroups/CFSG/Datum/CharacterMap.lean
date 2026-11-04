/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Steinberg
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GeckCarrier
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.CharacterMap

/-!
# The root-datum Steinberg maps as character maps on the Geck carrier

`TauCeti.ValidLieTypeIndex.datumFrobenius` and `TauCeti.GraphTwistedIndex.datumSteinberg` are the
shadows of `Frob_q` and of `γ ∘ Frob_q` on the pinned simply connected root datum: isogenies whose
weight maps are the pullbacks of characters along the group endomorphisms they stand for. This file
proves that on the pinned Geck carrier those weight maps are the character maps
(`TauCeti.IsCharacterMap`) of actual endomorphisms of the point group over the algebraic closure
of the prime field, acting on its weight torus `TauCeti.ValidLieTypeIndex.geckWeightTorus`.

* The `q`-power Frobenius `TauCeti.ValidLieTypeIndex.geckFrobenius` has character map the weight
  map of `datumFrobenius`, multiplication by `q`.
* For a graph-twisted index, the composite of the pinned graph automorphism of the index's diagram
  permutation with the `q`-power Frobenius, `TauCeti.DynkinType.geckTwistedFrobenius`, has character
  map the weight map of `datumSteinberg`. The inverse that `datumSteinberg` takes of the
  root-datum graph automorphism is exactly the inverse in the character map of the graph
  automorphism of the carrier, `TauCeti.DynkinType.isCharacterMap_geckGraphAutPoints`.

The Geck module is the adjoint module, so its weights span the root lattice, which is the full
character lattice only for `E₈`, `F₄` and `G₂`, the branches this carrier serves. For the other
diagrams the torus parametrization is not injective in general: its kernel is the group of
characters of the weight lattice modulo the root lattice, which is trivial only when that quotient
is a `p`-group for the characteristic `p`. So uniqueness of character maps
(`TauCeti.IsCharacterMap.unique`) needs additional hypotheses there. Nothing here identifies the
Geck carrier with the pinned simply connected group, or with the ambient group of a graph-twisted
branch, so no statement is made about the Steinberg endomorphisms of those branches.

## Main results

* `TauCeti.ValidLieTypeIndex.isCharacterMap_geckFrobenius`: the root-datum Frobenius is a character
  map of the Frobenius of the Geck carrier.
* `TauCeti.GraphTwistedIndex.isCharacterMap_geckTwistedFrobenius`: the root-datum Steinberg map of
  a graph-twisted index is a character map of the graph-twisted Frobenius of the Geck carrier.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §11.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti

/-- **The root-datum Frobenius is a character map of the Frobenius of the Geck carrier**: the
`q`-power Frobenius raises every point of the weight torus to its `q`-th power, which is the
pullback of characters by multiplication by `q`. -/
theorem ValidLieTypeIndex.isCharacterMap_geckFrobenius (d : ValidLieTypeIndex) :
    IsCharacterMap d.geckWeightTorus d.geckFrobenius d.datumFrobenius.weightMap := by
  rw [datumFrobenius_weightMap, d.fieldOrder_eq_characteristic_pow, ← Module.End.one_eq_id,
    geckFrobenius_def, geckWeightTorus_def]
  exact d.dynkinType.isCharacterMap_geckFrobenius d.dynkinType_valid _ _ _

/-- **The root-datum Steinberg map of a graph-twisted index is a character map of the graph-twisted
Frobenius of the Geck carrier**, the pinned graph automorphism of the index's diagram permutation
after the `q`-power Frobenius. -/
theorem GraphTwistedIndex.isCharacterMap_geckTwistedFrobenius (d : GraphTwistedIndex) :
    IsCharacterMap d.1.geckWeightTorus
      (d.1.dynkinType.geckTwistedFrobenius d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
        d.1.characteristic d.1.fieldExponent d.1.Closure)
      d.datumSteinberg.weightMap := by
  rw [datumSteinberg_weightMap, d.1.fieldOrder_eq_characteristic_pow, LinearMap.comp_smul,
    LinearMap.comp_id, ValidLieTypeIndex.geckWeightTorus_def, datumGraphAut_def]
  exact d.1.dynkinType.isCharacterMap_geckTwistedFrobenius d.1.dynkinType_valid _ _ _ _

end TauCeti
