/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.TopBranchedCover.Deck
public import TauCeti.Combinatorics.RibbonGraph.Classification

/-!
# Deck groups of topological branched covers as ribbon-graph automorphisms

Identifies `deck X.π` with the automorphism group of the monodromy triple's ribbon graph.
-/

public noncomputable section

namespace TauCeti.TopBranchedCover

open ThricePuncturedSphere

variable {n : ℕ} (X : TopBranchedCover.{u} n) (ν : X.restrict ⁻¹' {basePt} ≃ Fin n)

/-- **The deck group of `X` is the automorphism group of the ribbon graph of its monodromy.** -/
def deckMulEquivRibbonGraphAut :
    deck X.π ≃* (X.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  (X.deckMulEquivAutomorphismGroup ν).trans
    (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroupMulEquivRibbonGraphAut

/-- On edges (`Fin n`), `deckMulEquivRibbonGraphAut` acts by the induced permutation on `1/2`. -/
@[simp] theorem deckMulEquivRibbonGraphAut_apply_edge (φ : deck X.π) (i : Fin n) :
    (X.deckMulEquivRibbonGraphAut ν φ).edge i = ν (φ • ν.symm i) :=
  (Equiv.congr_fun (PermutationTriple.automorphismGroupMulEquivRibbonGraphAut_edge _ _) i).trans
    (X.coe_deckMulEquivAutomorphismGroup_apply ν φ i)

/-- The deck transformation attached to `f` sends `ν.symm i` to `ν.symm (f.edge i)`. -/
@[simp] theorem deckMulEquivRibbonGraphAut_symm_smul
    (f : (X.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut) (i : Fin n) :
    (X.deckMulEquivRibbonGraphAut ν).symm f • ν.symm i = ν.symm (f.edge i) := by
  simp [deckMulEquivRibbonGraphAut]; rfl

end TauCeti.TopBranchedCover
