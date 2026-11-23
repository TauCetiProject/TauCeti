/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Pair

/-!
# Relative singular homology and fibre homotopy equivalences

A fibre homotopy equivalence over `B` induces isomorphisms on relative singular homology,
relative to the preimage of any subset of `B`
(`TauCeti.FiberHomotopyEquiv.isIso_singularHomologyMap_preimagePairMap`). No openness or
closedness assumption on that subset is needed: the inverse homotopies stay over the base and
hence preserve its preimage.
-/

public section

open CategoryTheory Limits

namespace TauCeti.FiberHomotopyEquiv

universe u v w w'

variable {E E' : Type u} {B : Type v}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {q : C(E', B)}

/-- **A fibre homotopy equivalence induces isomorphisms on relative singular homology**: its map
of pairs relative to the preimages of any subset of the base induces isomorphisms on relative
singular homology in every degree. -/
theorem isIso_singularHomologyMap_preimagePairMap (Φ : FiberHomotopyEquiv p q) (S : Set B)
    {C : Type w} [Category.{w'} C] [HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) :
    IsIso ((TopPair.ofSubset (X := TopCat.of E) (p ⁻¹' S)).singularHomologyMap
      (Φ.preimagePairMap S) R n) := by
  -- The homotopy for the other composite comes from `Φ.symm`, whose `symm` is `Φ` again.
  have H' := Φ.symm.preimagePairCompHomotopy S
  rw [symm_symm] at H'
  exact TopPair.isIso_singularHomologyMap _ _ (Φ.preimagePairCompHomotopy S) H' R n

end TauCeti.FiberHomotopyEquiv
