/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.System
import TauCeti.Algebra.Lie.Weights.Dimension

/-!
# Dimension of the pinned Lie algebra

The pinned rational Lie algebra has one dimension for each root and one for each simple
coroot. The existing root-space dimension formula and `DynkinType.rootEquiv` give this count
without a second enumeration. It is useful when proving that a surjective matrix realization
of the pinned algebra is an isomorphism.
-/

public section

namespace TauCeti.DynkinType

/-- The dimension of the pinned Lie algebra is its rank plus its number of roots. -/
@[simp]
theorem finrank_lieAlgebra (t : DynkinType) (ht : t.Valid) :
    Module.finrank ℚ (t.lieAlgebra ht) = t.rank + t.numRoots := by
  have hcard : (t.cartanSubalgebra ht).root.card = t.numRoots := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr (t.rootEquiv ht)).symm.trans (Fintype.card_fin _)
  rw [finrank_eq_finrank_cartan_add_card_root (t.cartanSubalgebra ht),
    t.finrank_cartanSubalgebra ht, hcard]

end TauCeti.DynkinType
