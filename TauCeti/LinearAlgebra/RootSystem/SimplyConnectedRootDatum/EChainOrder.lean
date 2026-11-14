/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.EChainOrder
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient

/-!
# The pinned `E₆`, `E₇` and `E₈` data in chain order

The pinned data `TauCeti.DynkinType.simplyConnectedRootDatum` of types `E₆`, `E₇` and `E₈` number
their simple roots in Bourbaki order, so that the simple root `i` is row `i` of `CartanMatrix.E`.
This file reads them in the chain order of `CartanMatrix.eChain`, in which nodes `0, …, r - 2` form
a chain and node `r - 1` is attached to node `2`, through the relabelling
`CartanMatrix.eChainEquiv`. It proves the Cartan and root equations of this reindexing on the
actual root indices of the pinned datum, and that the root columns in chain order are the orbits
of the coordinate columns under the reflections of `CartanMatrix.eChain`.

No root index is renumbered: only the nodes are relabelled. The root equation reads a root in the
fundamental-weight coordinates of the character lattice, listed in chain order; the root columns
are its simple-root coefficients, listed in chain order.

## Main results

* `TauCeti.DynkinType.eChain_apply_eq_cartanMatrix`: in types `E₆`, `E₇`, `E₈`, the chain-order
  Cartan matrix is the Cartan matrix of the type, relabelled by `CartanMatrix.eChainEquiv`.
* `TauCeti.DynkinType.pairing_simpleIndex_eChainEquiv`: the Cartan integers of the pinned datum at
  the chain-ordered simple roots are the entries of `CartanMatrix.eChain`.
* `TauCeti.DynkinType.root_simpleIndex_eChainEquiv_comp`: in chain-order coordinates the simple
  roots are the rows of `CartanMatrix.eChain`. The simple coroots are the coordinate vectors in
  chain-order coordinates, by `TauCeti.DynkinType.coroot_simpleIndex_equiv_comp` applied to
  `CartanMatrix.eChainEquiv`, which holds for any relabelling.
* `TauCeti.DynkinType.iUnion_orbit_single_eq_range_simpleRootCoefficients_comp_eChainEquiv`: the
  chain-order root columns are the orbits of the coordinate columns.

## References

Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI §4, Plates V–VII.
-/

public section

open Set Matrix CartanMatrix

namespace TauCeti.DynkinType

variable {t : DynkinType} (ht : t.Valid) (hE : t ∈ ({E6, E7, E8} : Set DynkinType))

include hE

omit ht in
/-- In types `E₆`, `E₇` and `E₈` the Cartan matrix of the type is the Bourbaki-numbered
`CartanMatrix.E` of its rank. -/
theorem cartanMatrix_eq_E : t.cartanMatrix = CartanMatrix.E t.rank := by
  rcases hE with rfl | rfl | rfl
  exacts [cartanMatrix_E6, cartanMatrix_E7, cartanMatrix_E8]

omit ht in
/-- **In types `E₆`, `E₇` and `E₈` the chain-order Cartan matrix is the Cartan matrix of the type,
relabelled from chain order to Bourbaki order.** -/
theorem eChain_apply_eq_cartanMatrix (i j : Fin t.rank) :
    eChain t.rank i j = t.cartanMatrix (eChainEquiv t.rank i) (eChainEquiv t.rank j) := by
  rw [cartanMatrix_eq_E hE, E_eChainEquiv_apply]

/-- **The Cartan integers of the pinned `E₆`, `E₇` and `E₈` data in chain order** are the entries of
`CartanMatrix.eChain`. -/
theorem pairing_simpleIndex_eChainEquiv (i j : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).pairing (t.simpleIndex ht (eChainEquiv t.rank i))
        (t.simpleIndex ht (eChainEquiv t.rank j)) =
      eChain t.rank i j :=
  t.pairing_simpleIndex_equiv ht _ (eChain_apply_eq_cartanMatrix hE) i j

/-- **The simple roots of the pinned `E₆`, `E₇` and `E₈` data in chain order**: read in the
chain-ordered fundamental-weight coordinates, the simple root at chain node `i` is row `i` of
`CartanMatrix.eChain`. -/
theorem root_simpleIndex_eChainEquiv_comp (i : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht (eChainEquiv t.rank i)) ∘
        eChainEquiv t.rank =
      eChain t.rank i :=
  t.root_simpleIndex_equiv_comp ht _ (eChain_apply_eq_cartanMatrix hE) i

/-- **The root columns of the pinned `E₆`, `E₇` and `E₈` data in chain order are the orbits of the
coordinate columns** under the reflections of `CartanMatrix.eChain`, including the columns of
negative roots. -/
theorem iUnion_orbit_single_eq_range_simpleRootCoefficients_comp_eChainEquiv :
    ⋃ i : Fin t.rank,
        MulAction.orbit ((eChain t.rank).columnReflectionGroup (eChain_apply_same t.rank))
          (Pi.single i 1 : Fin t.rank → ℤ) =
      range fun k ↦ t.simpleRootCoefficients ht k ∘ eChainEquiv t.rank :=
  t.iUnion_orbit_single_eq_range_simpleRootCoefficients_comp ht _
    (eChain_apply_eq_cartanMatrix hE) _

end TauCeti.DynkinType
