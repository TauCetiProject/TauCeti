/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.RingTheory.IsTensorProduct
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# A full lattice as an integral form of its ambient space

Let `L` be a `ℤ`-lattice in a finite-dimensional vector space `E` over a normed ordered field `K`,
that is, a discrete subgroup spanning `E`. Every `ℤ`-basis of `L` is a `K`-basis of `E`
(`Module.Basis.ofZLatticeBasis`), so `E` is the base change `K ⊗[ℤ] L` through the inclusion of
`L`. This is the analogue, for a normed field such as `ℝ` in place of the field of fractions `ℚ`,
of `Submodule.isBaseChange_subtype`.

In this form a lattice can be fed to statements about integral forms of a representation, such
as the comparison of the Herbrand quotients of two Galois-stable lattices in one real
representation (`TauCeti.TateCohomology.herbrandQuotient_eq_of_isBaseChange`).

## Main results

* `ZLattice.isBaseChange_subtype`: the inclusion of a full `ℤ`-lattice exhibits the ambient space
  as its base change to `K`.
-/

public section

open Module

namespace ZLattice

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E] [ProperSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L]

/-- **A full lattice is an integral form of its ambient space**: the inclusion of a discrete
`ℤ`-submodule `L` spanning `E` over `K` exhibits `E` as the base change `K ⊗[ℤ] L`. -/
theorem isBaseChange_subtype : IsBaseChange K L.subtype := by
  have := ZLattice.module_free K L
  -- `L.subtype` carries a `ℤ`-basis `b` of `L` to the `K`-basis `b.ofZLatticeBasis K L` of `E`
  let b := Free.chooseBasis ℤ L
  exact b.isBaseChange_of_map_basis (b.ofZLatticeBasis K L) L.subtype
    fun i ↦ (b.ofZLatticeBasis_apply K L i).symm

end ZLattice
