/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient

/-!
# The quotient by a full lattice is compact

Let `L : Submodule ℤ E` be a full lattice, `IsZLattice ℝ L`, in a finite-dimensional real normed
space `E`. The orbit space `AddAction.orbitRel.Quotient L E` of translation by `L`, with the
additive group structure of `E ⧸ L` (`Submodule.orbitRelQuotientAddEquiv`), is the image of a
compact fundamental parallelepiped of the lattice, so it is compact. For a complex vector space
`E` this is the compactness of the complex torus `E / L`.

## Main results

* `Submodule.instCompactSpaceOrbitRelQuotient`: the quotient by a full lattice is compact.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.
-/

public section

/-- The quotient of a finite-dimensional real normed space by a full lattice is compact: it is the
image of a compact fundamental parallelepiped of the lattice. -/
instance Submodule.instCompactSpaceOrbitRelQuotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] : CompactSpace (AddAction.orbitRel.Quotient L E) := by
  refine isCompact_univ_iff.1 ?_
  rw [← Set.range_eq_univ.2 _root_.Quotient.mk_surjective]
  refine IsZLattice.isCompact_range_of_periodic L _ continuous_quotient_mk' fun z w hw ↦ ?_
  rw [Submodule.orbitRelQuotient_mk_add, (L.orbitRelQuotient_mk_eq_zero_iff).2 hw, add_zero]
