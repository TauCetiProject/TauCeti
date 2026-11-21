/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Smooth.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Examples of smooth representations

For an open subgroup `U` of a topological group, the permutation representation on `A[G ⧸ U]` is
smooth and its basis vector at the base coset has stabilizer `U`. Every representation of a discrete
group is smooth, and so is every trivial representation. The left regular representation of the
nondiscrete group `ℚ₂`, written multiplicatively, has no nonzero smooth vector.
-/

open Representation

namespace TauCeti

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module A V]

example (U : OpenSubgroup G) : IsSmooth (ofMulAction A G (G ⧸ (U : Subgroup G))) :=
  inferInstance

example [Nontrivial A] (U : OpenSubgroup G) :
    (ofMulAction A G (G ⧸ (U : Subgroup G))).stabilizer
      (MonoidAlgebra.single (QuotientGroup.mk 1) 1) = U := by
  rw [stabilizer_ofMulAction_single _ one_ne_zero, MulAction.stabilizer_quotient]

example : IsSmooth (trivial A G V) := inferInstance

example [DiscreteTopology G] (ρ : Representation A G V) : ρ.smoothVectors = ⊤ := by simp

example : (leftRegular ℤ (Multiplicative ℚ_[2])).smoothVectors = ⊥ := by
  refine smoothVectors_leftRegular_eq_bot fun h ↦ ?_
  -- `Multiplicative ℚ_[2]` carries the topology of `ℚ_[2]` by definition, so `h` is
  -- discreteness of `ℚ_[2]` itself.
  have : DiscreteTopology ℚ_[2] := h
  exact (NormedField.nhdsNE_neBot (0 : ℚ_[2])).ne (discreteTopology_iff_nhds_ne.1 this 0)

end TauCeti
