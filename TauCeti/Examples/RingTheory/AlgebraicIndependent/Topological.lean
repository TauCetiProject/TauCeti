/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.AlgebraicIndependent.Topological
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Checks for the topological transcendence degree

The invariant `TauCeti.topologicalTrdeg` sees the topology of the extension field. It vanishes
for the trivial extension and for `ℂ_p` over `ℚ_p`, although `ℂ_p` has infinite transcendence
degree over `ℚ_p`; it equals the transcendence degree for the discrete topology, including the
infinite case; and over a complete algebraically closed field embedded isometrically it vanishes
only for the trivial extension.
-/

open Cardinal

namespace TauCeti.Examples

-- The identity extension has topological transcendence degree zero, for any topology.
example (K : Type*) [Field K] [TopologicalSpace K] : topologicalTrdeg K K = 0 :=
  topologicalTrdeg_self K

-- A dense intermediate field algebraic over `K` forces the value zero, whether or not `L / K` is
-- algebraic.
example {K L : Type*} [Field K] [Field L] [Algebra K L] [TopologicalSpace L]
    (A : IntermediateField K L) (hA : Dense (A : Set L)) [Algebra.IsAlgebraic K A] :
    topologicalTrdeg K L = 0 :=
  topologicalTrdeg_eq_zero_iff.mpr ⟨A, hA, inferInstance⟩

-- For the discrete topology and transcendence degree one, the value is one.
example {K L : Type*} [Field K] [Field L] [Algebra K L] [TopologicalSpace L] [DiscreteTopology L]
    (h : Algebra.trdeg K L = 1) : topologicalTrdeg K L = 1 := by
  simp [topologicalTrdeg_of_discreteTopology, h]

-- For the discrete topology and infinite transcendence degree, the value is `⊤`, not zero.
example {K L : Type*} [Field K] [Field L] [Algebra K L] [TopologicalSpace L] [DiscreteTopology L]
    (h : ℵ₀ ≤ Algebra.trdeg K L) : topologicalTrdeg K L = ⊤ := by
  simpa [topologicalTrdeg_of_discreteTopology] using h

-- The algebraic closure of `ℚ_p` is dense in `ℂ_p`, so `ℂ_p` has topological transcendence degree
-- zero over `ℚ_p`. A definition through the transcendence degree of `ℂ_p` itself fails this test.
example (p : ℕ) [Fact p.Prime] : topologicalTrdeg ℚ_[p] ℂ_[p] = 0 :=
  topologicalTrdeg_eq_zero_of_denseRange (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])
    UniformSpace.Completion.denseRange_coe

-- Over a complete algebraically closed normed field `K` embedded isometrically in a normed field
-- `L`, the value is zero exactly when the embedding is surjective; `L` need be neither complete
-- nor algebraically closed.
example {K L : Type*} [NormedField K] [CompleteSpace K] [IsAlgClosed K] [NormedField L]
    [Algebra K L] (h : Isometry (algebraMap K L)) :
    topologicalTrdeg K L = 0 ↔ Function.Surjective (algebraMap K L) :=
  topologicalTrdeg_eq_zero_iff_surjective h.isUniformInducing.isComplete_range.isClosed

end TauCeti.Examples
