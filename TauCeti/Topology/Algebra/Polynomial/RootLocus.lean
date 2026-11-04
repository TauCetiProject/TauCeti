/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Polynomial.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Coefficient loci for roots in a compact set

For a compact subset `S` of a T₁ topological algebra, the monic polynomials of fixed
degree having a root in `S` form a closed set in coefficient space. Thus their indicators are
measurable whenever open sets are measurable. This applies in particular to compact valuation
balls, whose root loci occur in finite decompositions of root-count integrals.

The proof uses joint continuity of evaluation and closedness of projection along a compact
space. No separability or field hypothesis is needed.
-/

public section

namespace TauCeti.Polynomial

open _root_.Polynomial

/-- The coefficient vectors of monic polynomials having a root in a fixed compact subset of a
T₁ topological algebra form a closed set. The structure map is assumed continuous. -/
theorem isClosed_setOf_exists_aeval_monicOfCoeff_eq_zero
    {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [TopologicalSpace R] [TopologicalSpace A] [IsTopologicalSemiring A] [T1Space A]
    (hφ : Continuous (algebraMap R A)) {S : Set A} (hS : IsCompact S) (n : ℕ) :
    IsClosed {a : Fin n → R | ∃ z ∈ S, aeval z (monicOfCoeff a) = 0} := by
  let _ := isCompact_iff_compactSpace.mp hS
  have heval : Continuous fun p : (Fin n → R) × S ↦
      aeval (p.2 : A) (monicOfCoeff p.1) := by
    simp only [← eval_map_algebraMap, map_monicOfCoeff, eval_monicOfCoeff]
    exact ((continuous_subtype_val.comp continuous_snd).pow n).add
      (continuous_finsetSum _ fun i _ ↦
        (hφ.comp ((continuous_apply i).comp continuous_fst)).mul
          ((continuous_subtype_val.comp continuous_snd).pow (i : ℕ)))
  convert isClosedMap_fst_of_compactSpace _
    ((isClosed_singleton (x := (0 : A))).preimage heval) using 1
  ext a
  simp

end TauCeti.Polynomial
