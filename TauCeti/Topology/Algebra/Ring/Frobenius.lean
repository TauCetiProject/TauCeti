/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.Topology.Algebra.Monoid

/-!
# Continuity of the Frobenius automorphism

On a perfect ring of characteristic `p` with continuous multiplication, the Frobenius automorphism
`frobeniusEquiv R p : x ↦ x ^ p` is continuous, since `x ↦ x ^ p` is.

## Main statements

* `TauCeti.continuous_frobeniusEquiv`: the Frobenius automorphism is continuous.
-/

public section

namespace TauCeti

/-- The Frobenius automorphism `x ↦ x ^ p` of a perfect ring with continuous multiplication is
continuous. -/
theorem continuous_frobeniusEquiv (R : Type*) [CommSemiring R] [TopologicalSpace R]
    [ContinuousMul R] (p : ℕ) [ExpChar R p] [PerfectRing R p] :
    Continuous (frobeniusEquiv R p) :=
  (continuous_pow p).congr fun x => (frobeniusEquiv_def R p x).symm

end TauCeti
