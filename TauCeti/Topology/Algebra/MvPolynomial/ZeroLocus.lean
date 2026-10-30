/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Zero loci of polynomials are closed

Let `K` be a field with a topology in which the ring operations are continuous and points are
closed, such as `ℝ`, `ℂ` or a `p`-adic field, and let `k` be a field with `K` a `k`-algebra. The
common zeros in `K^σ` of an ideal of `k[X_σ]` form a closed set, since evaluating a polynomial is
continuous. Consequently the topological closure of a set of points lies in its Zariski closure,
the zero locus of its vanishing ideal: a polynomial identity holding on a set also holds on its
closure.

## Main results

* `MvPolynomial.isClosed_zeroLocus`: zero loci are closed.
* `MvPolynomial.closure_subset_zeroLocus_vanishingIdeal`: the closure of a set lies in the zero
  locus of its vanishing ideal.
-/

public section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [TopologicalSpace K]
  [IsTopologicalRing K] [T1Space K]

/-- In a field with continuous ring operations and closed points, the common zero locus of an
ideal of polynomials is closed. -/
theorem isClosed_zeroLocus (I : Ideal (MvPolynomial σ k)) : IsClosed (zeroLocus K I) := by
  have hI : zeroLocus K I =
      ⋂ p ∈ I, (fun x : σ → K ↦ eval x (map (algebraMap k K) p)) ⁻¹' {0} := by
    ext x
    simp [mem_zeroLocus_iff, aeval_def, eval_map]
  rw [hI]
  exact isClosed_biInter fun p _ ↦ isClosed_singleton.preimage (continuous_eval _)

/-- In a field with continuous ring operations and closed points, the closure of a set of points
lies in its Zariski closure, the zero locus of its vanishing ideal. -/
theorem closure_subset_zeroLocus_vanishingIdeal (V : Set (σ → K)) :
    closure V ⊆ zeroLocus K (vanishingIdeal k V) :=
  closure_minimal (zeroLocus_vanishingIdeal_le V) (isClosed_zeroLocus _)

end MvPolynomial
