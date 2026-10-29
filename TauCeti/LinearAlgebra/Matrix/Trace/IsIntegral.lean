/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# The trace of an integral matrix is integral

Let `k` be a field which is an `R`-algebra. A square matrix `M` over `k` that is integral over
`R`, in the `R`-algebra of matrices, has a trace integral over `R`. Over an algebraic closure the
trace is the sum of the roots of the characteristic polynomial; each root lies in the spectrum, so
the spectral mapping inclusion makes it a root of any monic polynomial over `R` killing `M`.

Over an integrally closed `R` with fraction field `k` this places the trace in `R`, which is how
traces of integral elements of a noncommutative finite-dimensional algebra are controlled.

## Main results

* `Matrix.isIntegral_of_isRoot_charpoly`: the roots of the characteristic polynomial of a matrix
  integral over `R` are integral over `R`.
* `Matrix.isIntegral_trace`: the trace of a matrix integral over `R` is integral over `R`.
-/

public section

open Polynomial

namespace Matrix

variable {R k n : Type*} [CommRing R] [Field k] [Algebra R k] [Fintype n] [DecidableEq n]

/-- Every root of the characteristic polynomial of a matrix integral over `R` is integral over `R`:
it lies in the spectrum, so it is killed by every monic polynomial over `R` killing the matrix. -/
theorem isIntegral_of_isRoot_charpoly {M : Matrix n n k}
    (hM : IsIntegral R M) {μ : k} (hμ : M.charpoly.IsRoot μ) : IsIntegral R μ := by
  obtain ⟨p, hpm, hp⟩ := hM
  have hn : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Matrix.charpoly, Matrix.det_isEmpty] at hμ
  have hσ : (p.map (algebraMap R k)).eval μ ∈ spectrum k (aeval M (p.map (algebraMap R k))) :=
    spectrum.subset_polynomial_aeval M _ ⟨μ, Matrix.mem_spectrum_iff_isRoot_charpoly.2 hμ, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hp, spectrum.zero_eq, Set.mem_singleton_iff,
    eval_map_algebraMap] at hσ
  exact ⟨p, hpm, by rwa [← aeval_def]⟩

/-- **The trace of an integral matrix is integral.** If a square matrix `M` over a field `k` is
integral over `R`, then so is its trace. -/
theorem isIntegral_trace {M : Matrix n n k} (hM : IsIntegral R M) : IsIntegral R M.trace := by
  let K := AlgebraicClosure k
  have hM' : IsIntegral R (M.map (algebraMap k K)) :=
    hM.map ((IsScalarTower.toAlgHom R k K).mapMatrix (m := n))
  have htr : algebraMap k K M.trace = (M.map (algebraMap k K)).trace :=
    AddMonoidHom.map_trace (algebraMap k K).toAddMonoidHom M
  rw [← isIntegral_algebraMap_iff (B := K), htr,
    Matrix.trace_eq_sum_roots_charpoly]
  exact IsIntegral.multiset_sum fun μ hμ =>
    isIntegral_of_isRoot_charpoly hM' (isRoot_of_mem_roots hμ)

end Matrix
