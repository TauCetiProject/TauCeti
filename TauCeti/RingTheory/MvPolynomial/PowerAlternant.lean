/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant

/-!
# Nonvanishing of determinants of column- or row-disjoint variable powers

For a matrix whose (u, b) entry is X (v u b) ^ e u in a multivariate polynomial ring over a
nontrivial commutative ring R, if variables in distinct columns are disjoint ( u b = v u' b' →
b = b') and the exponents e u are pairwise distinct, then the determinant is nonzero. Collapsing
each column's variables to a single variable X b maps the determinant to the generalized
Vandermonde alternant TauCeti.alternant e, which is nonzero by
TauCeti.alternant_ne_zero_of_injective.

## Main results

* TauCeti.det_X_pow_ne_zero: nonvanishing of det (X (v u b) ^ e u) when  separates columns
  and e is injective.
* TauCeti.det_X_pow_transpose_ne_zero: the transposed version det (X (v u b) ^ e b) when 
  separates rows and e is injective.

## Provenance

TauCeti.det_X_pow_ne_zero is adapted from New.det_X_pow_ne_zero in
src/New/UpperBound/ElementaryDivisors/Depth.lean in grh-lean
(https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Matrix MvPolynomial

namespace TauCeti

variable {ι σ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Nontrivial R]

/-- If the variable indices  u b determine the column index  and the exponents e u are
pairwise distinct, then the determinant of the matrix (X (v u b) ^ e u)_{u, b} is nonzero over
any nontrivial commutative ring R. -/
theorem det_X_pow_ne_zero {v : ι → ι → σ} (hv : ∀ u u' b b' : ι, v u b = v u' b' → b = b')
    {e : ι → ℕ} (he : Function.Injective e) :
    (of fun u b : ι ↦ (X (v u b) : MvPolynomial σ R) ^ e u).det ≠ 0 := by
  classical
  let φ : MvPolynomial σ R →ₐ[R] MvPolynomial ι R :=
    aeval fun s ↦ if h : ∃ b u, v u b = s then X h.choose else 0
  have hφ (u b : ι) : φ (X (v u b)) = X b := by
    have h : ∃ b' u', v u' b' = v u b := ⟨b, u, rfl⟩
    simpa [φ, h] using congrArg (X (R := R)) (hv _ _ _ _ h.choose_spec.choose_spec)
  refine fun h_zero ↦ alternant_ne_zero_of_injective (R := R) he ?_
  rw [alternant_def, ← det_transpose, ← map_zero φ, ← h_zero, AlgHom.map_det]
  exact congrArg det (Matrix.ext fun b u ↦ by simp [hφ])

/-- Transposed form of det_X_pow_ne_zero: if the variable indices  u b determine the row
index u and the exponents e b are pairwise distinct, then the determinant of
(X (v u b) ^ e b)_{u, b} is nonzero. -/
theorem det_X_pow_transpose_ne_zero {v : ι → ι → σ}
    (hv : ∀ u u' b b' : ι, v u b = v u' b' → u = u') {e : ι → ℕ} (he : Function.Injective e) :
    (of fun u b : ι ↦ (X (v u b) : MvPolynomial σ R) ^ e b).det ≠ 0 := by
  rw [← det_transpose]
  exact det_X_pow_ne_zero (v := fun b u ↦ v u b) (fun u u' b b' h ↦ hv b b' u u' h) he

end TauCeti
