/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.HermitianForm

/-!
# The trace of a real (1,1)-form relative to a Hermitian inner product

Let `E` be a finite-dimensional complex inner product space, whose inner product `h` plays the
role of a Hermitian metric, and let `α` be a real two-form on `E` of type (1,1), that is,
invariant under multiplication by `i`. Its Hermitian form `H_α(u, v) = α(u, i v) + i·α(u, v)`
(`ContinuousAlternatingMap.hermitianSesqForm`) is Hermitian, and its relative eigenvalue vector
`λ[α] = λ[H_α]` (`LinearMap.IsSymm.relEigenvalues`) is defined. This file proves

`Σ_j λ_j[α] = Σ_k α(u_k, i u_k)`

for every `h`-orthonormal basis `u`: the sum of the eigenvalues of `α` relative to `h` is the trace
`tr_ω α`, computed on the real frame `(u_k, i u_k)`. The right side is the sum that the
wedge-product form of the trace identity, `n·α ∧ ω^{n−1} = (tr_ω α)·ω^n`, produces on such a
frame.

## Main results

* `ContinuousAlternatingMap.sum_relEigenvalues_hermitianSesqForm`: `Σ_j λ_j[α] = Σ_k α(b_k, i b_k)`
  for an orthonormal basis `b` of `E`.
* `ContinuousAlternatingMap.sum_relEigenvalues_hermitianSesqForm_of_orthonormal`: the same for an
  orthonormal family `u` indexed by `Fin n`, `n = dim E`.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
-/

public section

open Complex Module

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {α : E [⋀^Fin 2]→L[ℝ] ℝ} (hα : ∀ u v : E, α ![I • u, I • v] = α ![u, v]) {n : ℕ}

include hα

/-- **The trace of a (1,1)-form.** For a real two-form `α` of type (1,1) on a finite-dimensional
complex inner product space, the eigenvalues of `H_α` relative to the inner product sum to
`Σ_k α(b_k, i b_k)` for any orthonormal basis `b`. -/
theorem sum_relEigenvalues_hermitianSesqForm {ι : Type*} [Fintype ι] (hn : finrank ℂ E = n)
    (b : OrthonormalBasis ι ℂ E) :
    ∑ j, (isSymm_hermitianSesqForm hα).relEigenvalues hn j = ∑ k, α ![b k, I • b k] := by
  rw [LinearMap.IsSymm.sum_relEigenvalues_eq_sum_re_apply _ hn b]
  simp [re_hermitianForm]

/-- **The trace of a (1,1)-form on an orthonormal frame.** For a real two-form `α` of type (1,1)
on a complex inner product space of dimension `n` and an orthonormal family `u` of `n` vectors,
`Σ_j λ_j[α] = Σ_k α(u_k, i u_k)`. -/
theorem sum_relEigenvalues_hermitianSesqForm_of_orthonormal (hn : finrank ℂ E = n)
    {u : Fin n → E} (hu : Orthonormal ℂ u) :
    ∑ j, (isSymm_hermitianSesqForm hα).relEigenvalues hn j = ∑ k, α ![u k, I • u k] := by
  rw [sum_relEigenvalues_hermitianSesqForm hα hn
    (OrthonormalBasis.mk hu (hu.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp [hn])).ge)]
  simp

end ContinuousAlternatingMap
