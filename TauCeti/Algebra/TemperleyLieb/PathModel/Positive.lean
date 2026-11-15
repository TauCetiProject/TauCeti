/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.PathModel.Basic
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.LinearAlgebra.Matrix.Trace.Positive
public import TauCeti.RingTheory.TraceFunctional.Positive
public import Mathlib.Analysis.Matrix.Order

/-!
# Positive walk models for Temperley–Lieb algebras

On a finite simple graph `G` with base vertex `v₀` and self-adjoint vertex weights `r`, restricting
the path model of `TauCeti.Algebra.TemperleyLieb.PathModel.Basic` to the invariant subspace of
`n`-step walks `{s : Fin (n + 1) → V // G.IsWalkFrom v₀ s}` eliminates the zero-weight non-walk
states. When every vertex weight `r v` is nonzero, the diagonal weights `walkWeight G v₀ r` are
strictly positive, so the weighted matrix trace `walkPositiveLinearMap` is a faithful positive
functional on walk matrices whose pullback along `walkRep` equals `pathTrace`.

Combining this faithful positive matrix functional with Markov trace uniqueness identifies the
two-sided trace radical `(tr n).traceRadical` of any complex Markov trace with the representation
kernel `RingHom.ker (walkRep G v₀ hr hδ)` at every level `n` where `IsAdjEigenvectorUpTo G v₀ r δ n`
holds (`IsMarkovTrace.traceRadical_eq_ker_walkRep`). This requires neither surjectivity of `walkRep`
nor traciality of `walkPositiveLinearMap` on the ambient matrix algebra.

Use `open scoped ComplexOrder MatrixOrder` for the scalar and positive-semidefinite matrix orders
when applying `walkPositiveLinearMap`.

## Main definitions

* `TauCeti.TemperleyLieb.walkPositiveLinearMap`: the positive diagonal-weighted matrix trace on
  `n`-step walks from `v₀`.

## Main results

* `TauCeti.TemperleyLieb.walkWeight_pos`: nonzero self-adjoint vertex weights give strictly
  positive walk weights.
* `TauCeti.TemperleyLieb.walkPositiveLinearMap_conjTranspose_mul_self_eq_zero_iff`: faithfulness of
  `walkPositiveLinearMap` on matrix squares.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.traceRadical_eq_ker_walkRep` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_walkRep`: at any level where the
  bounded-horizon adjacency eigenvector equation holds, the trace radical equals `ker walkRep`.

## References

* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.4–4.5.
-/

public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace TauCeti.TemperleyLieb

section StarOrderedField

variable {K : Type*} [Field K] [StarRing K] [PartialOrder K] [StarOrderedRing K]
  {V : Type*} {G : SimpleGraph V} {v₀ : V} {r : V → K}

/-- Nonzero self-adjoint vertex weights give strictly positive walk weights. -/
theorem walkWeight_pos (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v)) {m : ℕ}
    (s : {s : Fin (m + 1) → V // G.IsWalkFrom v₀ s}) :
    0 < walkWeight G v₀ r s := by
  refine (walkWeight_nonneg hrs s).lt_of_ne' ?_
  rw [walkWeight_def]
  exact pow_ne_zero 2 (div_ne_zero (hr _) (hr _))

end StarOrderedField

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (v₀ : V) {r : V → 𝕜} {n : ℕ}

/-- The positive diagonal-weighted matrix functional on `n`-step walks from `v₀`. It is tracial on
the image of `walkRep`, though need not be tracial on all walk matrices. -/
noncomputable def walkPositiveLinearMap (hrs : ∀ v, IsSelfAdjoint (r v)) :
    Matrix {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s}
      {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s} 𝕜 →ₚ[𝕜] 𝕜 :=
  PositiveLinearMap.mk₀
    (traceLinearMap {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s} 𝕜 𝕜 ∘ₗ
      LinearMap.mulLeft 𝕜 (diagonal (walkWeight G v₀ r)))
    fun _ hA ↦ hA.posSemidef.trace_diagonal_mul_nonneg (walkWeight_nonneg hrs)

/-- Evaluating `walkPositiveLinearMap` gives the matrix trace weighted by `walkWeight`. -/
@[simp]
theorem walkPositiveLinearMap_apply (hrs : ∀ v, IsSelfAdjoint (r v))
    (A : Matrix {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s}
      {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s} 𝕜) :
    walkPositiveLinearMap G v₀ hrs A = (diagonal (walkWeight G v₀ r) * A).trace :=
  (rfl)

/-- Pulling `walkPositiveLinearMap` back along `walkRep` recovers `pathTrace`. -/
@[simp↓]
theorem walkPositiveLinearMap_walkRep (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
    {δ : 𝕜} (hδ : IsAdjEigenvectorUpTo G v₀ r δ n) (x : TemperleyLieb 𝕜 δ n) :
    walkPositiveLinearMap G v₀ hrs (walkRep G v₀ hr hδ x) = pathTrace G v₀ hr hδ x :=
  trace_diagonal_walkWeight_mul_walkRep hr hδ x

/-- When the adjacency eigenvector equation holds up to `n` steps with eigenvalue `δ`, the value of
`walkPositiveLinearMap` at the identity walk matrix is `δ ^ n`. -/
theorem walkPositiveLinearMap_one (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
    {δ : 𝕜} (hδ : IsAdjEigenvectorUpTo G v₀ r δ n) :
    walkPositiveLinearMap (n := n) G v₀ hrs 1 = δ ^ n := by
  rw [← map_one (walkRep G v₀ hr hδ), walkPositiveLinearMap_walkRep, pathTrace_one]

/-- When all vertex weights are nonzero, `walkPositiveLinearMap` is faithful on matrix squares. -/
@[simp↓]
theorem walkPositiveLinearMap_conjTranspose_mul_self_eq_zero_iff (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v))
    (A : Matrix {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s}
      {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s} 𝕜) :
    walkPositiveLinearMap G v₀ hrs (Aᴴ * A) = 0 ↔ A = 0 :=
  trace_diagonal_mul_conjTranspose_mul_self_eq_zero_iff (walkWeight_pos hr hrs) A

/-- `walkPositiveLinearMap` is tracial on the represented Temperley–Lieb algebra. -/
theorem walkPositiveLinearMap_walkRep_mul_comm (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) {δ : 𝕜} (hδ : IsAdjEigenvectorUpTo G v₀ r δ n)
    (x y : TemperleyLieb 𝕜 δ n) :
    walkPositiveLinearMap G v₀ hrs (walkRep G v₀ hr hδ x * walkRep G v₀ hr hδ y) =
      walkPositiveLinearMap G v₀ hrs (walkRep G v₀ hr hδ y * walkRep G v₀ hr hδ x) := by
  simp only [← map_mul, walkPositiveLinearMap_walkRep, pathTrace_mul_comm]

end RCLike

section Complex

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {v₀ : V} {r : V → ℂ}

variable (G v₀) in
/-- Viewed as a `StarPositiveFunctional`, `walkPositiveLinearMap` has trivial GNS null space when
every vertex weight is nonzero. -/
theorem nullSubmodule_ofPositiveLinearMap_walkPositiveLinearMap (hr : ∀ v, r v ≠ 0)
    (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ} :
    (StarPositiveFunctional.ofPositiveLinearMap
      (walkPositiveLinearMap (n := n) G v₀ hrs)).nullSubmodule = ⊥ := by
  ext A
  simp only [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    StarPositiveFunctional.ofPositiveLinearMap_apply, star_eq_conjTranspose,
    walkPositiveLinearMap_conjTranspose_mul_self_eq_zero_iff G v₀ hr hrs, Submodule.mem_bot]

/-- For a bounded-level Markov trace up to `N` strands, when nonzero self-adjoint vertex weights
satisfy `IsAdjEigenvectorUpTo G v₀ r δ N`, the trace radical at level `n ≤ N` equals the kernel of
`walkRep`. -/
theorem IsMarkovTraceUpTo.traceRadical_eq_ker_walkRep {δ : ℂ} [Fact (IsSelfAdjoint δ)] {N : ℕ}
    {tr : ∀ m, m ≤ N → TemperleyLieb ℂ δ m →ₗ[ℂ] ℂ} (htr : IsMarkovTraceUpTo ℂ δ N tr)
    (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v))
    (hδ : IsAdjEigenvectorUpTo G v₀ r δ N) {n : ℕ} (hn : n ≤ N) :
    (tr n hn).traceRadical (htr.map_mul_comm n hn) =
      RingHom.ker (walkRep G v₀ hr (hδ.mono hn)) := by
  let f : TemperleyLieb ℂ δ n →⋆ₐ[ℂ]
      Matrix {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s}
        {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s} ℂ :=
    { walkRep G v₀ hr (hδ.mono hn) with map_star' x := walkRep_star hr hrs (hδ.mono hn) x }
  have hf (x : TemperleyLieb ℂ δ n) : f x = walkRep G v₀ hr (hδ.mono hn) x := rfl
  have hker : (tr n hn).traceRadical (htr.map_mul_comm n hn) = RingHom.ker f :=
    (tr n hn).traceRadical_eq_ker_of_nullSubmodule_eq_bot (htr.map_mul_comm n hn)
      (StarPositiveFunctional.ofPositiveLinearMap (walkPositiveLinearMap G v₀ hrs))
      (nullSubmodule_ofPositiveLinearMap_walkPositiveLinearMap G v₀ hr hrs) f fun x ↦ by
        rw [StarPositiveFunctional.ofPositiveLinearMap_apply, hf, walkPositiveLinearMap_walkRep,
          htr.eq_pathTrace G v₀ hr hδ]
  exact hker.trans (by ext; simp [RingHom.mem_ker, hf])

/-- For any Markov trace at a self-adjoint loop parameter `δ` and any level `n` where nonzero
self-adjoint vertex weights satisfy `IsAdjEigenvectorUpTo G v₀ r δ n`, the two-sided trace radical
`(tr n).traceRadical` equals the kernel of `walkRep`. -/
theorem IsMarkovTrace.traceRadical_eq_ker_walkRep {δ : ℂ} [Fact (IsSelfAdjoint δ)]
    {tr : ∀ m : ℕ, TemperleyLieb ℂ δ m →ₗ[ℂ] ℂ} (htr : IsMarkovTrace ℂ δ tr)
    (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v)) {n : ℕ}
    (hδ : IsAdjEigenvectorUpTo G v₀ r δ n) :
    (tr n).traceRadical (htr.map_mul_comm n) = RingHom.ker (walkRep G v₀ hr hδ) :=
  (htr.isMarkovTraceUpTo n).traceRadical_eq_ker_walkRep hr hrs hδ le_rfl

end Complex

end TauCeti.TemperleyLieb
