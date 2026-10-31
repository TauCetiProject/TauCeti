/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Covariant derivatives of negatives, differences and finite sums of sections

Mathlib's `IsCovariantDerivativeOn` is additive on pairs of sections differentiable at a point of
the set it is a covariant derivative on. This file derives the corresponding statements for
negatives and differences, and iterates additivity to finite sums of sections.

## Main results

* `IsCovariantDerivativeOn.neg` and `IsCovariantDerivativeOn.sub`: a covariant derivative over
  `u` commutes with negation and subtraction of sections differentiable at a point of `u`.
* `TauCeti.Manifold.covariantDerivative_sum`: a covariant derivative over `u` commutes with finite
  sums of sections differentiable at a point of `u`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {x : M}
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}

/-- A covariant derivative over `u` commutes with finite sums of sections differentiable at a
point of `u`. -/
theorem covariantDerivative_sum {κ : Type*} {u : Set M} {s : Finset κ} {τ : κ → Π x : M, V x}
    (hcov : IsCovariantDerivativeOn F cov u) (hx : x ∈ u)
    (hτ : ∀ i ∈ s, MDiffAt (T% (τ i)) x) :
    cov (∑ i ∈ s, τ i) x = ∑ i ∈ s, cov (τ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hcov.zero hx
  | insert i s hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hτ
    have hsum : MDiffAt (T% (∑ j ∈ s, τ j)) x := by
      simpa [Finset.sum_apply] using
        MDifferentiableAt.sum_section (t := fun j (y : M) ↦ τ j y) (s := s) hτ.2
    rw [Finset.sum_insert hi, hcov.add hτ.1 hsum hx, ih hτ.2, Finset.sum_insert hi]

end TauCeti.Manifold

namespace IsCovariantDerivativeOn

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {u : Set M}
  {σ σ' : Π x : M, V x} {x : M}

/-- A covariant derivative over `u` sends the negative of a section differentiable at a point of
`u` to the negative of its covariant derivative there. -/
theorem neg (hcov : IsCovariantDerivativeOn F cov u) (hσ : MDiffAt (T% σ) x)
    (hx : x ∈ u := by trivial) :
    cov (-σ) x = -cov σ x := by
  rw [eq_neg_iff_add_eq_zero, ← hcov.add (mdifferentiableAt_neg_section hσ) hσ hx,
    neg_add_cancel, hcov.zero hx]

/-- A covariant derivative over `u` sends the difference of two sections differentiable at a point
of `u` to the difference of their covariant derivatives there. -/
theorem sub (hcov : IsCovariantDerivativeOn F cov u) (hσ : MDiffAt (T% σ) x)
    (hσ' : MDiffAt (T% σ') x) (hx : x ∈ u := by trivial) :
    cov (σ - σ') x = cov σ x - cov σ' x := by
  rw [sub_eq_add_neg, hcov.add hσ (mdifferentiableAt_neg_section hσ') hx, hcov.neg hσ' hx,
    ← sub_eq_add_neg]

end IsCovariantDerivativeOn
