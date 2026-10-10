/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh,
Claude Opus 5
-/
module

public import TauCeti.SetTheory.Cardinal.Lift
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Natural-number rank bounds for composites

Mathlib bounds the rank of a composite by the rank of either factor, but only
`LinearMap.rank_comp_le_left` is universe-monomorphic: the bound by the *right*
(inner) factor compares ranks living in the domain and codomain universes, so
Mathlib states it as `LinearMap.lift_rank_comp_le_right`, through
`Cardinal.lift`.

Whenever the bound is a natural number that lift is invisible
(`Cardinal.lift_le_natCast`), and a natural-number bound is all any
finite-rank-approximation argument ever propagates.  This module records the
resulting two lemmas — one per factor — and their `ContinuousLinearMap`
specializations, which is what lets rank bounds be transported across the
independent source and target universes of a `ContinuousLinearMap`.

## Main declarations

* `LinearMap.rank_comp_le_natCast_right`: the cross-universe bound, the reason
  this module exists.
* `ContinuousLinearMap.rank_comp_le_left`,
  `ContinuousLinearMap.rank_comp_le_natCast_right`: the continuous
  specializations, stated so that `(f ∘L g).rank` needs no unfolding at the
  call site.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original declarations: `ContinuousLinearMap.rank_comp_left_le_of_rank_le` and
  the private `ContinuousLinearMap.rank_comp_right_le_rank`, both stated inside
  `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean` (itself
  adapted from Mathlib PR #32126).
* Extraction class: **moved and generalized.**  The signature-polish backlog
  flagged the public one as rank plumbing shipped inside an operator-ideal
  file, dispositioned "privatize or reuse".  Privatizing is not available —
  it has independent consumers in three `DavisKahan` modules and in a
  sibling `ApproximationNumber` module — so it takes the other route already
  used for `Cardinal.lift_le_natCast`: state the
  mathematics where it belongs, in its own dependency-closed module, and leave
  the operator-ideal PR carrying no rank API.  The `LinearMap` statement is new;
  it is the content, and the continuous versions are one-line specializations.
* Upstream targets are two different files, hence the two namespaces here:
  `Mathlib/LinearAlgebra/Dimension/LinearMap.lean` for the `LinearMap` lemma,
  next to `lift_rank_comp_le_right`, and a topology-side file for the
  `ContinuousLinearMap` ones.
* Spectra influence: **none** — this module imports only Mathlib.
-/

public section

noncomputable section

universe u v v' v''

open Cardinal

namespace LinearMap

variable {K : Type u} [Semiring K]
variable {V : Type v} [AddCommMonoid V] [Module K V]
variable {V' : Type v'} [AddCommMonoid V'] [Module K V']
variable {V'' : Type v''} [AddCommMonoid V''] [Module K V'']

/-- A natural-number bound on the rank of the inner factor bounds the rank of a
composite, across independent universes.

This is `LinearMap.lift_rank_comp_le_right` with the lift discharged: the two
ranks live in different universes, but a natural-number bound does not
(`Cardinal.lift_le_natCast`).  Compare `LinearMap.rank_comp_le_right`, which
gets rid of the lift instead by forcing the outer codomain into the domain's
universe. -/
theorem rank_comp_le_natCast_right (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') {n : ℕ}
    (hg : rank g ≤ (n : Cardinal)) : rank (f.comp g) ≤ (n : Cardinal) :=
  Cardinal.lift_le_natCast.mp
    ((lift_rank_comp_le_right g f).trans (Cardinal.lift_le_natCast.mpr hg))

end LinearMap

namespace ContinuousLinearMap

variable {K : Type u} [Semiring K]
variable {V : Type v} [TopologicalSpace V] [AddCommMonoid V] [Module K V]
variable {V' : Type v'} [TopologicalSpace V'] [AddCommMonoid V'] [Module K V']
variable {V'' : Type v''} [TopologicalSpace V''] [AddCommMonoid V''] [Module K V'']

/-- Continuous version of `LinearMap.rank_comp_le_left`: composing on the right
does not raise the rank. -/
theorem rank_comp_le_left (g : V →L[K] V') (f : V' →L[K] V'') :
    (f ∘L g).rank ≤ f.rank :=
  LinearMap.rank_comp_le_left g.toLinearMap f.toLinearMap

/-- Continuous version of `LinearMap.rank_comp_le_natCast_right`: a
natural-number bound on the rank of the inner factor survives composition, in
the cross-universe generality a `ContinuousLinearMap` between independent spaces
needs. -/
theorem rank_comp_le_natCast_right (g : V →L[K] V') (f : V' →L[K] V'') {n : ℕ}
    (hg : g.rank ≤ (n : Cardinal)) : (f ∘L g).rank ≤ (n : Cardinal) :=
  LinearMap.rank_comp_le_natCast_right g.toLinearMap f.toLinearMap hg

end ContinuousLinearMap

end

end
