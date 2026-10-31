/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# The rank of a continuous family of projections

Let `p : B → F →L[𝕜] F` be a continuous family of idempotent operators on a Banach space `F`.
Near any `x₀`, the operator `p x * p x₀ + (1 - p x) * (1 - p x₀)` is invertible, since it equals
`1` at `x₀` and the units of `F →L[𝕜] F` form an open set. It then carries the range of `p x₀`
isomorphically onto the range of `p x` (`ContinuousLinearMap.IsIdempotentElem.rangeEquiv`), so
the ranges of nearby projections are isomorphic and the rank of the family is locally constant.
No compactness, separation or finite-dimensionality is assumed of the base or the fibres.

## Main results

* `TauCeti.eventually_nonempty_continuousLinearEquiv_range`: the ranges of nearby projections in
  a continuous family are isomorphic.
* `TauCeti.isLocallyConstant_finrank_range`: the rank of a continuous family of projections is
  locally constant.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6.
-/

public section

open Topology Filter

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] {p : B → F →L[𝕜] F}

/-- The ranges of nearby projections in a continuous family are isomorphic. -/
theorem eventually_nonempty_continuousLinearEquiv_range (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ : B) :
    ∀ᶠ x in 𝓝 x₀, Nonempty ((p x₀).range ≃L[𝕜] (p x).range) := by
  have hU : Continuous fun x ↦ p x * p x₀ + (1 - p x) * (1 - p x₀) :=
    (hp.mul continuous_const).add ((continuous_const.sub hp).mul continuous_const)
  have h₀ : IsUnit (p x₀ * p x₀ + (1 - p x₀) * (1 - p x₀)) := by
    rw [(hidem x₀).eq, (hidem x₀).one_sub.eq, add_sub_cancel]
    exact isUnit_one
  filter_upwards [(Units.isOpen.preimage hU).mem_nhds h₀]
    with x (hx : IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀)))
  exact ⟨ContinuousLinearMap.IsIdempotentElem.rangeEquiv (hidem x₀) (hidem x) hx⟩

/-- **The rank of a continuous family of projections is locally constant.** -/
theorem isLocallyConstant_finrank_range (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) :
    IsLocallyConstant fun x ↦ Module.finrank 𝕜 ((p x).range) :=
  (IsLocallyConstant.iff_eventually_eq _).mpr fun x₀ ↦
    (eventually_nonempty_continuousLinearEquiv_range hp hidem x₀).mono fun _ ⟨e⟩ ↦
      e.toLinearEquiv.finrank_eq.symm

end TauCeti
