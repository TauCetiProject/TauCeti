/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Geometry.Manifold.ChartedSpace
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.ModelWithCorners.Boundaryless
public import TauCeti.Geometry.Manifold.RegularValue.Level

/-!
# Regular levels and sublevels in dimension zero

Let `M` be a manifold modelled on a zero-dimensional space `E`, and `f : M → ℝ` any function. This
file reads off what the regular-level and boundary-face API of
`TauCeti.Geometry.Manifold.RegularValue` says in this edge case.

* **Every attained value is critical.** The derivative of `f` at a point is a linear map from the
  zero space, which is not onto `ℝ`. So a value is regular exactly when it is not attained
  (`TauCeti.isRegularValue_iff_notMem_range_of_subsingleton`), and a regular level is empty.
* **The levels have dimension `0`.** The level atlas `TauCeti.regularLevelChartedSpace` is modelled
  on `Fin n → ℝ` with `n = dim E - 1`. This truncated subtraction is `0 - 1 = 0` here, so the
  (empty) regular levels carry atlases modelled on `Fin 0 → ℝ`, as the second example below shows.
* **Sublevels are clopen and have no half-space model.** The manifold `M` is discrete
  (`ModelWithCorners.discreteTopology`), so every sublevel `{f ≤ a}` and every band `f⁻¹[a, b]` is
  clopen. The half-space atlas of a regular sublevel (`TauCeti.scalarRegularSublevelChartedSpace`)
  is modelled on `EuclideanHalfSpace (n + 1)` with `dim E = n + 1`, which fails here. In fact a
  nonempty sublevel has no atlas modelled on a half-space of any positive dimension: a charted space
  over a space without isolated points has no isolated points
  (`ChartedSpace.isEmpty_of_discreteTopology`), and such a half-space has none
  (`EuclideanHalfSpace.instPerfectSpace`).
-/

public section

open Set Module
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℝ} {a b c : ℝ}

/- In dimension zero a regular level is empty: every attained value is critical. -/
example (hc : IsRegularValue I 𝓘(ℝ) f c) : IsEmpty {x : M // f x = c} :=
  ⟨fun x ↦ isRegularValue_iff_notMem_range_of_subsingleton.1 hc ⟨x, x.property⟩⟩

/- In dimension zero the level atlas of a regular value is modelled on `Fin 0 → ℝ`: the dimension
`dim E - 1` of the levels is the truncated subtraction `0 - 1 = 0`. The smoothness hypothesis on
the level is vacuous, since the level is empty, and a model on the zero space has no boundary
(`ModelWithCorners.boundaryless_of_subsingleton`). -/
noncomputable example (hc : IsRegularValue I 𝓘(ℝ) f c) :
    ChartedSpace (Fin 0 → ℝ) {x : M // f x = c} :=
  regularLevelChartedSpace
    (fun x hx ↦ (isRegularValue_iff_notMem_range_of_subsingleton.1 hc ⟨x, hx⟩).elim) hc
    (by simp [finrank_zero_of_subsingleton])

/- In dimension zero every sublevel is clopen. -/
example : IsClopen {x : M | f x ≤ a} :=
  have := I.discreteTopology M
  isClopen_discrete _

/- In dimension zero every band is clopen. -/
example : IsClopen (f ⁻¹' Icc a b) :=
  have := I.discreteTopology M
  isClopen_discrete _

/- In dimension zero a nonempty sublevel has no atlas modelled on a half-space of positive
dimension `n + 1`. -/
example (n : ℕ) [Nonempty {x : M | f x ≤ a}] :
    IsEmpty (ChartedSpace (EuclideanHalfSpace (n + 1)) {x : M | f x ≤ a}) :=
  have := I.discreteTopology M
  ChartedSpace.isEmpty_of_discreteTopology _ _

end TauCeti
