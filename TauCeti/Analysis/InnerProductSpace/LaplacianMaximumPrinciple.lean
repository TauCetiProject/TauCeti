/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Order.Compact
public import TauCeti.Analysis.InnerProductSpace.LaplacianLocalExtr

/-!
# Boundary maximum principles for strictly subharmonic functions

`TauCeti.Analysis.InnerProductSpace.LaplacianLocalExtr` proves the local second-derivative
obstruction: a `C²` scalar function with `0 < Δ f x` has no local maximum at `x`.  This file
turns that local statement into the compact-set boundary form used as the first maximum-principle
handoff in the PDE roadmap.

If a continuous function on a compact set has positive Laplacian at every interior point where
the second derivative is available, then some maximum point lies on the frontier.  The dual
minimum statement holds for negative Laplacian.

## Main declarations

* `TauCeti.exists_mem_frontier_isMaxOn_of_laplacian_pos`: a strictly subharmonic function on
  the interior of a compact set attains a maximum on the frontier.
* `TauCeti.exists_mem_frontier_isMinOn_of_laplacian_neg`: a strictly superharmonic function on
  the interior of a compact set attains a minimum on the frontier.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A maximum over a set becomes a local maximum when the maximizing point is an interior point
of the set. -/
theorem IsMaxOn.isLocalMax_of_mem_interior {f : E → ℝ} {s : Set E} {x : E}
    (hmax : IsMaxOn f s x) (hx : x ∈ interior s) :
    IsLocalMax f x :=
  hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hx)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A minimum over a set becomes a local minimum when the minimizing point is an interior point
of the set. -/
theorem IsMinOn.isLocalMin_of_mem_interior {f : E → ℝ} {s : Set E} {x : E}
    (hmin : IsMinOn f s x) (hx : x ∈ interior s) :
    IsLocalMin f x :=
  hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hx)

/-- **Boundary maximum principle for strictly subharmonic functions.**

Let `K` be compact and nonempty. If `f` is continuous on `K`, is `C²` at every interior point,
and satisfies `0 < Δ f x` throughout `interior K`, then some maximum point of `f` on `K` lies on
`frontier K`. -/
theorem exists_mem_frontier_isMaxOn_of_laplacian_pos {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → 0 < Δ f x) :
    ∃ x ∈ frontier K, IsMaxOn f K x := by
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨x, ?_, hxmax⟩
  rw [frontier]
  refine ⟨subset_closure hxK, ?_⟩
  intro hxint
  exact not_isLocalMax_of_laplacian_pos (hcd hxint) (hlap hxint)
    (IsMaxOn.isLocalMax_of_mem_interior hxmax hxint)

/-- **Boundary minimum principle for strictly superharmonic functions.**

Let `K` be compact and nonempty. If `f` is continuous on `K`, is `C²` at every interior point,
and satisfies `Δ f x < 0` throughout `interior K`, then some minimum point of `f` on `K` lies on
`frontier K`. -/
theorem exists_mem_frontier_isMinOn_of_laplacian_neg {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x < 0) :
    ∃ x ∈ frontier K, IsMinOn f K x := by
  obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hne hcont
  refine ⟨x, ?_, hxmin⟩
  rw [frontier]
  refine ⟨subset_closure hxK, ?_⟩
  intro hxint
  exact not_isLocalMin_of_laplacian_neg (hcd hxint) (hlap hxint)
    (IsMinOn.isLocalMin_of_mem_interior hxmin hxint)

end TauCeti

end
