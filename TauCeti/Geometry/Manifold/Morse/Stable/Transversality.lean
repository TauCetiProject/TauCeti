/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
public import TauCeti.Geometry.Manifold.TangentCone
import TauCeti.Dynamics.Flow.ConnectingOrbit

/-!
# Transverse intersections of unstable and stable manifolds

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, modelled on
`E`, and `X` a pseudo-gradient field adapted to `f`. For critical points `a` and `b`, the points of
`W^u(a) ∩ W^s(b)` are the points on the trajectories of the flow of `X` running from `a` to `b`.
Tangent spaces of subsets of `M` are taken intrinsically, as spans of the tangent cones
`TauCeti.mtangentConeAt` read in the preferred chart. The unstable manifold `W^u(a)` has tangent
spaces of dimension `ind a`, and the stable manifold `W^s(b)` has tangent spaces of dimension
`n - ind b`.

The **Morse–Smale condition** (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`) asks that
`W^u(a)` and `W^s(b)` meet transversally at every common point `y`: their tangent spaces at `y`
span the tangent space of `M`. This file proves the two basic consequences of transversality at a
point `y` of `W^u(a) ∩ W^s(b)`.

* Near `y`, the intersection is an embedded submanifold of dimension `ind a - ind b`: a chart of
  the maximal atlas flattens it onto the intersection of the two tangent spaces, which is its own
  tangent space at `y`. Under the Morse–Smale condition, `W^u(a) ∩ W^s(b)` is therefore a smooth
  manifold of dimension `ind a - ind b` with a smooth inclusion into `M`. This is the space of
  parametrized trajectories from `a` to `b`.
* If `a ≠ b`, the Morse index drops strictly: `ind b < ind a`. The velocity `X y` of the trajectory
  through `y` is tangent to the intersection and is nonzero, so the intersection has positive
  dimension.

These are the manifold forms of the results of `TauCeti.Analysis.Calculus.Morse.Transversality`
for a negative-gradient flow on a vector space. The intersection is read in the preferred chart at
`y`, where the slice charts of `W^u(a)` and `W^s(b)` given by
`TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_unstableSet` and
`TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_stableSet` meet transversally, and
`TauCeti.exists_isSliceChart_inter_of_span_mtangentConeAt_sup_eq_top` applies.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.finrank_span_mtangentConeAt_unstableSet` and
  `TauCeti.IsAdaptedPseudoGradient.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex`:
  the dimensions of the tangent spaces of the unstable and stable manifolds.
* `TauCeti.IsAdaptedPseudoGradient.mem_mtangentConeAt_of_isInvariant`: the velocity of a trajectory
  is tangent to every invariant set containing it, such as `W^u(a) ∩ W^s(b)`.
* `TauCeti.IsAdaptedPseudoGradient.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet`: a trajectory
  joining distinct critical points meets no critical point.
* `TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_inter_stableSet_chart`: a transverse
  intersection of an unstable and a stable manifold is flattened by a chart of the maximal atlas
  onto the intersection of their tangent spaces.
* `TauCeti.IsAdaptedPseudoGradient.span_mtangentConeAt_unstableSet_inter_stableSet` and
  `finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex` (in the same
  namespace): its tangent space is the intersection of the tangent spaces, of dimension
  `ind a - ind b`.
* `TauCeti.IsAdaptedPseudoGradient.manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet`:
  along a transverse trajectory joining distinct critical points, the Morse index drops strictly.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`: the Morse–Smale condition, with
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_unstableSet_inter_stableSet_isManifold`:
  the space of trajectories from `a` to `b` is a smooth manifold of dimension `ind a - ind b`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.2 (the Smale condition and the dimension of `W^u(a) ∩ W^s(b)`).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b y : M}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- The tangent space of the stable manifold of a critical point `b`, at any of its points, has
dimension `n - ind b`. -/
theorem finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hy : y ∈ hX.flow.stableSet b) :
    Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f b = Module.finrank ℝ E := by
  obtain ⟨L, q, hL, hyq, hq, hs⟩ := hX.exists_isSliceChart_stableSet hf hb hy
  rwa [hs.finrank_span_mtangentConeAt (by simp) hq L.closed_of_finiteDimensional hyq hy]

/-- The tangent space of the unstable manifold of a critical point `a`, at any of its points, has
dimension `ind a`. -/
theorem finrank_span_mtangentConeAt_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hy : y ∈ hX.flow.unstableSet a) :
    Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y)) =
      manifoldMorseIndex 𝓘(ℝ, E) f a := by
  obtain ⟨L, q, hL, hyq, hq, hs⟩ := hX.exists_isSliceChart_unstableSet hf ha hy
  rwa [hs.finrank_span_mtangentConeAt (by simp) hq L.closed_of_finiteDimensional hyq hy]

/-- The velocity `X y` of the trajectory through a point `y` of a set `S` invariant under the flow
is tangent to `S`, since the trajectory stays in `S`. This applies to `W^u(a) ∩ W^s(b)`. -/
theorem mem_mtangentConeAt_of_isInvariant {S : Set M} (hS : IsInvariant hX.flow S) (hy : y ∈ S) :
    X y ∈ mtangentConeAt 𝓘(ℝ, E) S y := by
  have h := ((hX.isMIntegralCurve_flow y).isMIntegralCurveAt 0).mem_mtangentConeAt (s := S)
    (Filter.Eventually.of_forall fun t ↦ hS t hy)
  rwa [Flow.map_zero_apply] at h

/-- The velocity `X y` of the trajectory through a point `y` of `W^u(a) ∩ W^s(b)` is tangent to
`W^u(a) ∩ W^s(b)`. -/
theorem mem_span_mtangentConeAt_unstableSet_inter_stableSet
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    X y ∈ Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) :=
  Submodule.subset_span
    (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_unstableSet_inter_stableSet a b) hy)

/-- **Connecting trajectories avoid the critical points.** A point `y` on a trajectory running from
a critical point `a` to a different critical point `b` is not a critical point of `f`: a critical
point is a rest point of the flow, and the constant orbit of `y` cannot have two different limits.
-/
theorem mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := fun h0 ↦ by
  have h01 : (0 : ℝ) = 1 :=
    Flow.orbit_injective_of_ne_of_mem_unstableSet_inter_stableSet hab hy
      (by simp [hX.flow_apply_of_mfderiv_eq_zero h0])
  exact zero_ne_one h01

/-- **Transverse unstable and stable manifolds meet in an embedded submanifold.** If the unstable
manifold of a critical point `a` and the stable manifold of a critical point `b` meet transversally
at `y`, then near `y` a chart of the maximal atlas flattens their intersection, the set of points
on trajectories from `a` to `b`, onto the intersection of their tangent spaces. -/
theorem exists_unstableSet_inter_stableSet_chart (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) :
          Submodule ℝ E) : Set E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) := by
  obtain ⟨L₁, q₁, -, hy₁, hq₁, h₁⟩ := hX.exists_isSliceChart_unstableSet hf ha hy.1
  obtain ⟨L₂, q₂, -, hy₂, hq₂, h₂⟩ :=
    hX.exists_isSliceChart_stableSet (hf.contMDiff.mdifferentiable (by simp)) hb hy.2
  exact exists_isSliceChart_inter_of_span_mtangentConeAt_sup_eq_top (by simp) hq₁ hq₂ h₁ h₂ hy₁
    hy₂ hy.1 hy.2 htr

/-- **The tangent space of a transverse intersection.** If the unstable manifold of a critical
point `a` and the stable manifold of a critical point `b` meet transversally at `y`, then the
tangent space of `W^u(a) ∩ W^s(b)` at `y` is the intersection of their tangent spaces. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) := by
  obtain ⟨L₁, q₁, -, hy₁, hq₁, h₁⟩ := hX.exists_isSliceChart_unstableSet hf ha hy.1
  obtain ⟨L₂, q₂, -, hy₂, hq₂, h₂⟩ :=
    hX.exists_isSliceChart_stableSet (hf.contMDiff.mdifferentiable (by simp)) hb hy.2
  exact span_mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top (by simp) hq₁ hq₂ h₁ h₂ hy₁
    hy₂ hy.1 hy.2 htr

/-- **The intersection has dimension the index difference.** If the unstable manifold of a critical
point `a` and the stable manifold of a critical point `b` meet transversally at `y`, then the
tangent space of `W^u(a) ∩ W^s(b)` at `y` has dimension `ind a - ind b`. -/
theorem finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex
    (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    Module.finrank ℝ (Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f b = manifoldMorseIndex 𝓘(ℝ, E) f a := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y))
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y))
  rw [htr, finrank_top, hX.finrank_span_mtangentConeAt_unstableSet hf ha hy.1,
    ← hX.span_mtangentConeAt_unstableSet_inter_stableSet hf ha hb hy htr] at hdim
  have hs := hX.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex
    (hf.contMDiff.mdifferentiable (by simp)) hb hy.2
  omega

/-- **The Morse index drops strictly along a transverse trajectory.** If a trajectory of the flow
runs from a critical point `a` to a different critical point `b`, and the unstable manifold of `a`
meets the stable manifold of `b` transversally at a point `y` of it, then `ind b < ind a`. -/
theorem manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    manifoldMorseIndex 𝓘(ℝ, E) f b < manifoldMorseIndex 𝓘(ℝ, E) f a := by
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf ha hb hy
      htr
  -- The velocity `X y` is tangent to `W^u(a) ∩ W^s(b)`, and it is nonzero since `y` is not a
  -- critical point.
  have hmem := hX.mem_span_mtangentConeAt_unstableSet_inter_stableSet hy
  have hX0 : X y ≠ 0 :=
    hX.ne_zero_of_mfderiv_ne_zero (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hab hy)
  have hpos : 0 < Module.finrank ℝ (Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y)) := by
    refine Nat.pos_of_ne_zero fun h ↦ hX0 ?_
    rw [Submodule.finrank_eq_zero.1 h] at hmem
    exact (Submodule.mem_bot ℝ).1 hmem
  omega

omit hX in
/-- **The Morse–Smale condition** for a pseudo-gradient `X` adapted to `f`: for all critical points
`a` and `b` of `f`, the unstable manifold of `a` and the stable manifold of `b` meet transversally
at each common point `y`, that is, their tangent spaces at `y` span the tangent space of `M`. -/
def IsMorseSmale (hX : IsAdaptedPseudoGradient f X) : Prop :=
  ∀ ⦃a b y : M⦄, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0 → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0 →
    y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b →
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤

omit hX in
/-- **The introduction rule for `IsMorseSmale`.** A pseudo-gradient is Morse–Smale once, at every
point `y` of `W^u(a) ∩ W^s(b)` for critical points `a` and `b`, the tangent spaces of `W^u(a)` and
`W^s(b)` span the tangent space of `M`. -/
theorem IsMorseSmale.of_forall {hX : IsAdaptedPseudoGradient f X}
    (h : ∀ ⦃a b y : M⦄, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0 → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0 →
      y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b →
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    hX.IsMorseSmale :=
  h

omit hX in
/-- **The pointwise elimination rule for `IsMorseSmale`.** Under the Morse–Smale condition, at a
point `y` of `W^u(a) ∩ W^s(b)` for critical points `a` and `b`, the tangent spaces of `W^u(a)` and
`W^s(b)` span the tangent space of `M`. -/
theorem IsMorseSmale.span_mtangentConeAt_sup_eq_top {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0)
    (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤ :=
  h ha hb hy

omit hX in
/-- **Spaces of trajectories are manifolds.** Under the Morse–Smale condition, if some trajectory
runs from a critical point `a` to a critical point `b`, then `W^u(a) ∩ W^s(b)` carries a smooth
manifold structure, modelled on a subspace of dimension `ind a - ind b`, with its subspace topology
and a smooth inclusion into `M`. -/
theorem IsMorseSmale.exists_unstableSet_inter_stableSet_isManifold
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hne : (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f b = manifoldMorseIndex 𝓘(ℝ, E) f a ∧
      ∃ C : ChartedSpace L ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b), letI := C
        IsManifold 𝓘(ℝ, L) ∞ ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b) → M) := by
  obtain ⟨y₀, hy₀⟩ := hne
  -- Every tangent space of the intersection has dimension `ind a - ind b`; model it on one of them.
  refine ⟨Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y₀),
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf ha hb hy₀
      (h ha hb hy₀), exists_isManifold_of_finrankSubspaceCharts fun y hy ↦ ?_⟩
  obtain ⟨q, hyq, hq, hs⟩ := hX.exists_unstableSet_inter_stableSet_chart hf ha hb hy (h ha hb hy)
  have hdim₀ :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf ha hb hy₀
      (h ha hb hy₀)
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf ha hb hy
      (h ha hb hy)
  rw [hX.span_mtangentConeAt_unstableSet_inter_stableSet hf ha hb hy (h ha hb hy)] at hdim
  exact ⟨q, _, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, isSliceChart_iff.1 hs, by omega⟩

omit hX in
/-- **Under the Morse–Smale condition, the Morse index drops along every trajectory** joining
distinct critical points: if a trajectory runs from `a` to `b ≠ a`, then `ind b < ind a`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0)
    (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hne : (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f b < manifoldMorseIndex 𝓘(ℝ, E) f a :=
  hX.manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet hf ha hb hab hne.some_mem
    (h ha hb hne.some_mem)

end IsAdaptedPseudoGradient

end TauCeti
