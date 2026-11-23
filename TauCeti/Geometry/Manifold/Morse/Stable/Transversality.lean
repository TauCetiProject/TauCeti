/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
public import TauCeti.Geometry.Manifold.TangentCone.Basic
import TauCeti.Dynamics.Flow.ConnectingOrbit
import TauCeti.Geometry.Manifold.Flow.HittingTime
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

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

The same dimension count applies to any set `Z` flattened by a chart, of dimension `n - ind q` and
transverse to `W^u(q)` at a regular point `y`: the tangent spaces of `Z` and `W^u(q)` at `y` meet
in `0`, so the velocity `X y` is not tangent to `Z`. Near `y` an orbit then meets `Z` at most once,
by the local uniqueness of hitting times of a transverse section
(`TauCeti.eventually_eq_flowHittingTime_iff`).

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
* `TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_inter_stableSet_isManifold`: an
  intersection that is transverse at each of its points is a smooth manifold of dimension
  `ind a - ind b`.

* `TauCeti.IsAdaptedPseudoGradient.manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet`:
  along a transverse trajectory joining distinct critical points, the Morse index drops strictly.
* `TauCeti.IsAdaptedPseudoGradient.notMem_span_mtangentConeAt_of_isSliceChart`: a set flattened
  by a chart, of dimension `n - ind q` and transverse to `W^u(q)` at a regular point `y`, is
  transverse to the flow at `y`.
* `TauCeti.IsAdaptedPseudoGradient.eventually_eq_zero_of_flow_eq_of_isSliceChart`: near a regular
  point, an orbit meets a flattened set transverse to the flow at most once.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`: the Morse–Smale condition, with
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_unstableSet_inter_stableSet_isManifold`:
  the space of trajectories from `a` to `b` is a smooth manifold of dimension `ind a - ind b`.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.neg`: reversing a Morse–Smale pseudo-gradient
  gives a Morse–Smale pseudo-gradient.
* `span_mtangentConeAt_unstableSet_sup_span_mtangentConeAt_stableSet_self` (in the namespace
  `TauCeti.IsAdaptedPseudoGradient`): `W^u(x)` and `W^s(x)` are transverse at the critical point
  `x`.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.of_forall_ne_of_manifoldMorseIndex_ne`: the
  Morse–Smale condition need only be checked between distinct critical points whose indices both
  differ from `0` and `n`.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.of_subsingleton` and
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.of_manifoldMorseIndex_eq_zero_or_eq_finrank`: if at
  most one critical point has an index other than `0` and `n`, in particular if none has, every
  adapted pseudo-gradient is Morse–Smale.

The chart, tangent-space, dimension and manifold results
`exists_unstableSet_inter_stableSet_chart`, `span_mtangentConeAt_unstableSet_inter_stableSet`,
`finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex` and
`exists_unstableSet_inter_stableSet_isManifold` (in the namespace
`TauCeti.IsAdaptedPseudoGradient`) allow the unstable manifold to be taken for one pseudo-gradient
`X₀`, adapted to `f₀`, and the stable manifold for another, `X₁`, adapted to `f₁`, as for
continuation maps.

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
  {f f₀ f₁ : M → ℝ} {X X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b y : M}

namespace IsAdaptedPseudoGradient

section TangentSpaces

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- The tangent space of the stable manifold of a critical point `b`, at any of its points, has
dimension `n - ind b`. -/
theorem finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex
    (hy : y ∈ hX.flow.stableSet b) :
    Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f b = Module.finrank ℝ E := by
  have hb := hX.mfderiv_eq_zero_of_mem_stableSet hy
  obtain ⟨L, q, hL, hyq, hq, hs⟩ := hX.exists_isSliceChart_stableSet hb hy
  rwa [hs.finrank_span_mtangentConeAt (by simp) hq L.isClosed_of_finiteDimensional hyq hy]

/-- The tangent space of the unstable manifold of a critical point `a`, at any of its points, has
dimension `ind a`. -/
theorem finrank_span_mtangentConeAt_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hy : y ∈ hX.flow.unstableSet a) :
    Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y)) =
      manifoldMorseIndex 𝓘(ℝ, E) f a := by
  have ha := hX.mfderiv_eq_zero_of_mem_unstableSet hy
  obtain ⟨L, q, hL, hyq, hq, hs⟩ := hX.exists_isSliceChart_unstableSet hf ha hy
  rwa [hs.finrank_span_mtangentConeAt (by simp) hq L.isClosed_of_finiteDimensional hyq hy]

/-- **The unstable and stable manifolds are transverse at their critical point.** At a critical
point `x` of a Morse function, the tangent spaces of `W^u(x)` and `W^s(x)` span the tangent space
of `M`. In a Morse chart at `x` in which `X` is linear, near `x` these manifolds are the coordinate
subspaces of positive and of negative weight, which together span the model space. -/
theorem span_mtangentConeAt_unstableSet_sup_span_mtangentConeAt_stableSet_self
    (hf : IsMorse 𝓘(ℝ, E) f) {x : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) x) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet x) x) = ⊤ := by
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
  -- Near `x`, membership in `W^s(x)` and in `W^u(x)` is read off the coordinates of `φ`.
  obtain ⟨εs, hεs, hs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  obtain ⟨εu, hεu, hu⟩ := (hX.neg hf).exists_forall_mem_stableSet_iff (φ.neg hnd)
    (φ.coord_mfderiv_neg hφ hnd)
  set D := φ.toChart.source ∩ φ.toChart ⁻¹' {v : E | ‖φ.coord v‖ < min εs εu}
  have hD : IsOpen D := φ.toChart.continuousOn.isOpen_inter_preimage φ.toChart.open_source
    (isOpen_lt (continuous_norm.comp φ.continuous_coord) continuous_const)
  have hxD : x ∈ D := ⟨φ.mem_source, by simpa using lt_min hεs hεu⟩
  have hsrc : (φ.toChart.restr D).source = D := by
    rw [OpenPartialHomeomorph.restr_source, hD.interior_eq, inter_eq_right.2 inter_subset_left]
  -- The chart restricted to `D` flattens `W^s(x)` onto the stable subspace of `φ`, and `W^u(x)`,
  -- the stable manifold of `-X`, onto the stable subspace of the negated chart.
  have hslice {S : Set M} {L : Submodule ℝ E} (hS : ∀ y ∈ D, y ∈ S ↔ φ.toChart y ∈ L) :
      IsSliceChart (φ.toChart.restr D) (L : Set E) S :=
    isSliceChart_iff.2 fun z hz ↦ hS z (hsrc ▸ hz)
  have hslices : IsSliceChart (φ.toChart.restr D) (φ.stableSubspace : Set E)
      (hX.flow.stableSet x) := hslice fun y hy ↦
    (hs y hy.1 (hy.2.trans_le (min_le_left _ _))).trans φ.mem_stableSubspace.symm
  have hsliceu : IsSliceChart (φ.toChart.restr D) ((φ.neg hnd).stableSubspace : Set E)
      (hX.flow.unstableSet x) := hslice fun y hy ↦ by
    rw [hX.unstableSet_eq_stableSet_neg hf, (φ.neg hnd).mem_stableSubspace]
    simpa only [MorseChart.neg_toChart] using hu y (by simpa using hy.1)
      (by simpa using hy.2.trans_le (min_le_right _ _))
  have hxs : x ∈ hX.flow.stableSet x :=
    Flow.mem_stableSet.2 (by simp [hX.flow_apply_of_mfderiv_eq_zero hx])
  have hxu : x ∈ hX.flow.unstableSet x :=
    Flow.mem_unstableSet.2 (by simp [hX.flow_apply_of_mfderiv_eq_zero hx])
  exact hsliceu.span_mtangentConeAt_sup_eq_top (by simp)
    (restr_mem_maximalAtlas _ φ.mem_maximalAtlas hD) hslices
    (Submodule.isClosed_of_finiteDimensional _) (Submodule.isClosed_of_finiteDimensional _)
    (by rw [hsrc]; exact hxD) hxu hxs
    (by rw [sup_comm]; exact φ.stableSubspace_sup_stableSubspace_neg hnd)

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

omit hX in
/-- **Transverse unstable and stable manifolds meet in an embedded submanifold.** Let `X₀` and
`X₁` be pseudo-gradients adapted to `f₀` and `f₁`, with `f₀` Morse. If the unstable manifold of `a`
for `X₀` and the stable manifold of `b` for `X₁` meet transversally at `y`, then near `y` a chart of
the maximal atlas flattens their intersection onto the intersection of their tangent spaces. For
`X₀ = X₁` this intersection is the set of points on trajectories from `a` to `b`. -/
theorem exists_unstableSet_inter_stableSet_chart (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) :
          Submodule ℝ E) : Set E) (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) := by
  obtain ⟨L₁, q₁, -, hy₁, hq₁, h₁⟩ :=
    hX₀.exists_isSliceChart_unstableSet hf₀ (hX₀.mfderiv_eq_zero_of_mem_unstableSet hy.1) hy.1
  obtain ⟨L₂, q₂, -, hy₂, hq₂, h₂⟩ :=
    hX₁.exists_isSliceChart_stableSet (hX₁.mfderiv_eq_zero_of_mem_stableSet hy.2) hy.2
  exact exists_isSliceChart_inter_of_span_mtangentConeAt_sup_eq_top (by simp) hq₁ hq₂ h₁ h₂ hy₁
    hy₂ htr
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _))
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _))
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _))

omit hX in
/-- **The tangent space of a transverse intersection.** Let `X₀` and `X₁` be pseudo-gradients
adapted to `f₀` and `f₁`, with `f₀` Morse. If the unstable manifold of `a` for `X₀` and the stable
manifold of `b` for `X₁` meet transversally at `y`, then the tangent space of
`W^u_{X₀}(a) ∩ W^s_{X₁}(b)` at `y` is the intersection of their tangent spaces. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤) :
    Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) := by
  obtain ⟨L₁, q₁, -, hy₁, hq₁, h₁⟩ :=
    hX₀.exists_isSliceChart_unstableSet hf₀ (hX₀.mfderiv_eq_zero_of_mem_unstableSet hy.1) hy.1
  obtain ⟨L₂, q₂, -, hy₂, hq₂, h₂⟩ :=
    hX₁.exists_isSliceChart_stableSet (hX₁.mfderiv_eq_zero_of_mem_stableSet hy.2) hy.2
  exact span_mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top (by simp) hq₁ hq₂ h₁ h₂ hy₁
    hy₂ htr
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _))
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _))
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _))

omit hX in
/-- **The intersection has dimension the index difference.** Let `X₀` and `X₁` be pseudo-gradients
adapted to `f₀` and `f₁`, with `f₀` Morse. If the unstable manifold of `a` for `X₀` and the stable
manifold of `b` for `X₁` meet transversally at `y`, then the tangent space of
`W^u_{X₀}(a) ∩ W^s_{X₁}(b)` at `y` has dimension `ind a - ind b`, the indices being taken for `f₀`
and `f₁`. -/
theorem finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex
    (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤) :
    Module.finrank ℝ (Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₀ a := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y))
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y))
  rw [htr, finrank_top, hX₀.finrank_span_mtangentConeAt_unstableSet hf₀ hy.1,
    ← hX₀.span_mtangentConeAt_unstableSet_inter_stableSet hX₁ hf₀ hy htr] at hdim
  have hs := hX₁.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex hy.2
  omega

omit hX in
/-- **Transverse intersections are manifolds.** Let `X₀` and `X₁` be pseudo-gradients adapted to
`f₀` and `f₁`, with `f₀` Morse. If `W^u_{X₀}(a)` meets `W^s_{X₁}(b)`, transversally at each of
their common points, then their intersection carries a smooth manifold structure, modelled on a
subspace of dimension `ind a - ind b`, with its subspace topology and a smooth inclusion into `M`.
-/
theorem exists_unstableSet_inter_stableSet_isManifold (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (htr : ∀ y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b,
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤)
    (hne : (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₀ a ∧
      ∃ C : ChartedSpace L ↥(hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b), letI := C
        IsManifold 𝓘(ℝ, L) ∞ ↥(hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : ↥(hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) → M) := by
  obtain ⟨y₀, hy₀⟩ := hne
  -- Every tangent space of the intersection has dimension `ind a - ind b`; model it on one of them.
  refine ⟨Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) y₀),
    hX₀.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hX₁ hf₀ hy₀
      (htr y₀ hy₀), exists_isManifold_of_finrankSubspaceCharts fun y hy ↦ ?_⟩
  obtain ⟨q, hyq, hq, hs⟩ := hX₀.exists_unstableSet_inter_stableSet_chart hX₁ hf₀ hy (htr y hy)
  have hdim₀ :=
    hX₀.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hX₁ hf₀ hy₀
      (htr y₀ hy₀)
  have hdim :=
    hX₀.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hX₁ hf₀ hy
      (htr y hy)
  rw [hX₀.span_mtangentConeAt_unstableSet_inter_stableSet hX₁ hf₀ hy (htr y hy)] at hdim
  exact ⟨q, _, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, isSliceChart_iff.1 hs, by omega⟩

/-- **The Morse index drops strictly along a transverse trajectory.** If a trajectory of the flow
runs from a critical point `a` to a different critical point `b`, and the unstable manifold of `a`
meets the stable manifold of `b` transversally at a point `y` of it, then `ind b < ind a`. -/
theorem manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    manifoldMorseIndex 𝓘(ℝ, E) f b < manifoldMorseIndex 𝓘(ℝ, E) f a := by
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hX hf hy htr
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

end TangentSpaces

/-- **The Morse–Smale condition** for a pseudo-gradient `X` adapted to `f`: for all critical points
`a` and `b` of `f`, the unstable manifold of `a` and the stable manifold of `b` meet transversally
at each common point `y`, that is, their tangent spaces at `y` span the tangent space of `M`. -/
def IsMorseSmale (hX : IsAdaptedPseudoGradient f X) : Prop :=
  ∀ ⦃a b y : M⦄, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0 → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0 →
    y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b →
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤

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

/-- **The Morse–Smale condition is only a condition between intermediate indices.** Let `f` be a
Morse function on a manifold of dimension `n`. A pseudo-gradient adapted to `f` is Morse–Smale as
soon as `W^u(a)` and `W^s(b)` meet transversally for all distinct critical points `a` and `b` whose
indices both differ from `0` and from `n`. All other pairs are transverse automatically:

* if `a = b`, the only common point is `a`, where `W^u(a)` and `W^s(a)` are transverse
  (`span_mtangentConeAt_unstableSet_sup_span_mtangentConeAt_stableSet_self`);
* if `ind a = n` or `ind b = 0`, the tangent space of `W^u(a)` or of `W^s(b)` is already the whole
  tangent space of `M`;
* if `ind a = 0` or `ind b = n` and `a ≠ b`, no trajectory runs from `a` to `b`, since the velocity
  of such a trajectory would be a nonzero tangent vector of `W^u(a)` or of `W^s(b)`, whose tangent
  spaces are then zero. -/
theorem IsMorseSmale.of_forall_ne_of_manifoldMorseIndex_ne {hX : IsAdaptedPseudoGradient f X}
    (hf : IsMorse 𝓘(ℝ, E) f)
    (htr : ∀ ⦃a b y : M⦄, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0 → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0 → a ≠ b →
      manifoldMorseIndex 𝓘(ℝ, E) f a ≠ 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f a ≠ Module.finrank ℝ E →
      manifoldMorseIndex 𝓘(ℝ, E) f b ≠ 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f b ≠ Module.finrank ℝ E →
      y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b →
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    hX.IsMorseSmale := by
  intro a b y ha hb hy
  obtain rfl | hab := eq_or_ne a b
  · obtain rfl := hX.eq_of_mem_unstableSet_inter_stableSet hy
    exact hX.span_mtangentConeAt_unstableSet_sup_span_mtangentConeAt_stableSet_self hf ha
  have hu := hX.finrank_span_mtangentConeAt_unstableSet hf hy.1
  have hs := hX.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex hy.2
  -- The velocity `X y` is a nonzero vector tangent to both `W^u(a)` and `W^s(b)`.
  have hXy := hX.ne_zero_of_mfderiv_ne_zero
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hab hy)
  have hmemu : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) :=
    Submodule.subset_span
      (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_unstableSet a) hy.1)
  have hmems : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) :=
    Submodule.subset_span
      (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_stableSet b) hy.2)
  by_cases ha0 : manifoldMorseIndex 𝓘(ℝ, E) f a = 0
  · rw [Submodule.finrank_eq_zero.1 (hu.trans ha0)] at hmemu
    exact (hXy ((Submodule.mem_bot ℝ).1 hmemu)).elim
  by_cases han : manifoldMorseIndex 𝓘(ℝ, E) f a = Module.finrank ℝ E
  · rw [Submodule.eq_top_of_finrank_eq (hu.trans han), top_sup_eq]
  by_cases hb0 : manifoldMorseIndex 𝓘(ℝ, E) f b = 0
  · rw [Submodule.eq_top_of_finrank_eq (by omega : Module.finrank ℝ (Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y)) = Module.finrank ℝ E), sup_top_eq]
  by_cases hbn : manifoldMorseIndex 𝓘(ℝ, E) f b = Module.finrank ℝ E
  · rw [Submodule.finrank_eq_zero.1 (by omega : Module.finrank ℝ (Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y)) = 0)] at hmems
    exact (hXy ((Submodule.mem_bot ℝ).1 hmems)).elim
  exact htr ha hb hab ha0 han hb0 hbn hy

/-- **At most one critical point of intermediate index forces the Morse–Smale condition.** If at
most one critical point of a Morse function `f` on a manifold of dimension `n` has an index other
than `0` and `n`, then every pseudo-gradient adapted to `f` is Morse–Smale. This applies, for
instance, to the moment function on the real projective plane, whose only such critical point is
its saddle. -/
theorem IsMorseSmale.of_subsingleton {hX : IsAdaptedPseudoGradient f X} (hf : IsMorse 𝓘(ℝ, E) f)
    (hsub : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧ manifoldMorseIndex 𝓘(ℝ, E) f x ≠ 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x ≠ Module.finrank ℝ E}.Subsingleton) :
    hX.IsMorseSmale :=
  of_forall_ne_of_manifoldMorseIndex_ne hf fun _ _ _ ha hb hab ha0 han hb0 hbn _ ↦
    (hab (hsub ⟨ha, ha0, han⟩ ⟨hb, hb0, hbn⟩)).elim

/-- **Extremal indices force the Morse–Smale condition.** If every critical point of a Morse
function `f` has Morse index `0` or `n`, then every pseudo-gradient adapted to `f` is Morse–Smale.
This applies, for instance, to the height function on the sphere. -/
theorem IsMorseSmale.of_manifoldMorseIndex_eq_zero_or_eq_finrank
    {hX : IsAdaptedPseudoGradient f X} (hf : IsMorse 𝓘(ℝ, E) f)
    (hind : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0 ∨
        manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E) :
    hX.IsMorseSmale :=
  of_subsingleton hf fun x hx ↦ ((hind x hx.1).elim hx.2.1 hx.2.2).elim

/-- **The pointwise elimination rule for `IsMorseSmale`.** Under the Morse–Smale condition, at a
point `y` of `W^u(a) ∩ W^s(b)` for critical points `a` and `b`, the tangent spaces of `W^u(a)` and
`W^s(b)` span the tangent space of `M`. -/
theorem IsMorseSmale.span_mtangentConeAt_sup_eq_top {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤ :=
  h (hX.mfderiv_eq_zero_of_mem_unstableSet hy.1) (hX.mfderiv_eq_zero_of_mem_stableSet hy.2) hy

/-- **Reversing a Morse–Smale pseudo-gradient.** If a pseudo-gradient `X` adapted to a Morse
function `f` is Morse–Smale, then so is `-X`, adapted to `-f`: reversing the flow exchanges the
unstable and stable manifolds of each critical point. -/
theorem IsMorseSmale.neg {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) : (hX.neg hf).IsMorseSmale := by
  intro a b y ha hb hy
  rw [mfderiv_neg_eq_zero_iff] at ha hb
  rw [hX.neg_flow hf, Flow.unstableSet_reverse, Flow.stableSet_reverse] at hy ⊢
  rw [sup_comm]
  exact h hb ha ⟨hy.2, hy.1⟩

/-- **Spaces of trajectories are manifolds.** Under the Morse–Smale condition, if some trajectory
runs from a critical point `a` to a critical point `b`, then `W^u(a) ∩ W^s(b)` carries a smooth
manifold structure, modelled on a subspace of dimension `ind a - ind b`, with its subspace topology
and a smooth inclusion into `M`. -/
theorem IsMorseSmale.exists_unstableSet_inter_stableSet_isManifold
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hne : (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f b = manifoldMorseIndex 𝓘(ℝ, E) f a ∧
      ∃ C : ChartedSpace L ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b), letI := C
        IsManifold 𝓘(ℝ, L) ∞ ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b) → M) :=
  hX.exists_unstableSet_inter_stableSet_isManifold hX hf
    (fun _ hy ↦ h.span_mtangentConeAt_sup_eq_top hy) hne

/-- **Under the Morse–Smale condition, the Morse index drops along every trajectory** joining
distinct critical points: if a trajectory runs from `a` to `b ≠ a`, then `ind b < ind a`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) (hab : a ≠ b)
    (hne : (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f b < manifoldMorseIndex 𝓘(ℝ, E) f a :=
  hX.manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet hf hab hne.some_mem
    (h.span_mtangentConeAt_sup_eq_top hne.some_mem)

section TransverseSets

open Filter Topology

/-- **A set transverse to an unstable manifold, of complementary dimension, is transverse to the
flow.** Let `Z` be flattened near a regular point `y` of `W^u(q)`, of dimension `n - ind q` and
transverse to `W^u(q)` at `y`. Then the tangent spaces of `Z` and `W^u(q)` at `y` meet in `0`, so
`X y`, which is tangent to `W^u(q)` and nonzero, is not tangent to `Z`. -/
theorem notMem_span_mtangentConeAt_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {q : M} {Z : Set M} {L : Submodule ℝ E}
    {φZ : OpenPartialHomeomorph M E} (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hZ : IsSliceChart φZ (L : Set E) Z) (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (hy : y ∈ hX.flow.unstableSet q) (hyc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0)
    (hdim : Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f q = Module.finrank ℝ E)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) = ⊤) :
    X y ∉ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) := by
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  intro hXy
  have hXu : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) :=
    Submodule.subset_span (hX.mem_mtangentConeAt_of_isInvariant
      (hX.flow.isInvariant_unstableSet q) hy)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y))
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y))
  rw [htr, finrank_top, hZ.finrank_span_mtangentConeAt (by simp) hφZ hL hyφZ hyZ,
    hX.finrank_span_mtangentConeAt_unstableSet hf hy] at hsum
  have hinf := Submodule.finrank_eq_zero.1 (by omega : Module.finrank ℝ ↥(
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊓
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y)) = 0)
  have hmem : X y ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y) ⊓
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet q) y) := ⟨hXy, hXu⟩
  have h0 : X y = 0 := by
    rw [hinf] at hmem
    exact (Submodule.mem_bot ℝ).1 hmem
  have := hX.mvfderiv_apply_lt_zero y hyc
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

/-- **An orbit meets a set transverse to the flow at most once near a regular point.** Let `Z` be
a set flattened near a point `y` by a chart of the maximal atlas, with `X y` not tangent to `Z` at
`y`, so that `X y ≠ 0` and `y` is not a critical point. Then two points of `Z` near `y` on a common
orbit are equal, and the time from one to the other is `0`. -/
theorem eventually_eq_zero_of_flow_eq_of_isSliceChart (hX : IsAdaptedPseudoGradient f X)
    {Z : Set M} {L : Submodule ℝ E} {φZ : OpenPartialHomeomorph M E}
    (hφZ : φZ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hZ : IsSliceChart φZ (L : Set E) Z)
    (hyφZ : y ∈ φZ.source) (hyZ : y ∈ Z)
    (hXZ : X y ∉ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) Z y)) :
    ∀ᶠ w : M × M in 𝓝 (y, y), w.1 ∈ Z → w.2 ∈ Z → ∀ t, hX.flow t w.1 = w.2 → t = 0 := by
  have hL : IsClosed (L : Set E) := Submodule.isClosed_of_finiteDimensional _
  -- `y` is not a critical point, since `X y` is not tangent to `Z`, so in particular nonzero.
  have hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := mt hX.eq_zero_iff.2 fun h0 ↦ hXZ (by
    rw [h0]
    exact zero_mem _)
  -- A linear form `ℓ` vanishing on `L` but not on the image of `X y` in the chart: the level of
  -- `g = ℓ ∘ φZ` through `y` contains `Z` near `y` and is transverse to the flow.
  have hXL : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φZ y (X y) ∉ L := fun h ↦ hXZ <| by
    rw [hZ.span_mtangentConeAt_eq_comap (by simp) hφZ hL hyφZ hyZ]
    exact h
  obtain ⟨ℓ, hℓ, hLℓ⟩ := Submodule.exists_le_ker_of_notMem hXL
  set ℓc : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ℓ
  set g : M → ℝ := ℓc ∘ φZ with hg
  have hφZy : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φZ y := contMDiffAt_of_mem_maximalAtlas hφZ hyφZ
  have hgd : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ g y := ℓc.contMDiff.contMDiffAt.comp y hφZy
  have hgv : mvfderiv 𝓘(ℝ, E) g y (X y) ≠ 0 := by
    have h := mvfderiv_comp_apply (g := ℓc) (f := φZ) y
      ((ℓc.contMDiff (n := ∞)).mdifferentiable (by simp) _) (hφZy.mdifferentiableAt (by simp)) (X y)
    rw [← hg] at h
    rw [h, mvfderiv_eq_fderiv_apply, ℓc.fderiv]
    exact hℓ
  -- Near `(0, y)` the orbit of a point meets the level of `g` through `y` at a unique time.
  have hv : CMDiff 1 (fun z ↦ (⟨z, X z⟩ : TangentBundle 𝓘(ℝ, E) M)) := hX.contMDiff.of_le (by simp)
  have hT := mem_flowDomain_zero hv y
  have hhit := eventually_eq_flowHittingTime_iff hv hT
    (by rw [flowOf_zero]; exact hgd.of_le (by simp)) (by rw [flowOf_zero]; exact hgv)
  rw [flowOf_zero] at hhit
  have hflow : ∀ t z, flowOf X t z = hX.flow t z := fun t z ↦ by
    rw [flowOf_apply, hX.flow_apply]
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hhit
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.1 hA
  -- Far from time `0`, `f` has dropped or risen along the orbit by a definite amount.
  have hanti := hX.strictAnti_comp (hX.isMIntegralCurve_flow y) (hX.mfderiv_flow_ne_zero hy)
  have h₁ : f (hX.flow (δ / 2) y) < f y := by
    simpa using hanti (half_pos hδ)
  have h₂ : f y < f (hX.flow (-(δ / 2)) y) := by
    simpa using hanti (neg_lt_zero.2 (half_pos hδ))
  have hc₁ : Continuous fun w ↦ f (hX.flow (δ / 2) w) :=
    hX.mdifferentiable.continuous.comp (hX.contMDiff_flow_apply _).continuous
  have hc₂ : Continuous fun w ↦ f (hX.flow (-(δ / 2)) w) :=
    hX.mdifferentiable.continuous.comp (hX.contMDiff_flow_apply _).continuous
  obtain ⟨m₁, hm₁, hm₁'⟩ := exists_between h₁
  obtain ⟨m₂, hm₂, hm₂'⟩ := exists_between h₂
  have hfy := hX.mdifferentiable.continuous.continuousAt (x := y)
  have hB' : ∀ᶠ w in 𝓝 y, w ∈ B := hB
  have hN₁ : ∀ᶠ w in 𝓝 y, f (hX.flow (δ / 2) w) < m₁ ∧ m₂ < f (hX.flow (-(δ / 2)) w) ∧
      w ∈ B ∧ w ∈ φZ.source :=
    (hc₁.continuousAt.eventually (gt_mem_nhds hm₁)).and
      ((hc₂.continuousAt.eventually (lt_mem_nhds hm₂')).and
        (hB'.and (φZ.open_source.mem_nhds hyφZ)))
  have hN₂ : ∀ᶠ w in 𝓝 y, m₁ < f w ∧ f w < m₂ ∧ w ∈ φZ.source :=
    (hfy.eventually (lt_mem_nhds hm₁')).and
      ((hfy.eventually (gt_mem_nhds hm₂)).and (φZ.open_source.mem_nhds hyφZ))
  have hgZ : ∀ w ∈ φZ.source, w ∈ Z → g w = 0 := fun w hw hwZ ↦
    LinearMap.mem_ker.1 (hLℓ ((hZ.mem_iff hw).1 hwZ))
  filter_upwards [hN₁.prodMk_nhds hN₂] with w ⟨⟨hw₁, hw₂, hwB, hwφ⟩, hw'₁, hw'₂, hw'φ⟩ hwZ hw'Z t ht
  have hw1 := hX.antitone_flow w.1
  rcases lt_or_ge t (δ / 2) with htδ | htδ
  · rcases lt_or_ge (-(δ / 2)) t with htδ' | htδ'
    · -- For small times, both `0` and `t` are the hitting time of the level of `g` through `y`.
      have htA : t ∈ A := hδA (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
      have h0A : (0 : ℝ) ∈ A := hδA (by simpa using hδ)
      have hgy : g y = 0 := hgZ y hyφZ hyZ
      have e₁ := (hAB (mk_mem_prod htA hwB)).1 (by
        simp only [hflow, ht, hgy]
        exact hgZ _ hw'φ hw'Z)
      have e₀ := (hAB (mk_mem_prod h0A hwB)).1 (by
        simp only [hflow, Flow.map_zero_apply, hgy]
        exact hgZ _ hwφ hwZ)
      exact e₁.trans e₀.symm
    · -- For times at most `-δ / 2`, `f` has risen.
      have := hw1 htδ'
      simp only [ht] at this
      linarith
  · -- For times at least `δ / 2`, `f` has dropped.
    have := hw1 htδ
    simp only [ht] at this
    linarith

end TransverseSets

end IsAdaptedPseudoGradient

end TauCeti
