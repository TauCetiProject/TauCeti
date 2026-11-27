/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Orientation.Basic
public import TauCeti.Geometry.Manifold.Orientation.Cover.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Transport
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.Orientation.Cover.Chart
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Frame orientations along stable and unstable manifolds in the orientation double cover

Let `X` be a pseudo-gradient adapted to a Morse function `f` on a compact manifold `M`, and `φ` a
Morse chart at a critical point `x` in which `X` is linear. Orientations `op` and `op'` of the
coordinates of negative and of positive weight orient the tangent space at every point `y` of the
unstable manifold `W^u(x)`, through the unstable frame and the normal coordinates of the stable
manifold of `-X` (`TauCeti.IsAdaptedPseudoGradient.unstableFrameOrientation`), and likewise at
every point of the stable manifold `W^s(x)`
(`TauCeti.IsAdaptedPseudoGradient.stableNormalOrientation`). No orientation of `M` is assumed.

This file shows that these orientations vary continuously: as maps from `W^u(x)`, respectively
`W^s(x)`, to the orientation double cover of `M` they are continuous
(`TauCeti.IsAdaptedPseudoGradient.continuous_mk_unstableFrameOrientation`,
`TauCeti.IsAdaptedPseudoGradient.continuous_mk_stableNormalOrientation`). Consequently, along any
path inside `W^u(x)`, transport of orientations
(`TauCeti.VectorBundleOrientationCover.orientationTransport`, the monodromy of the orientation
double cover) carries the frame orientation at the start to the frame orientation at the end
(`TauCeti.IsAdaptedPseudoGradient.orientationTransport_unstableFrameOrientation`), and likewise
inside `W^s(x)` (`TauCeti.IsAdaptedPseudoGradient.orientationTransport_stableNormalOrientation`).
On an oriented manifold this recovers the statement that the frame orientation agrees with the
orientation of `M` everywhere on `W^u(x)` or nowhere
(`TauCeti.IsAdaptedPseudoGradient.reindex_unstableFrameOrientation_eq_orientationAt_iff`); without
an orientation, it identifies the twist of the orientation local system along a trajectory.

The proof reads the tangent spaces in a single chart. Near a point of `W^u(x)` one time `T` of
linear backward flow serves all nearby points of `W^u(x)`, and in the chart `φ ∘ Φ_{-T}` the frame
and the normal coordinates at each of these points are positive multiples of those at `x` read
in `φ` (`TauCeti.IsAdaptedPseudoGradient.map_unstableFrameOrientation_eq`). So the frame
orientations read as one fixed orientation of the model space through this chart, and a family
read in this way near every point is continuous into the orientation double cover
(`TauCeti.Manifold.OrientationCover.continuous_mk_of_forall_exists_map_mfderiv_eq`). The stable
manifold is treated in the same way with the forward flow
(`TauCeti.IsAdaptedPseudoGradient.map_stableNormalOrientation_eq`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `continuous_mk_unstableFrameOrientation`, `continuous_mk_stableNormalOrientation`: the frame
  orientations are continuous maps to the orientation double cover.
* `orientationTransport_unstableFrameOrientation`, `orientationTransport_stableNormalOrientation`:
  along a path in the unstable, respectively stable, manifold, orientation transport carries the
  frame orientation at the start to the frame orientation at the end.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover).
-/

public section

open Filter Function Set Topology Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {φ : MorseChart E f x}

/-- The chart `φ ∘ Φ_t` of the `C¹` maximal atlas, defined at the points that the flow carries into
the source of `φ` in time `t`. -/
private theorem exists_mem_maximalAtlas_coe_eq_comp_flow (t : ℝ) :
    ∃ c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M,
      c.source = hX.flow t ⁻¹' φ.toChart.source ∧ (c : M → E) = φ.toChart ∘ hX.flow t :=
  ⟨(hX.flowDiffeomorph t).toHomeomorph.transOpenPartialHomeomorph φ.toChart,
    IsManifold.maximalAtlas_subset_of_le (by simp)
      ((hX.flowDiffeomorph t).transOpenPartialHomeomorph_mem_maximalAtlas le_rfl
        φ.mem_maximalAtlas),
    by ext z; simp, by funext z; simp⟩

variable (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))

include hφ

/-! ### Continuity in the orientation double cover -/

/-- **The frame orientations along the unstable manifold are continuous.** Reindexed to the
dimension of `M`, the frame orientations of `T_y M` induced by `op` and `op'` form a continuous
map from `W^u(x)` to the orientation double cover of `M`. -/
theorem continuous_mk_unstableFrameOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E) (-f) x) ≃
      Fin (finrank ℝ E)) :
    Continuous fun y : hX.flow.unstableSet x ↦ (⟨y, Orientation.reindex ℝ _ e
      (unstableFrameOrientation hφ hf hx op op' y.property)⟩ :
        Manifold.OrientationCover 𝓘(ℝ, E) M) := by
  have hxu := hX.mem_unstableSet_self hx.mem_criticalPoints
  obtain ⟨eDx, heDx⟩ := isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source
  refine Manifold.OrientationCover.continuous_mk_of_forall_exists_map_mfderiv_eq _ fun y₀ ↦ ?_
  -- One time `T` of linear backward flow serves the points of `W^u(x)` near `y₀`, and there the
  -- frame orientations read as one orientation through the chart `φ ∘ Φ_{-T}`.
  obtain ⟨T, hT⟩ := hX.exists_eventually_mem_linearBackwardTimes hφ hf y₀.property
  obtain ⟨c, hc, hcs, hcoe⟩ := exists_mem_maximalAtlas_coe_eq_comp_flow (hX := hX) (φ := φ) (-T)
  refine ⟨_, hT, c, hc, fun z hz ↦ hcs ▸ ((hX.mem_linearBackwardTimes φ).1 (hz.2 hz.1)).1,
    Orientation.reindex ℝ E e
      (Orientation.map _ (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E)
        (unstableFrameOrientation hφ hf hx op op' hxu)), fun z hz L hL ↦ ?_⟩
  rw [Orientation.map_reindex]
  congr 1
  exact map_unstableFrameOrientation_eq hφ hf hx op op' hxu z.property (hz z.property) L
    (hL.trans (by rw [hcoe])) eDx heDx

/-- **The frame orientations along the stable manifold are continuous.** Reindexed to the
dimension of `M`, the frame orientations of `T_y M` induced by `op'` and `op` form a continuous
map from `W^s(x)` to the orientation double cover of `M`. -/
theorem continuous_mk_stableNormalOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x + manifoldMorseIndex 𝓘(ℝ, E) f x) ≃
      Fin (finrank ℝ E)) :
    Continuous fun y : hX.flow.stableSet x ↦ (⟨y, Orientation.reindex ℝ _ e
      (stableNormalOrientation hφ hf hx op' op y.property)⟩ :
        Manifold.OrientationCover 𝓘(ℝ, E) M) := by
  have hxs := hX.mem_stableSet_self hx.mem_criticalPoints
  obtain ⟨eDx, heDx⟩ := isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source
  refine Manifold.OrientationCover.continuous_mk_of_forall_exists_map_mfderiv_eq _ fun y₀ ↦ ?_
  -- One time `T` of linear forward flow serves the points of `W^s(x)` near `y₀`, and there the
  -- frame orientations read as one orientation through the chart `φ ∘ Φ_T`.
  obtain ⟨T, hT⟩ := hX.exists_eventually_mem_linearForwardTimes hφ y₀.property
  obtain ⟨c, hc, hcs, hcoe⟩ := exists_mem_maximalAtlas_coe_eq_comp_flow (hX := hX) (φ := φ) T
  refine ⟨_, hT, c, hc, fun z hz ↦ hcs ▸ ((hX.mem_linearForwardTimes φ).1 (hz.2 hz.1)).1,
    Orientation.reindex ℝ E e
      (Orientation.map _ (eDx.toLinearEquiv : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] E)
        (stableNormalOrientation hφ hf hx op' op hxs)), fun z hz L hL ↦ ?_⟩
  rw [Orientation.map_reindex]
  congr 1
  exact map_stableNormalOrientation_eq hφ hf hx op' op hxs z.property (hz z.property) L
    (hL.trans (by rw [hcoe])) eDx heDx

/-! ### Transport along paths in the stable and unstable manifolds -/

/-- **Orientation transport along the unstable manifold.** Along a path inside `W^u(x)`,
orientation transport carries the frame orientation at the start to the frame orientation at the
end. -/
theorem orientationTransport_unstableFrameOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E) (-f) x) ≃
      Fin (finrank ℝ E)) {a b : M} (γ : Path a b) (hγ : ∀ t, γ t ∈ hX.flow.unstableSet x)
    (ha : a ∈ hX.flow.unstableSet x) (hb : b ∈ hX.flow.unstableSet x) :
    VectorBundleOrientationCover.orientationTransport (TangentSpace 𝓘(ℝ, E) : M → Type _)
        (Fintype.card_fin _) γ
        (Orientation.reindex ℝ _ e (unstableFrameOrientation hφ hf hx op op' ha)) =
      Orientation.reindex ℝ _ e (unstableFrameOrientation hφ hf hx op op' hb) :=
  VectorBundleOrientationCover.orientationTransport_eq_of_continuous
    (E := (TangentSpace 𝓘(ℝ, E) : M → Type _)) (Fintype.card_fin _)
    (fun y ↦ Orientation.reindex ℝ _ e (unstableFrameOrientation hφ hf hx op op' y.property))
    (continuous_mk_unstableFrameOrientation hφ hf hx op op' e) γ hγ ha hb

/-- **Orientation transport along the stable manifold.** Along a path inside `W^s(x)`,
orientation transport carries the frame orientation at the start to the frame orientation at the
end. -/
theorem orientationTransport_stableNormalOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (e : Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x + manifoldMorseIndex 𝓘(ℝ, E) f x) ≃
      Fin (finrank ℝ E)) {a b : M} (γ : Path a b) (hγ : ∀ t, γ t ∈ hX.flow.stableSet x)
    (ha : a ∈ hX.flow.stableSet x) (hb : b ∈ hX.flow.stableSet x) :
    VectorBundleOrientationCover.orientationTransport (TangentSpace 𝓘(ℝ, E) : M → Type _)
        (Fintype.card_fin _) γ
        (Orientation.reindex ℝ _ e (stableNormalOrientation hφ hf hx op' op ha)) =
      Orientation.reindex ℝ _ e (stableNormalOrientation hφ hf hx op' op hb) :=
  VectorBundleOrientationCover.orientationTransport_eq_of_continuous
    (E := (TangentSpace 𝓘(ℝ, E) : M → Type _)) (Fintype.card_fin _)
    (fun y ↦ Orientation.reindex ℝ _ e (stableNormalOrientation hφ hf hx op' op y.property))
    (continuous_mk_stableNormalOrientation hφ hf hx op' op e) γ hγ ha hb

end IsAdaptedPseudoGradient

end TauCeti
