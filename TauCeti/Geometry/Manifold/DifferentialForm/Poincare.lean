/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Cutoff
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# The Poincaré lemma on manifolds

A closed differential form of positive degree on a manifold is locally exact: near every point
it is the exterior derivative of a globally defined form of the same regularity
(`TauCeti.exists_mextDeriv_eq_nhds`). Boundary and corner points are included.

The form is read in the preferred extended chart at the point. Mathlib's `range I` is convex, so
the intersection of a small ball about the chart point with `range I` is a convex set with unique
derivatives inside the chart target, although it need not be open. The relative flat Poincaré
lemma `Convex.exists_contDiffOn_forall_extDerivWithin_eq` gives a primitive there. Its pullback
along the chart is cut off by a smooth bump function supported in the chart domain
(`TauCeti.RoughForm.exists_isSmoothForm_inChartAt_eventuallyEq`), which gives a primitive on all
of `M` near the point.

The cutoff is the only place where `[FiniteDimensional ℝ E]` and `[T2Space M]` are used: smooth
bump functions need both. The coefficient space is complete because the flat primitive is an
integral.

## Main declarations

* `TauCeti.exists_mextDeriv_eq_nhds`: the manifold Poincaré lemma.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 17.14 and Corollary 17.15.
-/

public section

noncomputable section

open Set Filter Metric Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- A form that is closed near `x` has a flat primitive in the chart at `x`, on the intersection
of a small ball about the chart point with the model range. -/
private theorem exists_primitive_inChartAt [IsManifold I ∞ M] {r : ℕ∞} (hr : 1 ≤ r)
    {φ : RoughForm I M F (k + 1)} (hφ : IsSmoothForm I r φ) {x : M}
    (hclosed : ∀ᶠ y in 𝓝 x, mextDeriv φ y = 0) :
    ∃ ε > 0, ∃ α : E → E [⋀^Fin k]→L[ℝ] F, ContDiffOn ℝ r α (ball (extChartAt I x x) ε ∩ range I) ∧
      ∀ z ∈ ball (extChartAt I x x) ε ∩ range I,
        extDerivWithin α (ball (extChartAt I x x) ε ∩ range I) z = φ.inChartAt x z := by
  have : IsManifold I ((r : WithTop ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hφ₁ : IsSmoothForm I 1 φ :=
    hφ.of_le (by exact_mod_cast hr)
  obtain ⟨ε, hε, hsub⟩ : ∃ ε > 0, ball (extChartAt I x x) ε ∩ range I ⊆
      (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' {y | mextDeriv φ y = 0} := by
    rw [← Metric.mem_nhdsWithin_iff]
    refine inter_mem (extChartAt_target_mem_nhdsWithin x) ?_
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) x] at hclosed
    exact hclosed
  have hxs : extChartAt I x x ∈ ball (extChartAt I x x) ε ∩ range I :=
    ⟨mem_ball_self hε, extChartAt_target_subset_range x (mem_extChartAt_target x)⟩
  have hω : ContDiffOn ℝ r (φ.inChartAt x) (ball (extChartAt I x x) ε ∩ range I) :=
    fun z hz ↦ (φ.contDiffWithinAt_inChartAt_of_contDiffWithinAt_inChartAt (hsub hz).1
      (mem_extChartAt_source _) (hφ.contDiffWithinAt_inChartAt_self _)).mono inter_subset_right
  -- Closedness in the chart: `mextDeriv φ` read in the chart is the flat derivative within
  -- `range I`, which agrees with the derivative within the ball near each of its points.
  have hcl (z : E) (hz : z ∈ ball (extChartAt I x x) ε ∩ range I) :
      extDerivWithin (φ.inChartAt x) (ball (extChartAt I x x) ε ∩ range I) z = 0 := by
    have hset : ball (extChartAt I x x) ε ∩ range I =ᶠ[𝓝 z] range I :=
      inter_eventuallyEqSet_right.mpr (eventually_of_mem (isOpen_ball.mem_nhds hz.1) fun _ h _ ↦ h)
    rw [extDerivWithin_congr_set hset, ← hφ₁.inChartAt_mextDeriv_eq x (hsub hz).1]
    ext v
    rw [RoughForm.inChartAt_apply, show mextDeriv φ ((extChartAt I x).symm z) = 0 from (hsub hz).2]
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  have hsu : UniqueDiffOn ℝ (ball (extChartAt I x x) ε ∩ range I) := by
    rw [inter_comm]
    exact I.uniqueDiffOn.inter isOpen_ball
  have hconv : Convex ℝ (ball (extChartAt I x x) ε ∩ range I) :=
    (convex_ball _ _).inter I.convex_range
  obtain ⟨α, hα, -, hdα⟩ := hconv.exists_contDiffOn_forall_extDerivWithin_eq hsu hxs hr hω hcl
  exact ⟨ε, hε, α, hα, hdα⟩

/-- **The Poincaré lemma on manifolds.** A `C^r` form of positive degree, `r ≥ 1`, that is closed
near a point `x` is, on a neighbourhood of `x`, the exterior derivative of a `C^r` form defined on
the whole manifold. The manifold may have boundary or corners.

The coefficient space is complete: with values in the finitely supported sequences there is a
smooth closed `1`-form on `ℝ` with no local primitive. Finite dimensionality of the model and the
Hausdorff property are used only to cut the local primitive off by a smooth bump function. -/
theorem exists_mextDeriv_eq_nhds [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    {r : ℕ∞} (hr : 1 ≤ r) {φ : RoughForm I M F (k + 1)} (hφ : IsSmoothForm I r φ) {x : M}
    (hclosed : ∀ᶠ y in 𝓝 x, mextDeriv φ y = 0) :
    ∃ U ∈ 𝓝 x, ∃ ψ : RoughForm I M F k, IsSmoothForm I r ψ ∧ ∀ y ∈ U, mextDeriv ψ y = φ y := by
  obtain ⟨ε, hε, α, hα, hdα⟩ := exists_primitive_inChartAt hr hφ hclosed
  -- Cut the pullback of the flat primitive `α` off; near `x` its chart expression is `α`.
  obtain ⟨U, hU, ψ, hψ, hUψ⟩ :=
    RoughForm.exists_isSmoothForm_inChartAt_eventuallyEq isOpen_ball (mem_ball_self hε) hα
  have hψ₁ : IsSmoothForm I 1 ψ := hψ.of_le (by exact_mod_cast hr)
  refine ⟨U, hU, ψ, hψ, fun y hy ↦ ?_⟩
  obtain ⟨hys, hyb, hψα⟩ := hUψ y hy
  have hset : ball (extChartAt I x x) ε ∩ range I =ᶠ[𝓝 (extChartAt I x y)] range I :=
    inter_eventuallyEqSet_right.mpr (eventually_of_mem (isOpen_ball.mem_nhds hyb.1) fun _ h _ ↦ h)
  rw [← RoughForm.inChartAt_chart_eq_iff hys,
    hψ₁.inChartAt_mextDeriv_eq x ((extChartAt I x).map_source hys), ← hdα _ hyb,
    extDerivWithin_congr_set hset]
  exact hψα.extDerivWithin_eq (hψα.self_of_nhdsWithin hyb.2)

end TauCeti
