/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# The Poincaré lemma on manifolds

A closed differential form of positive degree on a manifold is locally exact: near every point
it is the exterior derivative of a globally defined form of the same regularity
(`TauCeti.exists_mextDeriv_eq_nhds`). Boundary and corner points are included.

The form is read in the preferred extended chart at the point. Mathlib's `range I` is convex, so
the intersection of a small ball about the chart point with `range I` is a convex set with unique
derivatives inside the chart target, although it need not be open. The relative flat Poincaré
lemma `Convex.exists_contDiffOn_forall_extDerivWithin_eq` gives a primitive there. Its pullback
along the chart is cut off by a smooth bump function supported in the chart domain, which gives
a primitive on all of `M` near the point.

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
  have : IsManifold I ((r : WithTop ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨ε, hε, α, hα, hdα⟩ := exists_primitive_inChartAt hr hφ hclosed
  -- `p` is the pullback of the flat primitive along the chart; its chart expression is `α`.
  let p : RoughForm I M F k :=
    mpullback I 𝓘(ℝ, E) (extChartAt I x) (α : RoughForm 𝓘(ℝ, E) E F k)
  have hp (z : E) (hz : z ∈ (extChartAt I x).target) : p.inChartAt x z = α z :=
    RoughForm.inChartAt_mpullback_extChartAt _ x hz
  let u := (chartAt H x).source ∩ extChartAt I x ⁻¹' ball (extChartAt I x x) ε
  have hu : IsOpen u := isOpen_extChartAt_preimage x isOpen_ball
  have hmem {y : M} (hy : y ∈ u) : y ∈ (extChartAt I x).source ∧
      extChartAt I x y ∈ ball (extChartAt I x x) ε ∩ range I := by
    rw [extChartAt_source]
    exact ⟨hy.1, hy.2, extChartAt_target_subset_range x ((extChartAt I x).map_source
      (by rw [extChartAt_source]; exact hy.1))⟩
  -- On `u` the pullback is `C^r`, since its chart expression `α` is.
  have hpu (y : M) (hy : y ∈ u) : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) r
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (p y)) y := by
    obtain ⟨hys, hyb⟩ := hmem hy
    exact contMDiffAt_mpullback_extChartAt hys ((hα _ hyb).mono_of_mem_nhdsWithin
      (inter_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hyb.1)) self_mem_nhdsWithin))
  obtain ⟨χ, -, hχu⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hu.mem_nhds
      ⟨mem_chart_source H x, mem_ball_self hε⟩)
  have hψ : IsSmoothForm I r (fun y ↦ χ y • p y) := by
    rw [isSmoothForm_def]
    exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport hu
      hχu fun y hy ↦ (hpu y hy).contMDiffWithinAt
  have hψ₁ : IsSmoothForm I 1 (fun y ↦ χ y • p y) :=
    hψ.of_le (by exact_mod_cast hr)
  refine ⟨interior {y | χ y = 1}, interior_mem_nhds.mpr χ.eventuallyEq_one, _, hψ, ?_⟩
  intro y hy
  have hχy : χ y = 1 := interior_subset hy
  obtain ⟨hys, hyb⟩ :=
    hmem (hχu (subset_tsupport _ (Function.mem_support.mpr (by rw [hχy]; exact one_ne_zero))))
  -- Near the chart point of `y` the bump is `1`, so the chart expression of the cut-off
  -- pullback is the flat primitive `α`.
  have hone : ∀ᶠ w in 𝓝[range I] extChartAt I x y, χ ((extChartAt I x).symm w) = 1 := by
    have h : {y | χ y = 1} ∈ 𝓝 y := mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
    rw [← map_extChartAt_symm_nhdsWithin_range' hys] at h
    exact h
  have hψα : RoughForm.inChartAt (I := I) (fun y ↦ χ y • p y) x =ᶠ[𝓝[range I] extChartAt I x y]
      α := by
    filter_upwards [extChartAt_target_mem_nhdsWithin' hys, hone] with w hw hw₁
    rw [RoughForm.inChartAt_fun_smul, hw₁, one_smul, hp w hw]
  have hset : ball (extChartAt I x x) ε ∩ range I =ᶠ[𝓝 (extChartAt I x y)] range I :=
    inter_eventuallyEqSet_right.mpr (eventually_of_mem (isOpen_ball.mem_nhds hyb.1) fun _ h _ ↦ h)
  rw [← RoughForm.inChartAt_chart_eq_iff hys,
    hψ₁.inChartAt_mextDeriv_eq x ((extChartAt I x).map_source hys), ← hdα _ hyb,
    extDerivWithin_congr_set hset]
  exact hψα.extDerivWithin_eq (hψα.self_of_nhdsWithin hyb.2)

end TauCeti
