/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Cutting off a differential form that is regular on an open set

Let `φ` be a differential form on a finite-dimensional Hausdorff σ-compact manifold, which is a
`C^n` section of the bundle of forms at every point of an open set `U`, and let `K ⊆ U` be closed.
Multiplying `φ` by a smooth function equal to one near `K` and to zero near the complement of `U`
gives a globally `C^n` form that agrees with `φ` near `K` and vanishes near the complement of `U`
(`TauCeti.RoughForm.exists_isSmoothForm_eventuallyEq_nhdsSet`).

This applies for instance to a form only defined, or only regular, away from a closed set, such
as the logarithmic derivative `dlog u` of a function `u` away from its zeros.

Within a single chart no σ-compactness is needed: a flat `C^r` form `α` on `s ∩ range I`, for an
open set `s` containing the chart point of `x`, is pulled back along the chart at `x` and cut
off by a smooth bump function at `x`. This gives a global `C^r` form whose expression in the chart
at `x` agrees with `α` near the chart point of every point of a neighbourhood of `x`
(`TauCeti.RoughForm.exists_isSmoothForm_inChartAt_eventuallyEq`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 2 (smooth bump
  functions).
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.RoughForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ}

/-- **Cutting off a form.** A form `φ` which is a `C^n` section at every point of an open set `U`
agrees near a closed set `K ⊆ U` with a globally `C^n` form vanishing near the complement of
`U`. -/
theorem exists_isSmoothForm_eventuallyEq_nhdsSet {n : ℕ∞} {φ : RoughForm I M F k}
    {U K : Set M} (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hφ : ∀ x ∈ U, ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) x) :
    ∃ ψ : RoughForm I M F k, IsSmoothForm I n ψ ∧ (∀ᶠ x in 𝓝ˢ K, ψ x = φ x) ∧
      ∀ᶠ x in 𝓝ˢ Uᶜ, ψ x = 0 := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨b, hb0, hb1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I hU.isClosed_compl hK
    (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨fun x ↦ b x • φ x, ?_, hb1.mono fun x hx ↦ by simp [hx],
    hb0.mono fun x hx ↦ by simp [hx]⟩
  rw [isSmoothForm_def]
  intro x
  by_cases hx : x ∈ U
  · exact (b.contMDiff.of_le (mod_cast le_top) x).smul_section (hφ x hx)
  · refine ((IsSmoothForm.zero (I := I) (M := M) (F := F) (k := k) n).contMDiff x)
      |>.congr_of_eventuallyEq ?_
    filter_upwards [(nhds_le_nhdsSet (show x ∈ Uᶜ from hx)) hb0] with y hy
    simp only [hy, zero_smul, Pi.zero_apply]

omit [SigmaCompactSpace M] in
/-- **Cutting off a flat form in a chart.** Let `α` be a `C^r` flat form on `s ∩ range I`, for an
open set `s` containing the chart point of `x`. There are a neighbourhood `U` of `x` and a
globally `C^r` form `ψ` such that every `y ∈ U` lies in the chart at `x`, its chart point lies in
`s ∩ range I`, and near that chart point, within the model range, the expression of `ψ` in the
chart at `x` is `α`. The form `ψ` is the pullback of `α` along the chart cut off by a smooth bump
function at `x`. -/
theorem exists_isSmoothForm_inChartAt_eventuallyEq {r : ℕ∞} {x : M} {s : Set E} (hs : IsOpen s)
    (hxs : extChartAt I x x ∈ s) {α : E → E [⋀^Fin k]→L[ℝ] F}
    (hα : ContDiffOn ℝ r α (s ∩ range I)) :
    ∃ U ∈ 𝓝 x, ∃ ψ : RoughForm I M F k, IsSmoothForm I r ψ ∧ ∀ y ∈ U,
      y ∈ (extChartAt I x).source ∧ extChartAt I x y ∈ s ∩ range I ∧
        ψ.inChartAt x =ᶠ[𝓝[range I] extChartAt I x y] α := by
  have : IsManifold I ((r : WithTop ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨χ, -, hχs⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    ((isOpen_extChartAt_preimage x hs).mem_nhds ⟨mem_chart_source H x, hxs⟩)
  refine ⟨interior {y | χ y = 1}, interior_mem_nhds.mpr χ.eventuallyEq_one, _,
    isSmoothForm_smul_mpullback_extChartAt hs hα (χ.contMDiff.of_le (by exact_mod_cast le_top))
      hχs, fun y hy ↦ ?_⟩
  have hχy : χ y = 1 := interior_subset hy
  obtain ⟨hys, hyr⟩ := mem_extChartAt_source_and_mem_of_mem_preimage
    (hχs (subset_tsupport _ (Function.mem_support.mpr (by rw [hχy]; exact one_ne_zero))))
  refine ⟨hys, hyr, ?_⟩
  -- Near the chart point of `y` the bump is `1`, so the chart expression of the cut-off
  -- pullback is `α`.
  have hone : ∀ᶠ w in 𝓝[range I] extChartAt I x y, χ ((extChartAt I x).symm w) = 1 := by
    have h : {y | χ y = 1} ∈ 𝓝 y := mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
    rw [← map_extChartAt_symm_nhdsWithin_range' hys] at h
    exact h
  filter_upwards [extChartAt_target_mem_nhdsWithin' hys, hone] with w hw hw₁
  rw [inChartAt_fun_smul, hw₁, one_smul]
  exact inChartAt_mpullback_extChartAt _ x hw

end TauCeti.RoughForm
