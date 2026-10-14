/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Chart

/-!
# The exterior derivative squares to zero

For a twice continuously differentiable fixed-coefficient differential form, the second exterior
derivative vanishes. The relative theorem applies to subsets with unique derivatives that are
contained in the closure of their interior. The unrestricted theorem therefore includes manifolds
with boundary and corners and needs neither finite dimensionality nor completeness.

The unbundled results assume `C²` section regularity; differentiability of the exterior derivative
is not a separate hypothesis. A simp theorem gives the square-zero identity for bundled smooth
forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
* Mathlib's flat square-zero theorem (`extDerivWithin_extDerivWithin_apply`).
-/

public section

noncomputable section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} [IsManifold I 2 M]

/-- The exterior derivative within a subset squares to zero for a `C²` section. The subset has
unique derivatives and is contained in the closure of its interior. -/
theorem mextDerivWithin_mextDerivWithin (φ : RoughForm I M F k) {s : Set M}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 2
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s)
    (hs : UniqueMDiffOn I s) (hsc : s ⊆ closure (interior s)) {x : M} (hx : x ∈ s) :
    mextDerivWithin (mextDerivWithin φ s) s x = 0 := by
  let t : Set E := (extChartAt I x).symm ⁻¹' s ∩ range I
  let a : Set E := (extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target
  have hdiff {y : M} (hy : y ∈ s) :=
    (φ.contDiffWithinAt_inChartAt (hφ y hy)).differentiableWithinAt (by norm_num)
  have heq : RoughForm.inChartAt (I := I) (mextDerivWithin φ s) x =ᶠ[𝓝[t] (extChartAt I x x)]
      extDerivWithin (φ.inChartAt x) t := by
    filter_upwards [nhdsWithin_mono _ inter_subset_right
      (extChartAt_target_mem_nhdsWithin (I := I) x), self_mem_nhdsWithin] with z hz hzt
    exact φ.inChartAt_mextDerivWithin hs hz hzt.1 (hsc hzt.1) (hdiff hzt.1)
  have hpoint : RoughForm.inChartAt (I := I) (mextDerivWithin φ s) x (extChartAt I x x) =
      extDerivWithin (φ.inChartAt x) t (extChartAt I x x) :=
    heq.self_of_nhdsWithin ⟨by simpa only [mem_preimage, extChartAt_to_inv] using hx,
      mem_range_self _⟩
  have hta : t =ᶠ[𝓝 (extChartAt I x x)] a := by
    filter_upwards [extChartAt_target_eventuallyEqSet_of_mem (mem_extChartAt_target (I := I) x)]
      with z hz
    simp only [t, a, mem_inter_iff, hz]
  rw [mextDerivWithin_def, heq.extDerivWithin_eq hpoint,
    extDerivWithin_extDerivWithin_congr_set hta]
  apply extDerivWithin_extDerivWithin_apply
    ((φ.contDiffWithinAt_inChartAt (hφ x hx)).mono
      (inter_subset_inter_right _ (extChartAt_target_subset_range x))) (by norm_num)
  · simpa only [a, inter_comm] using hs.uniqueDiffOn_target_inter x
  · exact extChartAt_mem_closure_interior (hsc hx) (mem_extChartAt_source x)
  · exact ⟨by simpa only [mem_preimage, extChartAt_to_inv] using hx, mem_extChartAt_target x⟩

/-- The exterior derivative squares to zero on twice continuously differentiable
fixed-coefficient forms, over any model with corners. -/
theorem mextDeriv_mextDeriv (φ : RoughForm I M F k)
    (hφ : IsSmoothBundleForm (I := I) (F := F) (V := Trivial M F) 2 φ) :
    mextDeriv (mextDeriv φ) = 0 := by
  simp only [← mextDerivWithin_univ]
  funext x
  exact mextDerivWithin_mextDerivWithin φ ((isSmoothBundleForm_def 2 φ).mp hφ).contMDiffOn
    (uniqueMDiffOn_univ (I := I))
    (by simp) (mem_univ x)

/-- In particular, the second exterior derivative of a bundled smooth form vanishes. -/
@[simp]
theorem SmoothForm.mextDeriv_mextDeriv (φ : SmoothForm I M F k) :
    mextDeriv (mextDeriv φ.1) = 0 := by
  have hφ := (isSmoothBundleForm_def ∞ φ.1).mp (mem_smoothForms.mp φ.2)
  exact TauCeti.mextDeriv_mextDeriv φ.1 ((isSmoothBundleForm_def 2 φ.1).mpr
    (hφ.of_le (by simp)))

end TauCeti
