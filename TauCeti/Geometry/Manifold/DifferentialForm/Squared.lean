/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# The exterior derivative squares to zero

For a twice continuously differentiable fixed-coefficient differential form, the second exterior
derivative vanishes. The relative theorem applies to subsets with unique derivatives that are
contained in the closure of their interior. The unrestricted theorem therefore includes manifolds
with boundary and corners and needs neither finite dimensionality nor completeness.

The unbundled results assume `C²` section regularity; differentiability of the exterior derivative
is not a separate hypothesis. A simp theorem gives the square-zero identity for bundled smooth
forms, and `TauCeti.mextDerivₗ_comp_mextDerivₗ` gives the identity for the bundled linear maps.

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
  have heq : RoughForm.inChartAt (I := I) (mextDerivWithin φ s) x =ᶠ[𝓝[t] (extChartAt I x x)]
      extDerivWithin (φ.inChartAt x) t :=
    φ.inChartAt_mextDerivWithin_eventuallyEq (hφ.of_le (by norm_num)) hs hsc x
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
  have hφ : IsSmoothBundleForm (I := I) (F := F) (V := Trivial M F) 2 φ.1 := by
    rw [isSmoothBundleForm_def]
    exact φ.contMDiff.of_le (by simp)
  exact TauCeti.mextDeriv_mextDeriv φ.1 hφ

variable (I) in
/-- Successive exterior derivatives compose to zero as linear maps. -/
@[simp]
theorem mextDerivₗ_comp_mextDerivₗ (k : ℕ) :
    (mextDerivₗ I (k + 1)).comp (mextDerivₗ I (M := M) (F := F) k) = 0 := by
  ext φ : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv,
    LinearMap.zero_apply, Submodule.coe_zero]

end TauCeti
