/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# Local naturality of the exterior derivative within a set

The exterior derivative commutes with pullback when the map sends the source set into the target
set locally at the point. This version of Mathlib's `extDerivWithin_pullback` lets coordinate
changes be used only on their chart overlaps, without conditions on their total extensions.

The source set can have boundary: it need only have unique derivatives and accumulate at the
point from its interior. The latter condition guarantees symmetry of the second derivative.

Pulling a form back along a continuous linear equivalence `A` preserves regularity
(`TauCeti.contDiffOn_pullback_continuousLinearEquiv`) and closedness
(`TauCeti.extDeriv_pullback_continuousLinearEquiv_eq_zero`) on the preimage of the domain.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {k : ℕ} {r : WithTop ℕ∞} {ω : F → F [⋀^Fin k]→L[𝕜] G}
  {f : E → F} {s : Set E} {t : Set F} {x : E}

/-- Exterior differentiation within a set commutes with pullback if the map sends that set into
the target set near the base point. No condition is imposed away from that neighbourhood. -/
theorem extDerivWithin_pullback_of_preimage_mem_nhdsWithin
    (hω : DifferentiableWithinAt 𝕜 ω t (f x)) (hf : ContDiffWithinAt 𝕜 r f s x)
    (hr : minSmoothness 𝕜 2 ≤ r) (hs : UniqueDiffOn 𝕜 s)
    (hxc : x ∈ closure (interior s)) (hxs : x ∈ s) (hst : f ⁻¹' t ∈ 𝓝[s] x) :
    extDerivWithin (fun y ↦ (ω (f y)).compContinuousLinearMap (fderivWithin 𝕜 f s y)) s x =
      (extDerivWithin ω t (f x)).compContinuousLinearMap (fderivWithin 𝕜 f s x) := by
  obtain ⟨u, hu, hxu, hut⟩ := mem_nhdsWithin.mp hst
  have hux : u ∈ 𝓝 x := hu.mem_nhds hxu
  have heq : s ∩ u =ᶠ[𝓝 x] s := by
    filter_upwards [hux] with y hy
    simp [hy]
  have hxc' : x ∈ closure (interior (s ∩ u)) := by
    rw [mem_closure_iff_nhds] at hxc ⊢
    intro v hv
    obtain ⟨y, ⟨hyv, hyu⟩, hys⟩ := hxc (v ∩ u) (inter_mem hv hux)
    refine ⟨y, hyv, ?_⟩
    simpa only [interior_inter, hu.interior_eq, mem_inter_iff] using And.intro hys hyu
  have hderiv : (fun y ↦ fderivWithin 𝕜 f (s ∩ u) y) =ᶠ[𝓝[s] x]
      (fun y ↦ fderivWithin 𝕜 f s y) := by
    filter_upwards [nhdsWithin_le_nhds hux] with y hy
    exact fderivWithin_inter (hu.mem_nhds hy)
  have hpull : (fun y ↦ (ω (f y)).compContinuousLinearMap (fderivWithin 𝕜 f (s ∩ u) y))
      =ᶠ[𝓝[s] x] (fun y ↦ (ω (f y)).compContinuousLinearMap (fderivWithin 𝕜 f s y)) := by
    filter_upwards [hderiv] with y hy
    rw [hy]
  have hlocal := extDerivWithin_pullback hω (hf.mono inter_subset_left) hr (hs.inter hu)
    hxc' ⟨hxs, hxu⟩ (fun y hy ↦ hut ⟨hy.2, hy.1⟩)
  rw [extDerivWithin_congr_set heq, fderivWithin_inter hux] at hlocal
  exact hpull.extDerivWithin_eq (by rw [fderivWithin_inter hux]) |>.symm.trans hlocal

end TauCeti

namespace TauCeti

/-- Pulling a `C^r` form on `t` back along a continuous linear equivalence `A` gives a `C^r` form on
`A ⁻¹' t`. -/
theorem contDiffOn_pullback_continuousLinearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {r : WithTop ℕ∞}
    {ω : F → F [⋀^Fin k]→L[ℝ] ℝ} {t : Set F} (hω : ContDiffOn ℝ r ω t) (A : E ≃L[ℝ] F) :
    ContDiffOn ℝ r (fun x ↦ (ω (A x)).compContinuousLinearMap (A : E →L[ℝ] F)) (A ⁻¹' t) := by
  have h := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin k) (F := ℝ)
    (A : E →L[ℝ] F)).contDiff.comp_contDiffOn
      (hω.comp A.contDiff.contDiffOn fun x (hx : x ∈ A ⁻¹' t) ↦ hx)
  exact h.congr fun x _ ↦ (ContinuousAlternatingMap.compContinuousLinearMapCLM_apply _ _).symm

/-- Pulling a closed `C^r` form (`r ≥ 1`) on an open set `t` back along a continuous linear
equivalence `A` gives a closed form on `A ⁻¹' t`. -/
theorem extDeriv_pullback_continuousLinearEquiv_eq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {r : ℕ∞}
    {ω : F → F [⋀^Fin k]→L[ℝ] ℝ} {t : Set F} (hr : 1 ≤ r) (ht : IsOpen t)
    (hω : ContDiffOn ℝ r ω t) (hdω : ∀ x ∈ t, extDeriv ω x = 0) (A : E ≃L[ℝ] F) {x : E}
    (hx : x ∈ A ⁻¹' t) :
    extDeriv (fun x ↦ (ω (A x)).compContinuousLinearMap (A : E →L[ℝ] F)) x = 0 := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  have h : (fun x ↦ (ω (A x)).compContinuousLinearMap (A : E →L[ℝ] F)) =
      fun x ↦ (ω (A x)).compContinuousLinearMap (fderiv ℝ A x) := by
    funext x
    rw [A.fderiv]
  rw [h, extDeriv_pullback ((hω.differentiableOn hr0).differentiableAt (ht.mem_nhds hx))
    (A.contDiff (n := ⊤)).contDiffAt le_top, hdω _ hx]
  ext v
  simp

end TauCeti
