/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Regularity of integral curves on parameter sets

An integral curve gains one derivative when its vector field is `C^n` at every point of
the curve image and those points are interior to the manifold. Regularity is within any
parameter set with unique derivatives, including nondegenerate closed intervals: no extension
of the curve beyond its endpoints is assumed.

In coordinates the first derivative is the vector field evaluated along the curve. The
within-set ODE regularity theorem then gives `C^(n + 1)` regularity. Applied to the geodesic
spray, this removes the separate regularity assumption on the projected curve in the spray
characterization of geodesics.

## References

* The chart calculation adapts Tau Ceti's `IsMIntegralCurveAt.contMDiffAt_two` in
  `TauCeti.Geometry.Manifold.IntegralCurve.Basic` to within-derivatives on `UniqueDiffOn` sets.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An integral curve is `C^(n + 1)` within a parameter set with unique derivatives if the
vector field is `C^n` at every point of the curve image and those points are interior to the
manifold. -/
theorem contMDiffOn_succ_of_isMIntegralCurveOn (n : ℕ) [IsManifold I (n + 1 : ℕ) M]
    {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hγ : IsMIntegralCurveOn γ v s)
    (hinterior : ∀ t ∈ s, I.IsInteriorPoint (γ t))
    (hv : let _ : IsManifold I 1 M := IsManifold.of_le (n := (n + 1 : ℕ)) (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n));
      ∀ t ∈ s,
        ContMDiffAt I I.tangent n (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t)) :
    ContMDiffOn 𝓘(ℝ, ℝ) I (n + 1 : ℕ) γ s := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (n + 1 : ℕ)) (by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  -- Unfold the dependent let so the tangent bundle uses the installed low-order instance.
  change ∀ t ∈ s,
    ContMDiffAt I I.tangent n (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t) at hv
  intro t₀ ht₀
  rw [contMDiffWithinAt_iff_target]
  refine ⟨(hγ t₀ ht₀).continuousWithinAt, ?_⟩
  -- Read the equation in the chart at the current value and restrict to its source.
  let c : ℝ → E := extChartAt I (γ t₀) ∘ γ
  let w : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀)
      ((extChartAt I (γ t₀)).symm x) (v ((extChartAt I (γ t₀)).symm x))
  have hw : ContDiffAt ℝ n w (extChartAt I (γ t₀) (γ t₀)) := by
    have h := hv t₀ ht₀
    rw [contMDiffAt_iff] at h
    exact (h.2.contDiffAt
      (range_mem_nhds_isInteriorPoint (hinterior t₀ ht₀))).snd
  obtain ⟨u, hu, hwu⟩ := hw.contDiffOn le_rfl (by simp)
  have hcsrc : ∀ᶠ t in 𝓝[s] t₀, γ t ∈ (extChartAt I (γ t₀)).source :=
    (hγ t₀ ht₀).continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (I := I) _)
  have hcu : ∀ᶠ t in 𝓝[s] t₀, c t ∈ u :=
    ((continuousAt_extChartAt (γ t₀)).comp_continuousWithinAt
      (hγ t₀ ht₀).continuousWithinAt).eventually hu
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (hcsrc.and hcu)
  obtain ⟨V, hVU, hVopen, htV⟩ := mem_nhds_iff.mp hU
  let r := s ∩ V
  have hr : UniqueDiffOn ℝ r := hs.inter hVopen
  have hsrc (t : ℝ) (ht : t ∈ r) : γ t ∈ (extChartAt I (γ t₀)).source :=
    (hUs ⟨hVU ht.2, ht.1⟩).1
  have hmaps : MapsTo c r u := fun t ht ↦ (hUs ⟨hVU ht.2, ht.1⟩).2
  have hd (t : ℝ) (ht : t ∈ r) : HasDerivWithinAt c (w (c t)) r t := by
    have h := hasDerivWithinAt_comp_curve (s := r)
      (mdifferentiableAt_extChartAt (I := I) (extChartAt_source I (γ t₀) ▸ hsrc t ht))
      ((hγ t ht.1).mono inter_subset_left)
    convert h using 1
    simp only [w, c, Function.comp_apply, mvfderiv]
    rw [(extChartAt I (γ t₀)).left_inv (hsrc t ht),
      (hasMFDerivAt_extChartAt (I := I)
        (extChartAt_source I (γ t₀) ▸ hsrc t ht)).mfderiv,
      mfderiv_chartAt_eq_tangentCoordChange (extChartAt_source I (γ t₀) ▸ hsrc t ht)]
    rfl
  have hc : ContDiffOn ℝ (n + 1 : ℕ) c r :=
    TauCeti.contDiffOn_succ_of_hasDerivWithinAt_comp hr hwu hmaps hd
  have hct := hc t₀ ⟨ht₀, htV⟩
  rw [contDiffWithinAt_inter (hVopen.mem_nhds htV)] at hct
  exact hct.contMDiffWithinAt

/-- An integral curve on a boundaryless manifold is `C²` within a parameter set with unique
derivatives when the vector field is `C¹` at every point of the curve image. This includes
the endpoints of a nondegenerate closed interval. -/
theorem contMDiffOn_two_of_isMIntegralCurveOn [BoundarylessManifold I M] [IsManifold I 2 M]
    {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hγ : IsMIntegralCurveOn γ v s)
    (hv : ∀ t ∈ s,
      ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t)) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s :=
  contMDiffOn_succ_of_isMIntegralCurveOn 1 hs hγ
    (fun _ _ ↦ BoundarylessManifold.isInteriorPoint) hv

end TauCeti.Manifold
