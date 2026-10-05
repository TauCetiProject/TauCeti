/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Removable singularities along a coordinate hyperplane

Let `V` be a finite-dimensional complex normed space, `U ⊆ V` and `s ⊆ ℂ` open sets, and `c` a
point of `ℂ`. This file proves the Riemann extension theorem across the coordinate hyperplane
`V × {c}`: a function `f` analytic on `U × (s \ {c})` whose slices `z ↦ f (w, z)` are bounded near
`c` extends to a function analytic on all of `U × s`, and the extension is unique.

Only the slices of `f` are assumed bounded, not `f` itself near `U × {c}`. Each slice extends
across `c` by the one-variable removable singularity theorem
(`Complex.differentiableOn_update_limUnder_of_bddAbove`), and the slice extensions together form
the extension of `f`. They do not give its joint analyticity: near a point `(w₀, c)` the extension
is written as the Cauchy integral
`(w, z) ↦ (2πi)⁻¹ ∮ ζ in C(c, ρ), (ζ - z)⁻¹ • f (w, ζ)`
over a circle on which `f` is jointly analytic, and this integral depends analytically on the
parameter `(w, z)` by `TauCeti.analyticAt_circleIntegral`.

This extension theorem is the step of Puiseux-type arguments with parameters in which the roots of
a polynomial with analytic coefficients, known to be analytic off a hyperplane and bounded near
it, are shown to be analytic across it.

## Main results

* `TauCeti.exists_analyticOnNhd_prod_eqOn`: **the Riemann extension theorem across a coordinate
  hyperplane.**
* `TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton`: uniqueness of the extension, for continuous
  functions.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I (the
  Riemann extension theorem).
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), §4, for its use in Puiseux-type arguments with
  parameters.
-/

public section

open Complex Filter Function Metric Real Set Topology

namespace TauCeti

/-- **Uniqueness of extensions across a coordinate hyperplane.** Two functions continuous on
`U × s`, for `s ⊆ ℂ` open, which agree off the hyperplane `z = c` agree on all of `U × s`. -/
theorem eqOn_prod_of_eqOn_prod_diff_singleton {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {g₁ g₂ : X × ℂ → Y} {U : Set X} {s : Set ℂ} {c : ℂ}
    (hs : IsOpen s) (h₁ : ContinuousOn g₁ (U ×ˢ s)) (h₂ : ContinuousOn g₂ (U ×ˢ s))
    (h : EqOn g₁ g₂ (U ×ˢ (s \ {c}))) : EqOn g₁ g₂ (U ×ˢ s) := by
  refine h.of_subset_closure h₁ h₂ (prod_mono subset_rfl sdiff_subset) ?_
  rw [closure_prod_eq, sdiff_eq]
  exact prod_mono subset_closure ((dense_compl_singleton c).open_subset_closure_inter hs)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V × ℂ → E} {U : Set V} {s : Set ℂ}
  {c : ℂ}

/-- The slice of `f` at `w`, extended across `c` by its limit there, is complex differentiable on
`s`. -/
private theorem differentiableOn_update_limUnder_slice (hs : IsOpen s)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ (s \ {c}))) {w : V} (hw : w ∈ U)
    (hb : ∃ t ∈ 𝓝 c, BddAbove (norm ∘ (fun z => f (w, z)) '' (t \ {c}))) :
    DifferentiableOn ℂ (update (fun z => f (w, z)) c (limUnder (𝓝[≠] c) fun z => f (w, z))) s := by
  have hd : ∀ z ∈ s \ {c}, DifferentiableAt ℂ (fun z => f (w, z)) z := fun z hz =>
    ((hf (w, z) ⟨hw, hz⟩).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
  intro z hz
  by_cases hzc : z = c
  · subst hzc
    obtain ⟨t, ht, htb⟩ := hb
    have hts : t ∩ s ∈ 𝓝 z := inter_mem ht (hs.mem_nhds hz)
    exact ((differentiableOn_update_limUnder_of_bddAbove hts
      (fun y hy => (hd y ⟨hy.1.2, hy.2⟩).differentiableWithinAt)
      (htb.mono (image_mono (sdiff_subset_sdiff_left inter_subset_left)))).differentiableAt
        hts).differentiableWithinAt
  · refine ((hd z ⟨hz, hzc⟩).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [eventually_ne_nhds hzc] with y hy
    exact update_of_ne hy _ _

variable [FiniteDimensional ℂ V]

/-- **The Riemann extension theorem across a coordinate hyperplane.** Let `U ⊆ V` and `s ⊆ ℂ` be
open. If `f` is analytic on `U × (s \ {c})` and, when `c ∈ s`, each slice `z ↦ f (w, z)`, for
`w ∈ U`, is bounded on a punctured neighbourhood of `c`, then some `g` analytic on `U × s` agrees
with `f` on `U × (s \ {c})`. Such a `g` is unique on `U × s` by
`eqOn_prod_of_eqOn_prod_diff_singleton`. -/
theorem exists_analyticOnNhd_prod_eqOn (hU : IsOpen U) (hs : IsOpen s)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ (s \ {c})))
    (hb : c ∈ s → ∀ w ∈ U, ∃ t ∈ 𝓝 c, BddAbove (norm ∘ (fun z => f (w, z)) '' (t \ {c}))) :
    ∃ g : V × ℂ → E, AnalyticOnNhd ℂ g (U ×ˢ s) ∧ EqOn g f (U ×ˢ (s \ {c})) := by
  -- Extend each slice across `c` by its limit there.
  set g : V × ℂ → E := fun x =>
    update (fun z => f (x.1, z)) c (limUnder (𝓝[≠] c) fun z => f (x.1, z)) x.2 with hg_def
  have hgf : EqOn g f (U ×ˢ (s \ {c})) := fun x hx => update_of_ne hx.2.2 _ _
  refine ⟨g, ?_, hgf⟩
  rintro ⟨w₀, z₀⟩ ⟨hw₀, hz₀⟩
  obtain hz₀c | rfl := ne_or_eq z₀ c
  · -- Off the hyperplane, `g` is `f` near `(w₀, z₀)`.
    have hopen : IsOpen (U ×ˢ (s \ {c})) := hU.prod (hs.sdiff isClosed_singleton)
    refine (hf _ ⟨hw₀, hz₀, hz₀c⟩).congr ?_
    filter_upwards [hopen.mem_nhds ⟨hw₀, hz₀, hz₀c⟩] with x hx
    exact (hgf hx).symm
  -- Near `(w₀, c)`, `g` is a Cauchy integral over a circle on which `f` is jointly analytic.
  obtain ⟨ρ, hρ, hρs⟩ := nhds_basis_closedBall.mem_iff.1 (hs.mem_nhds hz₀)
  have hne : ∀ ζ ∈ sphere z₀ ρ, ζ ≠ z₀ := fun ζ hζ => ne_of_mem_sphere hζ hρ.ne'
  have hH : AnalyticAt ℂ
      (fun x : V × ℂ => (2 * π * I)⁻¹ • ∮ ζ in C(z₀, ρ), (ζ - x.2)⁻¹ • f (x.1, ζ)) (w₀, z₀) := by
    refine (analyticAt_circleIntegral (f := fun y : (V × ℂ) × ℂ => (y.2 - y.1.2)⁻¹ • f (y.1.1, y.2))
      fun ζ hζ => ?_).const_smul
    rw [abs_of_pos hρ] at hζ
    refine ((analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)).inv
      (sub_ne_zero.2 (hne ζ hζ))).smul ?_
    exact (hf (w₀, ζ) ⟨hw₀, hρs (sphere_subset_closedBall hζ), hne ζ hζ⟩).comp_of_eq
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd) rfl
  refine hH.congr ?_
  filter_upwards [prod_mem_nhds (hU.mem_nhds hw₀) (ball_mem_nhds z₀ hρ)] with ⟨w, z⟩ ⟨hw, hz⟩
  have hd := (differentiableOn_update_limUnder_slice hs hf hw (hb hz₀ w hw)).mono hρs
  dsimp only
  rw [circleIntegral.integral_congr hρ.le fun ζ hζ => by
      rw [← update_of_ne (hne ζ hζ) (limUnder (𝓝[≠] z₀) fun z => f (w, z)) fun z => f (w, z)],
    hd.circleIntegral_sub_inv_smul hz, inv_smul_smul₀ two_pi_I_ne_zero, hg_def]

end TauCeti
