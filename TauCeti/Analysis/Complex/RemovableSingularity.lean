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
* `TauCeti.eqOn_conj_extension`: compatibility of continuous extensions with complex conjugation
  of the punctured coordinate, carried through the exceptional hyperplane by continuity.
* `TauCeti.bddAbove_slice_of_local`, `TauCeti.extension_ne_zero_of_local`: the transverse slices
  of a function locally equal off the hyperplane to a function continuous on it are bounded, and
  an extension across the hyperplane keeps a local nonvanishing witness nonvanishing there.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I (the
  Riemann extension theorem).
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), §4, for its use in Puiseux-type arguments with
  parameters.
-/

public section

open Complex ComplexConjugate Filter Function Metric Real Set Topology

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

/-- Conjugation compatibility of the pole-removed extensions: if continuous functions `g i` on
`U × ball 0 R'` agree off the hyperplane `z = 0` with the monomial `z ^ (n * a)` times branches
`r i` that satisfy it, then the `g i` satisfy it on the full product, by continuity through the
exceptional hyperplane. The removed pole is a real monomial, so scaling commutes with
conjugation. -/
lemma eqOn_conj_extension {E ι : Type*} [TopologicalSpace E] {U : Set E} {n a : ℕ} {R' : ℝ}
    {τ : E → E} {g r : ι → E × ℂ → ℂ} {σ : ι → ι}
    (hgc : ∀ i, ContinuousOn (g i) (U ×ˢ ball 0 R'))
    (hge : ∀ i, EqOn (g i) (fun b ↦ b.2 ^ (n * a) * r i b) (U ×ˢ (ball 0 R' \ {0})))
    (hσ : ∀ i b, b ∈ U ×ˢ (ball 0 R' \ {0}) → r (σ i) b = conj (r i (τ b.1, conj b.2)))
    (hκ : ContinuousOn (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 R'))
    (hκT : MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 R') (U ×ˢ ball 0 R'))
    (i : ι) :
    EqOn (g (σ i)) (fun b ↦ conj (g i (τ b.1, conj b.2))) (U ×ˢ ball 0 R') := by
  have hκS : MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ (ball 0 R' \ {0}))
      (U ×ˢ (ball 0 R' \ {0})) := fun b hb ↦
    ⟨(hκT ⟨hb.1, hb.2.1⟩).1, (hκT ⟨hb.1, hb.2.1⟩).2, by simpa using hb.2.2⟩
  refine eqOn_prod_of_eqOn_prod_diff_singleton (c := (0 : ℂ)) isOpen_ball (hgc (σ i))
    (Complex.continuous_conj.comp_continuousOn ((hgc i).comp hκ hκT)) ?_
  intro b hb
  simp only [hge (σ i) hb, hge i (hκS hb), hσ i b hb, map_mul, map_pow, Complex.conj_conj]

/-- If a function agrees off the hyperplane `z = c` with a function continuous at `(x, c)`, for
each `x ∈ U`, then its transverse slices are bounded near `c` away from `c`. -/
theorem bddAbove_slice_of_local {X : Type*} [TopologicalSpace X] {Y : Type*}
    [SeminormedAddGroup Y] {q : X × ℂ → Y} {U : Set X} {c : ℂ}
    (hlocalq : ∀ x ∈ U, ∃ v : X × ℂ → Y,
      ContinuousAt v (x, c) ∧ ∀ᶠ p in 𝓝 (x, c), p.2 ≠ c → q p = v p) :
    ∀ x ∈ U, ∃ t ∈ 𝓝 c, BddAbove (norm ∘ (fun z ↦ q (x, z)) '' (t \ {c})) := by
  intro x hx
  obtain ⟨v, hv, heq⟩ := hlocalq x hx
  have hline : Tendsto (fun z : ℂ ↦ (x, z)) (𝓝 c) (𝓝 (x, c)) :=
    continuous_const.prodMk continuous_id |>.tendsto c
  obtain ⟨C, hC⟩ := (hv.tendsto.comp hline).norm.isBoundedUnder_le
  refine ⟨{z | (z ≠ c → q (x, z) = v (x, z)) ∧ ‖v (x, z)‖ ≤ C},
    (hline.eventually heq).and hC, C, ?_⟩
  rintro _ ⟨z, ⟨hz, hz0⟩, rfl⟩
  simpa only [comp_apply, hz.1 hz0] using hz.2

/-- An extension `w` of `q` across the hyperplane `z = c`, continuous along it, agrees with a
nonvanishing local witness also on the hyperplane, by uniqueness of the limit along a punctured
slice. Thus no zero is introduced by extension. -/
theorem extension_ne_zero_of_local {X : Type*} [TopologicalSpace X] {Y : Type*} [Zero Y]
    [TopologicalSpace Y] [T2Space Y] {q w : X × ℂ → Y} {U : Set X} {s : Set ℂ} {c : ℂ}
    (hs : IsOpen s) (hc : c ∈ s) (hw : ∀ x ∈ U, ContinuousAt w (x, c))
    (hwq : EqOn w q (U ×ˢ (s \ {c})))
    (hlocalq : ∀ x ∈ U, ∃ v : X × ℂ → Y,
      ContinuousAt v (x, c) ∧ v (x, c) ≠ 0 ∧
        ∀ᶠ p in 𝓝 (x, c), p.2 ≠ c → q p = v p) :
    ∀ x ∈ U, w (x, c) ≠ 0 := by
  intro x hx
  obtain ⟨v, hv, hv0, heq⟩ := hlocalq x hx
  have hline : Tendsto (fun z : ℂ ↦ (x, z)) (𝓝 c) (𝓝 (x, c)) :=
    continuous_const.prodMk continuous_id |>.tendsto c
  have hs0 : ∀ᶠ z in 𝓝[≠] c, z ∈ s := nhdsWithin_le_nhds (hs.mem_nhds hc)
  have heq' : (fun z : ℂ ↦ w (x, z)) =ᶠ[𝓝[≠] c] fun z ↦ v (x, z) := by
    filter_upwards [(hline.eventually heq).filter_mono nhdsWithin_le_nhds,
      hs0, self_mem_nhdsWithin] with z hz hzs hz0
    exact (hwq ⟨hx, hzs, hz0⟩).trans (hz hz0)
  have hlim : Tendsto (fun z : ℂ ↦ w (x, z)) (𝓝[≠] c) (𝓝 (w (x, c))) :=
    ((hw x hx).tendsto.comp hline).mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun z : ℂ ↦ v (x, z)) (𝓝[≠] c) (𝓝 (v (x, c))) :=
    (hv.tendsto.comp hline).mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique (hlim.congr' heq') hlim') ▸ hv0

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
