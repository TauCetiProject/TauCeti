/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.Basic
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Circle.Loop
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Contour.Winding.Number.Degree
import TauCeti.Topology.Circle.Degree.Disc
import TauCeti.Topology.Circle.Normalize

/-!
# Framed charges of continuous discs

Let `(a, α)` be an abelian Higgs pair with cutoff current `Θ = i F_a + d(χ(|α|²) τ)`
(`TauCeti.SeibergWitten.cutoffCurrent`). For a `C²` disc `σ` whose boundary circle lies in the
vacuum region `{χ(|α|²) = 1}`, the charge `(2π)⁻¹ ∫_D σ^* Θ` is an integer
(`TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_closedBall`). This file identifies
that integer with a topological invariant of the boundary values alone, which makes sense for
discs that are merely continuous.

The *framed charge* of a disc `σ` with boundary circle of radius `r` about `z₀` is the degree of
its boundary direction map `u : S¹ → S¹`, `u ζ = α(σ(z₀ + r ζ)) / |α(σ(z₀ + r ζ))|`, the number of
times the framing section `α` winds along the boundary circle. It is defined whenever `α ∘ σ` has
no zero on that circle, for instance when the circle lies in the vacuum region.

* For `C²` discs it is the charge of the cutoff current:
  `∫_D σ^* Θ = 2π deg u` (`integral_cutoffCurrent_comp_closedBall_eq_two_pi_mul_degree`).
* **Relative approximation.** The charge of a continuous disc is the cutoff-current charge of every
  `C²` disc whose boundary values are `δ`-close to it, as soon as the `δ`-neighbourhood of the
  boundary image lies in the vacuum region
  (`integral_cutoffCurrent_comp_closedBall_eq_two_pi_mul_degree_of_dist_lt`): the straight-line
  homotopy between their boundary values stays in that neighbourhood, where `α` has no zero.
* **Stabilization.** For a family of pairs `(bₖ, αₖ)` whose cutoff currents converge as
  distributions, and a continuous disc whose boundary image has a fixed open neighbourhood lying
  eventually in every vacuum region, the framed charges are eventually constant
  (`exists_int_eventually_degree_toBasedLoop_eq`). This follows from the stabilization of the
  charges of a `C²` approximation of the disc
  (`TauCeti.SeibergWitten.exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq`).

The homotopy invariance of the framed charge and its vanishing for discs on which `α ∘ σ` has no
zero hold for continuous maps in general, and are
`Circle.degree_toBasedLoop_eq_of_homotopy_div_norm` and
`Circle.degree_toBasedLoop_eq_zero_of_forall_ne_zero` applied to `α ∘ σ`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology Real ContDiff

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {χ : ℝ → ℝ}

/-- **The charge of a `C²` disc is its framed charge.** Let `σ` be a `C²` disc such that
`χ(|α|²) = 1` along `σ` of the boundary circle of the closed disc of radius `r` about `z₀`, and let
`u ζ = α(σ(z₀ + r ζ)) / |α(σ(z₀ + r ζ))|` be its boundary direction map. Then the integral of
the pullback of the cutoff current over the disc is `2π` times the degree of `u`. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_two_pi_mul_degree {α : E → ℂ}
    {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hσ : ContDiff ℝ 2 σ) (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1)
    {u : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = α (σ (z₀ + r * ζ)) / ‖α (σ (z₀ + r * ζ))‖) :
    ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
      2 * π * Circle.degree u.toBasedLoop := by
  obtain ⟨n, hn, hI⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr hα hb hχ hχ₀ hσ hbd
  have hdeg := Contour.windingNumber_comp_circleMap_eq_degree_toBasedLoop (f := α ∘ σ)
    (((hα.comp hσ).comp (contDiff_circleMap z₀ r)).of_le one_le_two) u hu
  have hn' : (n : ℂ) = Circle.degree u.toBasedLoop := hn.symm.trans hdeg
  rw [hI, Int.cast_inj.1 hn']

/-- **Relative approximation of the framed charge.** Let `σ` be a disc, continuous on the boundary
circle of radius `r` about `z₀`, with boundary direction map
`u ζ = α(σ(z₀ + r ζ)) / |α(σ(z₀ + r ζ))|`, and suppose that `χ(|α|²) = 1` on the
`δ`-neighbourhood of the image of that circle. Then every `C²` disc `σ'` whose values on the
circle are `δ`-close to those of `σ` has cutoff-current charge `2π` times the degree of `u`. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_two_pi_mul_degree_of_dist_lt {α : E → ℂ}
    {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ σ' : ℂ → E} {z₀ : ℂ} {r δ : ℝ} (hr : 0 ≤ r)
    (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hσ : ContinuousOn σ (Metric.sphere z₀ r))
    (hδ : ∀ y ∈ Metric.thickening δ (σ '' Metric.sphere z₀ r), χ (normSq (α y)) = 1)
    (hσ' : ContDiff ℝ 2 σ') (hσσ' : ∀ z ∈ Metric.sphere z₀ r, dist (σ' z) (σ z) < δ)
    {u : C(Circle, Circle)}
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = α (σ (z₀ + r * ζ)) / ‖α (σ (z₀ + r * ζ))‖) :
    ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ' z)).compContinuousLinearMap (fderiv ℝ σ' z) ![1, I] =
      2 * π * Circle.degree u.toBasedLoop := by
  have hsph (ζ : Circle) : z₀ + r * (ζ : ℂ) ∈ Metric.sphere z₀ r := by
    simp [abs_of_nonneg hr]
  -- The segment from `σ z` to `σ' z` stays in the `δ`-neighbourhood, where `α` has no zero.
  have hseg (s : unitInterval) {z : ℂ} (hz : z ∈ Metric.sphere z₀ r) :
      σ z + (s : ℝ) • (σ' z - σ z) ∈ Metric.thickening δ (σ '' Metric.sphere z₀ r) := by
    refine Metric.mem_thickening_iff.2 ⟨σ z, mem_image_of_mem σ hz, ?_⟩
    calc dist (σ z + (s : ℝ) • (σ' z - σ z)) (σ z) = (s : ℝ) * dist (σ' z) (σ z) := by
          simp [dist_eq_norm, norm_smul, abs_of_nonneg s.property.1]
      _ ≤ dist (σ' z) (σ z) := mul_le_of_le_one_left dist_nonneg s.property.2
      _ < δ := hσσ' z hz
  have hne (s : unitInterval) {z : ℂ} (hz : z ∈ Metric.sphere z₀ r) :
      α (σ z + (s : ℝ) • (σ' z - σ z)) ≠ 0 :=
    ne_zero_of_cutoff_eq_one hχ₀ (hδ _ (hseg s hz))
  have hσ'U {z : ℂ} (hz : z ∈ Metric.sphere z₀ r) :
      σ' z ∈ Metric.thickening δ (σ '' Metric.sphere z₀ r) := by
    have h := hseg 1 hz
    rwa [Set.Icc.coe_one, one_smul, add_sub_cancel] at h
  have hσc : Continuous fun ζ : Circle ↦ σ (z₀ + r * ζ) :=
    hσ.comp_continuous (by fun_prop) hsph
  let F : C(unitInterval × Circle, ℂ) :=
    ⟨fun p ↦ α (σ (z₀ + r * p.2) + (p.1 : ℝ) • (σ' (z₀ + r * p.2) - σ (z₀ + r * p.2))),
      hα.continuous.comp <| (hσc.comp continuous_snd).add <|
        (continuous_subtypeVal.comp continuous_fst).smul <|
          (hσ'.continuous.comp (by fun_prop)).sub (hσc.comp continuous_snd)⟩
  let f' : C(Circle, ℂ) := ⟨fun ζ ↦ α (σ' (z₀ + r * ζ)), by fun_prop⟩
  let u' := f'.normalizeToCircle fun ζ ↦ by simpa [f'] using hne 1 (hsph ζ)
  have hu' (ζ : Circle) : (u' ζ : ℂ) = α (σ' (z₀ + r * ζ)) / ‖α (σ' (z₀ + r * ζ))‖ :=
    f'.coe_normalizeToCircle_apply _ ζ
  have hdeg : Circle.degree u.toBasedLoop = Circle.degree u'.toBasedLoop :=
    Circle.degree_toBasedLoop_eq_of_homotopy_div_norm F (fun p ↦ hne p.1 (hsph p.2))
      (fun ζ ↦ by simp [F, hu]) (fun ζ ↦ by simp [F, hu'])
  rw [integral_cutoffCurrent_comp_closedBall_eq_two_pi_mul_degree hr hα hb hχ hχ₀ hσ'
    (fun θ ↦ hδ _ (hσ'U (circleMap_mem_sphere z₀ hr θ))) hu', hdeg]

/-- **Stabilization of the framed charges of a continuous disc.** Let `(bₖ, αₖ)` be a family of
abelian Higgs pairs along a filter `l` whose cutoff currents `Θₖ` have coefficients converging as
distributions, and let `σ` be a disc continuous on the boundary circle of radius `r` about `z₀`.
Suppose an open set `U` contains the image of that circle and eventually lies in the vacuum region
`{χ(|αₖ|²) = 1}`. Then the framed charges are eventually constant: there is an integer `n` such
that, eventually along `l`, every boundary direction map
`u ζ = αₖ(σ(z₀ + r ζ)) / |αₖ(σ(z₀ + r ζ))|` has degree `n`. -/
theorem exists_int_eventually_degree_toBasedLoop_eq {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {l : Filter ι} [l.NeBot] {α : ι → E → ℂ}
    {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r : ℝ} {U : Set E} (hr : 0 ≤ r)
    (hα : ∀ k, ContDiff ℝ 2 (α k)) (hb : ∀ k, ContDiff ℝ 1 (b k)) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContinuousOn σ (Metric.sphere z₀ r)) (hU : IsOpen U)
    (hσU : MapsTo σ (Metric.sphere z₀ r) U)
    (hUχ : ∀ᶠ k in l, ∀ y ∈ U, χ (normSq (α k y)) = 1)
    (hlim : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ m : Fin 2 → E,
      ∃ L, Tendsto (fun k ↦ ∫ y, φ y * cutoffCurrent χ (b k) (α k) y m ∂μ) l (𝓝 L)) :
    ∃ n : ℤ, ∀ᶠ k in l, ∀ u : C(Circle, Circle),
      (∀ ζ : Circle, (u ζ : ℂ) = α k (σ (z₀ + r * ζ)) / ‖α k (σ (z₀ + r * ζ))‖) →
        Circle.degree u.toBasedLoop = n := by
  -- A uniform buffer `δ` around the compact boundary image inside `U`.
  have hK : IsCompact (σ '' Metric.sphere z₀ r) := (isCompact_sphere z₀ r).image_of_continuousOn hσ
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU (image_subset_iff.2 hσU)
  -- Extend `σ` continuously from the circle and approximate it by a smooth disc `σ'`.
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (Metric.isClosed_sphere (x := z₀) (ε := r))
    ⟨fun z : Metric.sphere z₀ r ↦ σ z, hσ.domRestrict⟩
  have hgσ (z : ℂ) (hz : z ∈ Metric.sphere z₀ r) : g z = σ z :=
    congr($hg ⟨z, hz⟩)
  obtain ⟨σ', hσ', hσσ', -⟩ := g.continuous.exists_contDiff_approx (n := 2) (ε := fun _ ↦ δ / 2)
    continuous_const fun _ ↦ half_pos hδ
  have hclose (z : ℂ) (hz : z ∈ Metric.sphere z₀ r) : dist (σ' z) (σ z) < δ / 2 := by
    simpa [hgσ z hz] using hσσ' z
  -- The translates `σ' + p`, `‖p‖ ≤ δ / 2`, keep their boundary circles in `U`.
  have hbd : ∀ᶠ k in l, ∀ p ∈ Metric.closedBall (0 : E) (δ / 2), ∀ θ,
      χ (normSq (α k (σ' (circleMap z₀ r θ) + p))) = 1 := by
    filter_upwards [hUχ] with k hk p hp θ
    refine hk _ (hδU (Metric.mem_thickening_iff.2 ⟨σ (circleMap z₀ r θ),
      mem_image_of_mem σ (circleMap_mem_sphere z₀ hr θ), ?_⟩))
    have hp' : ‖p‖ ≤ δ / 2 := by simpa using hp
    calc dist (σ' (circleMap z₀ r θ) + p) (σ (circleMap z₀ r θ))
        ≤ dist (σ' (circleMap z₀ r θ)) (σ (circleMap z₀ r θ)) + ‖p‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le (hclose _ (circleMap_mem_sphere z₀ hr θ)) hp'
      _ = δ := add_halves δ
  obtain ⟨n, hn⟩ := exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq (μ := μ) hr
    (half_pos hδ) hα hb hχ hχ₀ hσ' hbd hlim
  refine ⟨n, ?_⟩
  filter_upwards [hn, hUχ] with k hnk hk u hu
  have h := integral_cutoffCurrent_comp_closedBall_eq_two_pi_mul_degree_of_dist_lt hr (hα k) (hb k)
    hχ hχ₀ hσ (fun y hy ↦ hk y (hδU hy)) hσ' (fun z hz ↦ (hclose z hz).trans (half_lt_self hδ))
    hu
  rw [hnk, mul_right_inj' (by positivity : (2 * π : ℝ) ≠ 0)] at h
  exact_mod_cast h.symm

end TauCeti.SeibergWitten
