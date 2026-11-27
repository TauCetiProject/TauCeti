/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.FDeriv.Antilipschitz
import TauCeti.Analysis.Convex.SecantEstimate
import TauCeti.Analysis.Normed.Group.Pi
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
import TauCeti.Geometry.Convex.ConvexSpace.Defs
import TauCeti.Analysis.Convex.StdSimplex.Faces

/-!
# Smooth triangulations are locally bi-Lipschitz in charts

A `Cⁿ` immersion `g` of a closed simplex into a manifold (`1 ≤ n`) is locally bi-Lipschitz in
charts: every point `x` of the simplex has a neighbourhood `s` in the simplex, mapped by `g` into
the source of the chart `φ = extChartAt I (g x)`, and constants `0 < c ≤ C` with
`c |y - z| ≤ |φ (g y) - φ (g z)| ≤ C |y - z|` for all `y, z ∈ s`, where `|y - z|` is the distance
of barycentric coordinate vectors in `σ → ℝ`
(`TauCeti.IsSimplexImmersion.exists_mem_nhds_mul_norm_sub_le_norm_sub_le_mul_extChartAt`).
Applied to the closed simplices of a smooth triangulation, this gives local bi-Lipschitz bounds in
charts on every closed simplex
(`TauCeti.IsSmoothTriangulation.exists_mem_nhds_mul_norm_sub_le_norm_sub_le_mul_extChartAt`).

The chart representative `φ ∘ F` of `g` in barycentric coordinates is `C¹` within the simplex
near `x`, with a family `A y` of derivatives within the simplex depending continuously on `y`. The
derivative `A x` is injective on the directions of the simplex, the vectors with coordinate sum
zero, since it agrees there with the injective derivative given by the immersion condition; so
`c₀ |v| ≤ |A x v|` on these directions for some `c₀ > 0`. On a small convex neighbourhood of `x`
in the simplex, `‖A y - A x‖ ≤ c₀ / 2`, and the mean value inequality against the fixed map `A x`
gives the lower bound with `c = c₀ / 2`, while the mean value inequality for the bounded
derivatives gives the upper bound.

## Main results

* `TauCeti.IsSimplexImmersion.exists_mem_nhds_mul_norm_sub_le_norm_sub_le_mul_extChartAt`: an
  immersion of a simplex is locally bi-Lipschitz in charts.
* `TauCeti.IsSmoothTriangulation.exists_mem_nhds_mul_norm_sub_le_norm_sub_le_mul_extChartAt`: a
  smooth triangulation is locally bi-Lipschitz in charts on every closed simplex.
-/

public section

open Set Function Filter Metric AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

namespace IsSimplexImmersion

/-- The chart representative `extChartAt I (F w) ∘ F` of the coordinate form `F` of an immersion
of a simplex has, near a point `w` of the simplex, derivatives within a neighbourhood of `w` in
the simplex which are continuous at `w`, the one at `w` being bounded below on the directions of
the simplex. -/
private theorem exists_hasFDerivWithinAt_extChartAt_comp {σ : Finset ι} {F : (σ → ℝ) → M}
    (hF : ContMDiffOn 𝓘(ℝ, σ → ℝ) I n F (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights))
    (hF' : ∀ t : Convexity.StdSimplex ℝ σ, ∃ F' : (σ → ℝ) →L[ℝ] E,
      HasMFDerivWithinAt 𝓘(ℝ, σ → ℝ) I F
        (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) t.weights F' ∧
        ∀ v : σ → ℝ, ∑ a, v a = 0 → F' v = 0 → v = 0)
    (hn : 1 ≤ n) {w : σ → ℝ} (hwS : w ∈ range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) :
    ∃ u ∈ 𝓝[range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights] w,
      ∃ A : (σ → ℝ) → (σ → ℝ) →L[ℝ] E,
        (∀ y ∈ u, HasFDerivWithinAt (extChartAt I (F w) ∘ F) (A y) u y) ∧
        ContinuousWithinAt A u w ∧
        ∃ c > 0, ∀ v : σ → ℝ, ∑ a, v a = 0 → c * ∑ a, |v a| ≤ ‖A w v‖ := by
  set S := range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights
  set φ := extChartAt I (F w)
  -- The chart representative `φ ∘ F` is `C¹` within the simplex at `w`.
  have hG : ContDiffWithinAt ℝ 1 (φ ∘ F) S w := by
    have hFw := ((hF w hwS).of_le hn)
    rw [contMDiffWithinAt_iff_target, contMDiffWithinAt_iff_contDiffWithinAt] at hFw
    exact hFw.2
  obtain ⟨u, hu, -, A, hA, hAc⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := 0) (by simp)).mp (by simpa using hG)
  rw [insert_eq_of_mem hwS] at hu
  refine ⟨u, hu, A, hA, hAc.continuousWithinAt, ?_⟩
  -- `A w` agrees on the directions with the injective derivative given by the immersion.
  have hAwS : HasFDerivWithinAt (φ ∘ F) (A w) S w :=
    (hA w (mem_of_mem_nhdsWithin hwS hu)).mono_of_mem_nhdsWithin hu
  obtain ⟨t₀, ht₀⟩ := hwS
  obtain ⟨F₀, hF₀, hinj⟩ := hF' t₀
  have hF₀w : ∀ p, ⇑t₀.weights = p → HasMFDerivWithinAt 𝓘(ℝ, σ → ℝ) I F S p F₀ := by
    rintro _ rfl
    exact hF₀
  -- The immersion's derivative at `w` is measured in the chart `φ` itself.
  have hF₀G : HasFDerivWithinAt (φ ∘ F) F₀ S w := by
    have h := (hF₀w w ht₀).2
    simp only [mfld_simps] at h
    exact h
  refine (A w).exists_pos_mul_sum_abs_le_norm fun v hv hv0 => hinj v hv ?_
  exact (hF₀G.apply_eq_of_sum_eq_zero hAwS ⟨t₀, ht₀⟩ hv).trans hv0

/-- **Immersions of simplices are locally bi-Lipschitz in charts.** Let `g` be a `Cⁿ` immersion of
the closed simplex on `σ` into a manifold, `1 ≤ n`, and `x` a point of the simplex. There are a
neighbourhood `s` of `x` in the simplex, mapped by `g` into the source of the chart
`φ = extChartAt I (g x)`, and constants `0 < c ≤ C`, with
`c |y - z| ≤ |φ (g y) - φ (g z)| ≤ C |y - z|` for all `y, z ∈ s`, distances of points of the simplex
being those of their barycentric coordinate vectors in `σ → ℝ`. -/
theorem exists_mem_nhds_mul_norm_sub_le_norm_sub_le_mul_extChartAt {σ : Finset ι}
    {g : StandardSimplex σ → M} (h : IsSimplexImmersion I n g) (hn : 1 ≤ n)
    (x : StandardSimplex σ) :
    ∃ s ∈ 𝓝 x, ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ (∀ y ∈ s, g y ∈ (extChartAt I (g x)).source) ∧
      ∀ y ∈ s, ∀ z ∈ s,
        c * ‖(fun a : σ => y.val a) - fun a : σ => z.val a‖ ≤
            ‖extChartAt I (g x) (g y) - extChartAt I (g x) (g z)‖ ∧
          ‖extChartAt I (g x) (g y) - extChartAt I (g x) (g z)‖ ≤
            C * ‖(fun a : σ => y.val a) - fun a : σ => z.val a‖ := by
  obtain ⟨F, hFg, hF, hF'⟩ := isSimplexImmersion_iff.mp h
  set S := range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights with hS
  set coords : StandardSimplex σ → σ → ℝ := fun y a => y.val a
  have hcoordsS (y : StandardSimplex σ) : coords y ∈ S := by
    rw [hS, ← Finset.range_standardSimplex_coordinates]
    exact mem_range_self y
  set w := coords x
  have hFw : F w = g x := hFg x
  obtain ⟨u, hu, A, hA, hAc, c, hc, hcA⟩ :=
    exists_hasFDerivWithinAt_extChartAt_comp hF hF' hn (hcoordsS x)
  rw [hFw] at hA
  set φ := extChartAt I (g x)
  -- A convex neighbourhood of `w` in the simplex on which `A` stays close to `A w`.
  have hsrc : ∀ᶠ z in 𝓝[S] w, F z ∈ φ.source :=
    (hF w (hcoordsS x)).continuousWithinAt.preimage_mem_nhdsWithin
      (by rw [hFw]; exact extChartAt_source_mem_nhds (g x))
  have hclose : ∀ᶠ z in 𝓝[S] w, ‖A z - A w‖ ≤ c / 2 := by
    filter_upwards [(hAc.tendsto.mono_left (nhdsWithin_le_of_mem hu)).eventually
      (closedBall_mem_nhds (A w) (half_pos hc))] with z hz
    rwa [dist_eq_norm] at hz
  have hu' : ∀ᶠ z in 𝓝[S] w, z ∈ u := hu
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp ((hu'.and hsrc).and hclose)
  set B := ball w r ∩ S
  have hB : Convex ℝ B :=
    (convex_ball w r).inter (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ)
  have hsum : ∀ y ∈ B, ∑ a, y a = 1 := fun y hy =>
    (Convexity.StdSimplex.mem_range_toFun_comp_weights_iff.mp hy.2).2
  have hlow : ∀ y ∈ B, ∀ z ∈ B, c * ‖y - z‖ ≤ ‖A w (y - z)‖ := fun y hy z hz =>
    (mul_le_mul_of_nonneg_left (by simpa using Pi.norm_pow_le_sum_norm_pow (y - z) one_ne_zero)
      hc.le).trans <| hcA _ <| by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, hsum y hy, hsum z hz, sub_self]
  -- Read back on the simplex.
  have hcoords : Continuous coords :=
    continuous_pi fun a => (continuous_apply a.val).comp continuous_induced_dom
  refine ⟨coords ⁻¹' ball w r, hcoords.continuousAt.preimage_mem_nhds (ball_mem_nhds w hr),
    c / 2, ‖A w‖ + c / 2, half_pos hc, by linarith [norm_nonneg (A w)],
    fun y hy => ?_, fun y hy z hz => ?_⟩
  · rw [← hFg y]
    exact (hrsub ⟨hy, hcoordsS y⟩).1.2
  · have hA' (y) (hy : y ∈ B) : HasFDerivWithinAt (φ ∘ F) (A y) B y :=
      (hA y (hrsub hy).1.1).mono fun z hz => (hrsub hz).1.1
    obtain ⟨hy', hz'⟩ : coords y ∈ B ∧ coords z ∈ B := ⟨⟨hy, hcoordsS y⟩, hz, hcoordsS z⟩
    -- The lower bound against the fixed map `A w`, and the upper bound `‖A u‖ ≤ ‖A w‖ + c / 2`.
    have hlow' := hB.mul_norm_sub_le_norm_image_sub_of_norm_hasFDerivWithin_sub_le hA'
      (fun u hu => (hrsub hu).2) hz' hy' (hlow _ hy' _ hz')
    have hup := hB.norm_image_sub_le_of_norm_hasFDerivWithin_le hA' (fun u hu =>
      (norm_le_norm_add_norm_sub' (A u) (A w)).trans (add_le_add_right (hrsub hu).2 _)) hz' hy'
    simpa only [sub_half, comp_apply, coords, hFg] using And.intro hlow' hup

end IsSimplexImmersion

/-- **Smooth triangulations are locally bi-Lipschitz in charts.** Let `κ` be a `Cⁿ` triangulation
of a manifold, `1 ≤ n`, `σ` a face, and `x` a point of the closed simplex of `σ`. There are a
neighbourhood `s` of `x` in the simplex, mapped by `κ` into the source of the chart
`φ = extChartAt I (κ x)`, and constants `0 < c ≤ C`, with
`c |y - z| ≤ |φ (κ y) - φ (κ z)| ≤ C |y - z|` for all `y, z ∈ s`, distances of points of the simplex
being those of their barycentric coordinate vectors in `σ → ℝ`. -/
theorem IsSmoothTriangulation.exists_mem_nhds_mul_norm_sub_le_norm_sub_le_mul_extChartAt
    {K : AbstractSimplicialComplex ι} {κ : Realization K ≃ₜ M}
    (h : IsSmoothTriangulation I n κ) (hn : 1 ≤ n) (σ : Face K) (x : StandardSimplex σ.val) :
    ∃ s ∈ 𝓝 x, ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ y ∈ s, κ (faceInclusion K σ y) ∈ (extChartAt I (κ (faceInclusion K σ x))).source) ∧
      ∀ y ∈ s, ∀ z ∈ s,
        c * ‖(fun a : σ.val => y.val a) - fun a : σ.val => z.val a‖ ≤
            ‖extChartAt I (κ (faceInclusion K σ x)) (κ (faceInclusion K σ y)) -
              extChartAt I (κ (faceInclusion K σ x)) (κ (faceInclusion K σ z))‖ ∧
          ‖extChartAt I (κ (faceInclusion K σ x)) (κ (faceInclusion K σ y)) -
              extChartAt I (κ (faceInclusion K σ x)) (κ (faceInclusion K σ z))‖ ≤
            C * ‖(fun a : σ.val => y.val a) - fun a : σ.val => z.val a‖ :=
  (isSmoothTriangulation_iff.mp h σ).exists_mem_nhds_mul_norm_sub_le_norm_sub_le_mul_extChartAt hn
    x

end TauCeti
