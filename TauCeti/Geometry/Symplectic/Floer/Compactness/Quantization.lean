/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Hofer
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import TauCeti.Geometry.Symplectic.Manifold.Energy
import TauCeti.Topology.Order.Interval

/-!
# Energy quantization for pseudoholomorphic planes in a manifold

Let `J` be a smooth almost complex structure on a boundaryless Hausdorff manifold `M`, tamed by a
two-form `ω`, as on a closed symplectic manifold. A pseudoholomorphic plane is a map
`u : ℝ × ℝ → M` solving `∂ₜu = J(u) ∂ₛu`, and its area is `∫ ω(∂ₛu, ∂ₜu)`. This file proves that
on a compact subset `K` of `M` there is an energy `κ > 0` below which every such `C³` plane with
values in `K` is constant
(`TauCeti.SmoothTwoForm.Tames.exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne`).

The same threshold works for a compact family of structures
(`TauCeti.SmoothTwoForm.exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne_parametric`): for smooth
almost complex structures `J p`, depending on a parameter `p` in a normed space with coordinate
expressions in the charts of `M` jointly `C²` in `p` and the point, and tamed by `ω` for `p` in a
compact set `C`, one `κ > 0` bounds from below the area of every nonconstant `J p`-holomorphic plane
with values in `K`, for every `p ∈ C`. The single structure is the case of a constant family.

This is the lower bound for the energy of bubbles in Gromov–Floer compactness. Where the
derivatives of a sequence of Floer solutions blow up, a limit of the rescaled solutions is
pseudoholomorphic for the almost complex structure frozen at the bubbling point
(`TauCeti.SmoothTwoForm.isComplexLinearMap_of_tendsto_rescale`), and its area is at most the energy
lost there (`TauCeti.SmoothTwoForm.lintegral_eval₂_le_liminf_of_tendsto_rescale`); a
pseudoholomorphic sphere restricts to a plane with the same area. For an inhomogeneous equation
with a domain-dependent structure `J(z, ·)` the bubbling points vary, and so do the frozen
structures; the structures frozen at the points of a compact window of the domain form a compact
family, so the uniform threshold bounds the energy of all bubbles from below at once. The
vector-space versions, for planes with values in a compact subset of a single chart, are
`TauCeti.exists_pos_forall_le_integral_norm_fderiv_one_sq_of_ne` and its parametric form
`TauCeti.exists_pos_forall_le_integral_norm_fderiv_one_sq_of_ne_parametric`.

The threshold is analytic, not a period of `ω`: the areas of spheres may be dense in `ℝ`. The
proof covers `K` by finitely many charts, in each of which the following holds.

* **Comparison with the chart norm.** In the tangent coordinates `ξ` of the chart, the energy form
  `ω(ζ, J p ζ)` of the tangent vectors `ζ` is between `c ‖ξ‖²` and `C ‖ξ‖²`, uniformly for `p ∈ C`
  (`IsCompact.exists_pos_forall_mul_norm_sq_le`, applied to the coordinate expressions of these
  bilinear forms over a compact set of parameters and chart coordinates).
* **Localization.** If the area density of `u` is at most `m²` on a ball of radius `r` with
  `m r` small, the ball is mapped into the chart, since the chart coordinate of `u` moves at speed
  at most a constant times `m` along each segment from the centre.
* **The mean-value inequality** for the coordinate expression, read in the complex coordinate of
  the domain: on such a ball, either the area is at least a fixed threshold, or `π r² m²` is
  bounded by a constant times the area. The constants are uniform over the family, by
  `exists_pos_exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_mul_setIntegral_ball_parametric`

A nonconstant plane has a point of positive density, and Hofer's lemma
(`TauCeti.hofer_of_continuousOn_closedBall`) moves it to a point `w` of density `m² > 0` with
density at most `(2m)²` on a ball about `w` whose radius times `m` is as large as required. On
the ball of radius `L / m` about `w`, for the constant `L` of the chart containing `u w`, the
mean-value inequality bounds the area of `u` from below by a constant depending only on the chart.

The corresponding statement for closed surfaces of higher genus is not treated here.

## Main results

* `TauCeti.SmoothTwoForm.exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne_parametric`: for a
  compact family of tame structures, a nonconstant pseudoholomorphic plane for any member of the
  family with values in a compact set has area at least `κ`.
* `TauCeti.SmoothTwoForm.Tames.exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne`: a
  nonconstant pseudoholomorphic plane with values in a compact set has area at least `κ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.1 (the lower bound for the energy of nonconstant
  spheres), Section 4.3 (the mean-value inequality) and Section 4.6 (Hofer's lemma).
-/

public section

noncomputable section

open Bundle Filter Function MeasureTheory Metric Set Topology
open scoped Manifold Real

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {u : ℝ × ℝ → M} {z : ℝ × ℝ} {α : M}

omit [FiniteDimensional ℝ E] in
/-- At a point `z` with `u z` in the source of the chart at `α`, the area density
`ω(∂ₛu, ∂ₜu)` of a solution of `∂ₜu = J(u) ∂ₛu` is the energy form `ω(ζ, J ζ)` of `ζ = ∂ₛu`, whose
tangent coordinate is `∂ₛv` for the coordinate expression `v = extChartAt I α ∘ u`. -/
private theorem eval₂_mfderiv_eq (hu : ContinuousAt u z) (hz : u z ∈ (extChartAt I α).source)
    (hCR : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) :
    SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) =
      SmoothBundleForm.eval₂ ω (u z)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (u z)
          (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal))
        (J (u z) ((trivializationAt E (TangentSpace I) α).symmL ℝ (u z)
          (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal))) := by
  rw [hCR, hu.symmL_fderiv_extChartAt_comp_apply hz]

omit [FiniteDimensional ℝ E] in
/-- **The area density bounds the derivative in a chart.** Let `u` solve `∂ₜu = J(u) ∂ₛu` at `z`,
with `u z` in the source of the chart at `α`, let `‖J‖ ≤ a` at `u z` in the chart, and let the
energy form at `u z` satisfy `c ‖ξ‖² ≤ ω(ζ, J ζ)` for the tangent vectors `ζ` with tangent
coordinate `ξ`. Then the coordinate expression `v = extChartAt I α ∘ u` has
`‖dv(z)‖ ≤ (1 + a) √(ρ / c)` for the area density `ρ = ω(∂ₛu, ∂ₜu)` at `z`. -/
private theorem norm_fderiv_extChartAt_comp_le (hu : ContinuousAt u z)
    (hz : u z ∈ (extChartAt I α).source)
    (hCR : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    {c a : ℝ} (hc : 0 < c) (ha : ‖J.inChart α (extChartAt I α (u z))‖ ≤ a)
    (hcoer : ∀ ξ : E, c * ‖ξ‖ ^ 2 ≤ SmoothBundleForm.eval₂ ω (u z)
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (u z) ξ)
      (J (u z) ((trivializationAt E (TangentSpace I) α).symmL ℝ (u z) ξ))) :
    ‖fderiv ℝ (extChartAt I α ∘ u) z‖ ≤
      (1 + a) * √(SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) / c) := by
  set ξ := fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal
  have hξ : ‖ξ‖ ≤ √(SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) / c) := by
    rw [eval₂_mfderiv_eq hu hz hCR]
    exact Real.le_sqrt_of_sq_le ((le_div_iff₀ hc).2 (by linarith [hcoer ξ]))
  -- `∂ₜv = J ∂ₛv` in the chart, so `‖∂ₜv‖ ≤ a ‖∂ₛv‖`.
  have hIm : fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineImag =
      J.inChart α (extChartAt I α (u z)) ξ :=
    J.fderiv_extChartAt_comp_apply_eq_inChart α hu hz hCR
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  calc ‖fderiv ℝ (extChartAt I α ∘ u) z‖
      ≤ ‖fderiv ℝ (extChartAt I α ∘ u) z (1, 0)‖ + ‖fderiv ℝ (extChartAt I α ∘ u) z (0, 1)‖ :=
        (fderiv ℝ (extChartAt I α ∘ u) z).opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one
    _ ≤ ‖ξ‖ + a * ‖ξ‖ := by
        rw [← stdComplexLineReal_eq, ← stdComplexLineImag_eq, hIm]
        exact add_le_add le_rfl (((J.inChart α _).le_opNorm ξ).trans
          (mul_le_mul_of_nonneg_right ha (norm_nonneg _)))
    _ = (1 + a) * ‖ξ‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hξ (by linarith)

omit [FiniteDimensional ℝ E] in
/-- **The chart coordinate moves slowly along a segment.** Let `u` be a `C¹` solution of
`∂ₜu = J(u) ∂ₛu`, let `‖J‖ ≤ a` and `c ‖ξ‖² ≤ ω(ζ, J ζ)` hold in the chart at `α` over the closed
ball of radius `3η` about its chart point, and let the area density of `u` be at most `m²` on the
closed ball of radius `r` about `w₀`, which contains `w`. If the points `w₀ + σ (w - w₀)`,
`0 ≤ σ ≤ τ`, have chart coordinates within `3η` of the chart point, then the chart coordinate of
`u` at `w₀ + τ (w - w₀)` is within `(1 + a) (m / √c) r` of that at `w₀`. -/
private theorem norm_extChartAt_comp_sub_le (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    {η c a m r : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    (hJa : ∀ y ∈ closedBall (extChartAt I α α) (3 * η), ‖J.inChart α y‖ ≤ a)
    (hcoer : ∀ x ∈ (extChartAt I α).source,
      extChartAt I α x ∈ closedBall (extChartAt I α α) (3 * η) → ∀ ξ : E,
        c * ‖ξ‖ ^ 2 ≤ SmoothBundleForm.eval₂ ω x
          ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)
          (J x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)))
    {w₀ w : ℝ × ℝ} (hw : w ∈ closedBall w₀ r)
    (hρ : ∀ w ∈ closedBall w₀ r, SmoothBundleForm.eval₂ ω (u w)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineImag) ≤ m ^ 2)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hG : ∀ σ ∈ Icc 0 τ, u (w₀ + σ • (w - w₀)) ∈
      (extChartAt I α).source ∩ extChartAt I α ⁻¹' ball (extChartAt I α α) (3 * η)) :
    ‖extChartAt I α (u (w₀ + τ • (w - w₀))) - extChartAt I α (u w₀)‖ ≤
      (1 + a) * (m / √c) * r := by
  set e := extChartAt I α
  have ha : 0 ≤ a := (norm_nonneg _).trans (hJa _ (ball_subset_closedBall (hG 0 ⟨le_rfl, hτ.1⟩).2))
  have hC0 : 0 ≤ (1 + a) * (m / √c) * r := mul_nonneg
    (mul_nonneg (by linarith) (div_nonneg hm (Real.sqrt_nonneg c))) (dist_nonneg.trans hw)
  -- The chart coordinate along the segment has derivative `d(e ∘ u)(w - w₀)`.
  have hderiv : ∀ σ ∈ Icc 0 τ, HasDerivWithinAt (fun t ↦ e (u (w₀ + t • (w - w₀))))
      (fderiv ℝ (e ∘ u) (w₀ + σ • (w - w₀)) (w - w₀)) (Icc 0 τ) σ := fun σ hσ ↦ by
    have hs : u (w₀ + σ • (w - w₀)) ∈ (chartAt H α).source := by
      rw [← extChartAt_source I]; exact (hG σ hσ).1
    have hd : DifferentiableAt ℝ (e ∘ u) (w₀ + σ • (w - w₀)) :=
      (contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_extChartAt' (n := 1) hs).comp _
        (hu _))).differentiableAt one_ne_zero
    have hγd : HasDerivAt (fun t : ℝ ↦ w₀ + t • (w - w₀)) (w - w₀) σ := by
      simpa using ((hasDerivAt_id' σ).smul_const (w - w₀)).const_add w₀
    exact (hd.hasFDerivAt.comp_hasDerivAt σ hγd).hasDerivWithinAt
  -- Its norm is at most `(1 + a) (m / √c) r`, by the bound on the derivative in the chart.
  have hnorm : ∀ σ ∈ Ico 0 τ, ‖fderiv ℝ (e ∘ u) (w₀ + σ • (w - w₀)) (w - w₀)‖ ≤
      (1 + a) * (m / √c) * r := fun σ hσ ↦ by
    have hGσ := hG σ (Ico_subset_Icc_self hσ)
    have hy := ball_subset_closedBall hGσ.2
    have hd := norm_fderiv_extChartAt_comp_le (ω := ω) hu.continuous.continuousAt hGσ.1
      (hCR _) hc (hJa _ hy) (hcoer _ hGσ.1 hy)
    have hρσ := hρ _ ((convex_closedBall w₀ r).add_smul_sub_mem
      (mem_closedBall_self (dist_nonneg.trans hw)) hw ⟨hσ.1, hσ.2.le.trans hτ.2⟩)
    have hsq : √(SmoothBundleForm.eval₂ ω (u (w₀ + σ • (w - w₀)))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (w₀ + σ • (w - w₀)) stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (w₀ + σ • (w - w₀)) stdComplexLineImag) / c) ≤ m / √c := by
      rw [Real.sqrt_div' _ hc.le]
      exact div_le_div_of_nonneg_right ((Real.sqrt_le_sqrt hρσ).trans_eq (Real.sqrt_sq hm))
        (Real.sqrt_nonneg c)
    refine ((fderiv ℝ (e ∘ u) _).le_opNorm _).trans (mul_le_mul
      (hd.trans (mul_le_mul_of_nonneg_left hsq (by linarith))) ?_ (norm_nonneg _)
      (mul_nonneg (by linarith) (div_nonneg hm (Real.sqrt_nonneg c))))
    rw [← dist_eq_norm]
    exact hw
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hnorm τ (right_mem_Icc.2 hτ.1)
  simp only [sub_zero, zero_smul, add_zero] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hτ.2 hC0).trans_eq (mul_one _))

/-- **Localization in a chart.** Let `u` be a `C¹` solution of `∂ₜu = J(u) ∂ₛu` and let the closed
ball of radius `3η` about the chart point `y₀` of `α` lie in the chart target, with `‖J‖ ≤ a` and
`c ‖ξ‖² ≤ ω(ζ, J ζ)` over it in the chart. If `u w₀` has chart coordinate within `η` of `y₀` and
the area density of `u` is at most `m²` on the closed ball of radius `r` about `w₀`, with
`(1 + a) (m / √c) r ≤ η`, then this ball is mapped into the chart source, with chart coordinates
within `2η` of `y₀`. -/
private theorem mapsTo_closedBall_of_le [T2Space M] (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    {η c a m r : ℝ} (hη : 0 < η) (hc : 0 < c) (hm : 0 ≤ m)
    (hK : closedBall (extChartAt I α α) (3 * η) ⊆ (extChartAt I α).target)
    (hJa : ∀ y ∈ closedBall (extChartAt I α α) (3 * η), ‖J.inChart α y‖ ≤ a)
    (hcoer : ∀ x ∈ (extChartAt I α).source,
      extChartAt I α x ∈ closedBall (extChartAt I α α) (3 * η) → ∀ ξ : E,
        c * ‖ξ‖ ^ 2 ≤ SmoothBundleForm.eval₂ ω x
          ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)
          (J x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)))
    {w₀ : ℝ × ℝ} (hw₀s : u w₀ ∈ (extChartAt I α).source)
    (hw₀ : extChartAt I α (u w₀) ∈ ball (extChartAt I α α) η)
    (hρ : ∀ w ∈ closedBall w₀ r, SmoothBundleForm.eval₂ ω (u w)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineImag) ≤ m ^ 2)
    (hrm : (1 + a) * (m / √c) * r ≤ η) :
    MapsTo u (closedBall w₀ r)
      ((extChartAt I α).source ∩ extChartAt I α ⁻¹' closedBall (extChartAt I α α) (2 * η)) := by
  -- Along a segment from `w₀`, the first point where the chart coordinate leaves the ball of
  -- radius `3η` would be a limit of points with chart coordinates within `2η`, by
  -- `norm_extChartAt_comp_sub_le`, so there is no such point.
  set e := extChartAt I α
  intro w hw
  set G := e.source ∩ e ⁻¹' ball (e α) (3 * η)
  set φ : ℝ → M := fun t ↦ u (w₀ + t • (w - w₀))
  have hφc : Continuous φ := hu.continuous.comp (by fun_prop)
  -- While the segment stays in `G`, its chart coordinates stay within `2η` of `e α`.
  have h2 : ∀ τ ∈ Icc (0 : ℝ) 1, (∀ σ ∈ Icc 0 τ, φ σ ∈ G) →
      φ τ ∈ e.source ∧ e (φ τ) ∈ closedBall (e α) (2 * η) := fun τ hτ hG ↦ by
    refine ⟨(hG τ (right_mem_Icc.2 hτ.1)).1, mem_closedBall.2 ?_⟩
    have hb := norm_extChartAt_comp_sub_le hu hCR hc hm hJa hcoer hw hρ hτ hG
    calc dist (e (φ τ)) (e α) ≤ dist (e (φ τ)) (e (u w₀)) + dist (e (u w₀)) (e α) :=
          dist_triangle _ _ _
      _ ≤ η + η := add_le_add ((dist_eq_norm _ _).trans_le (hb.trans hrm)) (mem_ball.1 hw₀).le
      _ = 2 * η := by ring
  -- Points with chart coordinates within `2η` form a closed subset `Gc` of `G`.
  have h23 : closedBall (e α) (2 * η) ⊆ closedBall (e α) (3 * η) := closedBall_subset_closedBall
    (by linarith)
  have hGc : IsClosed (e.symm '' closedBall (e α) (2 * η)) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm α).mono (h23.trans hK))).isClosed
  have hGcG : e.symm '' closedBall (e α) (2 * η) ⊆ G := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨e.map_target (hK (h23 hy)), ?_⟩
    rw [mem_preimage, e.right_inv (hK (h23 hy))]
    exact mem_ball.2 ((mem_closedBall.1 hy).trans_lt (by linarith))
  -- The segment never leaves `G`: its first exit point would be a limit of points of `Gc ⊆ G`.
  have hstay : ∀ σ ∈ Icc (0 : ℝ) 1, φ σ ∈ G := by
    by_contra! ⟨t, ht, htG⟩
    have hw₀G : φ 0 ∈ G := by
      simp only [φ, zero_smul, add_zero]
      exact ⟨hw₀s, ball_subset_ball (by linarith) hw₀⟩
    have hG : IsOpen G := isOpen_extChartAt_preimage' α isOpen_ball
    obtain ⟨T, hT, hT0, hTG, -, hbefore⟩ :=
      hG.exists_first_exit hφc.continuousOn hw₀G ⟨t, ht, htG⟩
    refine hTG (hGcG (hGc.mem_of_tendsto (hφc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio T))) ?_))
    filter_upwards [Ioo_mem_nhdsLT hT0] with σ hσ
    have hσ' := h2 σ ⟨hσ.1.le, hσ.2.le.trans hT.2⟩ fun σ' hσ' ↦
      hbefore σ' ⟨hσ'.1, hσ'.2.trans_lt hσ.2⟩
    exact ⟨e (φ σ), hσ'.2, e.left_inv hσ'.1⟩
  simpa [φ] using h2 1 (right_mem_Icc.2 zero_le_one) hstay

section Family

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
/-- **The energy form in a chart, uniformly over a family.** Let the structures `J p` be tamed by
`ω` for `p ∈ C`, with coordinate expressions in the chart at `α` continuous on `C × Kc`, for a
compact set `C` of parameters and a compact set `Kc` in the chart target. There are `c, C' > 0` such
that `c ‖ξ‖² ≤ ω(ζ, J p ζ) ≤ C' ‖ξ‖²` for every `p ∈ C` and the tangent vectors `ζ` with tangent
coordinate `ξ` at the points with chart coordinate in `Kc`. For a family indexed by the points of
the domain `ℝ × ℝ` this is
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_sq_le_eval₂_le_mul_norm_sq`;
here the parameters range over a general space `P`. -/
private theorem exists_pos_forall_mul_norm_sq_le_and_le_of_chart
    {J : P → SmoothAlmostComplexStructure I M} {C : Set P} (hC : IsCompact C)
    (hJt : ∀ p ∈ C, ω.Tames (J p)) (α : M) {Kc : Set E} (hKc : IsCompact Kc)
    (hK : Kc ⊆ (extChartAt I α).target)
    (hJ : ContinuousOn (fun q : P × E ↦ (J q.1).inChart α q.2) (C ×ˢ Kc)) :
    ∃ c > 0, ∃ C' > 0, ∀ p ∈ C, ∀ x ∈ (extChartAt I α).source, extChartAt I α x ∈ Kc →
      ∀ ξ : E,
        c * ‖ξ‖ ^ 2 ≤ SmoothBundleForm.eval₂ ω x
          ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)
          (J p x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)) ∧
        SmoothBundleForm.eval₂ ω x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)
          (J p x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)) ≤ C' * ‖ξ‖ ^ 2 := by
  set e := extChartAt I α
  set T := trivializationAt E (TangentSpace I) α with hT
  -- In the chart, `ω(·, J p ·)` is the bilinear form `b (p, y)`, continuous on `C × Kc`.
  set b : P × E → E →L[ℝ] E →L[ℝ] ℝ := fun q ↦
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip ((J q.1).inChart α q.2)).comp
      (ContinuousAlternatingMap.flatL ℝ E ℝ (RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α q.2))
    with hb_def
  have hb : ∀ q ∈ C ×ˢ Kc, ∀ a, b q a a = SmoothBundleForm.eval₂ ω (e.symm q.2)
      (T.symmL ℝ (e.symm q.2) a) (J q.1 (e.symm q.2) (T.symmL ℝ (e.symm q.2) a)) := by
    rintro ⟨p, y⟩ hq a
    have h := ω.inChartAt_apply_almostComplexInChartAt
      (J := fun _ ↦ (J p).almostComplexStructureAt) (hK hq.2) 0 a
    rw [Floer.almostComplexInChartAt_const] at h
    simpa only [hb_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply, ContinuousAlternatingMap.flatL_apply_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using h
  have hbc : ContinuousOn b (C ×ˢ Kc) :=
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip.continuous.comp_continuousOn hJ).clm_comp
      ((ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.comp_continuousOn
        ((ω.isSmoothForm.continuousOn_inChartAt α).comp continuousOn_snd
          fun q hq ↦ hK hq.2))
  obtain ⟨c, hc, hcb⟩ := (hC.prod hKc).exists_pos_forall_mul_norm_sq_le hbc fun q hq a ha ↦ by
    rw [hb q hq]
    have hbase : e.symm q.2 ∈ T.baseSet := by
      simpa only [hT, TangentBundle.trivializationAt_baseSet, ← extChartAt_source I] using
        e.map_target (hK hq.2)
    refine tames_iff.1 (hJt q.1 hq.1) _ _ fun h0 ↦ ha ?_
    rw [← Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ hbase a, h0, map_zero]
  obtain ⟨C', hC'⟩ := (hC.prod hKc).exists_forall_le_mul_norm_sq hbc
  refine ⟨c, hc, max C' 1, by positivity, fun p hp x hx hy ξ ↦ ?_⟩
  have h := hb (p, e x) ⟨hp, hy⟩ ξ
  rw [e.left_inv hx] at h
  exact ⟨h ▸ hcb _ ⟨hp, hy⟩ ξ, (h ▸ hC' _ ⟨hp, hy⟩ ξ).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩

omit [FiniteDimensional ℝ E] in
/-- The comparison of `exists_pos_forall_mul_norm_sq_le_and_le_of_chart` for `ζ = ∂ₛu` at
`equivRealProdCLM y`: its tangent coordinate is `∂ₛ` of the coordinate expression of `u` in the
chart, read in the complex coordinate of the domain, and its energy form is the area density. -/
private theorem mul_norm_fderiv_sq_le_and_le {c C : ℝ} {Kc : Set E}
    (hcmp : ∀ x ∈ (extChartAt I α).source, extChartAt I α x ∈ Kc → ∀ ξ : E,
      c * ‖ξ‖ ^ 2 ≤ SmoothBundleForm.eval₂ ω x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)
        (J x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)) ∧
      SmoothBundleForm.eval₂ ω x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)
        (J x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)) ≤ C * ‖ξ‖ ^ 2)
    (hu : Continuous u)
    (hCR : ∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) {y : ℂ}
    (hy : u (Complex.equivRealProdCLM y) ∈ (extChartAt I α).source ∧
      extChartAt I α (u (Complex.equivRealProdCLM y)) ∈ Kc) :
    c * ‖fderiv ℝ ((extChartAt I α ∘ u) ∘ Complex.equivRealProdCLM) y 1‖ ^ 2 ≤
        SmoothBundleForm.eval₂ ω (u (Complex.equivRealProdCLM y))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM y) stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM y) stdComplexLineImag) ∧
      SmoothBundleForm.eval₂ ω (u (Complex.equivRealProdCLM y))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM y) stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM y) stdComplexLineImag) ≤
        C * ‖fderiv ℝ ((extChartAt I α ∘ u) ∘ Complex.equivRealProdCLM) y 1‖ ^ 2 := by
  have h := hcmp _ hy.1 hy.2 (fderiv ℝ ((extChartAt I α ∘ u) ∘ Complex.equivRealProdCLM) y 1)
  rw [fderiv_comp_equivRealProdCLM_one] at h ⊢
  rwa [← eval₂_mfderiv_eq hu.continuousAt hy.1 (hCR _)] at h

/-- **The mean-value inequality in a chart, uniformly over a family.** Let the coordinate
expressions of the structures `J p` in the chart at `α` be jointly `C²` on `U × (chart target)` for
an open set `U` of parameters, let `C ⊆ U` be compact, and let `Kc` be a compact subset of the chart
target over which `c ‖ξ‖² ≤ ω(ζ, J p ζ) ≤ C' ‖ξ‖²` in the chart for `p ∈ C`. There are constants
`δ, A > 0` such that for every `p ∈ C`, every `C³` solution `u` of `∂ₜu = J p (u) ∂ₛu` mapping the
closed ball of radius `r` about `w₀` into the chart, with chart coordinates in `Kc`, satisfies the
following.
Either the area of `u` over the disc of radius `r` about `w₀` is at least `δ`, or `π r² ρ(w₀)` is at
most `A` times this area, where `ρ = ω(∂ₛu, ∂ₜu)` is the area density. The disc is taken in the
complex coordinate `Complex.equivRealProdCLM` of the domain. -/
private theorem exists_pos_forall_le_or_le_of_chart [I.Boundaryless]
    {J : P → SmoothAlmostComplexStructure I M} {U C : Set P} (hU : IsOpen U) (hCU : C ⊆ U)
    (hC : IsCompact C) (α : M)
    (hJ : ContDiffOn ℝ 2 (fun q : P × E ↦ (J q.1).inChart α q.2) (U ×ˢ (extChartAt I α).target))
    {Kc : Set E} (hKc : IsCompact Kc) (hK : Kc ⊆ (extChartAt I α).target) {c C' : ℝ} (hc : 0 < c)
    (hC' : 0 < C')
    (hcmp : ∀ p ∈ C, ∀ x ∈ (extChartAt I α).source, extChartAt I α x ∈ Kc → ∀ ξ : E,
      c * ‖ξ‖ ^ 2 ≤ SmoothBundleForm.eval₂ ω x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)
        (J p x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)) ∧
      SmoothBundleForm.eval₂ ω x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)
        (J p x ((trivializationAt E (TangentSpace I) α).symmL ℝ x ξ)) ≤ C' * ‖ξ‖ ^ 2) :
    ∃ δ > 0, ∃ A > 0, ∀ ⦃p : P⦄, p ∈ C → ∀ ⦃u : ℝ × ℝ → M⦄ ⦃w₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄,
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 u →
      (∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
        J p (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) → 0 ≤ r →
      (∀ w ∈ closedBall w₀ r, u w ∈ (extChartAt I α).source ∧ extChartAt I α (u w) ∈ Kc) →
      δ ≤ ∫ y in ball (Complex.equivRealProdCLM.symm w₀) r,
          SmoothBundleForm.eval₂ ω (u (Complex.equivRealProdCLM y))
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM y) stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM y) stdComplexLineImag) ∨
        π * r ^ 2 * SmoothBundleForm.eval₂ ω (u w₀)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w₀ stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w₀ stdComplexLineImag) ≤
          A * ∫ y in ball (Complex.equivRealProdCLM.symm w₀) r,
            SmoothBundleForm.eval₂ ω (u (Complex.equivRealProdCLM y))
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM y) stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (Complex.equivRealProdCLM y) stdComplexLineImag) := by
  obtain ⟨δ, hδ, A, hA, hmean⟩ :=
    exists_pos_exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_mul_setIntegral_ball_parametric
      (J := fun p y ↦ (J p).inChart α y) (hU.prod (isOpen_extChartAt_target α)) hJ hC hKc
      (prod_mono hCU hK) fun p _ y hy v ↦ (J p).inChart_inChart α (hK hy) v
  refine ⟨c * δ, by positivity, C' * A / c, by positivity, fun p hp u w₀ r hu hCR hr hmaps ↦ ?_⟩
  -- The coordinate expression `f` of `u` in the complex coordinate `φ` of the domain.
  set φ := Complex.equivRealProdCLM
  set f : ℂ → E := (extChartAt I α ∘ u) ∘ φ
  have hsrc (y : ℂ) (hy : y ∈ closedBall (φ.symm w₀) r) := hmaps _ <|
    mem_closedBall.2 ((Complex.dist_equivRealProdCLM_le y w₀).trans (mem_closedBall.1 hy))
  have hcd (y : ℂ) (hy : y ∈ closedBall (φ.symm w₀) r) : ContDiffAt ℝ 3 f y :=
    (contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_extChartAt'
      (show u (φ y) ∈ (chartAt H α).source by rw [← extChartAt_source I]; exact (hsrc y hy).1)).comp
        _ (hu _))).comp y φ.contDiff.contDiffAt
  have hlow (y : ℂ) (hy : y ∈ closedBall (φ.symm w₀) r) :=
    mul_norm_fderiv_sq_le_and_le (hcmp p hp) hu.continuous hCR (hsrc y hy)
  have hfc : ContinuousOn (fun y ↦ fderiv ℝ f y 1) (closedBall (φ.symm w₀) r) := fun y hy ↦
    (((hcd y hy).fderiv_right (m := 2) (by norm_num)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  -- The area over the disc bounds `c` times the coordinate energy.
  have hIf : c * ∫ y in ball (φ.symm w₀) r, ‖fderiv ℝ f y 1‖ ^ 2 ≤
      ∫ y in ball (φ.symm w₀) r, SmoothBundleForm.eval₂ ω (u (φ y))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ y) stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ y) stdComplexLineImag) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on
      ((((hfc.norm.pow 2).integrableOn_compact (isCompact_closedBall _ r)).mono_set
        ball_subset_closedBall).const_mul c)
      ((((continuous_eval₂_mfderiv ω (hu.of_le (by norm_num))).comp
        φ.continuous).continuousOn.integrableOn_compact (isCompact_closedBall _ r)).mono_set
        ball_subset_closedBall) measurableSet_ball
      fun y hy ↦ (hlow y (ball_subset_closedBall hy)).1
  by_cases hsmall : ∫ y in ball (φ.symm w₀) r, ‖fderiv ℝ f y 1‖ ^ 2 < δ
  · -- The mean-value inequality for `f` at the centre.
    right
    have hmv := hmean hp (u := f) (z₀ := φ.symm w₀) hr
      (fun y hy ↦ (hcd y (ball_subset_closedBall hy)).contDiffWithinAt) hfc
      (fun y hy ↦ by
        rw [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I]
        exact (J p).fderiv_extChartAt_comp_apply_eq_inChart α hu.continuous.continuousAt
          (hsrc y (ball_subset_closedBall hy)).1 (hCR _))
      (fun y hy ↦ (hsrc y (ball_subset_closedBall hy)).2) hsmall
    have hup := φ.apply_symm_apply w₀ ▸ (hlow _ (mem_closedBall_self hr)).2
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    -- `π r² ρ(w₀) ≤ C' π r² ‖∂ₛf‖² ≤ C' A ∫ ‖∂ₛf‖² ≤ (C' A / c) ∫ ρ`.
    have h1 := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ π * r ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hmv hC'.le
    nlinarith [mul_le_mul_of_nonneg_left hIf (by positivity : (0 : ℝ) ≤ C' * A)]
  · left
    nlinarith [mul_le_mul_of_nonneg_left (not_lt.1 hsmall) hc.le]

/-- **The energy threshold in one chart, uniformly over a family.** Let the structures `J p` be
tamed by `ω` for `p` in a compact subset `C` of an open set `U` of parameters, with coordinate
expressions in the chart at `α` jointly `C²` on `U × (chart target)`, and let the closed ball of
radius `3η` about the chart point of `α` lie in the chart target. There are a radius constant
`L > 0` and an energy `κ > 0` with the following property. Let `p ∈ C`, let `u` be a `C³` solution
of `∂ₜu = J p (u) ∂ₛu` and `m > 0`, with `u w₀` in the chart source and chart coordinate within
`η` of the chart point, with area density at least `m²` at `w₀` and at most `(2m)²` on the closed
ball of radius `L / m` about `w₀`. Then the area of `u` is at least `κ`. -/
private theorem exists_pos_forall_ofReal_le_lintegral_of_chart [I.Boundaryless] [T2Space M]
    {J : P → SmoothAlmostComplexStructure I M} {U C : Set P} (hU : IsOpen U) (hCU : C ⊆ U)
    (hC : IsCompact C) (hJt : ∀ p ∈ C, ω.Tames (J p)) (α : M)
    (hJ : ContDiffOn ℝ 2 (fun q : P × E ↦ (J q.1).inChart α q.2) (U ×ˢ (extChartAt I α).target))
    {η : ℝ} (hη : 0 < η) (hK : closedBall (extChartAt I α α) (3 * η) ⊆ (extChartAt I α).target) :
    ∃ L > 0, ∃ κ > 0, ∀ ⦃p : P⦄, p ∈ C → ∀ ⦃u : ℝ × ℝ → M⦄ ⦃w₀ : ℝ × ℝ⦄ ⦃m : ℝ⦄,
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 u →
      (∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
        J p (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) → 0 < m →
      u w₀ ∈ (extChartAt I α).source → extChartAt I α (u w₀) ∈ ball (extChartAt I α α) η →
      m ^ 2 ≤ SmoothBundleForm.eval₂ ω (u w₀) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w₀ stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w₀ stdComplexLineImag) →
      (∀ w ∈ closedBall w₀ (L / m), SmoothBundleForm.eval₂ ω (u w)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineImag) ≤ (2 * m) ^ 2) →
      ENNReal.ofReal κ ≤ ∫⁻ w, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (u w)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineImag)) := by
  set e := extChartAt I α
  set Kc := closedBall (e α) (3 * η)
  have hJc : ContinuousOn (fun q : P × E ↦ (J q.1).inChart α q.2) (C ×ˢ Kc) :=
    hJ.continuousOn.mono (prod_mono hCU hK)
  obtain ⟨c, hc, C', hC', hcmp⟩ :=
    exists_pos_forall_mul_norm_sq_le_and_le_of_chart hC hJt α (isCompact_closedBall _ _) hK hJc
  obtain ⟨δ, hδ, A, hA, hM⟩ :=
    exists_pos_forall_le_or_le_of_chart hU hCU hC α hJ (isCompact_closedBall _ _) hK hc hC' hcmp
  obtain ⟨a, ha⟩ :=
    (hC.prod (isCompact_closedBall (e α) (3 * η))).exists_bound_of_continuousOn hJc
  set L := √c * η / (2 * (1 + max a 0))
  have hL : 0 < L := by positivity
  refine ⟨L, hL, min δ (π * L ^ 2 / A), by positivity,
    fun p hp u w₀ m hu hCR hm hw₀s hw₀ hρ₀ hρ ↦ ?_⟩
  set φ := Complex.equivRealProdCLM
  have hr : 0 < L / m := by positivity
  -- The closed ball of radius `L / m` about `w₀` is mapped into the chart, by
  -- `mapsTo_closedBall_of_le`, where `exists_pos_forall_le_or_le_of_chart` applies.
  have hloc := mapsTo_closedBall_of_le (ω := ω) (hu.of_le (by norm_num)) hCR hη hc
    (show (0 : ℝ) ≤ 2 * m by positivity) hK
    (fun y hy ↦ (ha (p, y) ⟨hp, hy⟩).trans (le_max_left _ _))
    (fun x hx hy ξ ↦ (hcmp p hp x hx hy ξ).1) hw₀s hw₀ hρ (by
      rw [show (1 + max a 0) * (2 * m / √c) * (L / m) = η by simp only [L]; field_simp])
  have hdisc := hM hp hu hCR hr.le fun w hw ↦ ⟨(hloc hw).1,
    closedBall_subset_closedBall (by linarith) (hloc hw).2⟩
  -- The area of `u` is at least its area over the disc.
  have hint := (((continuous_eval₂_mfderiv ω (hu.of_le (by norm_num))).comp
    φ.continuous).continuousOn.integrableOn_compact (μ := volume)
      (isCompact_closedBall (φ.symm w₀) (L / m)))
    |>.mono_set ball_subset_closedBall
  refine (ENNReal.ofReal_le_ofReal ?_).trans ((ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y ↦ (hJt p hp).eval₂_mfderiv_nonneg (hCR _))).le.trans
    ((setLIntegral_le_lintegral _ _).trans_eq ?_))
  · rcases hdisc with h | h
    · exact (min_le_left _ _).trans h
    · refine (min_le_right _ _).trans ((div_le_iff₀' hA).2 (h.trans' ?_))
      calc π * L ^ 2 = π * (L / m) ^ 2 * m ^ 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hρ₀ (by positivity)
  · -- `equivRealProdCLM` and `measurableEquivRealProd` are both `z ↦ (re z, im z)`.
    have hφ : (φ : ℂ → ℝ × ℝ) = Complex.measurableEquivRealProd := funext fun z ↦ by
      simp only [φ, Complex.equivRealProdCLM_apply, Complex.measurableEquivRealProd_apply]
    rw [← (Complex.volume_preserving_equiv_real_prod).lintegral_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding, ← hφ, Function.comp_def]

/-- **Energy quantization for pseudoholomorphic planes in a manifold, uniformly over a compact
family of almost complex structures.** Let `J p` be smooth almost complex structures on a
boundaryless Hausdorff manifold `M`, depending on a parameter `p` in a normed space, with
coordinate expressions `(p, y) ↦ (J p).inChart α y` jointly `C²` on `U × (extChartAt I α).target`
in every chart, for an open set `U` of parameters. Let `C ⊆ U` be compact, let `J p` be tamed by a
two-form `ω` for every `p ∈ C`, and let `K ⊆ M` be compact. There is an energy `κ > 0` such that for
every `p ∈ C`, every nonconstant `C³` solution `u : ℝ × ℝ → M` of `∂ₜu = J p (u) ∂ₛu` with values in
`K` has area `∫ ω(∂ₛu, ∂ₜu) ≥ κ`.

The structures `J(z, ·)` frozen at the points `z` of a compact window of the domain of an
inhomogeneous Floer equation form such a family, and the bubbles of a sequence of its solutions are
planes for these frozen structures, at varying bubbling points. -/
theorem exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne_parametric [I.Boundaryless] [T2Space M]
    {J : P → SmoothAlmostComplexStructure I M} {U C : Set P} (hU : IsOpen U) (hCU : C ⊆ U)
    (hC : IsCompact C)
    (hJ : ∀ α : M, ContDiffOn ℝ 2 (fun q : P × E ↦ (J q.1).inChart α q.2)
      (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ω.Tames (J p)) {K : Set M} (hK : IsCompact K) :
    ∃ κ > 0, ∀ ⦃p : P⦄, p ∈ C → ∀ ⦃u : ℝ × ℝ → M⦄, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 u →
      (∀ z, u z ∈ K) →
      (∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
        J p (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) → (∃ z w, u z ≠ u w) →
      ENNReal.ofReal κ ≤ ∫⁻ z, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) := by
  -- Around every point, a ball of chart coordinates of radius `3η` lies in the chart target, and
  -- finitely many of the corresponding chart pieces cover `K`.
  have hpiece : ∀ x : M, ∃ η > 0,
      closedBall (extChartAt I x x) (3 * η) ⊆ (extChartAt I x).target := fun x ↦ by
    obtain ⟨ε, hε, hεt⟩ :=
      Metric.isOpen_iff.1 (isOpen_extChartAt_target x) _ (mem_extChartAt_target (I := I) x)
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hεt⟩
  choose η hη hηK using hpiece
  choose L hL κ hκ hbound using fun x ↦
    exists_pos_forall_ofReal_le_lintegral_of_chart hU hCU hC hJt x (hJ x) (hη x) (hηK x)
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover
    (fun x ↦ (extChartAt I x).source ∩ extChartAt I x ⁻¹' ball (extChartAt I x x) (η x))
    fun x _ ↦ (isOpen_extChartAt_preimage' x isOpen_ball).mem_nhds
      ⟨mem_extChartAt_source x, mem_ball_self (hη x)⟩
  -- The threshold is the least of the thresholds of these charts.
  set κ₀ := (insert 1 (t.image κ)).min' (Finset.insert_nonempty _ _)
  have hκ₀ : 0 < κ₀ := (Finset.lt_min'_iff _ _).2 fun y hy ↦ by
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
      exact hκ x
  set R := 1 + ∑ x ∈ t, L x
  have hR : 0 < R := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun x _ ↦ (hL x).le)
  refine ⟨κ₀, hκ₀, fun p hp u hu huK hCR hnc ↦ ?_⟩
  have hJp := hJt p hp
  set ρ : ℝ × ℝ → ℝ := fun w ↦ SmoothBundleForm.eval₂ ω (u w)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineReal) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u w stdComplexLineImag)
  have hsq (w : ℝ × ℝ) : √(ρ w) ^ 2 = ρ w := Real.sq_sqrt (hJp.eval₂_mfderiv_nonneg (hCR w))
  -- Hofer's lemma gives a point `w'` of density `m² > 0`, with density at most `(2m)²` on a ball
  -- about `w'` of radius at least `R / m`.
  obtain ⟨w₁, hw₁⟩ := hJp.exists_pos_eval₂_mfderiv (hu.mdifferentiable (by norm_num)) hCR hnc
  have hϕ1 : 0 < √(ρ w₁) := Real.sqrt_pos.2 hw₁
  obtain ⟨ε', hε', w', -, -, hmono, hball⟩ := hofer_of_continuousOn_closedBall w₁
    (show 0 < R / √(ρ w₁) by positivity)
    (continuous_eval₂_mfderiv ω (hu.of_le (by norm_num))).sqrt.continuousOn
    fun y _ ↦ Real.sqrt_nonneg _
  rw [div_mul_cancel₀ _ hϕ1.ne'] at hmono
  have hm : 0 < √(ρ w') := by
    by_contra! h
    linarith [mul_nonpos_of_nonneg_of_nonpos hε'.le h]
  -- The chart containing `u w'` gives the bound.
  obtain ⟨x, hxt, hxN⟩ := mem_iUnion₂.1 (htK (huK w'))
  refine (ENNReal.ofReal_le_ofReal (Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hxt)))).trans
    (hbound x hp hu hCR hm hxN.1 hxN.2 (hsq w').le fun w hw ↦ ?_)
  refine (hsq w).symm.le.trans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (hball w ?_) 2)
  rw [dist_comm]
  refine (mem_closedBall.1 hw).trans ((div_le_iff₀ hm).2 (le_trans ?_ hmono))
  exact (Finset.single_le_sum (fun y _ ↦ (hL y).le) hxt).trans
    (le_add_of_nonneg_left zero_le_one)

end Family

/-- **Energy quantization for pseudoholomorphic planes in a manifold.** Let `J` be a smooth almost
complex structure on a boundaryless Hausdorff manifold `M`, tamed by a two-form `ω`, as on a closed
symplectic manifold, and let `K ⊆ M` be compact. There is an energy `κ > 0` such that every
nonconstant `C³` solution `u : ℝ × ℝ → M` of `∂ₜu = J(u) ∂ₛu` with values in `K` has area
`∫ ω(∂ₛu, ∂ₜu) ≥ κ`. -/
theorem Tames.exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne [I.Boundaryless] [T2Space M]
    (hJ : ω.Tames J) {K : Set M} (hK : IsCompact K) :
    ∃ κ > 0, ∀ ⦃u : ℝ × ℝ → M⦄, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 u → (∀ z, u z ∈ K) →
      (∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
        J (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) → (∃ z w, u z ≠ u w) →
      ENNReal.ofReal κ ≤ ∫⁻ z, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) := by
  obtain ⟨κ, hκ, h⟩ := exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne_parametric
    (J := fun (_ : Unit) ↦ J) isOpen_univ (subset_univ {()}) isCompact_singleton
    (fun α ↦ ((J.contDiffOn_inChart α).of_le (by simp)).comp contDiffOn_snd fun _ hq ↦ hq.2)
    (fun _ _ ↦ hJ) hK
  exact ⟨κ, hκ, h rfl⟩

end TauCeti.SmoothTwoForm

namespace TauCeti.ContMDiffAlmostComplexStructureFamily

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Energy quantization for the structures frozen from a smooth family.** Let `J` be a smooth
family of almost complex structures on a boundaryless Hausdorff manifold `M`, over a parameter
space `P` that is a normed space, such as the domain `ℝ × ℝ` of a Floer equation with a
domain-dependent structure. Let the frozen structures `J p` be tamed by a two-form `ω` for `p` in a
compact set `C`, and let `K ⊆ M` be compact. There is an energy `κ > 0` such that for every
`p ∈ C`, every nonconstant `C³` solution `u : ℝ × ℝ → M` of `∂ₜu = J p (u) ∂ₛu` with values in `K`
has area `∫ ω(∂ₛu, ∂ₜu) ≥ κ`. -/
theorem exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne [I.Boundaryless] [T2Space M]
    (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, P) P ⊤) {ω : SmoothTwoForm I M}
    {C : Set P} (hC : IsCompact C) (hJt : ∀ p ∈ C, ω.Tames (J.freezeSmooth p)) {K : Set M}
    (hK : IsCompact K) :
    ∃ κ > 0, ∀ ⦃p : P⦄, p ∈ C → ∀ ⦃u : ℝ × ℝ → M⦄, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 u →
      (∀ z, u z ∈ K) →
      (∀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
        J.freezeSmooth p (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) →
      (∃ z w, u z ≠ u w) →
      ENNReal.ofReal κ ≤ ∫⁻ z, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) := by
  refine SmoothTwoForm.exists_pos_forall_ofReal_le_lintegral_eval₂_of_ne_parametric isOpen_univ
    (subset_univ C) hC (fun α ↦ ?_) hJt hK
  -- In the product chart at `(0, α)`, the coordinate expression of the family is that of the
  -- frozen structures, since the chart of the parameter space is the identity.
  have h := (J.contDiffOn_inChart ((0 : P), α)).of_le (m := 2) (by simp)
  rw [extChartAt_prod_target, extChartAt_model_space_eq_id, PartialEquiv.refl_target] at h
  refine h.congr fun ⟨w, y⟩ _ ↦ ?_
  rw [J.inChart_mk, extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    id_eq, SmoothAlmostComplexStructure.inChart_def, ContMDiffAlmostComplexStructure.inChart_def,
    freezeSmooth_toEndomorphism]

end TauCeti.ContMDiffAlmostComplexStructureFamily
