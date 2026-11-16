/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Contour.Cycle.Circle
import TauCeti.Analysis.Contour.Cycle.HomologyCauchy
import TauCeti.Analysis.Contour.Winding.Number.Rectangle

/-!
# Cauchy's theorem on rectangles with isolated singularities

For a function `f : ℂ → E` valued in a complex normed space that is continuous on a closed
rectangle `[σ₁, σ₂] ×ℂ [t₁, t₂]` minus a finite set `P` and complex differentiable on the open
rectangle `(σ₁, σ₂) ×ℂ (t₁, t₂)` minus `P`, the counterclockwise integral along the boundary of the
rectangle equals the sum of the circle integrals `∮ z in C(ρ, r ρ), f z` around each `ρ ∈ P`,
provided each closed disc `closedBall ρ (r ρ)` lies in the open rectangle and contains no other
point of `P`. Unlike residue theorems, no open neighbourhood of the closed rectangle and no
meromorphy at `P` are assumed, so the points of `P` may be essential singularities.

This feeds both the rectangle residue theorem without an ambient open neighbourhood (in
`TauCeti.Analysis.Contour.Residue.Rectangle`) and the L-shaped contour shift of a vertical segment
integral to `Re s = −∞`, which allows singularities both at `P` in the upper-left strip and inside
the removed lower-left block `{s | s.re < w.re ∧ s.im < w.im}`.

## Main results

* `TauCeti.Contour.integral_boundary_rect_eq_sum_circleIntegral`: the counterclockwise boundary
  integral of a rectangle equals the sum of circle integrals around isolated singularities inside
  the open rectangle.
* `TauCeti.Contour.I_smul_integral_vertical_eq_lShaped_add_sum_circleIntegral`: the L-shaped
  contour shift of a vertical segment integral to `Re s = −∞`, picking up circle integrals around
  isolated singularities in the upper-left strip.

## References

* L. V. Ahlfors, *Complex Analysis*, Ch. 4 (homology form of Cauchy's theorem).
* S. Lang, *Complex Analysis* (GTM 103), Ch. IV–VI.
* T. Tao and contributors, *IEANTN: Integrated Explicit Analytic Number Theory Network*
  (circle-integral form on rectangles and L-shaped contour shifts).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval Real

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Inside an open rectangle `U = (σ₁, σ₂) ×ℂ (t₁, t₂)`, a strictly smaller closed rectangle
containing all the discs `closedBall ρ (r ρ)` has the same boundary integral as the sum of the
circle integrals around `P`. -/
private theorem integral_boundary_rect_eq_sum_circleIntegral_of_subset_open
    {σ₁ σ₂ t₁ t₂ a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hrect : Icc a b ×ℂ Icc c d ⊆ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂)
    {P : Finset ℂ} {r : ℂ → ℝ}
    (hr : ∀ ρ ∈ P, 0 < r ρ)
    (hP : ∀ ρ ∈ P, closedBall ρ (r ρ) ⊆ Ioo a b ×ℂ Ioo c d)
    (hsep : ∀ ρ ∈ P, ∀ ρ' ∈ P, ρ ≠ ρ' → ρ' ∉ closedBall ρ (r ρ))
    {f : ℂ → E} (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P)) :
    (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
        I • (∫ y : ℝ in c..d, f (b + y * I)) - I • (∫ y : ℝ in c..d, f (a + y * I)) =
      ∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z := by
  let U : Set ℂ := Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂
  let z₀ : ℂ := a + c * I
  let w₀ : ℂ := b + d * I
  have hz₀_re : z₀.re = a := by simp [z₀]
  have hz₀_im : z₀.im = c := by simp [z₀]
  have hw₀_re : w₀.re = b := by simp [w₀]
  have hw₀_im : w₀.im = d := by simp [w₀]
  have hR_eq : Rectangle z₀ w₀ = Icc a b ×ℂ Icc c d := by
    rw [Rectangle, hz₀_re, hw₀_re, hz₀_im, hw₀_im, uIcc_of_le hab, uIcc_of_le hcd]
  have hint_eq : interior (Rectangle z₀ w₀) = Ioo a b ×ℂ Ioo c d := by
    rw [interior_rectangle (by simpa [z₀, w₀] using hab) (by simpa [z₀, w₀] using hcd),
      hz₀_re, hw₀_re, hz₀_im, hw₀_im]
  have hPU : ∀ ρ ∈ P, closedBall ρ (r ρ) ⊆ U := fun ρ hρ s hs ↦
    hrect ⟨Ioo_subset_Icc_self (hP ρ hρ hs).1, Ioo_subset_Icc_self (hP ρ hρ hs).2⟩
  -- Build the rectangle cycle `C` and the sum of circle cycles `D`, both supported in `U \ P`.
  let C : Cycle := (rectPolygon z₀ w₀).contourCycle
  let D : Cycle := ∑ ρ ∈ P, circleCycle ρ (r ρ)
  have hC_raw : C = FreeAbelianGroup.of (PiecewiseC1ClosedCurve.of (rectBoundary z₀ w₀)
      (isPiecewiseC1On_rectBoundary z₀ w₀) (by simp)) := by
    simp only [C, Polygon.contourCycle_def, Polygon.contourCurve_def, Nat.cast_ofNat,
      ← rectBoundary_def]
  have hC_in : Cycle.IsIn C (U \ P) := by
    rw [Cycle.isIn_iff, Polygon.trace_contourCycle, boundary_rectPolygon]
    intro s hs
    refine ⟨hrect (hR_eq ▸ (isClosed_rectangle z₀ w₀).frontier_subset hs), fun hsP ↦ ?_⟩
    have hs_int : s ∈ interior (Rectangle z₀ w₀) :=
      hint_eq ▸ hP s hsP (mem_closedBall_self (hr s hsP).le)
    exact disjoint_left.1 disjoint_interior_frontier hs_int hs
  have hD_in : Cycle.IsIn D (U \ P) :=
    Finset.sum_induction _ (fun Γ ↦ Cycle.IsIn Γ (U \ P)) (fun _ _ h₁ h₂ ↦ h₁.add h₂)
      (Cycle.IsIn.zero _) fun ρ hρ ↦ by
        rw [Cycle.isIn_iff, Cycle.trace_circleCycle, abs_of_pos (hr ρ hρ)]
        intro s hs
        refine ⟨hPU ρ hρ (sphere_subset_closedBall hs), fun hsP ↦ ?_⟩
        by_cases hEq : ρ = s
        · subst hEq; exact (hr ρ hρ).ne (by simpa [mem_sphere] using hs)
        · exact hsep ρ hρ s hsP hEq (sphere_subset_closedBall hs)
  -- Both cycles are null-homologous in `U` and have winding number `1` about every `p ∈ P`.
  have hC_null : Cycle.IsNullHomologous C U := by
    rw [hC_raw, Cycle.isNullHomologous_of_raw_iff]
    exact isNullHomologous_rectBoundary (hR_eq.symm ▸ hrect)
  have hD_null : Cycle.IsNullHomologous D U := by
    rw [Cycle.isNullHomologous_iff]
    intro s hsU
    rw [map_sum]
    refine Finset.sum_eq_zero fun ρ hρ ↦ ?_
    exact Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist (hr ρ hρ).le
      (lt_of_not_ge (mt mem_closedBall.mpr fun h ↦ hsU (hPU ρ hρ h)))
  have hCD : ∀ p ∈ (P : Set ℂ), Cycle.windingNumber p C = Cycle.windingNumber p D := by
    intro p hp
    have hpP : p ∈ P := hp
    have hC_p : Cycle.windingNumber p C = 1 := by
      rw [hC_raw, Cycle.windingNumber_of_raw]
      refine windingNumber_rectBoundary_eq_one ?_
      rw [hz₀_re, hw₀_re, hz₀_im, hw₀_im]
      exact hP p hpP (mem_closedBall_self (hr p hpP).le)
    have hD_p : Cycle.windingNumber p D = 1 := by
      rw [map_sum, Finset.sum_eq_single p]
      · exact Cycle.windingNumber_circleCycle_eq_one_of_dist_lt (by simpa using hr p hpP)
      · intro ρ hρ hne
        exact Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist (hr ρ hρ).le
          (lt_of_not_ge (mt mem_closedBall.mpr (hsep ρ hρ p hpP hne)))
      · intro hnot; exact (hnot hpP).elim
    rw [hC_p, hD_p]
  -- Apply the homology Cauchy theorem and evaluate both cycle integrals.
  have heq := Cycle.integral_eq_of_windingNumber_eq (isOpen_Ioo.reProdIm isOpen_Ioo)
    P.finite_toSet.isClosed hd hC_in hD_in hC_null hD_null hCD
  have hC_int : Cycle.integral f C =
      (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
        I • (∫ y : ℝ in c..d, f (b + y * I)) - I • (∫ y : ℝ in c..d, f (a + y * I)) := by
    have hf_fr : ContinuousOn f (frontier (Rectangle z₀ w₀)) :=
      hd.continuousOn.mono (by
        rw [← boundary_rectPolygon, ← Polygon.trace_contourCycle]
        exact Cycle.isIn_iff.mp hC_in)
    rw [hC_raw, Cycle.integral_of_raw, integral_rectBoundary hf_fr, hz₀_re, hw₀_re, hz₀_im, hw₀_im]
  have hD_int : Cycle.integral f D = ∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z := by
    simp [D, Cycle.integral_circleCycle]
  rw [← hC_int, ← hD_int, heq]

/-- There is a positive collar thickness `δ` strictly less than half the width and height of the
rectangle such that every disc `closedBall ρ (r ρ)` (`ρ ∈ P`) lies in the shrunken open rectangle
`(σ₁ + δ, σ₂ - δ) ×ℂ (t₁ + δ, t₂ - δ)`. -/
private theorem exists_collar_margin {σ₁ σ₂ t₁ t₂ : ℝ} (hσ : σ₁ < σ₂) (ht : t₁ < t₂)
    {P : Finset ℂ} {r : ℂ → ℝ} (hr : ∀ ρ ∈ P, 0 < r ρ)
    (hP : ∀ ρ ∈ P, closedBall ρ (r ρ) ⊆ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (σ₂ - σ₁) / 2 ∧ δ < (t₂ - t₁) / 2 ∧
      ∀ ρ ∈ P, closedBall ρ (r ρ) ⊆ Ioo (σ₁ + δ) (σ₂ - δ) ×ℂ Ioo (t₁ + δ) (t₂ - δ) := by
  induction P using Finset.cons_induction with
  | empty =>
    refine ⟨min ((σ₂ - σ₁) / 4) ((t₂ - t₁) / 4), by positivity,
      (min_le_left _ _).trans_lt (by linarith), (min_le_right _ _).trans_lt (by linarith), by simp⟩
  | cons ρ Q hρQ ih =>
    obtain ⟨δ₀, hδ₀, hδ₀σ, hδ₀t, hQ⟩ := ih
      (fun q hq ↦ hr q (Finset.mem_cons_of_mem hq))
      (fun q hq ↦ hP q (Finset.mem_cons_of_mem hq))
    have hρr : 0 < r ρ := hr ρ (Finset.mem_cons_self ρ Q)
    have hρP := hP ρ (Finset.mem_cons_self ρ Q)
    have hdir : ∀ u : ℂ, ‖u‖ = 1 → ρ + (r ρ : ℂ) * u ∈ closedBall ρ (r ρ) := fun u hu ↦ by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hρr.le, hu, mul_one]
    have hL : σ₁ < ρ.re - r ρ := by
      simpa [sub_eq_add_neg] using (hρP (hdir (-1) (by simp))).1.1
    have hR : ρ.re + r ρ < σ₂ := by simpa using (hρP (hdir 1 (by simp))).1.2
    have hB : t₁ < ρ.im - r ρ := by
      simpa [sub_eq_add_neg] using (hρP (hdir (-I) (by simp))).2.1
    have hT : ρ.im + r ρ < t₂ := by simpa using (hρP (hdir I (by simp))).2.2
    let δ₁ := min (min (ρ.re - r ρ - σ₁) (σ₂ - (ρ.re + r ρ)))
      (min (ρ.im - r ρ - t₁) (t₂ - (ρ.im + r ρ))) / 2
    have hδ₁ : 0 < δ₁ := div_pos
      (lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))) two_pos
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, (min_le_left _ _).trans_lt hδ₀σ,
      (min_le_left _ _).trans_lt hδ₀t, fun q hq s hs ↦ ?_⟩
    rcases Finset.mem_cons.mp hq with rfl | hqQ
    · have hdist : ‖s - q‖ ≤ r q := by simpa [dist_eq_norm] using mem_closedBall.mp hs
      have hre := abs_le.mp ((Complex.abs_re_le_norm (s - q)).trans hdist)
      have him := abs_le.mp ((Complex.abs_im_le_norm (s - q)).trans hdist)
      simp only [sub_re, sub_im] at hre him
      have hpos : 0 < min δ₀ δ₁ := lt_min hδ₀ hδ₁
      have hδle : 2 * min δ₀ δ₁ ≤ min (min (q.re - r q - σ₁) (σ₂ - (q.re + r q)))
          (min (q.im - r q - t₁) (t₂ - (q.im + r q))) := by
        have := min_le_right δ₀ δ₁; dsimp only [δ₁] at this; linarith
      simp only [le_min_iff] at hδle
      exact ⟨⟨by linarith [hre.1, hδle.1.1], by linarith [hre.2, hδle.1.2]⟩,
        ⟨by linarith [him.1, hδle.2.1], by linarith [him.2, hδle.2.2]⟩⟩
    · have hs' := hQ q hqQ hs
      exact ⟨⟨by linarith [hs'.1.1, min_le_left δ₀ δ₁], by linarith [hs'.1.2, min_le_left δ₀ δ₁]⟩,
        ⟨by linarith [hs'.2.1, min_le_left δ₀ δ₁], by linarith [hs'.2.2, min_le_left δ₀ δ₁]⟩⟩

/-- As the shrinking parameter `ε → 0⁺`, the four-edge boundary integral of the shrunken rectangle
`[σ₁ + ε, σ₂ - ε] ×ℂ [t₁ + ε, t₂ - ε]` converges to that of `[σ₁, σ₂] ×ℂ [t₁, t₂]` whenever `f` is
continuous on a collar of thickness `δ` around the perimeter. -/
private theorem tendsto_integral_boundary_rect_shrink {σ₁ σ₂ t₁ t₂ δ : ℝ}
    (hδ : 0 < δ) (hδσ : δ < (σ₂ - σ₁) / 2) (hδt : δ < (t₂ - t₁) / 2) {f : ℂ → E}
    (hf : ContinuousOn f
      ((Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) \ (Ioo (σ₁ + δ) (σ₂ - δ) ×ℂ Ioo (t₁ + δ) (t₂ - δ)))) :
    Tendsto
      (fun ε : ℝ ↦
        (∫ x : ℝ in (σ₁ + ε)..(σ₂ - ε), f (x + ((t₁ + ε : ℝ) : ℂ) * I)) -
          (∫ x : ℝ in (σ₁ + ε)..(σ₂ - ε), f (x + ((t₂ - ε : ℝ) : ℂ) * I)) +
          I • (∫ y : ℝ in (t₁ + ε)..(t₂ - ε), f (((σ₂ - ε : ℝ) : ℂ) + y * I)) -
          I • (∫ y : ℝ in (t₁ + ε)..(t₂ - ε), f (((σ₁ + ε : ℝ) : ℂ) + y * I)))
      (𝓝[>] 0)
      (𝓝 ((∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) +
        I • (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) - I • (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)))) := by
  let K : Set ℂ := (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) \ (Ioo (σ₁ + δ) (σ₂ - δ) ×ℂ Ioo (t₁ + δ) (t₂ - δ))
  have hK_compact : IsCompact K :=
    (isCompact_Icc.reProdIm isCompact_Icc).diff (isOpen_Ioo.reProdIm isOpen_Ioo)
  obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn hf
  -- Dominated convergence for a parametrized edge on `[0, 1]` staying inside the collar `K`.
  have hdom : ∀ (p : ℝ → ℝ → ℂ),
      (∀ ε ∈ Ioo (0 : ℝ) δ, Continuous (p ε)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun ε ↦ p ε t) 0) →
      (∀ ε ∈ Ioo (0 : ℝ) δ, ∀ t ∈ Icc (0 : ℝ) 1, p ε t ∈ K) →
      (∀ t ∈ Icc (0 : ℝ) 1, p 0 t ∈ K) →
      Tendsto (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..1, f (p ε t)) (𝓝[>] 0)
        (𝓝 (∫ t in (0 : ℝ)..1, f (p 0 t))) := by
    intro p hpc hpt hεK h0K
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      have hcont : ContinuousOn (fun t : ℝ ↦ f (p ε t)) (Icc 0 1) :=
        hf.comp (hpc ε hε).continuousOn fun t ht ↦ hεK ε hε t ht
      have hsub : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
        rw [uIoc_of_le zero_le_one]
        exact Ioc_subset_Icc_self
      exact (hcont.mono hsub).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      exact hM _ (hεK ε hε t (Ioc_subset_Icc_self ht))
    · refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have hlin : Tendsto (fun ε : ℝ ↦ p ε t) (𝓝[>] 0) (𝓝[K] (p 0 t)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          ((hpt t (Ioc_subset_Icc_self ht)).tendsto.mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
        exact hεK ε hε t (Ioc_subset_Icc_self ht)
      exact (hf _ (h0K t (Ioc_subset_Icc_self ht))).tendsto.comp hlin
  have hmem_K {x y : ℝ} (hx₁ : σ₁ ≤ x) (hx₂ : x ≤ σ₂) (hy₁ : t₁ ≤ y) (hy₂ : y ≤ t₂)
      (hnot : ¬ (σ₁ + δ < x ∧ x < σ₂ - δ ∧ t₁ + δ < y ∧ y < t₂ - δ)) :
      ((x : ℂ) + (y : ℂ) * I) ∈ K := by
    refine ⟨⟨⟨by simpa using hx₁, by simpa using hx₂⟩, ⟨by simpa using hy₁, by simpa using hy₂⟩⟩,
      fun h ↦ hnot ?_⟩
    simp only [mem_reProdIm, mem_Ioo, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, add_im, mul_im, zero_add] at h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  -- Affine reparametrization of horizontal and vertical edges onto `[0, 1]`.
  have hcov_h (p q r : ℝ) :
      (q - p) • ∫ t in (0 : ℝ)..1, f ((p + (q - p) * t : ℝ) + r * I) =
        ∫ x : ℝ in p..q, f (x + r * I) := by
    have h := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
      (fun x : ℝ ↦ f (x + r * I)) (q - p) p
    simpa [mul_zero, add_zero, mul_one, add_sub_cancel] using h
  have hcov_v (p q r : ℝ) :
      (q - p) • ∫ t in (0 : ℝ)..1, f (r + (p + (q - p) * t : ℝ) * I) =
        ∫ y : ℝ in p..q, f (r + y * I) := by
    have h := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
      (fun y : ℝ ↦ f (r + y * I)) (q - p) p
    simpa [mul_zero, add_zero, mul_one, add_sub_cancel] using h
  have hlen_x : Tendsto (fun ε : ℝ ↦ (σ₂ - ε) - (σ₁ + ε)) (𝓝[>] 0) (𝓝 (σ₂ - σ₁)) := by
    have hc : Continuous (fun ε : ℝ ↦ (σ₂ - ε) - (σ₁ + ε)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlen_y : Tendsto (fun ε : ℝ ↦ (t₂ - ε) - (t₁ + ε)) (𝓝[>] 0) (𝓝 (t₂ - t₁)) := by
    have hc : Continuous (fun ε : ℝ ↦ (t₂ - ε) - (t₁ + ε)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have htend_h (y : ℝ → ℝ) (hy_cont : Continuous y)
      (hy_mem : ∀ ε ∈ Ico (0 : ℝ) δ, t₁ ≤ y ε ∧ y ε ≤ t₂ ∧ (y ε ≤ t₁ + δ ∨ t₂ - δ ≤ y ε)) :
      Tendsto (fun ε : ℝ ↦ ∫ x : ℝ in (σ₁ + ε)..(σ₂ - ε), f (x + y ε * I))
        (𝓝[>] 0) (𝓝 (∫ x : ℝ in σ₁..σ₂, f (x + y 0 * I))) := by
    have hmem : ∀ ε ∈ Ico (0 : ℝ) δ, ∀ t ∈ Icc (0 : ℝ) 1,
        (((σ₁ + ε) + ((σ₂ - ε) - (σ₁ + ε)) * t : ℝ) : ℂ) + (y ε : ℂ) * I ∈ K := by
      intro ε hε t ht
      obtain ⟨hy₁, hy₂, hside⟩ := hy_mem ε hε
      refine hmem_K (by nlinarith [hε.1, hε.2, ht.1, ht.2])
        (by nlinarith [hε.1, hε.2, ht.1, ht.2]) hy₁ hy₂ ?_
      rintro ⟨_, _, h1, h2⟩
      rcases hside with h | h <;> linarith
    have h := hlen_x.smul (hdom
      (fun ε t ↦ (((σ₁ + ε) + ((σ₂ - ε) - (σ₁ + ε)) * t : ℝ) : ℂ) + (y ε : ℂ) * I)
      (fun _ _ ↦ by fun_prop) (fun _ _ ↦ by fun_prop)
      (fun ε hε ↦ hmem ε (Ioo_subset_Ico_self hε)) (hmem 0 ⟨le_rfl, hδ⟩))
    simpa only [hcov_h, sub_zero, add_zero] using h
  have htend_v (x : ℝ → ℝ) (hx_cont : Continuous x)
      (hx_mem : ∀ ε ∈ Ico (0 : ℝ) δ, σ₁ ≤ x ε ∧ x ε ≤ σ₂ ∧ (x ε ≤ σ₁ + δ ∨ σ₂ - δ ≤ x ε)) :
      Tendsto (fun ε : ℝ ↦ I • ∫ y : ℝ in (t₁ + ε)..(t₂ - ε), f (x ε + y * I))
        (𝓝[>] 0) (𝓝 (I • ∫ y : ℝ in t₁..t₂, f (x 0 + y * I))) := by
    have hmem : ∀ ε ∈ Ico (0 : ℝ) δ, ∀ t ∈ Icc (0 : ℝ) 1,
        (x ε : ℂ) + (((t₁ + ε) + ((t₂ - ε) - (t₁ + ε)) * t : ℝ) : ℂ) * I ∈ K := by
      intro ε hε t ht
      obtain ⟨hx₁, hx₂, hside⟩ := hx_mem ε hε
      refine hmem_K hx₁ hx₂ (by nlinarith [hε.1, hε.2, ht.1, ht.2])
        (by nlinarith [hε.1, hε.2, ht.1, ht.2]) ?_
      rintro ⟨h1, h2, _, _⟩
      rcases hside with h | h <;> linarith
    have h := (tendsto_const_nhds (x := I)).smul (hlen_y.smul (hdom
      (fun ε t ↦ (x ε : ℂ) + (((t₁ + ε) + ((t₂ - ε) - (t₁ + ε)) * t : ℝ) : ℂ) * I)
      (fun _ _ ↦ by fun_prop) (fun _ _ ↦ by fun_prop)
      (fun ε hε ↦ hmem ε (Ioo_subset_Ico_self hε)) (hmem 0 ⟨le_rfl, hδ⟩)))
    simpa only [hcov_v, sub_zero, add_zero] using h
  -- Apply the horizontal and vertical edge limits to the four shrinking sides.
  have hbot : Tendsto (fun ε : ℝ ↦ ∫ x : ℝ in (σ₁ + ε)..(σ₂ - ε), f (x + ((t₁ + ε : ℝ) : ℂ) * I))
      (𝓝[>] 0) (𝓝 (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I))) := by
    simpa only [add_zero] using htend_h (fun ε ↦ t₁ + ε) (by fun_prop)
      fun ε hε ↦ ⟨by linarith [hε.1], by linarith [hε.2], Or.inl (by linarith [hε.2])⟩
  have htop : Tendsto (fun ε : ℝ ↦ ∫ x : ℝ in (σ₁ + ε)..(σ₂ - ε), f (x + ((t₂ - ε : ℝ) : ℂ) * I))
      (𝓝[>] 0) (𝓝 (∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I))) := by
    simpa only [sub_zero] using htend_h (fun ε ↦ t₂ - ε) (by fun_prop)
      fun ε hε ↦ ⟨by linarith [hε.2], by linarith [hε.1], Or.inr (by linarith [hε.2])⟩
  have hright : Tendsto
      (fun ε : ℝ ↦ I • ∫ y : ℝ in (t₁ + ε)..(t₂ - ε), f (((σ₂ - ε : ℝ) : ℂ) + y * I))
      (𝓝[>] 0) (𝓝 (I • ∫ y : ℝ in t₁..t₂, f (σ₂ + y * I))) := by
    simpa only [sub_zero] using htend_v (fun ε ↦ σ₂ - ε) (by fun_prop)
      fun ε hε ↦ ⟨by linarith [hε.2], by linarith [hε.1], Or.inr (by linarith [hε.2])⟩
  have hleft : Tendsto
      (fun ε : ℝ ↦ I • ∫ y : ℝ in (t₁ + ε)..(t₂ - ε), f (((σ₁ + ε : ℝ) : ℂ) + y * I))
      (𝓝[>] 0) (𝓝 (I • ∫ y : ℝ in t₁..t₂, f (σ₁ + y * I))) := by
    simpa only [add_zero] using htend_v (fun ε ↦ σ₁ + ε) (by fun_prop)
      fun ε hε ↦ ⟨by linarith [hε.1], by linarith [hε.2], Or.inl (by linarith [hε.2])⟩
  exact ((hbot.sub htop).add hright).sub hleft

/-- **Cauchy's theorem for a rectangle with isolated singularities.** Let `σ₁ ≤ σ₂`, `t₁ ≤ t₂`,
and let `P` be a finite set of points in the open rectangle `(σ₁, σ₂) ×ℂ (t₁, t₂)` equipped with
positive radii `r ρ` such that each closed disc `closedBall ρ (r ρ)` lies in the open rectangle
and contains no other point of `P`. If `f : ℂ → E` is continuous on `[σ₁, σ₂] ×ℂ [t₁, t₂] \ P`
and complex differentiable on `(σ₁, σ₂) ×ℂ (t₁, t₂) \ P`, then the counterclockwise boundary
integral of the rectangle equals `∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z`.

No open neighbourhood of the closed rectangle and no meromorphy at `P` are assumed, so the
singularities in `P` may be essential. -/
theorem integral_boundary_rect_eq_sum_circleIntegral
    {σ₁ σ₂ t₁ t₂ : ℝ} (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
    {P : Finset ℂ} {r : ℂ → ℝ}
    (hr : ∀ ρ ∈ P, 0 < r ρ)
    (hP : ∀ ρ ∈ P, closedBall ρ (r ρ) ⊆ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂)
    (hsep : ∀ ρ ∈ P, ∀ ρ' ∈ P, ρ ≠ ρ' → ρ' ∉ closedBall ρ (r ρ))
    {f : ℂ → E}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P)) :
    (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) +
        I • (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) - I • (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)) =
      ∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z := by
  -- Handle degenerate rectangles where the open rectangle is empty, forcing `P = ∅`.
  rcases hσ.eq_or_lt with rfl | hσ_lt
  · have hPempty : P = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun ρ hρ ↦ by
      have := (hP ρ hρ (mem_closedBall_self (hr ρ hρ).le)).1
      exact this.1.not_ge this.2.le
    simp [hPempty]
  rcases ht.eq_or_lt with rfl | ht_lt
  · have hPempty : P = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun ρ hρ ↦ by
      have := (hP ρ hρ (mem_closedBall_self (hr ρ hρ).le)).2
      exact this.1.not_ge this.2.le
    simp [hPempty]
  -- Choose a positive collar thickness `δ` separating `P`'s discs from the rectangle boundary.
  obtain ⟨δ, hδ, hδσ, hδt, hPδ⟩ := exists_collar_margin hσ_lt ht_lt hr hP
  have hK_sub :
      (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) \ (Ioo (σ₁ + δ) (σ₂ - δ) ×ℂ Ioo (t₁ + δ) (t₂ - δ)) ⊆
        Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P := fun s hs ↦
    ⟨hs.1, fun hsP ↦ hs.2 (hPδ s hsP (mem_closedBall_self (hr s hsP).le))⟩
  have hlim := tendsto_integral_boundary_rect_shrink hδ hδσ hδt (hc.mono hK_sub)
  have hconst : Tendsto
      (fun ε : ℝ ↦
        (∫ x : ℝ in (σ₁ + ε)..(σ₂ - ε), f (x + ((t₁ + ε : ℝ) : ℂ) * I)) -
          (∫ x : ℝ in (σ₁ + ε)..(σ₂ - ε), f (x + ((t₂ - ε : ℝ) : ℂ) * I)) +
          I • (∫ y : ℝ in (t₁ + ε)..(t₂ - ε), f (((σ₂ - ε : ℝ) : ℂ) + y * I)) -
          I • (∫ y : ℝ in (t₁ + ε)..(t₂ - ε), f (((σ₁ + ε : ℝ) : ℂ) + y * I)))
      (𝓝[>] 0) (𝓝 (∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    refine (integral_boundary_rect_eq_sum_circleIntegral_of_subset_open
      (a := σ₁ + ε) (b := σ₂ - ε) (c := t₁ + ε) (d := t₂ - ε)
      (by linarith [hε.2]) (by linarith [hε.2])
      (fun s hs ↦ ⟨⟨by linarith [hs.1.1, hε.1], by linarith [hs.1.2, hε.1]⟩,
        ⟨by linarith [hs.2.1, hε.1], by linarith [hs.2.2, hε.1]⟩⟩)
      hr (fun ρ hρ s hs ↦ by
        have hs' := hPδ ρ hρ hs
        exact ⟨⟨by linarith [hs'.1.1, hε.2], by linarith [hs'.1.2, hε.2]⟩,
          ⟨by linarith [hs'.2.1, hε.2], by linarith [hs'.2.2, hε.2]⟩⟩)
      hsep hd).symm
  exact tendsto_nhds_unique hlim hconst

/-- **L-shaped contour shift to `Re s = −∞`.** Let `w : ℂ` satisfy `w.re ≤ σ` and
`t₁ ≤ w.im ≤ t₂`, and let `D` be the closed half-infinite strip `{s | s.re ≤ σ ∧ t₁ ≤ s.im ≤ t₂}`
with its open lower-left block `{s | s.re < w.re ∧ s.im < w.im}` removed. Let `P` be a finite set
equipped with positive radii `r ρ` whose closed discs `closedBall ρ (r ρ)` lie in
`{s | s.re < σ ∧ w.im < s.im < t₂}` and contain no other point of `P`.

If `f : ℂ → E` is continuous on `D \ P`, complex differentiable on the interior of `D` minus `P`,
tends to `0` uniformly as `Re s → −∞` with `w.im ≤ Im s ≤ t₂`, and is integrable along the
horizontal rays ending at `w` and at `σ + t₂ * I`, then the contour integral along the vertical
segment from `σ + t₁ * I` to `σ + t₂ * I` equals the integral along the L-shaped path
`σ + t₁ * I → w.re + t₁ * I → w → −∞ + w.im * I` plus the upper horizontal ray integral
`∫ x in Iic σ, f (x + t₂ * I)` plus the sum of the circle integrals around `P`. -/
theorem I_smul_integral_vertical_eq_lShaped_add_sum_circleIntegral
    {σ t₁ t₂ : ℝ} {w : ℂ} (hw : w.re ≤ σ) (hw₁ : t₁ ≤ w.im) (hw₂ : w.im ≤ t₂)
    {P : Finset ℂ} {r : ℂ → ℝ}
    (hr : ∀ ρ ∈ P, 0 < r ρ)
    (hP : ∀ ρ ∈ P, closedBall ρ (r ρ) ⊆ {s : ℂ | s.re < σ ∧ w.im < s.im ∧ s.im < t₂})
    (hsep : ∀ ρ ∈ P, ∀ ρ' ∈ P, ρ ≠ ρ' → ρ' ∉ closedBall ρ (r ρ))
    {f : ℂ → E}
    (hc : ContinuousOn f
      ({s : ℂ | s.re ≤ σ ∧ t₁ ≤ s.im ∧ s.im ≤ t₂ ∧ (w.re ≤ s.re ∨ w.im ≤ s.im)} \ P))
    (hd : DifferentiableOn ℂ f
      ({s : ℂ | s.re < σ ∧ t₁ < s.im ∧ s.im < t₂ ∧ (w.re < s.re ∨ w.im < s.im)} \ P))
    (hdecay : Tendsto f (comap Complex.re atBot ⊓ 𝓟 {s : ℂ | w.im ≤ s.im ∧ s.im ≤ t₂}) (𝓝 0))
    (hw_int : IntegrableOn (fun x : ℝ ↦ f (x + w.im * I)) (Iic w.re))
    (ht₂_int : IntegrableOn (fun x : ℝ ↦ f (x + t₂ * I)) (Iic σ)) :
    I • (∫ y : ℝ in t₁..t₂, f (σ + y * I)) =
      (∫ x : ℝ in σ..w.re, f (x + t₁ * I)) + I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
          (∫ x in Iic w.re, f (x + w.im * I)) + (∫ x in Iic σ, f (x + t₂ * I)) +
        ∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z := by
  -- Step 1: Cauchy–Goursat on the lower-right rectangle `[w.re, σ] ×ℂ [t₁, w.im]` avoiding `P`.
  have hlow_zero :
      (∫ x : ℝ in w.re..σ, f (x + t₁ * I)) - (∫ x : ℝ in w.re..σ, f (x + w.im * I)) +
          I • (∫ y : ℝ in t₁..w.im, f (σ + y * I)) -
          I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) = 0 := by
    have hlow := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f (w.re + t₁ * I) (σ + w.im * I)
      (hc.mono fun s hs ↦ by
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add, uIcc_of_le hw, uIcc_of_le hw₁] at hs
        refine ⟨⟨hs.1.2, hs.2.1, hs.2.2.trans hw₂, Or.inl hs.1.1⟩, fun hsP ↦ ?_⟩
        exact hs.2.2.not_gt (hP s hsP (mem_closedBall_self (hr s hsP).le)).2.1)
      (hd.mono fun s hs ↦ by
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, add_im, mul_im, zero_add, min_eq_left hw, max_eq_right hw,
          min_eq_left hw₁, max_eq_right hw₁] at hs
        refine ⟨⟨hs.1.2, hs.2.1, hs.2.2.trans_le hw₂, Or.inl hs.1.1⟩, fun hsP ↦ ?_⟩
        exact hs.2.2.not_gt (hP s hsP (mem_closedBall_self (hr s hsP).le)).2.1)
    simpa only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] using hlow
  -- Step 2: Split the right vertical edge at height `w.im`.
  have hright_cont : ContinuousOn (fun y : ℝ ↦ f (σ + y * I)) (Icc t₁ t₂) :=
    hc.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      fun y hy ↦ by
        refine ⟨⟨by simp, by simpa using hy.1, by simpa using hy.2, Or.inl (by simpa using hw)⟩,
          fun hPmem ↦ ?_⟩
        exact (lt_irrefl σ) (by simpa using (hP _ hPmem (mem_closedBall_self (hr _ hPmem).le)).1)
  have hright_split :
      (∫ y : ℝ in t₁..w.im, f (σ + y * I)) + (∫ y : ℝ in w.im..t₂, f (σ + y * I)) =
        ∫ y : ℝ in t₁..t₂, f (σ + y * I) :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hright_cont.mono (Icc_subset_Icc_right hw₂)).intervalIntegrable_of_Icc hw₁)
      ((hright_cont.mono (Icc_subset_Icc_left hw₁)).intervalIntegrable_of_Icc hw₂)
  -- Step 3: Choose a cutoff `X₀` placing every disc of `P` inside `(-X, σ) ×ℂ (w.im, t₂)`.
  obtain ⟨B, hB⟩ := (P.image fun ρ ↦ r ρ - ρ.re).bddAbove
  let X₀ : ℝ := max (-w.re) (max (-σ) B) + 1
  -- Step 4: For `X ≥ X₀`, add the upper rectangle `[−X, σ] ×ℂ [w.im, t₂]` and lower rectangle.
  have hev : ∀ᶠ X : ℝ in atTop,
      I • (∫ y : ℝ in t₁..t₂, f (σ + y * I)) =
        (∫ x : ℝ in σ..w.re, f (x + t₁ * I)) + I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
          (∫ x : ℝ in (-X)..w.re, f (x + w.im * I)) + (∫ x : ℝ in (-X)..σ, f (x + t₂ * I)) +
          I • (∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)) +
          ∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z := by
    filter_upwards [eventually_ge_atTop X₀] with X hX
    have hXw : -X ≤ w.re := by
      have : -w.re ≤ max (-w.re) (max (-σ) B) := le_max_left _ _
      linarith
    have hXσ : -X ≤ σ := hXw.trans hw
    have hup := integral_boundary_rect_eq_sum_circleIntegral hXσ hw₂ hr
      (fun ρ hρ s hs ↦ by
        have h1 := hP ρ hρ hs
        have hdist : ‖s - ρ‖ ≤ r ρ := by simpa [dist_eq_norm] using mem_closedBall.mp hs
        have hre_abs : |s.re - ρ.re| ≤ r ρ :=
          (Complex.abs_re_le_norm (s - ρ)).trans hdist
        have hBρ : r ρ - ρ.re ≤ B := hB (Finset.mem_image_of_mem _ hρ)
        have hB_le : B ≤ max (-w.re) (max (-σ) B) :=
          (le_max_right _ _).trans (le_max_right _ _)
        exact ⟨⟨by linarith [(abs_le.mp hre_abs).1], h1.1⟩, h1.2.1, h1.2.2⟩)
      hsep
      (hc.mono fun s hs ↦ ⟨⟨hs.1.1.2, hw₁.trans hs.1.2.1, hs.1.2.2, Or.inr hs.1.2.1⟩, hs.2⟩)
      (hd.mono fun s hs ↦ ⟨⟨hs.1.1.2, hw₁.trans_lt hs.1.2.1, hs.1.2.2, Or.inr hs.1.2.1⟩, hs.2⟩)
    have hmid_cont : ContinuousOn (fun x : ℝ ↦ f (x + w.im * I)) (Icc (-X) σ) :=
      hc.comp ((continuous_ofReal.add continuous_const)).continuousOn fun x hx ↦ by
        refine ⟨⟨by simpa using hx.2, by simpa using hw₁, by simpa using hw₂, Or.inr (by simp)⟩,
          fun hPmem ↦ ?_⟩
        exact (lt_irrefl w.im)
          (by simpa using (hP _ hPmem (mem_closedBall_self (hr _ hPmem).le)).2.1)
    have hmid_split :
        (∫ x : ℝ in (-X)..w.re, f (x + w.im * I)) + (∫ x : ℝ in w.re..σ, f (x + w.im * I)) =
          ∫ x : ℝ in (-X)..σ, f (x + w.im * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hmid_cont.mono (Icc_subset_Icc_right hw)).intervalIntegrable_of_Icc hXw)
        ((hmid_cont.mono (Icc_subset_Icc_left hXw)).intervalIntegrable_of_Icc hw)
    have hsymm : (∫ x : ℝ in w.re..σ, f (x + t₁ * I)) = -(∫ x : ℝ in σ..w.re, f (x + t₁ * I)) :=
      intervalIntegral.integral_symm σ w.re
    rw [← hright_split, smul_add]
    rw [← hmid_split] at hup
    rw [hsymm] at hlow_zero
    -- Combine `hup` and `hlow_zero`: the shared segment `w.re..σ` at height `w.im` cancels.
    have hcomb := congrArg₂ (· + ·) hup hlow_zero
    rw [add_zero] at hcomb
    rw [← hcomb]
    abel
  -- Step 5: Let `X → ∞`: the left edge vanishes by uniform decay and the rays converge.
  have hleft_tendsto :
      Tendsto (fun X : ℝ ↦ I • ∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)) atTop (𝓝 0) := by
    suffices Tendsto (fun X : ℝ ↦ ∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)) atTop (𝓝 0) by
      simpa only [smul_zero] using (tendsto_const_nhds (x := I)).smul this
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hden : 0 < t₂ - w.im + 1 := by linarith
    have hδ : 0 < ε / (t₂ - w.im + 1) := div_pos hε hden
    have hmem : f ⁻¹' ball 0 (ε / (t₂ - w.im + 1)) ∈
        comap Complex.re atBot ⊓ 𝓟 {s : ℂ | w.im ≤ s.im ∧ s.im ≤ t₂} :=
      hdecay (ball_mem_nhds 0 hδ)
    rw [mem_inf_principal, mem_comap] at hmem
    obtain ⟨S, hS, hSf⟩ := hmem
    obtain ⟨M, hM⟩ := mem_atBot_sets.mp hS
    filter_upwards [eventually_ge_atTop (-M)] with X hX
    rw [dist_zero_right]
    have hbound : ∀ y ∈ Ι w.im t₂, ‖f ((-X : ℝ) + y * I)‖ ≤ ε / (t₂ - w.im + 1) := by
      intro y hy
      rw [uIoc_of_le hw₂] at hy
      have hre : ((-X : ℝ) + y * I).re ≤ M := by simp; linarith
      have him : w.im ≤ ((-X : ℝ) + y * I).im ∧ ((-X : ℝ) + y * I).im ≤ t₂ := by
        simp [hy.1.le, hy.2]
      exact (mem_ball_zero_iff.mp (hSf (hM _ hre) him)).le
    calc ‖∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)‖
        ≤ ε / (t₂ - w.im + 1) * |t₂ - w.im| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ = ε / (t₂ - w.im + 1) * (t₂ - w.im) := by rw [abs_of_nonneg (sub_nonneg.mpr hw₂)]
      _ < ε / (t₂ - w.im + 1) * (t₂ - w.im + 1) :=
          mul_lt_mul_of_pos_left (by linarith) hδ
      _ = ε := div_mul_cancel₀ ε hden.ne'
  have hw_tendsto : Tendsto (fun X : ℝ ↦ ∫ x : ℝ in (-X)..w.re, f (x + w.im * I))
      atTop (𝓝 (∫ x in Iic w.re, f (x + w.im * I))) :=
    intervalIntegral_tendsto_integral_Iic w.re hw_int tendsto_neg_atTop_atBot
  have ht₂_tendsto : Tendsto (fun X : ℝ ↦ ∫ x : ℝ in (-X)..σ, f (x + t₂ * I))
      atTop (𝓝 (∫ x in Iic σ, f (x + t₂ * I))) :=
    intervalIntegral_tendsto_integral_Iic σ ht₂_int tendsto_neg_atTop_atBot
  have hrhs_tendsto :
      Tendsto
        (fun X : ℝ ↦
          (∫ x : ℝ in σ..w.re, f (x + t₁ * I)) + I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
            (∫ x : ℝ in (-X)..w.re, f (x + w.im * I)) + (∫ x : ℝ in (-X)..σ, f (x + t₂ * I)) +
            I • (∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)) +
            ∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z)
        atTop
        (𝓝 ((∫ x : ℝ in σ..w.re, f (x + t₁ * I)) + I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
            (∫ x in Iic w.re, f (x + w.im * I)) + (∫ x in Iic σ, f (x + t₂ * I)) +
          ∑ ρ ∈ P, ∮ z in C(ρ, r ρ), f z)) := by
    simpa only [add_zero] using
      ((((tendsto_const_nhds.sub hw_tendsto).add ht₂_tendsto).add hleft_tendsto).add
        tendsto_const_nhds)
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hrhs_tendsto

end TauCeti.Contour

end
