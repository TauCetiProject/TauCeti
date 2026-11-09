/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Triangle.Basic

/-!
# Green's theorem on the standard triangle

The independently constructed graph divisions and their geometric comparison certificates
give Green's theorem on the genuine convex hull of `0`, `1`, and `I`. The boundary consists
of the three actual straight paths. For fields `C¹` near the triangle, all gauge, curve,
and area integrability hypotheses follow from continuity and compactness.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The directional derivative of a field `C¹` on an open neighborhood of the standard triangle is
integrable on the triangle. -/
private theorem integrableOn_fderiv_standardTriangle {U : Set ℂ} (hU : IsOpen U)
    (hTU : standardTriangle ⊆ U) {F : ℂ → ℝ} (hF : ContDiffOn ℝ 1 F U) (v : ℂ) :
    IntegrableOn (fun z ↦ fderiv ℝ F z v) standardTriangle :=
  (((hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply
    continuousOn_const).mono hTU).integrableOn_compact isCompact_standardTriangle

/-- Along any segment between points of the standard triangle, the circulation integrand of
fields continuous on a neighborhood of the triangle is interval integrable. -/
private theorem intervalIntegrable_circulationFun_segment_standardTriangle {U : Set ℂ}
    (hTU : standardTriangle ⊆ U) {P Q : ℂ → ℝ} (hPc : ContinuousOn P U) (hQc : ContinuousOn Q U)
    {p q : ℂ} (hp : p ∈ standardTriangle) (hq : q ∈ standardTriangle) :
    IntervalIntegrable (circulationFun P Q (Path.segment p q).extend) volume 0 1 := by
  have hconv : Convex ℝ standardTriangle := by
    rw [standardTriangle_def]
    exact convex_convexHull ℝ _
  have hs : segment ℝ p q ⊆ U := (hconv.segment_subset hp hq).trans hTU
  exact intervalIntegrable_circulationFun_segment (hPc.mono hs) (hQc.mono hs)

/-- Every arc in the boundary chain of the standard triangle has an interval integrable
circulation integrand. -/
private theorem intervalIntegrable_circulationFun_of_mem_support_triangle {U : Set ℂ}
    (hTU : standardTriangle ⊆ U) {P Q : ℂ → ℝ} (hPc : ContinuousOn P U) (hQc : ContinuousOn Q U) :
    ∀ γ ∈ (BoundaryChain.triangle 0 1 Complex.I).support,
      IntervalIntegrable (circulationFun P Q γ.2.2.extend) volume 0 1 := by
  classical
  have hsegments {p q : ℂ} (hp : p ∈ standardTriangle) (hq : q ∈ standardTriangle) :=
    intervalIntegrable_circulationFun_segment_standardTriangle hTU hPc hQc hp hq
  have h₀ : (0 : ℂ) ∈ standardTriangle := by simp [mem_standardTriangle]
  have h₁ : (1 : ℂ) ∈ standardTriangle := by simp [mem_standardTriangle]
  have hI : Complex.I ∈ standardTriangle := by simp [mem_standardTriangle]
  intro γ hγ
  rw [BoundaryChain.triangle_def] at hγ
  rcases Finset.mem_union.mp (Finsupp.support_sub hγ) with h | h
  · have hm := Finsupp.support_add h
    simp only [BoundaryChain.support_ofPath, Finset.mem_union, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hsegments h₀ h₁
    · exact hsegments h₁ hI
  · simp only [BoundaryChain.support_ofPath, Finset.mem_singleton] at h
    subst γ
    exact hsegments h₀ hI

/-- Green on the standard triangle for fields `C¹` on any open neighborhood. The three
Bochner curve integrals add the edges from `0` to `1` and from `1` to `I`, and subtract
the edge from `0` to `I`. -/
theorem green_standardTriangle {U : Set ℂ} (hU : IsOpen U) (hTU : standardTriangle ⊆ U)
    {P Q : ℂ → ℝ} (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IntegrableOn (curl P Q) standardTriangle ∧
      curveIntegral (oneForm P Q) (Path.segment 0 1) +
        curveIntegral (oneForm P Q) (Path.segment 1 Complex.I) -
        curveIntegral (oneForm P Q) (Path.segment 0 Complex.I) =
          ∫ z in standardTriangle, curl P Q z := by
  have hPc := hP.continuousOn
  have hQc := hQ.continuousOn
  have hPd (z : ℂ) (hz : z ∈ standardTriangle) : DifferentiableAt ℝ P z :=
    (hP.contDiffAt (hU.mem_nhds (hTU hz))).differentiableAt (by norm_num)
  have hQd (z : ℂ) (hz : z ∈ standardTriangle) : DifferentiableAt ℝ Q z :=
    (hQ.contDiffAt (hU.mem_nhds (hTU hz))).differentiableAt (by norm_num)
  have hRP := integrableOn_fderiv_standardTriangle hU hTU hP Complex.I
  have hRQ := integrableOn_fderiv_standardTriangle hU hTU hQ (1 : ℂ)
  have h := Division.integrableOn_and_linearCombination_curveIntegral_eq_integral_sub
    (Division.standardTriangleDivision .re)
    (Division.standardTriangleDivision .im) (Division.standardTriangle_null_re hTU)
    (Division.standardTriangle_null_im U) hTU hPc hQc
    (RP := fun z ↦ fderiv ℝ P z Complex.I) (RQ := fun z ↦ fderiv ℝ Q z (1 : ℂ))
    (by
      intro K hK x hx y hy
      have hz : (⟨x, y⟩ : ℂ) ∈ standardTriangle :=
        (Division.standardTriangleDivision .re).region_subset hK (by
          rw [GraphCell.region_re, mem_verticalRegion]
          exact ⟨hx, Ioo_subset_Icc_self hy⟩)
      exact (hPd _ hz).hasFDerivAt.hasDerivAt_im_slice)
    (by
      intro K hK y hy x hx
      have hz : (⟨x, y⟩ : ℂ) ∈ standardTriangle :=
        (Division.standardTriangleDivision .im).region_subset hK (by
          rw [GraphCell.region_im, mem_horizontalRegion]
          exact ⟨hy, Ioo_subset_Icc_self hx⟩)
      exact (hQd _ hz).hasFDerivAt.hasDerivAt_re_slice)
    (fun K hK ↦ hRP.mono_set ((Division.standardTriangleDivision .re).region_subset hK))
    (fun K hK ↦ hRQ.mono_set ((Division.standardTriangleDivision .im).region_subset hK))
    (intervalIntegrable_circulationFun_of_mem_support_triangle hTU hPc hQc)
  unfold curl
  simpa only [BoundaryChain.triangle_def, map_sub, map_add,
    BoundaryChain.ofPath_def, Finsupp.linearCombination_single, one_smul] using h

end TauCeti.Green
