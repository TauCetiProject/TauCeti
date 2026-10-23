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
  have hRP : IntegrableOn (fun z ↦ fderiv ℝ P z Complex.I) standardTriangle :=
    (((hP.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply
      continuousOn_const).mono hTU).integrableOn_compact
      isCompact_standardTriangle
  have hRQ : IntegrableOn (fun z ↦ fderiv ℝ Q z (1 : ℂ)) standardTriangle :=
    (((hQ.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply
      continuousOn_const).mono hTU).integrableOn_compact
      isCompact_standardTriangle
  have hsegments {p q : ℂ} (hp : p ∈ standardTriangle) (hq : q ∈ standardTriangle) :
      IntervalIntegrable (circulationFun P Q (Path.segment p q).extend) volume 0 1 := by
    have hconv : Convex ℝ standardTriangle := by
      rw [standardTriangle_def]
      exact convex_convexHull ℝ _
    have hs : segment ℝ p q ⊆ U := (hconv.segment_subset hp hq).trans hTU
    exact intervalIntegrable_circulationFun_segment (hPc.mono hs) (hQc.mono hs)
  have h₀ : (0 : ℂ) ∈ standardTriangle := by simp [mem_standardTriangle]
  have h₁ : (1 : ℂ) ∈ standardTriangle := by simp [mem_standardTriangle]
  have hI : Complex.I ∈ standardTriangle := by simp [mem_standardTriangle]
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
    (by
      classical
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
        exact hsegments h₀ hI)
  unfold curl
  simpa only [BoundaryChain.triangle_def, map_sub, map_add,
    BoundaryChain.ofPath_def, Finsupp.linearCombination_single, one_smul] using h

end TauCeti.Green
