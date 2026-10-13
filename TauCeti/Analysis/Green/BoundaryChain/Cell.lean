/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Relations
public import TauCeti.Analysis.Green.Directional

/-!
# The oriented four-edge boundary of a graph cell

The graph edges are existing paths with affine base coordinate. The two endpoint fibers
are straight segments. Swapping real and imaginary coordinates reverses orientation, so the
horizontal cell uses the negative of the swapped vertical presentation. The endpoint boundary
vanishes, and actual Henstock integrability follows from graph regularity and field continuity.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

namespace BoundaryChain

/-- The signed four-edge boundary of a graph cell, positive when `a ≤ b` and `lower ≤ upper`.
Repeated edges and collapsed endpoint fibers are permitted. -/
def cellBoundary (d : Coordinate) (a b : ℝ) (lower upper : ℝ → ℝ)
    (hl : ContinuousOn lower (uIcc a b)) (hu : ContinuousOn upper (uIcc a b)) : BoundaryChain :=
  d.orientation • quadrilateral (graphPath d lower a b hl)
    (Path.segment (d.graph lower b) (d.graph upper b)) (graphPath d upper a b hu)
    (Path.segment (d.graph lower a) (d.graph upper a))

/-- The four actual parameterized edges, with the coordinate-orientation sign. -/
theorem cellBoundary_def (d : Coordinate) (a b : ℝ) (lower upper : ℝ → ℝ)
    (hl : ContinuousOn lower (uIcc a b)) (hu : ContinuousOn upper (uIcc a b)) :
    cellBoundary d a b lower upper hl hu =
      d.orientation • quadrilateral (graphPath d lower a b hl)
        (Path.segment (d.graph lower b) (d.graph upper b)) (graphPath d upper a b hu)
        (Path.segment (d.graph lower a) (d.graph upper a)) := (rfl)

/-- The cell has zero endpoint boundary. -/
@[simp]
theorem boundary_cellBoundary (d : Coordinate) (a b : ℝ) (lower upper : ℝ → ℝ)
    (hl : ContinuousOn lower (uIcc a b)) (hu : ContinuousOn upper (uIcc a b)) :
    boundary (cellBoundary d a b lower upper hl hu) = 0 := by
  simp [cellBoundary]

/-- The gauge boundary integral of a graph cell is the signed difference of its graph
integrals. The statement also supplies genuine integrability of all four edges. -/
theorem integrable_and_integral_cellBoundary (d : Coordinate) {a b : ℝ}
    {lower upper : ℝ → ℝ} (hab : a ≤ b)
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hdl : ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ lower t)
    (hdu : ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ upper t)
    {P : ℂ → ℝ} (hPl : ContinuousOn P (d.graph lower '' Icc a b))
    (hPu : ContinuousOn P (d.graph upper '' Icc a b)) :
    Integrable d.proj P (cellBoundary d a b lower upper
        (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])) ∧
      integral d.proj P (cellBoundary d a b lower upper
        (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])) =
      d.orientation • ((∫ t in a..b, P (d.graph lower t)) -
        ∫ t in a..b, P (d.graph upper t)) := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hL := graphArc_graphPath d hl hdl ha hb
  have hU := graphArc_graphPath d hu hdu ha hb
  have hR := (NullChain.segment (d := d) (U := ∅)
    (p := d.graph lower b) (q := d.graph upper b) (by simp)).integrable_and_integral_eq_zero
      (P := P) (continuousOn_empty P)
  have hA := (NullChain.segment (d := d) (U := ∅)
    (p := d.graph lower a) (q := d.graph upper a) (by simp)).integrable_and_integral_eq_zero
      (P := P) (continuousOn_empty P)
  constructor
  · unfold cellBoundary
    rw [quadrilateral_def, sub_eq_add_neg, sub_eq_add_neg]
    exact (((hL.integrable hPl).add hR.1).add
      (integrable_neg_iff.mpr (hU.integrable hPu))).add
        (integrable_neg_iff.mpr hA.1) |>.zsmul _
  · simp only [cellBoundary, map_zsmul, quadrilateral_def, map_sub, map_add,
      integral_ofPath, hL.arcIntegral_eq hPl, hU.arcIntegral_eq hPu, Coordinate.proj_graph]
    have hR' := hR.2
    have hA' := hA.2
    simp only [integral_ofPath] at hR' hA'
    rw [hR', hA', add_zero, sub_zero]

/-- Directional Green on the actual oriented boundary of a vertical graph cell. -/
theorem integral_cellBoundary_re {a b : ℝ} {lower upper : ℝ → ℝ} (hab : a ≤ b)
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hdl : ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ lower t)
    (hdu : ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ upper t)
    (hlu : ∀ x ∈ Icc a b, lower x ≤ upper x) {P R : ℂ → ℝ}
    (hP : ContinuousOn P (verticalRegion a b lower upper))
    (hdP : ∀ x ∈ Icc a b, ∀ y ∈ Ioo (lower x) (upper x),
      HasDerivAt (fun y ↦ P ⟨x, y⟩) (R ⟨x, y⟩) y)
    (hR : IntegrableOn R (verticalRegion a b lower upper)) :
    Integrable Complex.reCLM P (cellBoundary .re a b lower upper
        (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])) ∧
      integral Complex.reCLM P (cellBoundary .re a b lower upper
        (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])) =
      -(∫ z in verticalRegion a b lower upper, R z) := by
  have hPl : ContinuousOn P (Coordinate.re.graph lower '' Icc a b) := by
    apply hP.mono
    rintro z ⟨x, hx, rfl⟩
    simpa only [Coordinate.graph_re_apply, mem_verticalRegion] using ⟨hx, le_rfl, hlu x hx⟩
  have hPu : ContinuousOn P (Coordinate.re.graph upper '' Icc a b) := by
    apply hP.mono
    rintro z ⟨x, hx, rfl⟩
    simpa only [Coordinate.graph_re_apply, mem_verticalRegion] using ⟨hx, hlu x hx, le_rfl⟩
  have h := integrable_and_integral_cellBoundary .re hab hl hu hdl hdu hPl hPu
  simp only [Coordinate.proj_re] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hiL := (hPl.comp (Coordinate.re.continuousOn_graph hl)
    (mapsTo_image _ _)).intervalIntegrable_of_Icc (μ := volume) hab
  have hiU := (hPu.comp (Coordinate.re.continuousOn_graph hu)
    (mapsTo_image _ _)).intervalIntegrable_of_Icc (μ := volume) hab
  simp only [Coordinate.orientation_re, one_zsmul]
  simp only [Function.comp_def] at hiL hiU
  rw [← intervalIntegral.integral_sub hiL hiU]
  simpa only [Coordinate.graph_re_apply] using
    integral_graphs_sub_eq_neg_integral_verticalRegion hab hl hu hlu hP hdP hR

/-- Directional Green on the actual oriented boundary of a horizontal graph cell. -/
theorem integral_cellBoundary_im {a b : ℝ} {lower upper : ℝ → ℝ} (hab : a ≤ b)
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hdl : ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ lower t)
    (hdu : ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Ioo a b \ S, DifferentiableAt ℝ upper t)
    (hlu : ∀ y ∈ Icc a b, lower y ≤ upper y) {Q R : ℂ → ℝ}
    (hQ : ContinuousOn Q (horizontalRegion a b lower upper))
    (hdQ : ∀ y ∈ Icc a b, ∀ x ∈ Ioo (lower y) (upper y),
      HasDerivAt (fun x ↦ Q ⟨x, y⟩) (R ⟨x, y⟩) x)
    (hR : IntegrableOn R (horizontalRegion a b lower upper)) :
    Integrable Complex.imCLM Q (cellBoundary .im a b lower upper
        (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])) ∧
      integral Complex.imCLM Q (cellBoundary .im a b lower upper
        (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])) =
      ∫ z in horizontalRegion a b lower upper, R z := by
  have hQl : ContinuousOn Q (Coordinate.im.graph lower '' Icc a b) := by
    apply hQ.mono
    rintro z ⟨y, hy, rfl⟩
    simpa only [Coordinate.graph_im_apply, mem_horizontalRegion] using ⟨hy, le_rfl, hlu y hy⟩
  have hQu : ContinuousOn Q (Coordinate.im.graph upper '' Icc a b) := by
    apply hQ.mono
    rintro z ⟨y, hy, rfl⟩
    simpa only [Coordinate.graph_im_apply, mem_horizontalRegion] using ⟨hy, hlu y hy, le_rfl⟩
  have h := integrable_and_integral_cellBoundary .im hab hl hu hdl hdu hQl hQu
  simp only [Coordinate.proj_im] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hiL := (hQl.comp (Coordinate.im.continuousOn_graph hl)
    (mapsTo_image _ _)).intervalIntegrable_of_Icc (μ := volume) hab
  have hiU := (hQu.comp (Coordinate.im.continuousOn_graph hu)
    (mapsTo_image _ _)).intervalIntegrable_of_Icc (μ := volume) hab
  simp only [Coordinate.orientation_im, neg_smul, one_smul, neg_sub]
  simp only [Function.comp_def] at hiL hiU
  rw [← intervalIntegral.integral_sub hiU hiL]
  simpa only [Coordinate.graph_im_apply] using
    integral_graphs_sub_eq_integral_horizontalRegion hab hl hu hlu hQ hdQ hR

/-- The type-I and type-II presentations of a rectangle have the same actual integer chain.
This supplies a common boundary directly from geometry, before any field is chosen. -/
theorem cellBoundary_rectangle_re_eq_im (a b c e : ℝ) :
    cellBoundary .re a b (fun _ ↦ c) (fun _ ↦ e) continuousOn_const continuousOn_const =
      cellBoundary .im c e (fun _ ↦ a) (fun _ ↦ b) continuousOn_const continuousOn_const := by
  have hre (g : ℝ → ℝ) : Coordinate.re.graph g = fun x ↦ (⟨x, g x⟩ : ℂ) :=
    funext (Coordinate.graph_re_apply g)
  have him (g : ℝ → ℝ) : Coordinate.im.graph g = fun y ↦ (⟨g y, y⟩ : ℂ) :=
    funext (Coordinate.graph_im_apply g)
  simp only [cellBoundary_def, graphPath_const, Coordinate.orientation_re,
    Coordinate.orientation_im, one_smul,
    neg_smul, quadrilateral_def]
  rw [hre (fun _ ↦ c), hre (fun _ ↦ e), him (fun _ ↦ a), him (fun _ ↦ b)]
  abel

/-- The unit square has nonzero circulation for `y dx`: this checks the orientation and
exercises graph certificates and integrability on a nondegenerate cell. -/
theorem integral_cellBoundary_unitSquare :
    integral Complex.reCLM (fun z : ℂ ↦ z.im)
      (cellBoundary .re 0 1 (fun _ ↦ 0) (fun _ ↦ 1)
        continuousOn_const continuousOn_const) = -1 := by
  have hd (c : ℝ) : ∃ S : Set ℝ, S.Countable ∧
      ∀ t ∈ Ioo 0 1 \ S, DifferentiableAt ℝ (fun _ : ℝ ↦ c) t :=
    ⟨∅, countable_empty, fun _ _ ↦ differentiableAt_const _⟩
  have h := integrable_and_integral_cellBoundary .re zero_le_one
    (continuousOn_const (c := (0 : ℝ))) (continuousOn_const (c := (1 : ℝ)))
    (hd 0) (hd 1) (P := fun z : ℂ ↦ z.im)
    Complex.continuous_im.continuousOn Complex.continuous_im.continuousOn
  simpa using h.2

end BoundaryChain
end TauCeti.Green
