/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Cell
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Directional Green identities on graph cells

Fubini slices the area integral over a vertical cell into integrals over its vertical fibers.
Area integrability supplies both almost-everywhere fiber integrability and measurability of the
zero-extended fiber integral. Applying the one-dimensional FTC gives the directional Green
identity, requiring only the vertical derivative of the horizontal field component.

The horizontal identity follows by interchanging the coordinates, with its corresponding sign.

## References

* M. Abdulaziz and L. C. Paulson, *Green's Theorem*, Archive of Formal Proofs.
-/

public section

open MeasureTheory Set

namespace TauCeti.Green

variable {E : Type*} [NormedAddCommGroup E]
variable {a b : ℝ} {lower upper : ℝ → ℝ} {R : ℂ → E}

private theorem integrable_indicator_coordinates
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hR : IntegrableOn R (verticalRegion a b lower upper)) :
    Integrable (fun p : ℝ × ℝ ↦ (verticalRegion a b lower upper).indicator R ⟨p.1, p.2⟩) := by
  simpa only [Function.comp_def, Complex.measurableEquivRealProd_symm_apply] using
    (Complex.volume_preserving_equiv_real_prod.symm _).integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding |>.2
        (hR.integrable_indicator (measurableSet_verticalRegion hl hu))

private theorem indicator_coordinates (x y : ℝ) :
    (verticalRegion a b lower upper).indicator R ⟨x, y⟩ =
      (Icc a b).indicator (fun x ↦ (Icc (lower x) (upper x)).indicator
        (fun y ↦ R ⟨x, y⟩) y) x := by
  classical
  simp only [Set.indicator_apply, mem_verticalRegion]
  by_cases hx : x ∈ Icc a b
  · by_cases hy : y ∈ Icc (lower x) (upper x)
    · simp only [hx, hy, true_and, ite_true]
    · simp only [hx, hy, and_false, ite_true, ite_false]
  · simp only [hx, false_and, ite_false]

/-- An area-integrable function is integrable on almost every vertical fiber of a graph cell. -/
theorem ae_integrableOn_verticalRegion_fiber
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hR : IntegrableOn R (verticalRegion a b lower upper)) :
    ∀ᵐ x ∂volume.restrict (Icc a b),
      IntegrableOn (fun y ↦ R ⟨x, y⟩) (Icc (lower x) (upper x)) := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [(integrable_indicator_coordinates hl hu hR).prod_right_ae] with x hx hxab
  apply (integrable_indicator_iff measurableSet_Icc).mp
  convert hx using 1
  ext y
  rw [indicator_coordinates]
  rw [Set.indicator_of_mem hxab]

/-- A continuous graph lying inside a vertical cell has a Bochner-integrable field value along
its base interval. It applies to both boundary graphs
when `lower ≤ upper` on `[a,b]`, without any graph-speed bound. -/
theorem intervalIntegrable_verticalRegion_graph {P : ℂ → E} {graph : ℝ → ℝ} (hab : a ≤ b)
    (hgraph : ContinuousOn graph (Icc a b))
    (hbetween : ∀ x ∈ Icc a b, graph x ∈ Icc (lower x) (upper x))
    (hP : ContinuousOn P (verticalRegion a b lower upper)) :
    IntervalIntegrable (fun x ↦ P ⟨x, graph x⟩) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  exact hP.comp (Complex.equivRealProdCLM.symm.continuous.comp_continuousOn
    (continuousOn_id.prodMk hgraph)) (fun x hx ↦ mem_verticalRegion.mpr ⟨hx, hbetween x hx⟩)

variable [NormedSpace ℝ E]

private theorem integral_indicator_coordinates (x : ℝ) :
    (∫ y, (verticalRegion a b lower upper).indicator R ⟨x, y⟩) =
      (Icc a b).indicator (fun x ↦ ∫ y in Icc (lower x) (upper x), R ⟨x, y⟩) x := by
  simp_rw [indicator_coordinates]
  classical
  by_cases hx : x ∈ Icc a b
  · simp [hx, integral_indicator measurableSet_Icc]
  · simp [hx]

/-- The zero-extended fiber integral is integrable, so no extra fiber-measurability hypothesis is
needed for an area-integrable function. -/
theorem integrable_verticalRegion_fiberIntegral
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hR : IntegrableOn R (verticalRegion a b lower upper)) :
    Integrable ((Icc a b).indicator
      (fun x ↦ ∫ y in Icc (lower x) (upper x), R ⟨x, y⟩)) := by
  convert (integrable_indicator_coordinates hl hu hR).integral_prod_left using 1
  ext x
  exact (integral_indicator_coordinates x).symm

/-- Fubini's slicing formula for the area integral over a vertical graph cell. -/
theorem integral_verticalRegion
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hR : IntegrableOn R (verticalRegion a b lower upper)) :
    (∫ z in verticalRegion a b lower upper, R z) =
      ∫ x in Icc a b, ∫ y in Icc (lower x) (upper x), R ⟨x, y⟩ := by
  rw [← integral_indicator (measurableSet_verticalRegion hl hu)]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).integral_comp'
    (fun z ↦ (verticalRegion a b lower upper).indicator R z)]
  -- Express the transported integral in product coordinates before applying Fubini.
  rw [Measure.volume_eq_prod]
  simp only [Complex.measurableEquivRealProd_symm_apply]
  rw [integral_prod _ (integrable_indicator_coordinates hl hu hR)]
  simp_rw [integral_indicator_coordinates]
  exact integral_indicator measurableSet_Icc

omit [NormedSpace ℝ E] in
/-- Coordinate swap transports integrability from a horizontal cell to its vertical cell. -/
theorem integrableOn_comp_coordinateSwap
    (hR : IntegrableOn R (horizontalRegion a b lower upper)) :
    IntegrableOn (R ∘ Complex.coordinateSwap) (verticalRegion a b lower upper) := by
  rw [← preimage_coordinateSwap_horizontalRegion]
  exact (Complex.measurePreserving_coordinateSwap.integrableOn_comp_preimage
    Complex.coordinateSwap.toMeasurableEquiv.measurableEmbedding).2 hR

/-- Coordinate swap transports the set integral from a vertical cell to its horizontal cell. -/
theorem integral_comp_coordinateSwap_verticalRegion :
    (∫ z in verticalRegion a b lower upper, (R ∘ Complex.coordinateSwap) z) =
      ∫ z in horizontalRegion a b lower upper, R z := by
  simpa only [preimage_coordinateSwap_horizontalRegion, Function.comp_apply] using
    Complex.measurePreserving_coordinateSwap.setIntegral_preimage_emb
      Complex.coordinateSwap.toMeasurableEquiv.measurableEmbedding R
      (horizontalRegion a b lower upper)

/-- Fubini's slicing formula for a horizontal graph cell, obtained by interchanging coordinates. -/
theorem integral_horizontalRegion
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hR : IntegrableOn R (horizontalRegion a b lower upper)) :
    (∫ z in horizontalRegion a b lower upper, R z) =
      ∫ y in Icc a b, ∫ x in Icc (lower y) (upper y), R ⟨x, y⟩ := by
  have hi := integrableOn_comp_coordinateSwap hR
  calc
    _ = ∫ z in verticalRegion a b lower upper, (R ∘ Complex.coordinateSwap) z :=
      integral_comp_coordinateSwap_verticalRegion.symm
    _ = _ := by
      simpa only [Function.comp_apply, Complex.coordinateSwap_apply] using
        integral_verticalRegion hl hu hi

variable [CompleteSpace E]

/-- The directional Green identity on a vertical graph cell. The positively oriented graph
boundary contributes the bottom graph minus the top graph; the vertical sides contribute zero
to `P dx`. Only the vertical derivative is assumed, and no continuity of that derivative is
required. -/
theorem integral_graphs_sub_eq_neg_integral_verticalRegion {P : ℂ → E} (hab : a ≤ b)
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hlu : ∀ x ∈ Icc a b, lower x ≤ upper x)
    (hP : ContinuousOn P (verticalRegion a b lower upper))
    (hdP : ∀ x ∈ Icc a b, ∀ y ∈ Ioo (lower x) (upper x),
      HasDerivAt (fun y ↦ P ⟨x, y⟩) (R ⟨x, y⟩) y)
    (hR : IntegrableOn R (verticalRegion a b lower upper)) :
    (∫ x in a..b, P ⟨x, lower x⟩ - P ⟨x, upper x⟩) =
      -(∫ z in verticalRegion a b lower upper, R z) := by
  have hslice : (fun x ↦ ∫ y in Icc (lower x) (upper x), R ⟨x, y⟩) =ᵐ[
      volume.restrict (Icc a b)] (fun x ↦ P ⟨x, upper x⟩ - P ⟨x, lower x⟩) := by
    filter_upwards [ae_integrableOn_verticalRegion_fiber hl hu hR,
      ae_restrict_mem measurableSet_Icc] with x hx hxab
    have hc : ContinuousOn (fun y ↦ P ⟨x, y⟩) (Icc (lower x) (upper x)) :=
      hP.comp (Complex.equivRealProdCLM.symm.continuous.comp_continuousOn
        (continuousOn_const.prodMk continuousOn_id)) (fun y hy ↦ mem_verticalRegion.mpr ⟨hxab, hy⟩)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hlu x hxab)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (hlu x hxab) hc
      (hdP x hxab) ((intervalIntegrable_iff_integrableOn_Icc_of_le (hlu x hxab)).2 hx)
  rw [integral_verticalRegion hl hu hR, integral_congr_ae hslice,
    ← integral_neg, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards with x
  exact (neg_sub _ _).symm

/-- The directional Green identity on a horizontal graph cell. The positively oriented graph
boundary contributes the right graph minus the left graph; the horizontal sides contribute zero
to `Q dy`. Only the horizontal derivative is assumed. -/
theorem integral_graphs_sub_eq_integral_horizontalRegion {Q : ℂ → E} (hab : a ≤ b)
    (hl : ContinuousOn lower (Icc a b)) (hu : ContinuousOn upper (Icc a b))
    (hlu : ∀ y ∈ Icc a b, lower y ≤ upper y)
    (hQ : ContinuousOn Q (horizontalRegion a b lower upper))
    (hdQ : ∀ y ∈ Icc a b, ∀ x ∈ Ioo (lower y) (upper y),
      HasDerivAt (fun x ↦ Q ⟨x, y⟩) (R ⟨x, y⟩) x)
    (hR : IntegrableOn R (horizontalRegion a b lower upper)) :
    (∫ y in a..b, Q ⟨upper y, y⟩ - Q ⟨lower y, y⟩) =
      ∫ z in horizontalRegion a b lower upper, R z := by
  have hQ' : ContinuousOn (Q ∘ Complex.coordinateSwap) (verticalRegion a b lower upper) :=
    hQ.comp Complex.coordinateSwap.continuous.continuousOn (fun z hz ↦ by
      simpa only [mem_horizontalRegion, Complex.coordinateSwap_apply] using
        mem_verticalRegion.mp hz)
  have hR' := integrableOn_comp_coordinateSwap hR
  have hdQ' : ∀ x ∈ Icc a b, ∀ y ∈ Ioo (lower x) (upper x),
      HasDerivAt (fun y ↦ (Q ∘ Complex.coordinateSwap) ⟨x, y⟩)
        ((R ∘ Complex.coordinateSwap) ⟨x, y⟩) y := by
    intro x hx y hy
    simpa only [Function.comp_apply, Complex.coordinateSwap_apply] using hdQ x hx y hy
  have hv := integral_graphs_sub_eq_neg_integral_verticalRegion hab hl hu hlu hQ' hdQ' hR'
  simp only [Function.comp_apply, Complex.coordinateSwap_apply] at hv
  calc
    (∫ y in a..b, Q ⟨upper y, y⟩ - Q ⟨lower y, y⟩) =
        -(∫ y in a..b, Q ⟨lower y, y⟩ - Q ⟨upper y, y⟩) := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      ext y
      exact (neg_sub _ _).symm
    _ = ∫ z in horizontalRegion a b lower upper, R z := by
      rw [hv, neg_neg]
      simpa only [Function.comp_apply, Complex.coordinateSwap_apply] using
        integral_comp_coordinateSwap_verticalRegion (a := a) (b := b)
        (lower := lower) (upper := upper) (R := R)

end TauCeti.Green
