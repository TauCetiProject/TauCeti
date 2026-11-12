/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Rectangle
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Calculus.Bilinear
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Agreement with existing rectangle formulas

The finite-chain boundary of a rectangle gives its four oriented interval integrals.
This identifies its gauge circulation with Mathlib's rectangle divergence formula and with
Tau Ceti's Green formula for bilinear pairings, including their signs and boundary carriers.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The actual rectangle chain has the usual four oriented interval integrals, with genuine
gauge integrability. This comparison requires only continuity of the two coefficients. -/
theorem integral_rectangle_boundary {a b c e : ℝ} (hab : a < b) (hce : c < e)
    {P Q : ℂ → ℝ} (hP : ContinuousOn P (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e)))
    (hQ : ContinuousOn Q (verticalRegion a b (fun _ ↦ c) (fun _ ↦ e))) :
    let C := (Division.rectangleRe a b c e hab hce).boundary
    BoundaryChain.Integrable Complex.reCLM P C ∧ BoundaryChain.Integrable Complex.imCLM Q C ∧
      BoundaryChain.integral Complex.reCLM P C + BoundaryChain.integral Complex.imCLM Q C =
        ((∫ x in a..b, P ⟨x, c⟩) - ∫ x in a..b, P ⟨x, e⟩) +
          ((∫ y in c..e, Q ⟨b, y⟩) - ∫ y in c..e, Q ⟨a, y⟩) := by
  have hd (k r s : ℝ) : ∃ S : Set ℝ, S.Countable ∧
      ∀ t ∈ Ioo r s \ S, DifferentiableAt ℝ (fun _ : ℝ ↦ k) t :=
    ⟨∅, countable_empty, fun _ _ ↦ differentiableAt_const _⟩
  have hdx := BoundaryChain.integrable_and_integral_cellBoundary .re hab.le
    continuousOn_const continuousOn_const (hd c a b) (hd e a b)
    (hP.mono (by rintro _ ⟨x, hx, rfl⟩; simpa [hx] using hce.le))
    (hP.mono (by rintro _ ⟨x, hx, rfl⟩; simpa [hx] using hce.le))
  have hdy := BoundaryChain.integrable_and_integral_cellBoundary .im hce.le
    continuousOn_const continuousOn_const (hd a c e) (hd b c e)
    (hQ.mono (by rintro _ ⟨y, hy, rfl⟩; simpa [hy] using hab.le))
    (hQ.mono (by rintro _ ⟨y, hy, rfl⟩; simpa [hy] using hab.le))
  dsimp only
  rw [Division.boundary_rectangleRe]
  rw [← BoundaryChain.cellBoundary_rectangle_re_eq_im a b c e] at hdy
  simp only [Coordinate.proj_re, Coordinate.orientation_re, one_smul,
    Coordinate.graph_re_apply] at hdx
  simp only [Coordinate.proj_im, Coordinate.orientation_im, neg_smul, one_smul,
    Coordinate.graph_im_apply, neg_sub] at hdy
  exact ⟨hdx.1, hdy.1, by rw [hdx.2, hdy.2]⟩

/-- Mathlib's rectangle divergence theorem agrees with the actual gauge circulation of
`-g dx + f dy` on the finite-chain rectangle boundary, including countable derivative exceptions. -/
theorem integral_rectangle_boundary_eq_divergence (f g : ℝ × ℝ → ℝ)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ × ℝ)
    (hx : a.1 < b.1) (hy : a.2 < b.2) (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (hcf : ContinuousOn f (Icc a b)) (hcg : ContinuousOn g (Icc a b))
    (hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt f (f' x) x)
    (hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt g (g' x) x)
    (hi : IntegrableOn (fun x ↦ f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    let C := (Division.rectangleRe a.1 b.1 a.2 b.2 hx hy).boundary
    BoundaryChain.Integrable Complex.reCLM (fun z ↦ -g (z.re, z.im)) C ∧
      BoundaryChain.Integrable Complex.imCLM (fun z ↦ f (z.re, z.im)) C ∧
      BoundaryChain.integral Complex.reCLM (fun z ↦ -g (z.re, z.im)) C +
        BoundaryChain.integral Complex.imCLM (fun z ↦ f (z.re, z.im)) C =
          ∫ x in Icc a b, f' x (1, 0) + g' x (0, 1) := by
  have hc := integral_rectangle_boundary hx hy
    (continuousOn_rectangle_of_prod hcg.neg) (continuousOn_rectangle_of_prod hcf)
  simp only [Pi.neg_apply] at hc
  have hd := integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
    f g f' g' a b ⟨hx.le, hy.le⟩ s hs hcf hcg hdf hdg hi
  refine ⟨hc.1, hc.2.1, ?_⟩
  rw [hc.2.2, hd]
  simp only [intervalIntegral.integral_neg]
  ring

/-- Tau Ceti's bilinear rectangle Green formula is the same gauge circulation on the actual
four-path boundary. The pullback coefficients are `B u (∂x u)` and `B u (∂y u)`. -/
theorem integral_rectangle_boundary_eq_bilinear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ) {u : ℝ × ℝ → V} {a b : ℝ × ℝ}
    (hx : a.1 < b.1) (hy : a.2 < b.2)
    (hu : ∀ z ∈ Icc a b, ContDiffAt ℝ 2 u z) :
    let C := (Division.rectangleRe a.1 b.1 a.2 b.2 hx hy).boundary
    let P := fun z : ℂ ↦ B (u (z.re, z.im)) (fderiv ℝ u (z.re, z.im) (1, 0))
    let Q := fun z : ℂ ↦ B (u (z.re, z.im)) (fderiv ℝ u (z.re, z.im) (0, 1))
    BoundaryChain.Integrable Complex.reCLM P C ∧ BoundaryChain.Integrable Complex.imCLM Q C ∧
      BoundaryChain.integral Complex.reCLM P C + BoundaryChain.integral Complex.imCLM Q C =
        ∫ z in Icc a b, B (fderiv ℝ u z (1, 0)) (fderiv ℝ u z (0, 1)) -
          B (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (1, 0)) := by
  have hcoeff (v : ℝ × ℝ) : ContinuousOn (fun z ↦ B (u z) (fderiv ℝ u z v)) (Icc a b) :=
    fun z hz ↦ (B.hasFDerivAt_bilinear_fderiv_apply (hu z hz) v).continuousAt.continuousWithinAt
  have hc := integral_rectangle_boundary hx hy
    (continuousOn_rectangle_of_prod (hcoeff (1, 0)))
    (continuousOn_rectangle_of_prod (hcoeff (0, 1)))
  refine ⟨hc.1, hc.2.1, ?_⟩
  rw [hc.2.2, B.integral_bilinear_fderiv_sub_prod_Icc ⟨hx.le, hy.le⟩ hu]
  ring

end TauCeti.Green
