/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Herglotz
public import TauCeti.Analysis.Complex.UpperHalfPlane.DiscCoordinate
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# Pick functions in Cayley coordinates

A Pick function is holomorphic on the upper half-plane and has nonnegative imaginary part there.
The Cayley coordinate `z ↦ (z - i) / (z + i)` carries the upper half-plane to the unit disc,
and multiplication by `-i` carries nonnegative imaginary part to nonnegative real part.  The
Herglotz representation on the disc therefore gives

`F z = i · ∫ ζ, (ζ + w) / (ζ - w) ∂μ(ζ) + Re F(i)`,

where `w = (z - i) / (z + i)` and `μ` is a finite positive measure on the unit circle.  The
converse holds as well.  This is the Cayley-coordinate form of the Pick representation; moving
the circle measure to the real line gives the usual Nevanlinna representation.

## Main declarations

* `TauCeti.exists_isFiniteMeasure_eq_I_mul_herglotzTransform_cayley_add`: existence of the
  Cayley-coordinate Herglotz representation of a Pick function.
* `TauCeti.differentiableOn_and_im_nonneg_iff_exists_eq_I_mul_herglotzTransform_cayley_add`:
  the characterization of Pick functions by this representation.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Chapter 6.
-/

public section

noncomputable section

open Complex MeasureTheory Metric Set
open scoped ComplexConjugate

namespace TauCeti

private lemma add_I_ne_zero_of_mem_upperHalfPlane {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    z + I ≠ 0 := by
  let τ : UpperHalfPlane := ⟨z, hz⟩
  let i : UpperHalfPlane := ⟨I, by simp⟩
  simpa only [τ, i, UpperHalfPlane.coe_mk, map_neg, conj_I, sub_neg_eq_add] using
    UpperHalfPlane.coe_sub_conj_ne_zero i τ

private lemma cayley_mem_ball {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    (z - I) / (z + I) ∈ ball (0 : ℂ) 1 := by
  let τ : UpperHalfPlane := ⟨z, hz⟩
  let i : UpperHalfPlane := ⟨I, by simp⟩
  have h := UpperHalfPlane.norm_discCoordinate_lt_one i τ
  rw [UpperHalfPlane.discCoordinate_def] at h
  simpa only [τ, i, UpperHalfPlane.coe_mk, map_neg, conj_I, sub_neg_eq_add,
    mem_ball_zero_iff] using h

/-- **Cayley-coordinate Herglotz representation of a Pick function.** A function holomorphic on
the upper half-plane with nonnegative imaginary part is, after the Cayley coordinate
`z ↦ (z - i) / (z + i)`, `i` times the Herglotz transform of a finite positive measure on the
unit circle, plus the real constant `Re F(i)`. -/
theorem exists_isFiniteMeasure_eq_I_mul_herglotzTransform_cayley_add {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    ∃ μ : Measure Circle, IsFiniteMeasure μ ∧ ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = I * μ.herglotzTransform ((z - I) / (z + I)) + (F I).re := by
  let G : ℂ → ℂ := fun w => -I * F (I * (1 + w) / (1 - w))
  have hG : DifferentiableOn ℂ G (ball 0 1) := by
    intro w hw
    have hmem := bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hw
    have hinner : DifferentiableAt ℂ (fun u : ℂ => I * (1 + u) / (1 - u)) w :=
      (hasDerivAt_I_mul_one_add_div_one_sub
        (ne_of_mem_ball_of_norm_eq_one hw norm_one)).differentiableAt
    have hF' : DifferentiableAt ℂ F (I * (1 + w) / (1 - w)) :=
      (hF _ hmem).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hmem)
    exact ((differentiableAt_const (-I)).mul (hF'.comp w hinner)).differentiableWithinAt
  have hGre : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (G w).re := by
    intro w hw
    simpa [G, mul_re] using him _ (bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hw)
  obtain ⟨μ, hμ, hrep⟩ := exists_isFiniteMeasure_eq_herglotzTransform_add hG hGre
  refine ⟨μ, hμ, fun z hz => ?_⟩
  have hcz := cayley_mem_ball hz
  have h := hrep ((z - I) / (z + I)) hcz
  dsimp only [G] at h
  rw [I_mul_one_add_sub_I_div_add_I_div_one_sub (add_I_ne_zero_of_mem_upperHalfPlane hz)] at h
  have hc : (G 0).im = -(F I).re := by
    simp [G]
  rw [hc] at h
  calc
    F z = I * (-I * F z) := by
      rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
    _ = I * (μ.herglotzTransform ((z - I) / (z + I)) + ((-(F I).re : ℝ) : ℂ) * I) :=
      congrArg (I * ·) h
    _ = I * μ.herglotzTransform ((z - I) / (z + I)) + (F I).re := by
      rw [mul_add]
      congr 1
      rw [← mul_assoc, mul_comm I ((-(F I).re : ℝ) : ℂ), mul_assoc, I_mul_I]
      simp

/-- **Characterization of Pick functions in Cayley coordinates.** A function is holomorphic on
the upper half-plane with nonnegative imaginary part if and only if it is `i` times the Herglotz
transform of a finite positive circle measure in the Cayley coordinate, plus a real constant. -/
theorem differentiableOn_and_im_nonneg_iff_exists_eq_I_mul_herglotzTransform_cayley_add
    {F : ℂ → ℂ} :
    (DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) ↔
      ∃ (μ : Measure Circle) (a : ℝ), IsFiniteMeasure μ ∧
        ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
          F z = I * μ.herglotzTransform ((z - I) / (z + I)) + a := by
  constructor
  · rintro ⟨hF, him⟩
    obtain ⟨μ, hμ, hrep⟩ :=
      exists_isFiniteMeasure_eq_I_mul_herglotzTransform_cayley_add hF him
    exact ⟨μ, (F I).re, hμ, hrep⟩
  · rintro ⟨μ, a, hμ, hrep⟩
    let c : ℂ → ℂ := fun z => (z - I) / (z + I)
    have hc : DifferentiableOn ℂ c UpperHalfPlane.upperHalfPlaneSet := by
      intro z hz
      exact (((differentiableAt_id.sub (differentiableAt_const I)).div
        (differentiableAt_id.add (differentiableAt_const I))
        (add_I_ne_zero_of_mem_upperHalfPlane hz)).differentiableWithinAt)
    have htransform : DifferentiableOn ℂ (fun z => μ.herglotzTransform (c z))
        UpperHalfPlane.upperHalfPlaneSet :=
      (Measure.differentiableOn_herglotzTransform μ).comp hc
        (fun z hz => cayley_mem_ball hz)
    refine ⟨?_, fun z hz => ?_⟩
    · refine DifferentiableOn.congr ?_ (fun z hz => hrep z hz)
      intro z hz
      exact ((differentiableWithinAt_const (c := I)).mul (htransform z hz)).add
        (differentiableWithinAt_const (c := (a : ℂ)))
    · rw [hrep z hz, add_im, mul_im]
      simp only [I_re, zero_mul, I_im, one_mul, ofReal_im, add_zero]
      simpa using Measure.re_herglotzTransform_nonneg μ (cayley_mem_ball hz)

end TauCeti

end
