/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Orientation.Preserving
public import TauCeti.Analysis.Calculus.DifferentialForm.Stokes.Jordan
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Side
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.JordanCurve

/-!
# Inward normals and the orientation of a Jordan boundary in surface coordinates

In orientation-preserving coordinates on a Riemannian surface, a boundary tangent `T` and its
rotation `J T` have positively oriented images. If a curve with initial velocity `J T` enters
the coordinate region, its simple closed boundary therefore has Jordan sign `+1`
(`IsOrientationPreservingAt.jordanSign_eq_one_of_inward`). Only one regular boundary point is
needed, so corners elsewhere on the boundary are allowed. The normal curve need only have a
right derivative; in particular it can be the inward normal exponential curve.

`IsOrientationPreservingAt.integral_oneForm_of_inward` applies this comparison to Stokes'
formula for a coordinate one-form, yielding the integral of its exterior derivative over the
compact coordinate region with positive sign. No compatibility with a surface volume measure
is asserted here.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 9.
-/

public section

noncomputable section

open Bundle Set MeasureTheory ComplexConjugate Filter
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {o : Manifold.Orientation I M (Fin 2)} {φ : M → ℂ} {c p : ℝ → M}
  {a b t₀ : ℝ} {T : TangentSpace I (c t₀)} {D : Set ℂ}

/-- An inward normal at one regular boundary point fixes the Jordan orientation in
orientation-preserving surface coordinates. The normal is `J T`, with no unit-speed assumption:
`T` need only be nonzero. The inward condition is eventual membership of the normal curve's
coordinate image in the interior of the compact region. -/
theorem IsOrientationPreservingAt.jordanSign_eq_one_of_inward
    (hφ : IsOrientationPreservingAt o
      (model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp [Complex.finrank_real_complex])) φ (c t₀))
    (hT : T ≠ 0)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) I c t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight T))
    (hp0 : p 0 = c t₀)
    (hp : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I p (Ici 0) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (letI := o.fact_finrank_tangentSpace (c t₀)
        (o.orientationAt (c t₀)).rightAngleRotation T)))
    (hγ : AbsolutelyContinuousOnInterval (φ ∘ c) a b)
    (hclosed : (φ ∘ c) a = (φ ∘ c) b) (hinj : InjOn (φ ∘ c) (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hD : IsCompact D)
    (htrace : (φ ∘ c) '' uIcc a b = frontier D)
    (hinward : ∀ᶠ s in 𝓝[>] (0 : ℝ), φ (p s) ∈ interior D) :
    Contour.jordanSign (φ ∘ c) a b = 1 := by
  let := o.fact_finrank_tangentSpace (c t₀)
  have hφd : MDifferentiableAt I 𝓘(ℝ, ℂ) φ (c t₀) := by
    obtain ⟨e, he, _⟩ := (isOrientationPreservingAt_iff _ _ _ _).mp hφ
    exact mdifferentiableAt_of_mfderiv_injective (he ▸ e.injective)
  have hd := hasDerivAt_comp_curve hφd hc
  have hp' : HasDerivWithinAt (φ ∘ p)
      (mvfderiv I φ (c t₀) ((o.orientationAt (c t₀)).rightAngleRotation T)) (Ici 0) 0 := by
    convert hasDerivWithinAt_comp_curve (hp0.symm ▸ hφd) hp using 1
    rw [hp0]
  have hw : 0 < (conj (mvfderiv I φ (c t₀) T) *
      mvfderiv I φ (c t₀) ((o.orientationAt (c t₀)).rightAngleRotation T)).im := by
    apply (hφ.im_conj_mvfderiv_mul_pos_iff _ _).mpr
    simpa only [Orientation.areaForm_rightAngleRotation_right] using real_inner_self_pos.mpr hT
  have hint : (interior D).Nonempty := ⟨_, hinward.exists.choose_spec⟩
  have hJ : IsJordanCurve (frontier D) :=
    htrace ▸ hγ.isJordanCurve_image_uIcc (ht₀.1.trans ht₀.2) hclosed hinj
  have hins : filledHull ((φ ∘ c) '' uIcc a b) \ (φ ∘ c) '' uIcc a b = interior D := by
    rw [htrace, hJ.filledHull_frontier_eq hD hint, self_sdiff_frontier]
  have hpos := (hγ.jordanSign_mul_im_conj_mul_pos_iff_eventually_mem_filledHull_sdiff
    hclosed hinj ht₀ hd (congrArg φ hp0) hp' hw.ne').mpr (by rw [hins]; exact hinward)
  rcases hγ.jordanSign_eq_one_or_neg_one (ht₀.1.trans ht₀.2) hclosed hinj with h | h
  · exact h
  · simp only [h, Int.cast_neg, Int.cast_one, neg_one_mul] at hpos
    exact False.elim (not_lt_of_ge hw.le (neg_pos.mp hpos))

/-- **Stokes with the inward-normal orientation in surface coordinates.** A coordinate one-form
that is `C¹` near a compact Jordan region integrates around its boundary to the integral of its
exterior derivative over the region. An inward normal curve at one regular point, read through
an orientation-preserving surface coordinate map, determines the positive sign. -/
theorem IsOrientationPreservingAt.integral_oneForm_of_inward
    (hφ : IsOrientationPreservingAt o
      (model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp [Complex.finrank_real_complex])) φ (c t₀))
    (hT : T ≠ 0)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) I c t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight T))
    (hp0 : p 0 = c t₀)
    (hp : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I p (Ici 0) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (letI := o.fact_finrank_tangentSpace (c t₀)
        (o.orientationAt (c t₀)).rightAngleRotation T)))
    (hγ : AbsolutelyContinuousOnInterval (φ ∘ c) a b)
    (hclosed : (φ ∘ c) a = (φ ∘ c) b) (hinj : InjOn (φ ∘ c) (Ico a b))
    (ht₀ : t₀ ∈ Ioo a b) (hD : IsCompact D)
    (htrace : (φ ∘ c) '' uIcc a b = frontier D)
    (hinward : ∀ᶠ s in 𝓝[>] (0 : ℝ), φ (p s) ∈ interior D)
    {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hregion : D ⊆ U) (hω : ContDiffOn ℝ 1 ω U) :
    IntervalIntegrable (fun t ↦ ω (φ (c t)) fun _ ↦ deriv (φ ∘ c) t) volume a b ∧
      IntegrableOn (fun z ↦ extDeriv ω z ![1, Complex.I]) D ∧
      (∫ t in a..b, ω (φ (c t)) fun _ ↦ deriv (φ ∘ c) t) =
        ∫ z in D, extDeriv ω z ![1, Complex.I] := by
  have hsign := hφ.jordanSign_eq_one_of_inward hT hc hp0 hp hγ hclosed hinj ht₀ hD
    htrace hinward
  have hint : (interior D).Nonempty := ⟨_, hinward.exists.choose_spec⟩
  simpa only [hsign, Int.cast_one, one_mul, Function.comp_apply] using
    integral_oneForm_of_isCompact hD hint (ht₀.1.trans ht₀.2) hγ hclosed hinj htrace hU hregion hω

end TauCeti.Manifold.Orientation
