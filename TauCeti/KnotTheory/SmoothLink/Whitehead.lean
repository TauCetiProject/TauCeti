/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothLink.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# The Whitehead link

The **Whitehead link** is the two-component link obtained from an unknot `U` and a curve `P` in
the solid torus `V = S³ ∖ U` that runs once around `V`, comes back along a parallel strand, and is
closed up by a clasp. Its component `P` has linking number `0` with `U`, yet the two do not come
apart. This file presents it on the geometric side, as a smooth link in `S³ ⊆ ℂ² = ℝ⁴`
(`TauCeti.whiteheadLink`), with explicit formulas, so that constructions read off a link, such as
its exterior and the Dehn surgeries on it, apply to it; the Weeks manifold, for instance, is a
Dehn surgery on the Whitehead link.

The component `0` is the unknot `TauCeti.unknot`, the circle `w = 0` of `S³`. Its complement is
the open solid torus `w ≠ 0`, with coordinates `(z, w / ‖w‖)` in the open unit disc times the
circle; the curve `z = 0` is its core, and the product longitudes `z = const` are its Seifert
longitudes. The component `1` is the **Whitehead curve** `TauCeti.whiteheadCurve`, which sends
`ζ = x + y i` on the unit circle to

`(x / 2 + x y i, √(1 - x² / 4 - x² y²) · exp (3π y i / 2))`.

So its disc coordinate traces the figure eight `ζ ↦ x / 2 + x y i`, which stays in the disc of
radius `1 / √2` (`TauCeti.norm_fst_complexProdToEuclideanFour_symm_whiteheadCurve_sq_le`), and its
angle around the solid torus is `3π y / 2`. Writing `ζ = exp (t i)`, the half `x > 0` of the curve
winds forward through the angle `3π`, from `-3π / 2` to `3π / 2`, and the half `x < 0` winds back,
so the curve has winding number `0` around the solid torus. It is an embedding: the figure eight is
injective except at `ζ = ±i`, whose angles `±3π / 2` differ modulo `2π`.

Its diagram on the annulus, the projection `(z, w) ↦ (Re z, w / ‖w‖)` that forgets `Im z`, has
exactly two crossings, at the pairs `{ζ, conj ζ}` with `Im ζ = ±2 / 3`
(`TauCeti.whiteheadCurve_crossing_iff`); the two halves `Re z > 0` and `Re z < 0` meet nowhere
else, so the band they bound is untwisted. Over a crossing the point higher in `Im z = x y` is the
one with `Im (ζ²) > 0`: at the crossing with `Re ζ > 0` it is the point near `i`, and at the
crossing with `Re ζ < 0` the point near `-i`. So each of the two turning arcs of the curve, through
`ζ = i` and through `ζ = -i`, passes once over the other and once under it: they hook through each
other and the two crossings form a clasp. For the orientation of `S³` as the boundary of the unit
ball of `ℝ⁴` both crossings are positive, whichever way the curve is oriented. This is the diagram
of the untwisted Whitehead double pattern with a positive clasp, and the core of the complementary
solid torus completes it to the Whitehead link. That identification with the link of the knot
tables is read off this diagram; it is not formalized, as there is no isotopy classification of
links here. On its own the Whitehead curve is unknotted in `S³`.

## Main definitions

* `TauCeti.whiteheadCurve`: the Whitehead curve, a smooth embedding of the circle into `S³`.
* `TauCeti.whiteheadLink`: the Whitehead link, the unknot together with the Whitehead curve.

## Main results

* `TauCeti.complexProdToEuclideanFour_symm_whiteheadCurve`, `TauCeti.coe_whiteheadCurve_apply`:
  the formula of the Whitehead curve in the complex coordinates of `ℝ⁴`.
* `TauCeti.norm_fst_complexProdToEuclideanFour_symm_whiteheadCurve_sq_le`: the Whitehead curve
  lies in the solid torus `‖z‖² ≤ 1 / 2`, away from the unknot.
* `TauCeti.whiteheadCurve_crossing_iff`: its diagram on the annulus has exactly two crossings.

## References

* J. H. C. Whitehead, *A certain open manifold whose group is unity*, Quart. J. Math. Oxford 6
  (1935), 268--279, where the link first appears.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Appendix C, the link `5²₁`.
-/

public section

noncomputable section

open Metric Function Set Complex
open scoped Manifold ContDiff Real ComplexConjugate

namespace TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact finrank_real_complex_fact'

/-! ### The curve in `ℂ²` -/

/-- The disc coordinate of the Whitehead curve, `ζ ↦ (Re ζ / 2, Re ζ Im ζ)`. On the unit circle
it traces a figure eight whose only double point is the image `0` of `±i`. -/
private def whiteheadDisc (ζ : ℂ) : ℂ :=
  ((ζ.re / 2 : ℝ) : ℂ) + ((ζ.re * ζ.im : ℝ) : ℂ) * I

/-- The squared modulus of the disc coordinate. -/
private theorem norm_whiteheadDisc_sq (ζ : ℂ) :
    ‖whiteheadDisc ζ‖ ^ 2 = (ζ.re / 2) ^ 2 + (ζ.re * ζ.im) ^ 2 := by
  rw [← normSq_eq_norm_sq, normSq_apply]
  simp [whiteheadDisc]
  ring

/-- On the unit circle the disc coordinate stays in the disc of radius `1 / √2`. -/
private theorem norm_whiteheadDisc_sq_le (z : Circle) : ‖whiteheadDisc z‖ ^ 2 ≤ 1 / 2 := by
  have h := Circle.normSq_coe z
  rw [normSq_apply] at h
  rw [norm_whiteheadDisc_sq]
  nlinarith [sq_nonneg ((z : ℂ).re ^ 2 - (z : ℂ).im ^ 2), sq_nonneg (z : ℂ).im]

/-- The modulus of the second coordinate, making the point of `ℂ²` a unit vector. -/
private def whiteheadRadius (ζ : ℂ) : ℝ :=
  √(1 - (ζ.re / 2) ^ 2 - (ζ.re * ζ.im) ^ 2)

private theorem whiteheadRadius_sq (z : Circle) :
    whiteheadRadius z ^ 2 = 1 - ‖whiteheadDisc z‖ ^ 2 := by
  have h := norm_whiteheadDisc_sq_le z
  rw [norm_whiteheadDisc_sq] at h ⊢
  rw [whiteheadRadius, Real.sq_sqrt (by linarith)]
  ring

private theorem whiteheadRadius_pos (z : Circle) : 0 < whiteheadRadius z := by
  have h := norm_whiteheadDisc_sq_le z
  rw [norm_whiteheadDisc_sq] at h
  rw [whiteheadRadius, Real.sqrt_pos]
  linarith

/-- The angle of the second coordinate, `3π / 2` times `Im ζ`. -/
private def whiteheadAngle (ζ : ℂ) : ℝ :=
  3 * π / 2 * ζ.im

/-- The Whitehead curve in the coordinates of `ℂ²`. -/
private def whiteheadComplexMap (ζ : ℂ) : ℂ × ℂ :=
  (whiteheadDisc ζ, (whiteheadRadius ζ : ℂ) * exp (whiteheadAngle ζ * I))

/-- The Whitehead curve, as a map from the plane to `ℝ⁴`. -/
private def whiteheadMap (ζ : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  complexProdToEuclideanFour (WithLp.toLp 2 (whiteheadComplexMap ζ))

/-- The map to `ℝ⁴` is the map to `ℂ × ℂ` followed by a continuous linear equivalence. -/
private theorem whiteheadMap_eq_comp : whiteheadMap =
    ⇑((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.trans
      complexProdToEuclideanFour.toContinuousLinearEquiv) ∘ whiteheadComplexMap :=
  (rfl)

private theorem norm_whiteheadMap (z : Circle) : ‖whiteheadMap z‖ = 1 := by
  rw [whiteheadMap, LinearIsometryEquiv.norm_map]
  refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 ?_
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [whiteheadComplexMap, whiteheadRadius_sq]

/-! ### Smoothness -/

private theorem contDiff_whiteheadDisc : ContDiff ℝ ∞ whiteheadDisc := by
  have : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := ofRealCLM.contDiff
  have : ContDiff ℝ ∞ Complex.re := reCLM.contDiff
  have : ContDiff ℝ ∞ Complex.im := imCLM.contDiff
  unfold whiteheadDisc
  fun_prop

private theorem contDiffAt_whiteheadComplexMap (z : Circle) :
    ContDiffAt ℝ ∞ whiteheadComplexMap z := by
  have hr : ContDiffAt ℝ ∞ whiteheadRadius z := by
    have : ContDiff ℝ ∞ Complex.re := reCLM.contDiff
    have : ContDiff ℝ ∞ Complex.im := imCLM.contDiff
    refine ContDiffAt.sqrt (by fun_prop) ?_
    have h := norm_whiteheadDisc_sq_le z
    rw [norm_whiteheadDisc_sq] at h
    exact ne_of_gt (by linarith)
  have ha : ContDiff ℝ ∞ whiteheadAngle := by
    have : ContDiff ℝ ∞ Complex.im := imCLM.contDiff
    unfold whiteheadAngle
    fun_prop
  exact contDiff_whiteheadDisc.contDiffAt.prodMk
    ((ofRealCLM.contDiff.contDiffAt.comp _ hr).mul
      ((ofRealCLM.contDiff.comp ha).mul contDiff_const).cexp.contDiffAt)

private theorem contMDiff_whiteheadMap :
    ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞ fun z : Circle ↦ whiteheadMap z := by
  rw [whiteheadMap_eq_comp]
  exact fun z ↦ ((ContinuousLinearEquiv.contDiff _).contDiffAt.comp _
    (contDiffAt_whiteheadComplexMap z)).contMDiffAt.comp z (contMDiff_coe_sphere z)

/-! ### Injectivity -/

/-- The angle `3π / 2 · y` and its negative have the same exponential exactly when `3 y` is an
even integer. -/
private theorem exp_whiteheadAngle_eq_exp_neg_iff (y : ℝ) :
    exp ((3 * π / 2 * y : ℝ) * I) = exp ((3 * π / 2 * -y : ℝ) * I) ↔ ∃ n : ℤ, 3 * y = 2 * n := by
  rw [exp_eq_exp_iff_exists_int]
  refine exists_congr fun n ↦ ?_
  rw [Complex.ext_iff]
  simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_re,
    intCast_re, re_ofNat, im_ofNat, intCast_im, zero_mul, add_zero, mul_im, add_im,
    true_and]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- The Whitehead curve on the circle is injective: the disc coordinate separates all points but
`±i`, and the angles `±3π / 2` separate those. -/
private theorem whiteheadMap_injective : Injective fun z : Circle ↦ whiteheadMap z := by
  intro z w h
  simp only [whiteheadMap_eq_comp, comp_apply] at h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 ((ContinuousLinearEquiv.injective _) h)
  simp only [whiteheadComplexMap] at h1 h2
  have hre : (z : ℂ).re = (w : ℂ).re := by
    have := congrArg Complex.re h1
    simp only [whiteheadDisc, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero] at this
    linarith
  have hreim : (z : ℂ).re * (z : ℂ).im = (w : ℂ).re * (w : ℂ).im := by
    have := congrArg Complex.im h1
    simpa [whiteheadDisc] using this
  have hr : whiteheadRadius z = whiteheadRadius w := by
    rw [whiteheadRadius, whiteheadRadius, hreim, hre]
  have hexp : exp (whiteheadAngle z * I) = exp (whiteheadAngle w * I) :=
    mul_left_cancel₀ (ofReal_ne_zero.2 (whiteheadRadius_pos z).ne') (by rw [h2, hr])
  have hz := Circle.normSq_coe z
  have hw := Circle.normSq_coe w
  rw [normSq_apply] at hz hw
  refine Circle.coe_inj.1 (Complex.ext hre ?_)
  by_cases hx : (z : ℂ).re = 0
  · have hsq : (z : ℂ).im ^ 2 = (w : ℂ).im ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with him | him
    · exact him
    · exfalso
      rw [whiteheadAngle, whiteheadAngle, him] at hexp
      obtain ⟨n, hn⟩ := (exp_whiteheadAngle_eq_exp_neg_iff (w : ℂ).im).1 hexp.symm
      have hw1 : (w : ℂ).im ^ 2 = 1 ^ 2 := by rw [← hre, hx] at hw; linarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hw1 with h | h <;> rw [h] at hn
      · have : (3 : ℤ) = 2 * n := by exact_mod_cast (by linarith : (3 : ℝ) = 2 * n)
        omega
      · have : (-3 : ℤ) = 2 * n := by exact_mod_cast (by linarith : (-3 : ℝ) = 2 * n)
        omega
  · rw [hre] at hreim hx
    exact mul_left_cancel₀ hx hreim

/-! ### The immersion property -/

/-- The derivative of the disc coordinate: `w ↦ (Re w / 2, Re ζ Im w + Re w Im ζ)`. -/
private theorem hasFDerivAt_whiteheadDisc (ζ : ℂ) :
    HasFDerivAt whiteheadDisc
      ((ofRealCLM.comp ((1 / 2 : ℝ) • reCLM)) +
        (ofRealCLM.comp (ζ.re • imCLM + ζ.im • reCLM)).smulRight I) ζ := by
  have h1 := ofRealCLM.hasFDerivAt.comp ζ (reCLM.hasFDerivAt.const_mul (1 / 2 : ℝ))
  have h2 := (ofRealCLM.hasFDerivAt.comp ζ (reCLM.hasFDerivAt.mul imCLM.hasFDerivAt)).mul_const I
  convert h1.add h2 using 1
  · ext ζ'
    simp [whiteheadDisc, div_eq_inv_mul]
  · ext w
    simp
    ring

/-- The derivative of the disc coordinate at `ζ`, applied to `w`. -/
private theorem fderiv_whiteheadDisc_apply (ζ w : ℂ) :
    fderiv ℝ whiteheadDisc ζ w =
      ((w.re / 2 : ℝ) : ℂ) + ((ζ.re * w.im + w.re * ζ.im : ℝ) : ℂ) * I := by
  rw [(hasFDerivAt_whiteheadDisc ζ).fderiv]
  simp [div_eq_inv_mul, mul_comm]

/-- The derivative of the Whitehead curve is injective on the tangent line `(ℝ ζ)ᗮ` of the circle
at `ζ`: already the disc coordinate is. -/
private theorem fderiv_whiteheadMap_eq_zero {z : Circle} {w : ℂ} (hw : inner ℝ (z : ℂ) w = 0)
    (h : fderiv ℝ whiteheadMap z w = 0) : w = 0 := by
  have hF := (contDiffAt_whiteheadComplexMap z).differentiableAt (by simp)
  rw [whiteheadMap_eq_comp, ((ContinuousLinearEquiv.hasFDerivAt _).comp _ hF.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.map_eq_zero_iff] at h
  have h0 := congrArg Prod.fst h
  have hfst : fderiv ℝ whiteheadDisc z = (ContinuousLinearMap.fst ℝ ℂ ℂ).comp
      (fderiv ℝ whiteheadComplexMap z) :=
    ((ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp _ hF.hasFDerivAt).fderiv
  have hd : fderiv ℝ whiteheadDisc z w = 0 := by
    rw [hfst]
    exact h0
  rw [fderiv_whiteheadDisc_apply] at hd
  have hre : w.re = 0 := by simpa using congrArg Complex.re hd
  have him : (z : ℂ).re * w.im + w.re * (z : ℂ).im = 0 := by simpa using congrArg Complex.im hd
  rw [Complex.inner] at hw
  simp only [mul_re, conj_re, conj_im, mul_neg, sub_neg_eq_add, hre, zero_mul, zero_add,
    add_zero] at hw him
  have hz := Circle.normSq_coe z
  rw [normSq_apply] at hz
  have him0 : w.im = 0 := by
    linear_combination (w.im) * hz.symm + (z : ℂ).re * him + (z : ℂ).im * hw
  exact Complex.ext hre him0

/-- The Whitehead curve, as a map into the unit sphere of `ℝ⁴`. -/
private def whiteheadSphereMap (z : Circle) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  ⟨whiteheadMap z, mem_sphere_zero_iff_norm.2 (norm_whiteheadMap z)⟩

private theorem isSmoothEmbedding_whiteheadSphereMap :
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞ whiteheadSphereMap := by
  have hsmooth : ContMDiff (𝓡 1) (𝓡 3) ∞ whiteheadSphereMap :=
    contMDiff_whiteheadMap.codRestrict_sphere _
  have hinj : Injective whiteheadSphereMap := fun z w hzw ↦
    whiteheadMap_injective (congrArg Subtype.val hzw)
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun z ↦ ?_,
    (hsmooth.continuous.isClosedEmbedding hinj).isEmbedding⟩
  refine (hsmooth.contMDiffOn (s := univ).isImmersionAt_iff_injective_mfderiv isOpen_univ
    (mem_univ _) (by simp)).2 ?_
  -- The derivative of the curve in `ℝ⁴` is that of the curve in the sphere followed by the
  -- derivative of the inclusion, so its injectivity suffices.
  have hcomp := mvfderiv_comp (f := whiteheadSphereMap)
    (g := ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin 4))) z
    ((contMDiff_coe_sphere (n := 3) (m := ∞) (whiteheadSphereMap z)).mdifferentiableAt
      (by simp))
    (hsmooth.mdifferentiableAt (by simp))
  suffices h : Injective (mvfderiv (𝓡 1) (Subtype.val ∘ whiteheadSphereMap) z) by
    rw [hcomp, ContinuousLinearMap.coe_comp] at h
    exact h.of_comp
  -- That curve is the plane map `whiteheadMap` restricted to the circle, whose derivative is
  -- injective on the tangent line of the circle. `Circle` is by definition the unit sphere of
  -- `ℂ` with the charted-space structure of that sphere, so the sphere lemmas apply to `z` read as
  -- a point `z'` of the sphere.
  let z' : sphere (0 : ℂ) 1 := z
  have hF : DifferentiableAt ℝ whiteheadMap z := by
    rw [whiteheadMap_eq_comp]
    exact ((ContinuousLinearEquiv.contDiff _).contDiffAt.comp _
      (contDiffAt_whiteheadComplexMap z)).differentiableAt (by simp)
  have hcomp' := mvfderiv_comp (f := ((↑) : sphere (0 : ℂ) 1 → ℂ)) (g := whiteheadMap) z'
    hF.mdifferentiableAt ((contMDiff_coe_sphere (n := 1) (m := ∞) z').mdifferentiableAt (by simp))
  have hsame : mvfderiv (𝓡 1) (Subtype.val ∘ whiteheadSphereMap) z =
      mvfderiv (𝓡 1) (whiteheadMap ∘ ((↑) : sphere (0 : ℂ) 1 → ℂ)) z' :=
    rfl
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  rw [hsame, hcomp'] at hv
  have hv' : fderiv ℝ whiteheadMap z (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z' v) = 0 := by
    rw [mvfderiv_eq_fderiv] at hv
    -- `NormedSpace.fromTangentSpace` identifies the tangent spaces of `ℂ` with `ℂ` by the identity
    -- map, and `mvfderiv` of the inclusion is by definition its `mfderiv` read through it.
    exact hv
  have hmem : mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z' v ∈ (ℝ ∙ (z : ℂ))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := 1) z']
    exact ⟨v, rfl⟩
  have h0 := fderiv_whiteheadMap_eq_zero
    (Submodule.mem_orthogonal_singleton_iff_inner_right.1 hmem) hv'
  exact injective_mvfderiv_subtypeVal_sphere z' (h0.trans (map_zero _).symm)

/-- Two distinct points of the circle have the same real part and the same angle `3π / 2 · Im`
exactly when they are complex conjugates with imaginary parts `±2 / 3`. -/
private theorem re_eq_and_exp_whiteheadAngle_eq_iff {z z' : Circle} (h : z ≠ z') :
    ((z : ℂ).re = (z' : ℂ).re ∧
        exp (whiteheadAngle z * I) = exp (whiteheadAngle z' * I)) ↔
      z' = z⁻¹ ∧ |(z : ℂ).im| = 2 / 3 := by
  have hz := Circle.normSq_coe z
  have hz' := Circle.normSq_coe z'
  rw [normSq_apply] at hz hz'
  have hinv : (((z⁻¹ : Circle) : ℂ)) = conj (z : ℂ) := by rw [Circle.coe_inv_eq_conj]
  constructor
  · rintro ⟨hre, hexp⟩
    have him : (z' : ℂ).im = -(z : ℂ).im := by
      have hsq : (z' : ℂ).im ^ 2 = (z : ℂ).im ^ 2 := by
        linear_combination hz' - hz + ((z : ℂ).re + (z' : ℂ).re) * hre
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with him | him
      · exact absurd (Circle.coe_inj.1 (Complex.ext hre him.symm)) h
      · exact him
    refine ⟨Circle.coe_inj.1 ?_, ?_⟩
    · rw [hinv]
      exact Complex.ext (by simp [hre]) (by simp [him])
    rw [whiteheadAngle, whiteheadAngle, him] at hexp
    obtain ⟨n, hn⟩ := (exp_whiteheadAngle_eq_exp_neg_iff (z : ℂ).im).1 hexp
    have hne : (z : ℂ).im ≠ 0 := fun h0 ↦
      h (Circle.coe_inj.1 (Complex.ext hre (by rw [him, h0, neg_zero])))
    have hn1 : (n : ℝ) < 2 := by nlinarith
    have hn2 : (-2 : ℝ) < n := by nlinarith
    have hn0 : (n : ℝ) ≠ 0 := fun h0 ↦ hne (by linarith)
    have h1 : n < 2 := by exact_mod_cast hn1
    have h2 : -2 < n := by exact_mod_cast hn2
    have h0 : n ≠ 0 := by exact_mod_cast hn0
    have : n = 1 ∨ n = -1 := by omega
    rcases this with rfl | rfl
    · rw [abs_of_pos (by push_cast at hn; linarith)]
      push_cast at hn
      linarith
    · rw [abs_of_neg (by push_cast at hn; linarith)]
      push_cast at hn
      linarith
  · rintro ⟨rfl, habs⟩
    rw [hinv]
    refine ⟨by simp, ?_⟩
    rw [whiteheadAngle, whiteheadAngle, conj_im]
    refine (exp_whiteheadAngle_eq_exp_neg_iff _).2 ?_
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 2 / 3) |>.1 habs with h | h
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨-1, by rw [h]; norm_num⟩

/-! ### The Whitehead link -/

/-- The **Whitehead curve**, the second component of `TauCeti.whiteheadLink`: the smooth embedding
of the circle into the unit sphere of `ℂ² = ℝ⁴` sending `ζ = x + y i` to
`((x / 2) + x y i, √(1 - x² / 4 - x² y²) · exp (3π y i / 2))`. -/
def whiteheadCurve : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  SmoothEmbedding.ofIsSmoothEmbedding whiteheadSphereMap isSmoothEmbedding_whiteheadSphereMap

/-- The Whitehead curve in the complex coordinates of `ℝ⁴ = ℂ²`. -/
theorem complexProdToEuclideanFour_symm_whiteheadCurve (z : Circle) :
    complexProdToEuclideanFour.symm (whiteheadCurve z) =
      WithLp.toLp 2 ((((z : ℂ).re / 2 : ℝ) : ℂ) + (((z : ℂ).re * (z : ℂ).im : ℝ) : ℂ) * I,
        ((√(1 - ((z : ℂ).re / 2) ^ 2 - ((z : ℂ).re * (z : ℂ).im) ^ 2) : ℝ) : ℂ) *
          exp ((3 * π / 2 * (z : ℂ).im : ℝ) * I)) := by
  rw [whiteheadCurve, SmoothEmbedding.ofIsSmoothEmbedding_apply,
    LinearIsometryEquiv.symm_apply_eq]
  -- Both sides are `complexProdToEuclideanFour` applied to the same pair: the right-hand side is
  -- `whiteheadComplexMap z` with `whiteheadDisc`, `whiteheadRadius` and `whiteheadAngle` unfolded.
  rfl

/-- The Whitehead curve as a point of `ℝ⁴`, through the real coordinates of `ℂ²`. -/
@[simp]
theorem coe_whiteheadCurve_apply (z : Circle) :
    (whiteheadCurve z : EuclideanSpace ℝ (Fin 4)) =
      complexProdToEuclideanFour (WithLp.toLp 2
        ((((z : ℂ).re / 2 : ℝ) : ℂ) + (((z : ℂ).re * (z : ℂ).im : ℝ) : ℂ) * I,
          ((√(1 - ((z : ℂ).re / 2) ^ 2 - ((z : ℂ).re * (z : ℂ).im) ^ 2) : ℝ) : ℂ) *
            exp ((3 * π / 2 * (z : ℂ).im : ℝ) * I))) :=
  complexProdToEuclideanFour.symm_apply_eq.1 (complexProdToEuclideanFour_symm_whiteheadCurve z)

/-- The Whitehead curve lies in the solid torus `‖z‖² ≤ 1 / 2` of `S³ ⊆ ℂ²`, the closed complement
of an open tubular neighbourhood of the unknot `TauCeti.unknot`. -/
theorem norm_fst_complexProdToEuclideanFour_symm_whiteheadCurve_sq_le (z : Circle) :
    ‖(complexProdToEuclideanFour.symm (whiteheadCurve z)).fst‖ ^ 2 ≤ 1 / 2 := by
  rw [complexProdToEuclideanFour_symm_whiteheadCurve]
  exact norm_whiteheadDisc_sq_le z

/-- **The crossings of the Whitehead curve.** Project the complement of the unknot in `S³ ⊆ ℂ²`
to the annulus by `(z, w) ↦ (Re z, w / ‖w‖)`. Two distinct points `ζ ≠ ζ'` of the circle are sent
by the Whitehead curve to points with the same projection exactly when `ζ' = ζ⁻¹ = conj ζ` and
`Im ζ = ±2 / 3`. So the diagram of the Whitehead curve on the annulus has exactly two crossings. -/
theorem whiteheadCurve_crossing_iff {z z' : Circle} (h : z ≠ z') :
    ((complexProdToEuclideanFour.symm (whiteheadCurve z)).fst.re =
          (complexProdToEuclideanFour.symm (whiteheadCurve z')).fst.re ∧
        (complexProdToEuclideanFour.symm (whiteheadCurve z)).snd /
            (‖(complexProdToEuclideanFour.symm (whiteheadCurve z)).snd‖ : ℂ) =
          (complexProdToEuclideanFour.symm (whiteheadCurve z')).snd /
            (‖(complexProdToEuclideanFour.symm (whiteheadCurve z')).snd‖ : ℂ)) ↔
      z' = z⁻¹ ∧ |(z : ℂ).im| = 2 / 3 := by
  have hsnd (ζ : Circle) : (complexProdToEuclideanFour.symm (whiteheadCurve ζ)).snd /
      (‖(complexProdToEuclideanFour.symm (whiteheadCurve ζ)).snd‖ : ℂ) =
        exp (whiteheadAngle ζ * I) := by
    have hr := whiteheadRadius_pos ζ
    rw [complexProdToEuclideanFour_symm_whiteheadCurve]
    simp only [WithLp.toLp_snd, norm_mul, norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I,
      mul_one]
    rw [← whiteheadRadius, abs_of_pos hr, mul_div_cancel_left₀ _ (ofReal_ne_zero.2 hr.ne'),
      whiteheadAngle]
  rw [hsnd, hsnd, ← re_eq_and_exp_whiteheadAngle_eq_iff h,
    complexProdToEuclideanFour_symm_whiteheadCurve, complexProdToEuclideanFour_symm_whiteheadCurve]
  simp only [WithLp.toLp_fst, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩

/-- The unknot lies in the plane `w = 0` of `ℂ²`, which the Whitehead curve misses. -/
private theorem disjoint_range_unknot_whiteheadCurve :
    Disjoint (range unknot) (range whiteheadCurve) := by
  refine Set.disjoint_range_iff.2 fun z z' h ↦ ?_
  have h' := congrArg (fun x ↦ (complexProdToEuclideanFour.symm x).snd) (congrArg Subtype.val h)
  simp only [complexProdToEuclideanFour_symm_whiteheadCurve] at h'
  rw [coe_unknot_apply, ← complexToEuclideanFour_apply, ← complexProdToEuclideanFour_toLp_zero,
    LinearIsometryEquiv.symm_apply_apply, WithLp.toLp_snd, WithLp.toLp_snd, ← whiteheadRadius]
    at h'
  exact mul_ne_zero (ofReal_ne_zero.2 (whiteheadRadius_pos z').ne') (exp_ne_zero _) h'.symm

/-- The **Whitehead link** in `S³ ⊆ ℂ²`: its component `0` is the unknot `TauCeti.unknot`, the
circle `w = 0`, and its component `1` is the Whitehead curve `TauCeti.whiteheadCurve`, which lies
in the complementary solid torus, winds around it and back, and clasps itself. -/
def whiteheadLink : SmoothLinkEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) 2 where
  component := ![unknot, whiteheadCurve]
  pairwiseDisjoint_range := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_range_unknot_whiteheadCurve
    · exact disjoint_range_unknot_whiteheadCurve.symm
    · exact absurd rfl hij

/-- The component `0` of the Whitehead link is the unknot. -/
@[simp]
theorem whiteheadLink_zero : whiteheadLink 0 = unknot :=
  (rfl)

/-- The component `1` of the Whitehead link is the Whitehead curve. -/
@[simp]
theorem whiteheadLink_one : whiteheadLink 1 = whiteheadCurve :=
  (rfl)

end TauCeti
