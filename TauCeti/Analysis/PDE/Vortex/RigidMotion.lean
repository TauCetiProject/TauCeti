/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
public import TauCeti.Analysis.PDE.Vortex.Symmetry
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Complex.Isometry
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rigid motions of the plane and the `H¹` realization of the vortex operator

The orientation-preserving isometries `z ↦ u z + a` of the plane, `u` on the unit circle, act on
plane vortex fields by `rotateField u ∘ translateField a`
(`TauCeti.Analysis.PDE.Vortex.Symmetry`), and the gauge-fixed operator `L_x = d₀* ⊕ d₁`
intertwines this action with `rotateTarget u ∘ translateField a` on its target `ℝ ⊕ ℝ ⊕ ℂ`. This
file proves the same law for the bounded realization

`TauCeti.Vortex.sobolevGaugeFixedOperator c : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`

of `L_x` with `L∞` coefficient `c`, on which the Fredholm theory of plane vortices is built. The
motion acts by continuous linear equivalences

* `TauCeti.Vortex.coefficientMotion u a` on the `L∞` classes of fields,
* `TauCeti.Vortex.variationMotion u a` on `H¹(ℂ)⁴`, and
* `TauCeti.Vortex.targetMotion u a` on `L²(ℂ; ℝ⁴)`,

each composing with the motion and rotating the values by `fieldRotation u` or `targetRotation u`
(`TauCeti.Vortex.coeFn_coefficientMotion`, `TauCeti.Vortex.value_variationMotion_ae`,
`TauCeti.Vortex.coeFn_targetMotion`). Their inverses are the motions by the inverse isometry
`z ↦ u⁻¹ z - u⁻¹ a`.

The realization at the moved coefficient is the conjugate of the realization at `c`:
`L_{g·c} (g·y) = g·(L_c y)`
(`TauCeti.Vortex.sobolevGaugeFixedOperator_coefficientMotion_apply`). Consequently the kernel at
the moved coefficient is the moved kernel, and surjectivity, the Fredholm property and the index
are unchanged. The moved class of a field `x` is the class of `rotateField u (translateField a x)`
(`TauCeti.Vortex.coeFn_coefficientMotion_of_ae_eq`), so these laws transport the Fredholm theory
of the realization at a vortex to all of its translates and rotations.

## Main definitions

* `TauCeti.Vortex.coefficientMotion`, `TauCeti.Vortex.variationMotion`,
  `TauCeti.Vortex.targetMotion`: the motion `z ↦ u z + a` on coefficients, variations and targets.

## Main results

* `TauCeti.Vortex.sobolevGaugeFixedOperator_coefficientMotion_apply`,
  `TauCeti.Vortex.sobolevGaugeFixedOperator_coefficientMotion`: the intertwining law.
* `TauCeti.Vortex.ker_sobolevGaugeFixedOperator_coefficientMotion`,
  `TauCeti.Vortex.surjective_sobolevGaugeFixedOperator_coefficientMotion_iff`,
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_coefficientMotion_iff`,
  `TauCeti.Vortex.index_sobolevGaugeFixedOperator_coefficientMotion`: its consequences.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal ComplexConjugate

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-- The rigid motion `z ↦ u z + a` of the plane. -/
private def motion (u : Circle) (a : ℂ) : ℂ ≃ᵃⁱ[ℝ] ℂ :=
  AffineIsometryEquiv.mk' (fun z ↦ u * z + a) (rotation u) 0 fun z ↦ by simp

@[simp] private theorem motion_apply (u : Circle) (a z : ℂ) : motion u a z = u * z + a := (rfl)

@[simp] private theorem linearIsometryEquiv_motion (u : Circle) (a : ℂ) :
    (motion u a).linearIsometryEquiv = rotation u := by
  simp [motion]

private theorem measurePreserving_top (g : ℂ ≃ᵃⁱ[ℝ] ℂ) : MeasurePreserving g μ⊤ μ⊤ := by
  simpa using g.measurePreserving

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Precomposition with an affine isometry `g` followed by the pointwise isometry `R`, on `Lᵖ`. -/
private def lpMotion (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤ :=
  (R.toContinuousLinearEquiv :
      EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)).compLpL p μ⊤ ∘L
    (Lp.compMeasurePreservingₗᵢ ℝ g (measurePreserving_top g)).toContinuousLinearMap

private theorem lpMotion_apply (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (f : Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤) :
    lpMotion p R g f = (R.toContinuousLinearEquiv :
      EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)).compLp
        (Lp.compMeasurePreserving g (measurePreserving_top g) f) := (rfl)

private theorem coeFn_lpMotion (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (f : Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤) :
    ⇑(lpMotion p R g f) =ᵐ[μ⊤] fun z ↦ R (f (g z)) := by
  rw [lpMotion_apply]
  filter_upwards [ContinuousLinearMap.coeFn_compLp (R.toContinuousLinearEquiv :
      EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
      (Lp.compMeasurePreserving g (measurePreserving_top g) f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_top g)] with z h₁ h₂
  rw [h₁, h₂, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    Function.comp_apply]

/-- The pointwise isometry `R.symm` after `g.symm` undoes `R` after `g`. -/
private theorem lpMotion_symm_lpMotion
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤) :
    lpMotion p R.symm g.symm (lpMotion p R g f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_lpMotion R.symm g.symm (lpMotion p R g f),
    (measurePreserving_top g.symm).quasiMeasurePreserving.ae_eq_comp (coeFn_lpMotion R g f)]
    with z h₁ h₂
  rw [h₁]
  simp only [Function.comp_apply] at h₂
  rw [h₂]
  simp

private theorem lpMotion_lpMotion_symm
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤) :
    lpMotion p R g (lpMotion p R.symm g.symm f) = f := by
  simpa using lpMotion_symm_lpMotion (p := p) R.symm g.symm f

/-- `lpMotion p R g` as a continuous linear equivalence. -/
private def lpMotionEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤ ≃L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤ :=
  .equivOfInverse (lpMotion p R g) (lpMotion p R.symm g.symm) (lpMotion_symm_lpMotion R g)
    (lpMotion_lpMotion_symm R g)

/-- Precomposition of the four coordinates with an affine isometry `g` followed by the pointwise
isometry `R`, on `H¹(ℂ)⁴`. -/
private def w1pMotion (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  ContinuousLinearMap.pi fun i ↦ ∑ k, R (EuclideanSpace.single k 1) i •
    (W1p.compAffineIsometryEquivL g rfl).comp (ContinuousLinearMap.proj k)

private theorem w1pMotion_apply (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (i : Fin 4) :
    w1pMotion R g y i =
      ∑ k, R (EuclideanSpace.single k 1) i • W1p.compAffineIsometryEquivL g rfl (y k) := by
  simp [w1pMotion]

private theorem value_w1pMotion_ae (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z ∂μ⊤, (WithLp.toLp 2 fun i ↦ W1p.value (w1pMotion R g y i) z :
      EuclideanSpace ℝ (Fin 4)) = R (WithLp.toLp 2 fun k ↦ W1p.value (y k) (g z)) := by
  -- The coordinates of `R v` in terms of the images of the standard basis.
  have hR (v : EuclideanSpace ℝ (Fin 4)) (i : Fin 4) :
      R v i = ∑ k, R (EuclideanSpace.single k 1) i * v k := by
    have hv : v = ∑ k, v k • EuclideanSpace.single k (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp [mul_comm]
  have hs (i : Fin 4) := W1p.value_finsetSum_ae (mu := volume) (Omega := ⊤) (p := 2) Finset.univ
    fun k ↦ R (EuclideanSpace.single k 1) i • W1p.compAffineIsometryEquivL g rfl (y k)
  have hc (i k : Fin 4) := W1p.value_smul_ae (R (EuclideanSpace.single k 1) i)
    (W1p.compAffineIsometryEquivL g (U := ⊤) (V := ⊤) (p := 2) rfl (y k))
  filter_upwards [ae_all_iff.2 hs, ae_all_iff.2 fun i ↦ ae_all_iff.2 (hc i),
    ae_all_iff.2 fun k ↦ W1p.value_compAffineIsometryEquivL_ae g rfl (y k)] with z h₁ h₂ h₃
  ext i
  rw [hR, PiLp.toLp_apply, w1pMotion_apply, h₁ i]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [h₂ i k, Pi.smul_apply, h₃ k, smul_eq_mul]

private theorem gradient_w1pMotion_ae
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z ∂μ⊤, ∀ i, W1p.gradient (w1pMotion R g y i) z =
      ∑ k, R (EuclideanSpace.single k 1) i •
        g.linearIsometryEquiv.symm (W1p.gradient (y k) (g z)) := by
  have hs (i : Fin 4) := Lp.coeFn_fun_finsetSum (μ := μ⊤) Finset.univ fun k ↦
    R (EuclideanSpace.single k 1) i •
      W1p.gradient (W1p.compAffineIsometryEquivL g (U := ⊤) (V := ⊤) (p := 2) rfl (y k))
  have hc (i k : Fin 4) := Lp.coeFn_smul (R (EuclideanSpace.single k 1) i)
    (W1p.gradient (W1p.compAffineIsometryEquivL g (U := ⊤) (V := ⊤) (p := 2) rfl (y k)))
  filter_upwards [ae_all_iff.2 hs, ae_all_iff.2 fun i ↦ ae_all_iff.2 (hc i),
    ae_all_iff.2 fun k ↦ W1p.gradient_compAffineIsometryEquivL_ae g rfl (y k)] with z h₁ h₂ h₃ i
  rw [w1pMotion_apply, W1p.gradient_sum]
  simp only [W1p.gradient_smul]
  rw [h₁ i]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [h₂ i k, Pi.smul_apply, h₃ k]

private theorem w1pMotion_symm_w1pMotion
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    w1pMotion R.symm g.symm (w1pMotion R g y) = y := by
  funext i
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_w1pMotion_ae R.symm g.symm (w1pMotion R g y),
    (measurePreserving_top g.symm).quasiMeasurePreserving.ae (value_w1pMotion_ae R g y)]
    with z h₁ h₂
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v i) h₁
  simp only at h
  rw [h, h₂]
  simp

private theorem w1pMotion_w1pMotion_symm
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    w1pMotion R g (w1pMotion R.symm g.symm y) = y := by
  simpa using w1pMotion_symm_w1pMotion R.symm g.symm y

/-- `w1pMotion R g` as a continuous linear equivalence. -/
private def w1pMotionEquiv (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) ≃L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  .equivOfInverse (w1pMotion R g) (w1pMotion R.symm g.symm) (w1pMotion_symm_w1pMotion R g)
    (w1pMotion_w1pMotion_symm R g)

/-- The first-order part of `L_x` intertwines the rotation of the gradients of the coordinates
with `targetRotation u`: the gradient of a coordinate composed with `z ↦ u z + a` is `u⁻¹` times
the gradient at the image point, and the coordinates are mixed by `fieldRotation u`. -/
private theorem gaugeFixedFirstOrder_fieldRotation (u : Circle) (G : Fin 4 → ℂ) :
    gaugeFixedFirstOrder (fun i ↦ ∑ k, fieldRotation u (EuclideanSpace.single k 1) i •
      (conj (u : ℂ) * G k)) = targetRotation u (gaugeFixedFirstOrder G) := by
  have hn := Circle.re_sq_add_im_sq u
  ext i
  fin_cases i <;> simp [Fin.sum_univ_four, Complex.inner]
  · linear_combination ((G 0).re + (G 1).im) * hn
  · linear_combination ((G 0).im - (G 1).re) * hn
  · ring
  · ring

private theorem lpMotionEquiv_apply (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (f : Lp (EuclideanSpace ℝ (Fin 4)) p μ⊤) :
    lpMotionEquiv p R g f = lpMotion p R g f := (rfl)

private theorem w1pMotionEquiv_apply
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) : w1pMotionEquiv R g y = w1pMotion R g y := (rfl)

private theorem motion_linearIsometryEquiv_symm_apply (u : Circle) (a w : ℂ) :
    (motion u a).linearIsometryEquiv.symm w = conj (u : ℂ) * w := by
  rw [linearIsometryEquiv_motion, rotation_symm, rotation_apply, Circle.coe_inv_eq_conj]

/-! ### The rigid motions of the plane on the Sobolev realization -/

/-- **The rigid motion `z ↦ u z + a` on the `L∞` classes of fields.** It sends the class of a
field `x` to the class of `rotateField u (translateField a x)`, the pullback of `x` by the motion
(`coeFn_coefficientMotion`). These are the coefficients of `sobolevGaugeFixedOperator`. -/
def coefficientMotion (u : Circle) (a : ℂ) :
    Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ ≃L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ :=
  lpMotionEquiv ∞ (fieldRotation u) (motion u a)

/-- **The rigid motion `z ↦ u z + a` on the `L²` targets of `sobolevGaugeFixedOperator`.** It
sends the class of `η` to the class of `rotateTarget u (translateField a η)`
(`coeFn_targetMotion`). -/
def targetMotion (u : Circle) (a : ℂ) :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ≃L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  lpMotionEquiv 2 (targetRotation u) (motion u a)

/-- **The rigid motion `z ↦ u z + a` on `H¹` variations.** It acts on the four coordinates in
`H¹(ℂ) = W^{1,2}(ℂ)` as `rotateField u ∘ translateField a` acts on their values
(`value_variationMotion_ae`): each coordinate is composed with the motion, and the connection
coordinates are mixed by `fieldRotation u`. -/
def variationMotion (u : Circle) (a : ℂ) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) ≃L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  w1pMotionEquiv (fieldRotation u) (motion u a)

/-- The coefficient moved by `z ↦ u z + a` is the rotated translate of the coefficient. -/
theorem coeFn_coefficientMotion (u : Circle) (a : ℂ) (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    ⇑(coefficientMotion u a c) =ᵐ[μ⊤] rotateField u (translateField a c) := by
  filter_upwards [coeFn_lpMotion (fieldRotation u) (motion u a) c] with z hz
  rw [coefficientMotion, lpMotionEquiv_apply, hz, rotateField_apply_eq_fieldRotation,
    translateField_apply, motion_apply]

/-- If the coefficient `c` is the class of a field `x`, the moved coefficient is the class of
`rotateField u (translateField a x)`. -/
theorem coeFn_coefficientMotion_of_ae_eq {c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hcx : c =ᵐ[μ⊤] x) (u : Circle) (a : ℂ) :
    ⇑(coefficientMotion u a c) =ᵐ[μ⊤] rotateField u (translateField a x) := by
  filter_upwards [coeFn_coefficientMotion u a c,
    (measurePreserving_top (motion u a)).quasiMeasurePreserving.ae hcx] with z h₁ h₂
  rw [h₁, rotateField_apply_eq_fieldRotation, rotateField_apply_eq_fieldRotation,
    translateField_apply, translateField_apply, ← motion_apply, h₂]

/-- The target moved by `z ↦ u z + a` is the rotated translate of the target. -/
theorem coeFn_targetMotion (u : Circle) (a : ℂ) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    ⇑(targetMotion u a f) =ᵐ[μ⊤] rotateTarget u (translateField a f) := by
  filter_upwards [coeFn_lpMotion (targetRotation u) (motion u a) f] with z hz
  rw [targetMotion, lpMotionEquiv_apply, hz, rotateTarget_apply_eq_targetRotation,
    translateField_apply, motion_apply]

/-- The values of a variation moved by `z ↦ u z + a` are the rotated translates of its values. -/
theorem value_variationMotion_ae (u : Circle) (a : ℂ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z ∂μ⊤, (WithLp.toLp 2 fun j ↦ W1p.value (variationMotion u a y j) z :
      EuclideanSpace ℝ (Fin 4)) =
        rotateField u (translateField a fun w ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) w) z := by
  filter_upwards [value_w1pMotion_ae (fieldRotation u) (motion u a) y] with z hz
  rw [variationMotion, w1pMotionEquiv_apply, hz, rotateField_apply_eq_fieldRotation,
    translateField_apply, motion_apply]

private theorem motion_symm (u : Circle) (a : ℂ) :
    (motion u a).symm = motion u⁻¹ (-((u : ℂ)⁻¹ * a)) := by
  ext z
  rw [AffineIsometryEquiv.symm_apply_eq, motion_apply, motion_apply, Circle.coe_inv]
  field_simp [Circle.coe_ne_zero u]
  ring

private theorem lpMotionEquiv_symm (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) : (lpMotionEquiv p R g).symm = lpMotionEquiv p R.symm g.symm := by
  refine ContinuousLinearEquiv.ext (funext fun f ↦ ?_)
  rw [lpMotionEquiv_apply, lpMotionEquiv, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply]

private theorem w1pMotionEquiv_symm
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ) :
    (w1pMotionEquiv R g).symm = w1pMotionEquiv R.symm g.symm := by
  refine ContinuousLinearEquiv.ext (funext fun y ↦ ?_)
  rw [w1pMotionEquiv_apply, w1pMotionEquiv, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply]

/-- The inverse of the motion `z ↦ u z + a` on coefficients is the motion by the inverse
isometry `z ↦ u⁻¹ z - u⁻¹ a`. -/
theorem coefficientMotion_symm (u : Circle) (a : ℂ) :
    (coefficientMotion u a).symm = coefficientMotion u⁻¹ (-((u : ℂ)⁻¹ * a)) := by
  rw [coefficientMotion, coefficientMotion, lpMotionEquiv_symm, fieldRotation_symm, motion_symm]

/-- The inverse of the motion `z ↦ u z + a` on targets is the motion by the inverse isometry
`z ↦ u⁻¹ z - u⁻¹ a`. -/
theorem targetMotion_symm (u : Circle) (a : ℂ) :
    (targetMotion u a).symm = targetMotion u⁻¹ (-((u : ℂ)⁻¹ * a)) := by
  rw [targetMotion, targetMotion, lpMotionEquiv_symm, targetRotation_symm, motion_symm]

/-- The inverse of the motion `z ↦ u z + a` on variations is the motion by the inverse isometry
`z ↦ u⁻¹ z - u⁻¹ a`. -/
theorem variationMotion_symm (u : Circle) (a : ℂ) :
    (variationMotion u a).symm = variationMotion u⁻¹ (-((u : ℂ)⁻¹ * a)) := by
  rw [variationMotion, variationMotion, w1pMotionEquiv_symm, fieldRotation_symm, motion_symm]

/-- **Rigid motions intertwine the `H¹` realization of `L_x`.** Moving the coefficient and the
variation by `z ↦ u z + a` moves the image: `L_{g·c} (g·y) = g·(L_c y)`, where the motion acts on
coefficients by `coefficientMotion`, on variations by `variationMotion` and on targets by
`targetMotion`. -/
theorem sobolevGaugeFixedOperator_coefficientMotion_apply (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevGaugeFixedOperator (coefficientMotion u a c) (variationMotion u a y) =
      targetMotion u a (sobolevGaugeFixedOperator c y) := by
  refine Lp.ext ?_
  rw [coefficientMotion, variationMotion, targetMotion, lpMotionEquiv_apply, w1pMotionEquiv_apply,
    lpMotionEquiv_apply]
  filter_upwards [sobolevGaugeFixedOperator_apply_ae (lpMotion ∞ (fieldRotation u) (motion u a) c)
      (w1pMotion (fieldRotation u) (motion u a) y),
    coeFn_lpMotion (fieldRotation u) (motion u a) c,
    coeFn_lpMotion (targetRotation u) (motion u a) (sobolevGaugeFixedOperator c y),
    (measurePreserving_top (motion u a)).quasiMeasurePreserving.ae
      (sobolevGaugeFixedOperator_apply_ae c y),
    value_w1pMotion_ae (fieldRotation u) (motion u a) y,
    gradient_w1pMotion_ae (fieldRotation u) (motion u a) y] with z h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, h₃, h₄, h₅, map_add, ← gaugeFixedZerothOrder_fieldRotation]
  refine congrArg (· + _) ((congrArg gaugeFixedFirstOrder (funext fun i ↦ ?_)).trans
    (gaugeFixedFirstOrder_fieldRotation u fun k ↦ W1p.gradient (y k) (motion u a z)))
  rw [h₆ i]
  simp only [motion_linearIsometryEquiv_symm_apply]

/-- **Rigid motions conjugate the `H¹` realization of `L_x`.** The realization at the coefficient
moved by `z ↦ u z + a` is the realization at `c` conjugated by the motions of variations and
targets. -/
theorem sobolevGaugeFixedOperator_coefficientMotion (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    sobolevGaugeFixedOperator (coefficientMotion u a c) =
      ((targetMotion u a : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] _).comp
        (sobolevGaugeFixedOperator c)).comp
          ((variationMotion u a).symm : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] _) := by
  ext1 y
  simpa using sobolevGaugeFixedOperator_coefficientMotion_apply u a c ((variationMotion u a).symm y)

/-- The kernel of the realization at a moved coefficient is the moved kernel. -/
theorem ker_sobolevGaugeFixedOperator_coefficientMotion (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (sobolevGaugeFixedOperator (coefficientMotion u a c)).ker =
      (sobolevGaugeFixedOperator c).ker.map ((variationMotion u a :
        (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
          (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →ₗ[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, sobolevGaugeFixedOperator_coefficientMotion]
  refine ⟨fun h ↦ ⟨(variationMotion u a).symm y, by simpa using h, by simp⟩, ?_⟩
  rintro ⟨y₀, hy₀, rfl⟩
  simpa using hy₀

/-- The realization at a moved coefficient is onto exactly when the realization at `c` is. -/
theorem surjective_sobolevGaugeFixedOperator_coefficientMotion_iff (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    Function.Surjective (sobolevGaugeFixedOperator (coefficientMotion u a c)) ↔
      Function.Surjective (sobolevGaugeFixedOperator c) := by
  rw [sobolevGaugeFixedOperator_coefficientMotion]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    EquivLike.comp_surjective, EquivLike.surjective_comp]

/-- The realization at a moved coefficient is Fredholm exactly when the realization at `c` is. -/
theorem isFredholm_sobolevGaugeFixedOperator_coefficientMotion_iff (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (sobolevGaugeFixedOperator (coefficientMotion u a c)).IsFredholm ↔
      (sobolevGaugeFixedOperator c).IsFredholm := by
  rw [sobolevGaugeFixedOperator_coefficientMotion]
  simp

/-- Rigid motions preserve the index of the realization. -/
theorem index_sobolevGaugeFixedOperator_coefficientMotion (u : Circle) (a : ℂ)
    (c : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (sobolevGaugeFixedOperator (coefficientMotion u a c)).index =
      (sobolevGaugeFixedOperator c).index := by
  rw [sobolevGaugeFixedOperator_coefficientMotion]
  simp

end TauCeti.Vortex
