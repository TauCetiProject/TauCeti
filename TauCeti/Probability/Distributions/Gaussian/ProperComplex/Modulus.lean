/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Basic
public import TauCeti.Probability.Distributions.Chi.Gaussian
import TauCeti.Probability.Distributions.Exponential.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Moduli of proper complex Gaussian coordinates

The real and imaginary parts of a centered proper complex Gaussian coordinate are independent
real Gaussians with variance half its complex variance. At positive variance its squared modulus
is exponential with mean equal to the complex variance, and its modulus is Rayleigh (the
two-degree chi law). These identities hold coordinatewise even when the full covariance is
singular. A zero coordinate variance gives a point mass at zero through the scaled-exponential
identity.

For a standard complex coordinate, the real variances are `1 / 2`, the squared modulus has
rate-one exponential law, and the Rayleigh scale is `Real.sqrt (1 / 2)`.

The proofs reuse real Gaussian coordinate independence, `map_sum_sq_pi_gaussianReal`, and
`map_norm_pi_gaussianReal`.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The centered real and imaginary parts of a proper complex Gaussian coordinate are
independent Gaussians of variance half its complex variance, including zero variance. -/
@[simp]
theorem map_re_im_sub_eval_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i : ι) :
    (properComplexGaussianMeasure m C).map
        (fun z ↦ ((z i).re - (m i).re, (z i).im - (m i).im)) =
      (gaussianReal 0 ((C i i).re / 2).toNNReal).prod
        (gaussianReal 0 ((C i i).re / 2).toNNReal) := by
  let μ := multivariateGaussian (complexToRealEuclidean ι m) (complexGaussianRealCovariance C)
  have hS := (posSemidef_complexGaussianRealCovariance_iff C).2 hC
  have him : (C i i).im = 0 := by
    have h := congrArg Complex.im (hC.isHermitian.apply i i)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have hpair : HasGaussianLaw (fun x : EuclideanSpace ℝ (ι ⊕ ι) ↦
      (x (Sum.inl i), x (Sum.inr i))) μ :=
    (IsGaussian.hasGaussianLaw_id (μ := μ)).map_fun
      ((EuclideanSpace.proj (Sum.inl i)).prod (EuclideanSpace.proj (Sum.inr i)))
  have hind : IndepFun (fun x : EuclideanSpace ℝ (ι ⊕ ι) ↦ x (Sum.inl i))
      (fun x ↦ x (Sum.inr i)) μ := by
    apply hpair.indepFun_of_covariance_eq_zero
    simpa [μ, him] using covariance_eval_multivariateGaussian
      (μ := complexToRealEuclidean ι m) hS (Sum.inl i) (Sum.inr i)
  have hlaw (k : ι ⊕ ι) : HasLaw
      (fun x : EuclideanSpace ℝ (ι ⊕ ι) ↦ x k - complexToRealEuclidean ι m k)
      (gaussianReal 0 ((complexGaussianRealCovariance C) k k).toNNReal) μ := by
    simpa only [sub_self] using
      gaussianReal_sub_const (HasLaw.mk (by fun_prop)
        (measurePreserving_eval_multivariateGaussian
          (μ := complexToRealEuclidean ι m) hS (i := k)).map_eq)
        (complexToRealEuclidean ι m k)
  have hprod := (hind.comp (by fun_prop : Measurable
    (fun x : ℝ ↦ x - complexToRealEuclidean ι m (Sum.inl i)))
    (by fun_prop : Measurable (fun x : ℝ ↦ x - complexToRealEuclidean ι m (Sum.inr i)))).hasLaw_prod
      (hlaw (Sum.inl i)) (hlaw (Sum.inr i))
  rw [properComplexGaussianMeasure_def, Measure.map_map (by fun_prop) (by fun_prop)]
  simpa [μ, Function.comp_def, Complex.sub_re, Complex.sub_im] using hprod.map_eq

/-- The centered real and imaginary coordinates, indexed by `Fin 2`, have the product
Gaussian law with variance half the complex variance, including zero variance. -/
@[simp]
theorem map_finTwo_re_im_sub_eval_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i : ι) :
    (properComplexGaussianMeasure m C).map
        (fun z ↦ ![(z i).re - (m i).re, (z i).im - (m i).im]) =
      Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 ((C i i).re / 2).toNNReal) := by
  apply MeasurableEquiv.map_measurableEquiv_injective MeasurableEquiv.finTwoArrow
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, MeasurableEquiv.finTwoArrow_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    (map_re_im_sub_eval_properComplexGaussianMeasure m hC i).trans
      (measurePreserving_finTwoArrow (gaussianReal 0 ((C i i).re / 2).toNNReal)).map_eq.symm

/-- The squared modulus of a centered proper complex Gaussian coordinate is a rate-one
exponential scaled by its complex variance. At zero variance this is the point mass at zero. -/
@[simp]
theorem map_norm_sq_sub_eval_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i : ι) :
    (properComplexGaussianMeasure m C).map (fun z ↦ ‖z i - m i‖ ^ 2) =
      (expMeasure 1).map (fun x ↦ (C i i).re * x) := by
  have hdiag : 0 ≤ (C i i).re := RCLike.nonneg_iff.mp hC.diag_nonneg |>.1
  let v := ((C i i).re / 2).toNNReal
  have hv : (v : ℝ) = (C i i).re / 2 := Real.coe_toNNReal _ (by positivity)
  have hsum := map_sum_sq_pi_gaussianReal (ι := Fin 2) v
  have h := congrArg (fun ν : Measure (Fin 2 → ℝ) ↦ ν.map (fun x ↦ x 0 ^ 2 + x 1 ^ 2))
    (map_finTwo_re_im_sub_eval_properComplexGaussianMeasure m hC i)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hsum' : (Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 v).map
      (fun x ↦ x 0 ^ 2 + x 1 ^ 2) =
      (expMeasure 1).map (fun x ↦ (C i i).re * x) := by
    simp only [Fin.sum_univ_two, Fintype.card_fin, Nat.cast_ofNat,
      chiSquaredMeasure_two] at hsum
    rw [← expMeasure_map_const_mul (r := 1) zero_lt_one (c := 2) (by norm_num),
      Measure.map_map (by fun_prop) (by fun_prop)] at hsum
    convert hsum using 1
    congr 1
    funext x
    simp only [Function.comp_apply, hv]
    ring
  simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ← pow_two] using
    h.trans hsum'

/-- A positive-variance centered proper complex Gaussian coordinate has a Rayleigh modulus:
the chi law with two degrees of freedom and scale the square root of half its variance. -/
@[simp]
theorem map_norm_sub_eval_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i : ι) (hi : 0 < (C i i).re) :
    (properComplexGaussianMeasure m C).map (fun z ↦ ‖z i - m i‖) =
      chiMeasure 2 (Real.sqrt ((C i i).re / 2)) := by
  let v := ((C i i).re / 2).toNNReal
  have hv : (v : ℝ) = (C i i).re / 2 := Real.coe_toNNReal _ (by positivity)
  have hvpos : v ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    positivity
  have h := congrArg (fun ν : Measure (Fin 2 → ℝ) ↦
    ν.map (fun x ↦ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 2))‖))
    (map_finTwo_re_im_sub_eval_properComplexGaussianMeasure m hC i)
  rw [Measure.map_map (by fun_prop) (by fun_prop), map_norm_pi_gaussianReal hvpos] at h
  simpa [Function.comp_def, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    ← Complex.sub_re, ← Complex.sub_im, ← Complex.norm_eq_sqrt_sq_add_sq, hv] using h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {Z : Ω → ι → ℂ} {m : ι → ℂ} {C : Matrix ι ι ℂ}

/-- The centered real and imaginary parts of a proper complex Gaussian coordinate have
the product of their two real Gaussian laws. -/
theorem HasLaw.re_im_sub_eval_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef) (i : ι) :
    HasLaw (fun ω ↦ ((Z ω i).re - (m i).re, (Z ω i).im - (m i).im))
      ((gaussianReal 0 ((C i i).re / 2).toNNReal).prod
        (gaussianReal 0 ((C i i).re / 2).toNNReal)) P :=
  (HasLaw.mk (by fun_prop)
    (map_re_im_sub_eval_properComplexGaussianMeasure m hC i)).fun_comp hZ

/-- The squared modulus of a centered complex Gaussian coordinate has a scaled exponential
law, with the scale equal to its complex variance. Zero variance is included. -/
theorem HasLaw.norm_sq_sub_eval_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef) (i : ι) :
    HasLaw (fun ω ↦ ‖Z ω i - m i‖ ^ 2)
      ((expMeasure 1).map (fun x ↦ (C i i).re * x)) P :=
  (HasLaw.mk (by fun_prop : Measurable (fun z : ι → ℂ ↦ ‖z i - m i‖ ^ 2)).aemeasurable
    (map_norm_sq_sub_eval_properComplexGaussianMeasure m hC i)).fun_comp hZ

/-- The modulus of a centered positive-variance proper complex Gaussian coordinate is
Rayleigh with scale the square root of half its complex variance. -/
theorem HasLaw.norm_sub_eval_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef) (i : ι)
    (hi : 0 < (C i i).re) :
    HasLaw (fun ω ↦ ‖Z ω i - m i‖) (chiMeasure 2 (Real.sqrt ((C i i).re / 2))) P :=
  (HasLaw.mk (by fun_prop : Measurable (fun z : ι → ℂ ↦ ‖z i - m i‖)).aemeasurable
    (map_norm_sub_eval_properComplexGaussianMeasure m hC i hi)).fun_comp hZ

end ProbabilityTheory
