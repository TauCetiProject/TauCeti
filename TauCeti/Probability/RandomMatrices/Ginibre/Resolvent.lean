/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Basic
import TauCeti.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Matrix.Resolvent.Derivative
import TauCeti.Analysis.Matrix.Resolvent.DilationTrace
import TauCeti.Data.Matrix.Basis
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts.Multivariate
import TauCeti.Probability.Distributions.Gaussian.Isotropic
import TauCeti.Probability.Distributions.Gaussian.Poincare
import TauCeti.Probability.Distributions.Gaussian.ProperComplex.MixedMoments

/-!
# Integration by parts for the shifted complex Ginibre resolvent

For a shifted complex Gaussian matrix, integration by parts expresses the expected product
of the Gaussian part of the Hermitian dilation and its resolvent through the diagonal block
traces. Gaussian Poincaré controls the fluctuation of the normalized resolvent trace.
For a scalar shift, this yields a quantitative residual bound for the cubic equation of
the shifted singular-value transform on the imaginary axis.

## References

* Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*, Cambridge University
  Press, 2010, Lemma 2.4.5 (Gaussian integration by parts).
* Bordenave and Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), 1–89, §4.5,
  proof of Corollary 4.10 (the shifted singular-value transform and its equation).
-/

public section

noncomputable section

open Complex MeasureTheory Matrix ProbabilityTheory
open scoped ComplexConjugate Matrix.Norms.L2Operator NNReal ProbabilityTheory

attribute [local instance] Matrix.l2OpNormedAlgebraReal

namespace TauCeti.Probability

private abbrev Entry (n : ℕ) := Fin n × Fin n
private abbrev RealEntry (n : ℕ) := Entry n ⊕ Entry n
private abbrev DilationIndex (n : ℕ) := Fin n ⊕ Fin n

private def rawGinibre {n : ℕ} (x : RealEntry n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j ↦ (x (.inl (i, j)) : ℂ) + (x (.inr (i, j)) : ℂ) * I

private def dilationLinear (n : ℕ) :
    (RealEntry n → ℝ) →L[ℝ] Matrix (DilationIndex n) (DilationIndex n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ fromBlocks 0 (rawGinibre x) (rawGinibre x)ᴴ 0
      map_add' := by
        intro x y
        ext (i | i) (j | j) <;>
          simp [rawGinibre, Pi.add_apply, add_mul, add_add_add_comm]
      map_smul' := by
        intro c x
        ext (i | i) (j | j) <;>
          simp [rawGinibre, Pi.smul_apply, Complex.real_smul, mul_assoc] }

private theorem dilationLinear_apply {n : ℕ} (x : RealEntry n → ℝ) :
    dilationLinear n x = fromBlocks 0 (rawGinibre x) (rawGinibre x)ᴴ 0 := rfl

private theorem dilationLinear_single_inl {n : ℕ} (i j : Fin n) :
    dilationLinear n (Pi.single (Sum.inl (i, j)) 1) =
      single (.inl i) (.inr j) 1 + single (.inr j) (.inl i) 1 := by
  classical
  ext (u | u) (v | v) <;>
    simp [dilationLinear_apply, rawGinibre, Matrix.single_apply, Pi.single_apply, Prod.ext_iff,
      and_comm] <;> split_ifs <;> simp_all [eq_comm]

private theorem dilationLinear_single_inr {n : ℕ} (i j : Fin n) :
    dilationLinear n (Pi.single (Sum.inr (i, j)) 1) =
      single (.inl i) (.inr j) I + single (.inr j) (.inl i) (-I) := by
  classical
  ext (u | u) (v | v) <;>
    simp [dilationLinear_apply, rawGinibre, Matrix.single_apply, Pi.single_apply, Prod.ext_iff,
      and_comm] <;> split_ifs <;> simp_all [eq_comm]

private abbrev coordinatesGaussian (n : ℕ) : Measure (RealEntry n → ℝ) :=
  Measure.pi fun _ ↦ gaussianReal 0 1

private def resolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (w : ℂ)
    (x : RealEntry n → ℝ) : Matrix (DilationIndex n) (DilationIndex n) ℂ :=
  (fromBlocks 0 D Dᴴ 0 + a • dilationLinear n x - w • 1)⁻¹

private theorem isHermitian_shiftedDilation {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) (x : RealEntry n → ℝ) : (fromBlocks 0 D Dᴴ 0 + a • dilationLinear n x).IsHermitian := by
  rw [dilationLinear_apply]
  exact (isHermitian_zero.fromBlocks rfl isHermitian_zero).add
    ((isHermitian_zero.fromBlocks rfl isHermitian_zero).smul (by simp [IsSelfAdjoint]))

private theorem continuous_resolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) : Continuous (resolvent D a w) := by
  exact Continuous.matrix_inv_sub_smul_one (by fun_prop) (isHermitian_shiftedDilation D a)
    (by simpa using hw)

private theorem norm_resolvent_le {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) (x : RealEntry n → ℝ) : ‖resolvent D a w x‖ ≤ |w.im|⁻¹ := by
  simpa only [resolvent, RCLike.im_eq_complex_im] using
    (isHermitian_shiftedDilation D a x).l2_opNorm_inv_sub_smul_one_le (z := w) (by simpa using hw)

private theorem hasFDerivAt_resolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) (x : RealEntry n → ℝ) :
    HasFDerivAt (resolvent D a w)
      (-(ContinuousLinearMap.mulLeftRight ℝ _ (resolvent D a w x) (resolvent D a w x) ∘L
        (a • dilationLinear n))) x := by
  have hu := (isHermitian_shiftedDilation D a x).isUnit_sub_smul_one_of_im_ne_zero
    (z := w) (by simpa using hw)
  have hd := ((a • dilationLinear n).hasFDerivAt (x := x)).const_add (fromBlocks 0 D Dᴴ 0)
  have h := (hd.sub_const (w • 1)).ringInverse hu
  unfold resolvent
  simpa only [nonsing_inv_eq_ringInverse, smul_apply] using! h

private theorem fderiv_resolvent_apply {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) (x y : RealEntry n → ℝ) (k l : DilationIndex n) :
    fderiv ℝ (fun x ↦ resolvent D a w x k l) x y =
      -(resolvent D a w x * (a • dilationLinear n y) * resolvent D a w x) k l := by
  have h := ((entryLinearMap ℝ ℂ k l).toContinuousLinearMap.hasFDerivAt).comp x
    (hasFDerivAt_resolvent D a hw x)
  have heq : (fun x ↦ resolvent D a w x k l) =
      (entryLinearMap ℝ ℂ k l).toContinuousLinearMap ∘ resolvent D a w := rfl
  rw [heq, h.fderiv]
  simp [ContinuousLinearMap.mulLeftRight_apply]

private theorem integrable_apply_mul_resolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) (p : RealEntry n) (k l : DilationIndex n) :
    Integrable (fun x ↦ (x p : ℂ) * resolvent D a w x k l) (coordinatesGaussian n) := by
  have hcoord : Integrable (fun x : RealEntry n → ℝ ↦ |x p|) (coordinatesGaussian n) :=
    (measurePreserving_eval (fun _ : RealEntry n ↦ gaussianReal 0 1) p)
      |>.integrable_comp_of_integrable (integrable_abs_gaussianReal 0 1)
  refine (hcoord.const_mul |w.im|⁻¹).mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · have hR := continuous_resolvent D a hw
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (((resolvent D a w x).norm_apply_le_l2_opNorm k l).trans (norm_resolvent_le D a hw x))
      (abs_nonneg _)

private theorem integral_apply_mul_resolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) (p : RealEntry n) (k l : DilationIndex n) :
    (∫ x, (x p : ℂ) * resolvent D a w x k l ∂coordinatesGaussian n) =
      ∫ x, -(resolvent D a w x * (a • dilationLinear n (Pi.single p 1)) *
        resolvent D a w x) k l ∂coordinatesGaussian n := by
  let R := resolvent D a w
  let B := a • dilationLinear n (Pi.single p 1)
  have hR := continuous_resolvent D a hw
  have hint : Integrable (fun x ↦ -(R x * B * R x) k l) (coordinatesGaussian n) := by
    refine Integrable.of_bound (by fun_prop) (|w.im|⁻¹ * ‖B‖ * |w.im|⁻¹) (ae_of_all _ fun x ↦ ?_)
    rw [norm_neg]
    exact ((R x * B * R x).norm_apply_le_l2_opNorm k l).trans
      ((norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_resolvent_le D a hw x) (norm_nonneg _))) (norm_resolvent_le D a hw x)
        (norm_nonneg _) (by positivity)))
  have h := integral_apply_sub_smul_eq_smul_integral_fderiv_pi_gaussianReal
    (fun _ ↦ 0) (fun _ ↦ 1) (f := fun x ↦ R x k l)
    (fun x ↦ ((entryLinearMap ℝ ℂ k l).toContinuousLinearMap.hasFDerivAt.comp x
      (hasFDerivAt_resolvent D a hw x)).differentiableAt)
    p (by simpa only [sub_zero, Complex.real_smul] using
      integrable_apply_mul_resolvent D a hw p k l)
    (by simpa only [R, B, fderiv_resolvent_apply D a hw] using hint)
  simpa only [R, sub_zero, Complex.real_smul, NNReal.coe_one, one_smul,
    fderiv_resolvent_apply D a hw] using h

private theorem integrable_resolvent_mul_resolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) (i j k l : DilationIndex n) :
    Integrable (fun x ↦ resolvent D a w x i j * resolvent D a w x k l) (coordinatesGaussian n) := by
  have hR := continuous_resolvent D a hw
  refine Integrable.of_bound (by fun_prop) (|w.im|⁻¹ ^ 2) (ae_of_all _ fun x ↦ ?_)
  rw [norm_mul, sq]
  exact mul_le_mul
    (((resolvent D a w x).norm_apply_le_l2_opNorm i j).trans (norm_resolvent_le D a hw x))
    (((resolvent D a w x).norm_apply_le_l2_opNorm k l).trans (norm_resolvent_le D a hw x))
    (norm_nonneg _) (by positivity)

private theorem integral_rawGinibre_mul_resolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) (i j : Fin n) (k l : DilationIndex n) :
    let R := resolvent D a w
    let P := coordinatesGaussian n
    (∫ x, rawGinibre x i j * R x k l ∂P) =
      -(2 * (a : ℂ)) * ∫ x, R x k (.inr j) * R x (.inl i) l ∂P ∧
    (∫ x, conj (rawGinibre x i j) * R x k l ∂P) =
      -(2 * (a : ℂ)) * ∫ x, R x k (.inl i) * R x (.inr j) l ∂P := by
  intro R P
  let p : RealEntry n := .inl (i, j)
  let q : RealEntry n := .inr (i, j)
  let U x := R x k (.inl i) * R x (.inr j) l
  let V x := R x k (.inr j) * R x (.inl i) l
  have hU : Integrable U P := integrable_resolvent_mul_resolvent D a hw _ _ _ _
  have hV : Integrable V P := integrable_resolvent_mul_resolvent D a hw _ _ _ _
  have h₁ : (∫ x, (x p : ℂ) * R x k l ∂P) =
      -(a : ℂ) * ((∫ x, U x ∂P) + ∫ x, V x ∂P) := by
    rw [← integral_add hU hV, ← integral_const_mul]
    refine (integral_apply_mul_resolvent D a hw p k l).trans (integral_congr_ae (.of_forall ?_))
    intro x
    simp only [p, dilationLinear_single_inl, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, U, V, R]
    simp only [mul_single_one_mul_apply]
    ring
  have h₂ : (∫ x, (x q : ℂ) * R x k l ∂P) =
      -(a : ℂ) * I * ((∫ x, U x ∂P) - ∫ x, V x ∂P) := by
    rw [← integral_sub hU hV, ← integral_const_mul]
    refine (integral_apply_mul_resolvent D a hw q k l).trans (integral_congr_ae (.of_forall ?_))
    intro x
    dsimp only [q]
    rw [dilationLinear_single_inr, single_eq_smul_single_one _ _ I,
      single_eq_smul_single_one _ _ (-I)]
    simp only [Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul, U, V, R, mul_single_one_mul_apply]
    ring
  have hp : Integrable (fun x ↦ (x p : ℂ) * R x k l) P :=
    integrable_apply_mul_resolvent D a hw _ _ _
  have hq : Integrable (fun x ↦ (x q : ℂ) * R x k l) P :=
    integrable_apply_mul_resolvent D a hw _ _ _
  constructor
  · calc
      _ = (∫ x, (x p : ℂ) * R x k l ∂P) + I * ∫ x, (x q : ℂ) * R x k l ∂P := by
        rw [← integral_const_mul, ← integral_add hp (hq.const_mul I)]
        exact integral_congr_ae (.of_forall fun x ↦ by simp only [rawGinibre, of_apply, p, q]; ring)
      _ = _ := by
        rw [h₁, h₂]
        linear_combination (a : ℂ) * ((∫ x, V x ∂P) - ∫ x, U x ∂P) *
          (congrArg (· + 1) I_mul_I)
  · calc
      _ = (∫ x, (x p : ℂ) * R x k l ∂P) - I * ∫ x, (x q : ℂ) * R x k l ∂P := by
        rw [← integral_const_mul, ← integral_sub hp (hq.const_mul I)]
        exact integral_congr_ae (.of_forall fun x ↦ by simp [rawGinibre, p, q]; ring)
      _ = _ := by
        rw [h₁, h₂]
        linear_combination (a : ℂ) * ((∫ x, U x ∂P) - ∫ x, V x ∂P) *
          (congrArg (· + 1) I_mul_I)

private def ginibreOfCoordinates {n : ℕ} (x : RealEntry n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt 2)⁻¹ • rawGinibre x

private theorem continuous_ginibreOfCoordinates (n : ℕ) :
    Continuous (@ginibreOfCoordinates n) := by
  apply continuous_matrix
  intro i j
  simp only [ginibreOfCoordinates, rawGinibre, Matrix.smul_apply, Matrix.of_apply]
  fun_prop

private theorem map_ginibreOfCoordinates (n : ℕ) :
    (coordinatesGaussian n).map ginibreOfCoordinates = ginibreComplex n n := by
  have hc : (2 : ℝ)⁻¹ = (Real.sqrt 2)⁻¹ ^ 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
  rw [ginibreComplex_eq_map_properComplexGaussianMeasure, properComplexGaussianMeasure_def,
    map_zero, complexGaussianRealCovariance_def, Matrix.realify_one, hc,
    EuclideanSpace.multivariateGaussian_sq_smul_one_eq_map_stdGaussian, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  ext i j
  simp [ginibreOfCoordinates, rawGinibre, Function.comp_def, complexToRealEuclidean_symm_apply,
    Complex.real_smul, mul_assoc]

private theorem resolvent_ginibreOfCoordinates {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) (w : ℂ) (x : RealEntry n → ℝ) :
    let X := D + a • ginibreOfCoordinates x
    (fromBlocks 0 X Xᴴ 0 - w • 1)⁻¹ = resolvent D (a * (Real.sqrt 2)⁻¹) w x := by
  dsimp only [ginibreOfCoordinates, resolvent, dilationLinear_apply]
  rw [smul_smul]
  congr 2
  ext (i | i) (j | j) <;> simp [conjTranspose_add, conjTranspose_smul]

/-- Gaussian integration by parts for the entries of the Hermitian dilation resolvent. For a
standard complex Ginibre draw `G`, let `R` be the resolvent of the dilation of `D + a • G`.
In an expectation against an entry of `R`, an entry of `a • G` differentiates in the conjugate
entry direction and vice versa. The corresponding variance is `a²`. -/
theorem integral_ginibreComplex_smul_mul_dilationResolvent {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) (i j : Fin n)
    (k l : Fin n ⊕ Fin n) :
    let P := ginibreComplex n n
    let R (G : Matrix (Fin n) (Fin n) ℂ) :=
      (fromBlocks 0 (D + a • G) (D + a • G)ᴴ 0 - w • 1)⁻¹
    (∫ G, (a • G) i j * R G k l ∂P) =
      -((a : ℂ) ^ 2) * ∫ G, R G k (.inr j) * R G (.inl i) l ∂P ∧
    (∫ G, conj ((a • G) i j) * R G k l ∂P) =
      -((a : ℂ) ^ 2) * ∫ G, R G k (.inl i) * R G (.inr j) l ∂P := by
  let P₀ := coordinatesGaussian n
  let f : (RealEntry n → ℝ) → Matrix (Fin n) (Fin n) ℂ := ginibreOfCoordinates
  have hf : Continuous f := continuous_ginibreOfCoordinates n
  intro P R
  have hR : Continuous R := Continuous.matrix_inv_sub_smul_one (by fun_prop)
    (fun _ ↦ isHermitian_zero.fromBlocks rfl isHermitian_zero) (by simpa using hw)
  have hmap : MeasurePreserving f P₀ P := ⟨hf.measurable, map_ginibreOfCoordinates n⟩
  let b := a * (Real.sqrt 2)⁻¹
  have hc : (2 : ℂ) * (b : ℂ) * (b : ℂ) = (a : ℂ) ^ 2 := by
    have h : (Real.sqrt 2)⁻¹ ^ 2 = (2 : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]
    have hb : (2 : ℝ) * b * b = a ^ 2 := by
      calc
        _ = 2 * a ^ 2 * (Real.sqrt 2)⁻¹ ^ 2 := by dsimp only [b]; ring
        _ = _ := by rw [h]; ring
    exact_mod_cast hb
  obtain ⟨h₁, h₂⟩ := integral_rawGinibre_mul_resolvent D b hw i j k l
  have hcomp (G : RealEntry n → ℝ) : R (f G) = resolvent D b w G :=
    resolvent_ginibreOfCoordinates D a w G
  have hscale (G : RealEntry n → ℝ) : (a • f G) i j = (b : ℂ) * rawGinibre G i j := by
    simp [f, ginibreOfCoordinates, b, Matrix.smul_apply, Complex.real_smul, mul_assoc]
  constructor
  · rw [← hmap.hasLaw.integral_comp (Continuous.aestronglyMeasurable (by fun_prop)),
      ← hmap.hasLaw.integral_comp (Continuous.aestronglyMeasurable (by fun_prop))]
    simp_rw [Function.comp_apply, hcomp, hscale, mul_assoc]
    rw [integral_const_mul, h₁, ← mul_assoc]
    rw [mul_neg, ← mul_assoc (b : ℂ) 2, mul_comm (b : ℂ) 2, hc]
  · rw [← hmap.hasLaw.integral_comp (Continuous.aestronglyMeasurable (by fun_prop)),
      ← hmap.hasLaw.integral_comp (Continuous.aestronglyMeasurable (by fun_prop))]
    simp_rw [Function.comp_apply, hcomp, hscale, map_mul, conj_ofReal, mul_assoc]
    rw [integral_const_mul, h₂, ← mul_assoc]
    rw [mul_neg, ← mul_assoc (b : ℂ) 2, mul_comm (b : ℂ) 2, hc]

private def ginibreResolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (w : ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (DilationIndex n) (DilationIndex n) ℂ :=
  (fromBlocks 0 (D + a • G) (D + a • G)ᴴ 0 - w • 1)⁻¹

private theorem continuous_ginibreResolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) : Continuous (ginibreResolvent D a w) := by
  unfold ginibreResolvent
  exact Continuous.matrix_inv_sub_smul_one (by fun_prop)
    (fun _ ↦ isHermitian_zero.fromBlocks rfl isHermitian_zero) (by simpa using hw)

private theorem norm_ginibreResolvent_le {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ)
    (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) (G : Matrix (Fin n) (Fin n) ℂ) :
    ‖ginibreResolvent D a w G‖ ≤ |w.im|⁻¹ := by
  simpa only [ginibreResolvent, RCLike.im_eq_complex_im] using
    (isHermitian_zero.fromBlocks (B := D + a • G) rfl isHermitian_zero)
      |>.l2_opNorm_inv_sub_smul_one_le (z := w) (by simpa using hw)

private theorem integrable_ginibreResolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) : Integrable (ginibreResolvent D a w) (ginibreComplex n n) :=
  Integrable.of_bound (continuous_ginibreResolvent D a hw).aestronglyMeasurable _
    (.of_forall (norm_ginibreResolvent_le D a hw))

private theorem integrable_ginibreResolvent_apply_mul_apply {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0)
    (i j k l : DilationIndex n) :
    Integrable (fun G ↦ ginibreResolvent D a w G i j * ginibreResolvent D a w G k l)
      (ginibreComplex n n) := by
  have hc := continuous_ginibreResolvent D a hw
  refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
    (|w.im|⁻¹ ^ 2) (.of_forall fun G ↦ ?_)
  have hb (s t : DilationIndex n) : ‖ginibreResolvent D a w G s t‖ ≤ |w.im|⁻¹ :=
    ((ginibreResolvent D a w G).norm_apply_le_l2_opNorm s t).trans
      (norm_ginibreResolvent_le D a hw G)
  rw [norm_mul, sq]
  exact mul_le_mul (hb i j) (hb k l) (norm_nonneg _) (by positivity)

private theorem integrable_ginibreComplex_entry_pow_mul_conj_pow {n : ℕ} (i j : Fin n)
    (s t : ℕ) :
    Integrable (fun G : Matrix (Fin n) (Fin n) ℂ ↦ G i j ^ s * conj (G i j) ^ t)
      (ginibreComplex n n) :=
  (MeasurePreserving.mk (by fun_prop) (map_apply_ginibreComplex n n i j))
    |>.integrable_comp_of_integrable (integrable_pow_mul_conj_pow_properComplexGaussianScalar s t)

private theorem integral_dilationNoise_mul_ginibreResolvent_apply {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0)
    (i k : DilationIndex n) :
    let P := ginibreComplex n n
    let R := ginibreResolvent D a w
    (∫ G, (fromBlocks 0 (a • G) (a • G)ᴴ 0 * R G) i k ∂P) =
      -((a : ℂ) ^ 2) * ∫ G, (R G).toBlocks₁₁.trace * R G i k ∂P := by
  intro P R
  have hc : Continuous R := continuous_ginibreResolvent D a hw
  have hbd (i j : DilationIndex n) (G : Matrix (Fin n) (Fin n) ℂ) :
      ‖R G i j‖ ≤ |w.im|⁻¹ :=
    ((R G).norm_apply_le_l2_opNorm i j).trans (norm_ginibreResolvent_le D a hw G)
  have hint (i j : Fin n) : Integrable (fun G ↦ (a • G) i j) P := by
    simpa [Matrix.smul_apply, Complex.real_smul] using
      (integrable_ginibreComplex_entry_pow_mul_conj_pow i j 1 0).const_mul (a : ℂ)
  have hint' (i j : Fin n) : Integrable (fun G ↦ conj ((a • G) i j)) P := by
    simpa [Matrix.smul_apply, Complex.real_smul] using
      (integrable_ginibreComplex_entry_pow_mul_conj_pow i j 0 1).const_mul (a : ℂ)
  have hr := integrable_ginibreResolvent_apply_mul_apply D a hw
  have htrace (G : Matrix (Fin n) (Fin n) ℂ) :
      (R G).toBlocks₁₁.trace = (R G).toBlocks₂₂.trace :=
    trace_toBlocks₁₁_inv_fromBlocks_zero_sub_smul_one_eq _ _ w
  cases i with
  | inl i =>
    calc
      _ = ∑ j, ∫ G, (a • G) i j * R G (.inr j) k ∂P := by
        simp only [Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, Matrix.zero_apply,
          zero_mul, Finset.sum_const_zero, fromBlocks_apply₁₂, zero_add]
        exact integral_finsetSum _ fun j _ ↦
          (hint i j).mul_bdd (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall (hbd _ k))
      _ = ∑ j, -((a : ℂ) ^ 2) *
          ∫ G, R G (.inr j) (.inr j) * R G (.inl i) k ∂P := by
        exact Finset.sum_congr rfl fun j _ ↦
          (integral_ginibreComplex_smul_mul_dilationResolvent D a hw i j (.inr j) k).1
      _ = _ := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ (fun j _ ↦ hr _ _ _ _)]
        congr 1
        refine integral_congr_ae (.of_forall fun G ↦ ?_)
        dsimp only
        rw [htrace G]
        simp only [trace, diag, toBlocks₂₂, of_apply, Finset.sum_mul, R]
  | inr i =>
    calc
      _ = ∑ j, ∫ G, conj ((a • G) j i) * R G (.inl j) k ∂P := by
        simp only [Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₂₂, Matrix.zero_apply,
          zero_mul, Finset.sum_const_zero, fromBlocks_apply₂₁, add_zero, conjTranspose_apply,
          ← starRingEnd_apply]
        exact integral_finsetSum _ fun j _ ↦
          (hint' j i).mul_bdd (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall (hbd _ k))
      _ = ∑ j, -((a : ℂ) ^ 2) *
          ∫ G, R G (.inl j) (.inl j) * R G (.inr i) k ∂P := by
        exact Finset.sum_congr rfl fun j _ ↦
          (integral_ginibreComplex_smul_mul_dilationResolvent D a hw j i (.inl j) k).2
      _ = _ := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ (fun j _ ↦ hr _ _ _ _)]
        simp only [trace, diag, toBlocks₁₁, of_apply, Finset.sum_mul, R, P]

/-- The expected resolvent of a shifted complex Ginibre dilation satisfies a matrix equation
whose second term is the expectation of the resolvent times a diagonal block trace. The shift
matrix `D` and entry scale `a` are arbitrary, and the spectral parameter is nonreal. -/
theorem mul_integral_ginibreComplex_dilationResolvent_eq {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    let P := ginibreComplex n n
    let R (G : Matrix (Fin n) (Fin n) ℂ) :=
      (fromBlocks 0 (D + a • G) (D + a • G)ᴴ 0 - w • 1)⁻¹
    (fromBlocks 0 D Dᴴ 0 - w • 1) * (∫ G, R G ∂P) =
      1 + (a : ℂ) ^ 2 • ∫ G, (R G).toBlocks₁₁.trace • R G ∂P := by
  let P := ginibreComplex n n
  let R := ginibreResolvent D a w
  let S := fromBlocks 0 D Dᴴ 0 - w • 1
  let N (G : Matrix (Fin n) (Fin n) ℂ) := fromBlocks 0 (a • G) (a • G)ᴴ 0
  let C (G : Matrix (Fin n) (Fin n) ℂ) := (R G).toBlocks₁₁.trace • R G
  have hc : Continuous R := continuous_ginibreResolvent D a hw
  have hint : Integrable R P := integrable_ginibreResolvent D a hw
  let L := ContinuousLinearMap.mul ℝ (Matrix (DilationIndex n) (DilationIndex n) ℂ) S
  have hnoise (G : Matrix (Fin n) (Fin n) ℂ) : N G * R G = 1 - S * R G := by
    have hu := (isHermitian_zero.fromBlocks (B := D + a • G) rfl isHermitian_zero)
      |>.isUnit_sub_smul_one_of_im_ne_zero (z := w) (by simpa using hw)
    have h := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hu)
    apply eq_sub_of_add_eq
    rw [← add_mul]
    simpa only [R, ginibreResolvent, S, N, ← add_sub_assoc, fromBlocks_add,
      conjTranspose_add, zero_add, add_comm (a • G), add_comm (a • G)ᴴ] using h
  have hN : Integrable (fun G ↦ N G * R G) P :=
    ((integrable_const 1).sub (L.integrable_comp hint)).congr (.of_forall fun G ↦ (hnoise G).symm)
  have hC : Integrable C P := by
    have hcont : Continuous fun G ↦ (R G).toBlocks₁₁.trace := by
      simp only [trace, diag, toBlocks₁₁, of_apply]
      fun_prop
    refine Integrable.of_bound (hcont.smul hc).aestronglyMeasurable
      (Fintype.card (Fin n) * |w.im|⁻¹ ^ 2) (.of_forall fun G ↦ ?_)
    have ht : ‖(R G).toBlocks₁₁.trace‖ ≤ Fintype.card (Fin n) * |w.im|⁻¹ := by
      refine (norm_trace_le_card_mul_l2_opNorm _).trans ?_
      gcongr
      exact (l2_opNorm_submatrix_le _ Sum.inl_injective Sum.inl_injective).trans
        (norm_ginibreResolvent_le D a hw G)
    dsimp only [C]
    rw [norm_smul, sq, ← mul_assoc]
    exact mul_le_mul ht (norm_ginibreResolvent_le D a hw G) (norm_nonneg _) (by positivity)
  have hsum : (∫ G, N G * R G ∂P) = -((a : ℂ) ^ 2) • ∫ G, C G ∂P := by
    ext i k
    let e := (entryLinearMap ℝ ℂ i k).toContinuousLinearMap
    -- Express entry evaluation as a continuous linear map to commute it with integration.
    change e (∫ G, N G * R G ∂P) = -((a : ℂ) ^ 2) * e (∫ G, C G ∂P)
    rw [← e.integral_comp_comm hN, ← e.integral_comp_comm hC]
    exact integral_dilationNoise_mul_ginibreResolvent_apply D a hw i k
  -- The local abbreviations name the resolvent and its trace-weighted matrix.
  change S * (∫ G, R G ∂P) = 1 + (a : ℂ) ^ 2 • ∫ G, C G ∂P
  rw [← sub_neg_eq_add, ← neg_smul, ← hsum]
  calc
    _ = ∫ G, S * R G ∂P := (L.integral_comp_comm hint).symm
    _ = ∫ G, 1 - N G * R G ∂P := integral_congr_ae
      (.of_forall fun G ↦ by simp only [hnoise, sub_sub_cancel])
    _ = _ := by rw [integral_sub (integrable_const _) hN, integral_const, probReal_univ, one_smul]

section Fluctuations

private abbrev traceFactor (n : ℕ) : ℂ := (Fintype.card (DilationIndex n) : ℂ)⁻¹

private def normalizedDilationTrace {n : ℕ} :
    Matrix (DilationIndex n) (DilationIndex n) ℂ →L[ℂ] ℂ :=
  traceFactor n • (traceLinearMap (DilationIndex n) ℂ ℂ).toContinuousLinearMap

private theorem normalizedDilationTrace_apply {n : ℕ}
    (M : Matrix (DilationIndex n) (DilationIndex n) ℂ) :
    normalizedDilationTrace M = traceFactor n * M.trace := rfl

private theorem contDiff_resolvent {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) : ContDiff ℝ 1 (resolvent D a w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h := (isHermitian_shiftedDilation D a x).isUnit_sub_smul_one_of_im_ne_zero
    (z := w) (by simpa using hw)
  let H (y : RealEntry n → ℝ) := fromBlocks 0 D Dᴴ 0 + a • dilationLinear n y
  have hH : ContDiffAt ℝ 1 H x := by
    dsimp only [H]
    fun_prop
  have hR := ((contDiffAt_inv_sub_smul_one h 1).restrict_scalars ℝ).comp x hH
  unfold resolvent
  simpa only [Function.comp_def, H] using hR

private theorem fderiv_im_normalizedDilationTrace_resolvent {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) (x y : RealEntry n → ℝ) :
    let R := resolvent D a w
    fderiv ℝ (fun z ↦ (normalizedDilationTrace (R z)).im) x y =
      (normalizedDilationTrace (-(R x * (a • dilationLinear n y) * R x))).im := by
  intro R
  let L := imCLM ∘L (@normalizedDilationTrace n).restrictScalars ℝ
  have h := L.hasFDerivAt.comp x (hasFDerivAt_resolvent D a hw x)
  have heq : (fun z ↦ (normalizedDilationTrace (R z)).im) = L ∘ R := rfl
  rw [heq, h.fderiv]
  rfl

private theorem norm_trace_resolvent_mul_dilationLinear_single_mul_le {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) (x : RealEntry n → ℝ)
    (p : RealEntry n) :
    let R := resolvent D a w x
    ‖(R * (a • dilationLinear n (Pi.single p 1)) * R).trace‖ ≤ 2 * |a| * |w.im|⁻¹ ^ 2 := by
  intro R
  have hsingle (i j : DilationIndex n) (c : ℂ) (hc : ‖c‖ = 1) :
      ‖(R * single i j c * R).trace‖ ≤ |w.im|⁻¹ ^ 2 := by
    rw [trace_mul_cycle, trace_mul_comm (R * R), trace_single_mul, smul_eq_mul, norm_mul, hc,
      one_mul, sq]
    exact ((R * R).norm_apply_le_l2_opNorm j i).trans ((norm_mul_le _ _).trans
      (mul_le_mul (norm_resolvent_le D a hw x) (norm_resolvent_le D a hw x)
        (norm_nonneg _) (by positivity)))
  have hadd (i j : DilationIndex n) (c d : ℂ) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
      ‖(R * (single i j c + single j i d) * R).trace‖ ≤ 2 * |w.im|⁻¹ ^ 2 := by
    rw [Matrix.mul_add, Matrix.add_mul, trace_add, two_mul]
    exact (norm_add_le _ _).trans (add_le_add (hsingle i j c hc) (hsingle j i d hd))
  rw [Matrix.mul_smul, smul_mul_assoc, trace_smul, norm_smul, Real.norm_eq_abs,
    mul_comm (2 : ℝ) |a|, mul_assoc |a| 2]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rcases p with ⟨i, j⟩ | ⟨i, j⟩
  · rw [dilationLinear_single_inl]
    exact hadd (.inl i) (.inr j) 1 1 (by simp) (by simp)
  · rw [dilationLinear_single_inr]
    exact hadd (.inl i) (.inr j) I (-I) (by simp) (by simp)

private theorem abs_fderiv_im_normalizedDilationTrace_resolvent_le {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0)
    (x : RealEntry (n + 1) → ℝ) (p : RealEntry (n + 1)) :
    |fderiv ℝ (fun y ↦ (normalizedDilationTrace (resolvent D a w y)).im) x (Pi.single p 1)| ≤
      |a| * |w.im|⁻¹ ^ 2 / (n + 1) := by
  rw [fderiv_im_normalizedDilationTrace_resolvent D a hw]
  refine (abs_im_le_norm _).trans ?_
  rw [normalizedDilationTrace_apply, trace_neg, norm_mul, norm_neg, norm_inv,
    Complex.norm_natCast, Fintype.card_sum, Fintype.card_fin, Nat.cast_add,
    Nat.cast_succ, ← two_mul]
  have h := norm_trace_resolvent_mul_dilationLinear_single_mul_le D a hw x p
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem variance_im_normalizedDilationTrace_resolvent_le {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    variance (fun x ↦ (normalizedDilationTrace (resolvent D a w x)).im)
      (coordinatesGaussian (n + 1)) ≤ 2 * a ^ 2 * |w.im|⁻¹ ^ 4 := by
  let f x := (normalizedDilationTrace (resolvent D a w x)).im
  let C := |a| * |w.im|⁻¹ ^ 2 / ((n : ℝ) + 1)
  have hf : ContDiff ℝ 1 f :=
    (imCLM ∘L (@normalizedDilationTrace (n + 1)).restrictScalars ℝ).contDiff.comp
      (contDiff_resolvent D a hw)
  have hB (x) : |f x| ≤ |w.im|⁻¹ := (abs_im_le_norm _).trans
    ((norm_normalized_trace_le_l2_opNorm _).trans (norm_resolvent_le D a hw x))
  have hC (x p) : |fderiv ℝ f x (Pi.single p 1)| ≤ C :=
    abs_fderiv_im_normalizedDilationTrace_resolvent_le D a hw x p
  calc
    _ ≤ ∑ p : RealEntry (n + 1), ∫ x, fderiv ℝ f x (Pi.single p 1) ^ 2
        ∂coordinatesGaussian (n + 1) := variance_le_sum_integral_fderiv_sq_pi hf ⟨_, hB⟩ ⟨C, hC⟩
    _ ≤ ∑ _ : RealEntry (n + 1), C ^ 2 := by
      refine Finset.sum_le_sum fun p _ ↦ ?_
      refine (Real.le_norm_self _).trans ?_
      have h (x) : ‖fderiv ℝ f x (Pi.single p 1) ^ 2‖ ≤ C ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq.mpr ((hC x p).trans (le_abs_self _))
      simpa using norm_integral_le_of_norm_le_const
        (μ := coordinatesGaussian (n + 1)) (.of_forall h)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_succ, C]
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      rw [div_pow, mul_pow, sq_abs]
      field_simp
      ring

private theorem variance_im_normalizedDilationTrace_ginibreResolvent_le {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    variance (fun G ↦ (normalizedDilationTrace (ginibreResolvent D a w G)).im)
      (ginibreComplex (n + 1) (n + 1)) ≤ a ^ 2 * |w.im|⁻¹ ^ 4 := by
  have hR := continuous_ginibreResolvent D a hw
  have hcont : Continuous fun G ↦ (normalizedDilationTrace (ginibreResolvent D a w G)).im :=
    continuous_im.comp (normalizedDilationTrace.continuous.comp hR)
  have hmap := map_ginibreOfCoordinates (n + 1)
  rw [← hmap, variance_map hcont.measurable.aemeasurable
    (continuous_ginibreOfCoordinates _).measurable.aemeasurable]
  have h (x : RealEntry (n + 1) → ℝ) :
      ginibreResolvent D a w (ginibreOfCoordinates x) = resolvent D (a * (Real.sqrt 2)⁻¹) w x :=
    resolvent_ginibreOfCoordinates D a w x
  simp only [Function.comp_def, h]
  refine (variance_im_normalizedDilationTrace_resolvent_le D _ hw).trans_eq ?_
  rw [mul_pow, inv_pow (Real.sqrt 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

private theorem normalizedDilationTrace_ginibreResolvent_re {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (a η : ℝ) (G : Matrix (Fin n) (Fin n) ℂ) :
    (normalizedDilationTrace (ginibreResolvent D a ((η : ℂ) * I) G)).re = 0 := by
  have hc : traceFactor n = (((Fintype.card (DilationIndex n) : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [traceFactor, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [normalizedDilationTrace_apply, hc, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_eq_zero_of_right _ (re_trace_inv_fromBlocks_zero_conjTranspose_sub_smul_one _ η)

private theorem integral_norm_centered_dilationTrace_le {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ) {η : ℝ} (hη : 0 < η) :
    let P := ginibreComplex (n + 1) (n + 1)
    let t (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
      normalizedDilationTrace (ginibreResolvent D a ((η : ℂ) * I) G)
    let m := ∫ G, t G ∂P
    (∫ G, ‖t G - m‖ ∂P) ≤ |a| * η⁻¹ ^ 2 := by
  intro P t m
  let f G := (t G).im
  have hw : ((η : ℂ) * I).im ≠ 0 := by simpa using hη.ne'
  have ht : Continuous t :=
    normalizedDilationTrace.continuous.comp (continuous_ginibreResolvent D a hw)
  have hf : Continuous f := continuous_im.comp ht
  have hb (G) : ‖t G‖ ≤ η⁻¹ := by
    refine (norm_normalized_trace_le_l2_opNorm _).trans ?_
    simpa [abs_of_pos hη] using norm_ginibreResolvent_le D a hw G
  have ht_int : Integrable t P := Integrable.of_bound ht.aestronglyMeasurable _
    (.of_forall hb)
  have hm_re : m.re = 0 := by
    calc
      _ = ∫ G, (t G).re ∂P := (reCLM.integral_comp_comm ht_int).symm
      _ = 0 := by simp [t, normalizedDilationTrace_ginibreResolvent_re]
  have hm_im : m.im = ∫ G, f G ∂P := (imCLM.integral_comp_comm ht_int).symm
  have heq (G) : ‖t G - m‖ ^ 2 = (f G - ∫ Y, f Y ∂P) ^ 2 := by
    have hz : (t G - m).re = 0 := by
      rw [sub_re, hm_re, sub_zero]
      exact normalizedDilationTrace_ginibreResolvent_re D a η G
    rw [← Complex.abs_im_eq_norm.mpr hz, sq_abs, sub_im, hm_im]
  have hL : MemLp f 2 P := MemLp.of_bound hf.aestronglyMeasurable η⁻¹
    (.of_forall fun G ↦ (abs_im_le_norm _).trans (hb G))
  have hsq : Integrable (fun G ↦ ‖t G - m‖ ^ 2) P :=
    ((hL.sub (memLp_const _)).integrable_sq).congr (.of_forall fun G ↦ (heq G).symm)
  have hv : (∫ G, ‖t G - m‖ ^ 2 ∂P) ≤ a ^ 2 * η⁻¹ ^ 4 := by
    have he : (∫ G, ‖t G - m‖ ^ 2 ∂P) = variance f P := by
      rw [variance_eq_integral hf.measurable.aemeasurable]
      exact integral_congr_ae (.of_forall heq)
    rw [he]
    have hi : ((η : ℂ) * I).im = η := by simp
    simpa only [f, t, P, hi, abs_of_pos hη] using
      variance_im_normalizedDilationTrace_ginibreResolvent_le D a hw
  calc
    _ ≤ √(∫ G, ‖t G - m‖ ^ 2 ∂P) := by
      have hh := hsq.integral_norm_pow_le_sqrt_integral_norm_pow_two_mul (k := 1) (by simp [P])
      simpa only [pow_one] using hh
    _ ≤ √(a ^ 2 * η⁻¹ ^ 4) := Real.sqrt_le_sqrt hv
    _ = _ := by
      have hh : a ^ 2 * η⁻¹ ^ 4 = (a * η⁻¹ ^ 2) ^ 2 := by ring
      rw [hh, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg η⁻¹)]

end Fluctuations

section SelfConsistency

private theorem normalizedDilationTrace_eq_inv_mul_trace_toBlocks₁₁ {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (w : ℂ) :
    let R := (fromBlocks 0 A B 0 - w • 1)⁻¹
    normalizedDilationTrace R = (n : ℂ)⁻¹ * R.toBlocks₁₁.trace := by
  intro R
  have htrace : R.trace = R.toBlocks₁₁.trace + R.toBlocks₂₂.trace := by
    conv_lhs => rw [← fromBlocks_toBlocks R, trace_fromBlocks]
  rw [← trace_toBlocks₁₁_inv_fromBlocks_zero_sub_smul_one_eq A B w, ← two_mul] at htrace
  rw [normalizedDilationTrace_apply, htrace, traceFactor, Fintype.card_sum, Fintype.card_fin,
    Nat.cast_add, ← two_mul]
  by_cases hn : (n : ℂ) = 0
  · simp [hn]
  · field_simp

private theorem mul_integral_normalized_ginibreResolvent_eq {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {w : ℂ} (hw : w.im ≠ 0) :
    let P := ginibreComplex (n + 1) (n + 1)
    let R := ginibreResolvent D (Real.sqrt (n + 1))⁻¹ w
    let t G := normalizedDilationTrace (R G)
    let m := ∫ G, t G ∂P
    (fromBlocks 0 D Dᴴ 0 - (w + m) • 1) * (∫ G, R G ∂P) =
      1 + ∫ G, (t G - m) • R G ∂P := by
  intro P R t m
  let H := fromBlocks 0 D Dᴴ 0
  let a := (Real.sqrt ((n : ℝ) + 1))⁻¹
  have hr : Continuous R := continuous_ginibreResolvent D a hw
  have hb (G) : ‖R G‖ ≤ |w.im|⁻¹ := norm_ginibreResolvent_le D a hw G
  have hint : Integrable R P := integrable_ginibreResolvent D a hw
  have htR : Integrable (fun G ↦ t G • R G) P := by
    have hc := (normalizedDilationTrace.continuous.comp hr).smul hr
    refine Integrable.of_bound hc.aestronglyMeasurable (|w.im|⁻¹ ^ 2) (.of_forall fun G ↦ ?_)
    rw [norm_smul, sq]
    exact mul_le_mul ((norm_normalized_trace_le_l2_opNorm _).trans (hb G)) (hb G)
      (norm_nonneg _) (by positivity)
  have ha : (a : ℂ) ^ 2 = ((n + 1 : ℕ) : ℂ)⁻¹ := by
    have ha' : a ^ 2 = (((n + 1 : ℕ) : ℝ))⁻¹ := by
      simp only [a, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1), Nat.cast_succ]
    simpa only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast] using
      congrArg Complex.ofReal ha'
  have hmain : (H - w • 1) * (∫ G, R G ∂P) = 1 + ∫ G, t G • R G ∂P := by
    have h := mul_integral_ginibreComplex_dilationResolvent_eq D a hw
    dsimp only at h
    rw [← integral_smul, ha] at h
    simpa only [H, P, R, a, t, ginibreResolvent, smul_smul, smul_eq_mul,
      normalizedDilationTrace_eq_inv_mul_trace_toBlocks₁₁] using h
  have hmR : Integrable (fun G ↦ m • R G) P := hint.smul m
  rw [add_smul, ← sub_sub, sub_mul, smul_mul_assoc, Matrix.one_mul, hmain, add_sub_assoc,
    ← integral_smul, ← integral_sub htR hmR]
  simp only [sub_smul]

private theorem normalizedDilationTrace_one (n : ℕ) :
    normalizedDilationTrace (1 : Matrix (DilationIndex (n + 1)) (DilationIndex (n + 1)) ℂ) = 1 := by
  have hn : (Fintype.card (DilationIndex (n + 1)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [normalizedDilationTrace_apply, trace_one, inv_mul_cancel₀ hn]

private theorem scalarShift_dilation_mul_self (n : ℕ) (z : ℂ) :
    let D : Matrix (Fin n) (Fin n) ℂ := -(z • 1)
    let H := fromBlocks 0 D Dᴴ 0
    H * H = ((‖z‖ ^ 2 : ℝ) : ℂ) • 1 := by
  intro D H
  have hD : Dᴴ = -(conj z • 1) := by simp [D, conjTranspose_smul, ← starRingEnd_apply]
  dsimp only [H]
  rw [fromBlocks_multiply, hD]
  simp only [D, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, neg_mul_neg,
    smul_mul_smul_comm, Matrix.mul_one, Complex.mul_conj', Complex.conj_mul', ← Complex.ofReal_pow]
  rw [← fromBlocks_one, fromBlocks_smul, smul_zero]

private theorem norm_scalarShift_dilation_le (n : ℕ) (z : ℂ) :
    let D : Matrix (Fin n) (Fin n) ℂ := -(z • 1)
    ‖fromBlocks 0 D Dᴴ 0‖ ≤ ‖z‖ := by
  intro D
  let H := fromBlocks 0 D Dᴴ 0
  have hH : H.IsHermitian := isHermitian_zero.fromBlocks rfl isHermitian_zero
  have h := hH.isSelfAdjoint.norm_mul_self
  rw [scalarShift_dilation_mul_self n z, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)] at h
  have hsq : ‖H‖ ^ 2 ≤ ‖z‖ ^ 2 := h.symm.le.trans <|
    mul_le_of_le_one_right (sq_nonneg _) l2_opNorm_one_le
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem normalizedDilationTrace_resolvent_polynomial {n : ℕ} (z c : ℂ)
    (M E : Matrix (DilationIndex (n + 1)) (DilationIndex (n + 1)) ℂ)
    (h : let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := -(z • 1)
         (fromBlocks 0 D Dᴴ 0 - c • 1) * M = 1 + E) :
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := -(z • 1)
    let H := fromBlocks 0 D Dᴴ 0
    (((‖z‖ ^ 2 : ℝ) : ℂ) - c ^ 2) * normalizedDilationTrace M - c =
      normalizedDilationTrace ((H + c • 1) * E) := by
  intro D H
  have hsq : H * H = ((‖z‖ ^ 2 : ℝ) : ℂ) • 1 := scalarShift_dilation_mul_self _ z
  have hprod : (H + c • 1) * (H - c • 1) = (((‖z‖ ^ 2 : ℝ) : ℂ) - c ^ 2) • 1 := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc,
      Matrix.mul_sub, Matrix.one_mul, hsq, smul_sub, Matrix.one_mul, smul_smul, ← sq, sub_smul]
    abel
  have hmat := congrArg (fun X ↦ (H + c • 1) * X) h
  -- Fold the deterministic shift into `H` to apply the product formula.
  change (H + c • 1) * ((H - c • 1) * M) = (H + c • 1) * (1 + E) at hmat
  rw [← Matrix.mul_assoc, hprod, smul_mul_assoc, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    at hmat
  have htrace : normalizedDilationTrace H = 0 := by
    simp [normalizedDilationTrace_apply, H, trace_fromBlocks]
  have htr := congrArg normalizedDilationTrace hmat
  simp only [map_add, map_smul, htrace, normalizedDilationTrace_one, zero_add, smul_eq_mul,
    mul_one] at htr
  rw [htr]
  abel

private theorem norm_integral_ginibreResolvent_fluctuation_le {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ) {η : ℝ} (hη : 0 < η) :
    let P := ginibreComplex (n + 1) (n + 1)
    let R := ginibreResolvent D a ((η : ℂ) * I)
    let t G := normalizedDilationTrace (R G)
    let m := ∫ G, t G ∂P
    ‖∫ G, (t G - m) • R G ∂P‖ ≤ |a| * η⁻¹ ^ 3 := by
  intro P R t m
  have hw : ((η : ℂ) * I).im ≠ 0 := by simpa using hη.ne'
  have hr : Continuous R := continuous_ginibreResolvent D a hw
  have hb (G) : ‖R G‖ ≤ η⁻¹ := by simpa [abs_of_pos hη] using norm_ginibreResolvent_le D a hw G
  have hti : Integrable t P := Integrable.of_bound
    (normalizedDilationTrace.continuous.comp hr).aestronglyMeasurable _
    (.of_forall fun G ↦ (norm_normalized_trace_le_l2_opNorm _).trans (hb G))
  calc
    _ ≤ ∫ G, η⁻¹ * ‖t G - m‖ ∂P := by
      refine norm_integral_le_of_norm_le ((hti.sub (integrable_const _)).norm.const_mul _)
        (.of_forall fun G ↦ ?_)
      rw [norm_smul, mul_comm η⁻¹]
      exact mul_le_mul_of_nonneg_left (hb G) (norm_nonneg _)
    _ ≤ η⁻¹ * (|a| * η⁻¹ ^ 2) := by
      rw [integral_const_mul]
      have h := integral_norm_centered_dilationTrace_le D a hη
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

private theorem normalizedDilationTrace_ginibreResolvent_im_pos {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ) {η : ℝ} (hη : 0 < η)
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    0 < (normalizedDilationTrace (ginibreResolvent D a ((η : ℂ) * I) G)).im := by
  have hc : traceFactor (n + 1) =
      (((Fintype.card (DilationIndex (n + 1)) : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [traceFactor, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [normalizedDilationTrace_apply, hc, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  refine mul_pos (by positivity) ?_
  simp only [trace, diag, Complex.im_sum]
  refine Finset.sum_pos (fun i _ ↦ ?_) Finset.univ_nonempty
  exact (isHermitian_zero.fromBlocks (B := D + a • G) rfl isHermitian_zero)
    |>.im_inv_sub_smul_one_apply_self_pos (z := (η : ℂ) * I) (by simpa using hη) i

private theorem mean_normalizedDilationTrace_ginibreResolvent {n : ℕ}
    (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ) {η : ℝ} (hη : 0 < η) :
    let P := ginibreComplex (n + 1) (n + 1)
    let R := ginibreResolvent D a ((η : ℂ) * I)
    let m := ∫ G, normalizedDilationTrace (R G) ∂P
    m.re = 0 ∧ 0 < m.im ∧ ‖m‖ ≤ η⁻¹ := by
  intro P R m
  let w := (η : ℂ) * I
  let t G := normalizedDilationTrace (R G)
  have hw : w.im ≠ 0 := by simpa [w] using hη.ne'
  have hRb (G) : ‖R G‖ ≤ η⁻¹ := by
    simpa [w, abs_of_pos hη] using norm_ginibreResolvent_le D a hw G
  have hRi : Integrable R P := integrable_ginibreResolvent D a hw
  have ht : Integrable t P := normalizedDilationTrace.integrable_comp hRi
  have hm : ‖m‖ ≤ η⁻¹ := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := P) (f := t) (.of_forall fun G ↦
        (norm_normalized_trace_le_l2_opNorm (R G)).trans (hRb G))
  have hpos : 0 < m.im := by
    have hi : m.im = ∫ G, (t G).im ∂P := (imCLM.integral_comp_comm ht).symm
    rw [hi]
    have hp (G) : 0 < (t G).im := normalizedDilationTrace_ginibreResolvent_im_pos D a hη G
    refine (integral_pos_iff_support_of_nonneg (fun G ↦ (hp G).le) (imCLM.integrable_comp ht)).2 ?_
    have hs : Function.support (fun G ↦ (t G).im) = Set.univ := by
      ext G
      simp [Function.mem_support, (hp G).ne']
    simp [hs]
  have hre : m.re = 0 := by
    have hr : m.re = ∫ G, reCLM (t G) ∂P := (reCLM.integral_comp_comm ht).symm
    rw [hr]
    simp [t, R, normalizedDilationTrace_ginibreResolvent_re]
  exact ⟨hre, hpos, hm⟩

private theorem norm_mean_normalizedDilationTrace_polynomial_le (n : ℕ) (z : ℂ) {η : ℝ}
    (hη : 0 < η) :
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := -(z • 1)
    let a := (Real.sqrt (n + 1))⁻¹
    let w := (η : ℂ) * I
    let R := ginibreResolvent D a w
    let P := ginibreComplex (n + 1) (n + 1)
    let m := ∫ G, normalizedDilationTrace (R G) ∂P
    let c := w + m
    ‖(((‖z‖ ^ 2 : ℝ) : ℂ) - c ^ 2) * m - c‖ ≤
      (‖z‖ + η + η⁻¹) * a * η⁻¹ ^ 3 := by
  intro D a w R P m c
  let H := fromBlocks 0 D Dᴴ 0
  let t G := normalizedDilationTrace (R G)
  let M := ∫ G, R G ∂P
  let E := ∫ G, (t G - m) • R G ∂P
  have hw : w.im ≠ 0 := by simpa [w] using hη.ne'
  have hRi : Integrable R P := integrable_ginibreResolvent D a hw
  have hm : ‖m‖ ≤ η⁻¹ := (mean_normalizedDilationTrace_ginibreResolvent D a hη).2.2
  have hM : normalizedDilationTrace M = m := (normalizedDilationTrace.integral_comp_comm hRi).symm
  have heq : (H - c • 1) * M = 1 + E := mul_integral_normalized_ginibreResolvent_eq D hw
  have he := norm_integral_ginibreResolvent_fluctuation_le D a hη
  have ha : |a| = a := abs_of_nonneg (by positivity)
  rw [← hM, normalizedDilationTrace_resolvent_polynomial z c M E heq]
  refine (norm_normalized_trace_le_l2_opNorm _).trans ((norm_mul_le _ _).trans ?_)
  rw [mul_assoc]
  apply mul_le_mul _ (he.trans_eq (by rw [ha])) (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  have hc_le : ‖c‖ ≤ η + η⁻¹ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ hm)
    simp [w, abs_of_pos hη]
  calc
    _ ≤ ‖z‖ + ‖c‖ := add_le_add (norm_scalarShift_dilation_le _ z) (by
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) l2_opNorm_one_le)
    _ ≤ _ := by rw [add_assoc]; gcongr

/-- At imaginary height `η > 0`, the mean normalized resolvent trace of the Hermitian dilation of
`G / √(n+1) - z • 1` has positive imaginary part `u`. The residual in the shifted
singular-value equation `u * ((η + u)^2 + ‖z‖^2) = η + u` is bounded by an explicit
multiple of `1 / √(n+1)` at fixed `η` and `z`. -/
theorem abs_ginibreComplex_shifted_resolvent_cubic_sub_le (n : ℕ) (z : ℂ) {η : ℝ} (hη : 0 < η) :
    let X (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
      (Real.sqrt (n + 1))⁻¹ • G - z • 1
    let R G := (fromBlocks 0 (X G) (X G)ᴴ 0 - ((η : ℂ) * I) • 1)⁻¹
    let u := (∫ G, ((2 : ℂ) * (n + 1))⁻¹ * (R G).trace ∂ginibreComplex (n + 1) (n + 1)).im
    0 < u ∧ u ≤ η⁻¹ ∧
      |u * ((η + u) ^ 2 + ‖z‖ ^ 2) - (η + u)| ≤
        (‖z‖ + η + η⁻¹) * (Real.sqrt (n + 1))⁻¹ * η⁻¹ ^ 3 := by
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := -(z • 1)
  let a := (Real.sqrt ((n : ℝ) + 1))⁻¹
  let w := (η : ℂ) * I
  let R := ginibreResolvent D a w
  let P := ginibreComplex (n + 1) (n + 1)
  let t G := normalizedDilationTrace (R G)
  let m := ∫ G, t G ∂P
  let c := w + m
  have hp : m.re = 0 ∧ 0 < m.im ∧ ‖m‖ ≤ η⁻¹ :=
    mean_normalizedDilationTrace_ginibreResolvent D a hη
  obtain ⟨hre, hpos, hm⟩ := hp
  have hmi : m = (m.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hc : c = ((η + m.im : ℝ) : ℂ) * I := by
    simp only [c, w, Complex.ofReal_add, add_mul]
    rw [← hmi]
  have hbound : ‖(((‖z‖ ^ 2 : ℝ) : ℂ) - c ^ 2) * m - c‖ ≤
      (‖z‖ + η + η⁻¹) * a * η⁻¹ ^ 3 := norm_mean_normalizedDilationTrace_polynomial_le n z hη
  have hpoly : (((‖z‖ ^ 2 : ℝ) : ℂ) - c ^ 2) * m - c =
      ((m.im * ((η + m.im) ^ 2 + ‖z‖ ^ 2) - (η + m.im) : ℝ) : ℂ) * I := by
    have hi : ((m.im : ℂ) * I).im = m.im := by simp
    rw [hc]
    conv_lhs => rw [hmi]
    simp only [mul_pow, I_sq, hi, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_pow]
    ring
  rw [hpoly, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hbound
  have htdef : ∀ G, t G = ((2 : ℂ) * (n + 1))⁻¹ *
      (fromBlocks 0 (a • G - z • 1) (a • G - z • 1)ᴴ 0 - w • 1)⁻¹.trace := by
    intro G
    have hshift : D + a • G = a • G - z • 1 := by
      simp only [D, sub_eq_add_neg, add_comm]
    simp only [t, R, ginibreResolvent, hshift, normalizedDilationTrace_apply, traceFactor,
      Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_succ, two_mul]
  simpa only [m, htdef, w, a] using
    And.intro hpos (And.intro ((le_abs_self _).trans ((abs_im_le_norm m).trans hm)) hbound)

end SelfConsistency

end TauCeti.Probability
