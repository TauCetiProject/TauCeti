/- 
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.MixedMoments
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Moments

/-!
# Fourth mixed moments of proper complex Gaussian laws

The fourth centered mixed moment with two coordinates and two conjugated coordinates is the sum
of the two covariance pairings. This is the proper-complex Wick formula, including singular
covariance matrices.

## References

* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134–139.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder ENNReal

namespace TauCeti.Probability

variable {ι : Type*}

private theorem integral_four_real_coordinates (m : ι → ℂ) {C : Matrix ι ι ℂ}
    [Fintype ι] [DecidableEq ι] (hC : C.PosSemidef) (a b c d : ι ⊕ ι) :
    ∫ z, (complexToRealEuclidean ι z a - complexToRealEuclidean ι m a) *
        (complexToRealEuclidean ι z b - complexToRealEuclidean ι m b) *
        (complexToRealEuclidean ι z c - complexToRealEuclidean ι m c) *
        (complexToRealEuclidean ι z d - complexToRealEuclidean ι m d)
        ∂properComplexGaussianMeasure m C =
      complexGaussianRealCovariance C a b * complexGaussianRealCovariance C c d +
      complexGaussianRealCovariance C a c * complexGaussianRealCovariance C b d +
      complexGaussianRealCovariance C a d * complexGaussianRealCovariance C b c := by
  rw [properComplexGaussianMeasure_def,
    integral_map (by fun_prop) (by fun_prop)]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    integral_mul_mul_mul_sub_multivariateGaussian
      (complexToRealEuclidean ι m)
      ((posSemidef_complexGaussianRealCovariance_iff C).2 hC) a b c d

private def complexGaussianPart (m : ι → ℂ) (i : ι) :
    Bool → (ι → ℂ) → ℝ :=
  fun
  | false, z => (z i).re - (m i).re
  | true, z => (z i).im - (m i).im

private def complexGaussianPartIndex (i : ι) : Bool → ι ⊕ ι :=
  fun
  | false => Sum.inl i
  | true => Sum.inr i

private def complexGaussianPartCoeff (conjugated : Bool) : Bool → ℂ :=
  fun
  | false => 1
  | true => if conjugated then -Complex.I else Complex.I

private theorem memLp_complexGaussianPart (m : ι → ℂ) (C : Matrix ι ι ℂ) (i : ι)
    [Fintype ι] [DecidableEq ι] (a : Bool) :
    MemLp (complexGaussianPart m i a) 4 (properComplexGaussianMeasure m C) := by
  have h := (memLp_apply_properComplexGaussianMeasure m C i 4 (by norm_num)).sub
    (memLp_const (m i))
  cases a
  · change MemLp (fun (z : ι → ℂ) ↦ (z i).re - (m i).re) 4
      (properComplexGaussianMeasure m C)
    exact h.continuousLinearMap_comp Complex.reCLM
  · change MemLp (fun (z : ι → ℂ) ↦ (z i).im - (m i).im) 4
      (properComplexGaussianMeasure m C)
    exact h.continuousLinearMap_comp Complex.imCLM

private theorem complexGaussianCoordinate_eq_sum_parts (m : ι → ℂ) (i : ι)
    (z : ι → ℂ) :
    z i - m i =
      ∑ a : Bool, complexGaussianPartCoeff false a *
        (complexGaussianPart m i a z : ℂ) := by
  rw [← Complex.re_add_im (z i - m i), Fintype.sum_bool]
  simp [complexGaussianPartCoeff, complexGaussianPart, Complex.sub_re, Complex.sub_im]
  ring

private theorem star_complexGaussianCoordinate_eq_sum_parts (m : ι → ℂ) (i : ι)
    (z : ι → ℂ) :
    star (z i - m i) =
      ∑ a : Bool, complexGaussianPartCoeff true a *
        (complexGaussianPart m i a z : ℂ) := by
  rw [complexGaussianCoordinate_eq_sum_parts]
  simp [complexGaussianPartCoeff, complexGaussianPart,
    Complex.conj_ofReal, Complex.conj_I]

private theorem integral_four_complexGaussianParts (m : ι → ℂ) {C : Matrix ι ι ℂ}
    [Fintype ι] [DecidableEq ι] (hC : C.PosSemidef) (i j k l : ι)
    (a b c d : Bool) :
    ∫ z, complexGaussianPart m i a z * complexGaussianPart m j b z *
        complexGaussianPart m k c z * complexGaussianPart m l d z
        ∂properComplexGaussianMeasure m C =
      complexGaussianRealCovariance C (complexGaussianPartIndex i a)
          (complexGaussianPartIndex j b) *
        complexGaussianRealCovariance C (complexGaussianPartIndex k c)
          (complexGaussianPartIndex l d) +
      complexGaussianRealCovariance C (complexGaussianPartIndex i a)
          (complexGaussianPartIndex k c) *
        complexGaussianRealCovariance C (complexGaussianPartIndex j b)
          (complexGaussianPartIndex l d) +
      complexGaussianRealCovariance C (complexGaussianPartIndex i a)
          (complexGaussianPartIndex l d) *
        complexGaussianRealCovariance C (complexGaussianPartIndex j b)
          (complexGaussianPartIndex k c) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simpa [complexGaussianPart, complexGaussianPartIndex, ha, hb, hc, hd,
      complexToRealEuclidean_apply] using
      integral_four_real_coordinates m hC
        (complexGaussianPartIndex i a) (complexGaussianPartIndex j b)
        (complexGaussianPartIndex k c) (complexGaussianPartIndex l d)

private def complexGaussianFourthTerm (m : ι → ℂ) (i j k l : ι)
    (a b c d : Bool) (z : ι → ℂ) : ℂ :=
  complexGaussianPartCoeff false a * complexGaussianPartCoeff true b *
    complexGaussianPartCoeff false c * complexGaussianPartCoeff true d *
      ((complexGaussianPart m i a z : ℂ) * complexGaussianPart m j b z *
        complexGaussianPart m k c z * complexGaussianPart m l d z)

private theorem complexGaussianFourth_eq_sum_parts (m : ι → ℂ) (i j k l : ι)
    (z : ι → ℂ) :
    (z i - m i) * star (z j - m j) * (z k - m k) * star (z l - m l) =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        complexGaussianFourthTerm m i j k l a b c d z := by
  rw [complexGaussianCoordinate_eq_sum_parts, star_complexGaussianCoordinate_eq_sum_parts,
    complexGaussianCoordinate_eq_sum_parts, star_complexGaussianCoordinate_eq_sum_parts]
  simp_rw [Fintype.sum_bool]
  simp only [complexGaussianFourthTerm, complexGaussianPartCoeff, complexGaussianPart]
  ; ring

private theorem integrable_complexGaussianFourthTerm (m : ι → ℂ) (C : Matrix ι ι ℂ)
    [Fintype ι] [DecidableEq ι] (i j k l : ι) (a b c d : Bool) :
    Integrable (fun z ↦ complexGaussianFourthTerm m i j k l a b c d z)
      (properComplexGaussianMeasure m C) := by
  let F : Fin 4 → (ι → ℂ) → ℂ := ![
    fun z ↦ (complexGaussianPart m i a z : ℂ),
    fun z ↦ (complexGaussianPart m j b z : ℂ),
    fun z ↦ (complexGaussianPart m k c z : ℂ),
    fun z ↦ (complexGaussianPart m l d z : ℂ)]
  have hF (q : Fin 4) :
      MemLp (F q) 4 (properComplexGaussianMeasure m C) := by
    fin_cases q <;>
      simpa [F] using
        (memLp_complexGaussianPart m C _ _).continuousLinearMap_comp Complex.ofRealCLM
  have hprod := MemLp.fun_prod (s := Finset.univ)
    (p := fun _ : Fin 4 ↦ (4 : ℝ≥0∞)) (fun q _ ↦ hF q)
  have hexp :
      (∑ _q ∈ (Finset.univ : Finset (Fin 4)), (4 : ℝ≥0∞)⁻¹)⁻¹ = 1 := by
    norm_num [Fin.sum_univ_succ]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [hexp] at hprod
  have hint := memLp_one_iff_integrable.mp hprod
  simpa [complexGaussianFourthTerm, F, Fin.prod_univ_succ, mul_assoc] using
    hint.const_mul
    (complexGaussianPartCoeff false a * complexGaussianPartCoeff true b *
      complexGaussianPartCoeff false c * complexGaussianPartCoeff true d)

private theorem integral_complexGaussianFourthTerm (m : ι → ℂ) {C : Matrix ι ι ℂ}
    [Fintype ι] [DecidableEq ι] (hC : C.PosSemidef) (i j k l : ι)
    (a b c d : Bool) :
    ∫ z, complexGaussianFourthTerm m i j k l a b c d z
        ∂properComplexGaussianMeasure m C =
      complexGaussianPartCoeff false a * complexGaussianPartCoeff true b *
        complexGaussianPartCoeff false c * complexGaussianPartCoeff true d *
          (complexGaussianRealCovariance C (complexGaussianPartIndex i a)
              (complexGaussianPartIndex j b) *
            complexGaussianRealCovariance C (complexGaussianPartIndex k c)
              (complexGaussianPartIndex l d) +
            complexGaussianRealCovariance C (complexGaussianPartIndex i a)
              (complexGaussianPartIndex k c) *
            complexGaussianRealCovariance C (complexGaussianPartIndex j b)
              (complexGaussianPartIndex l d) +
            complexGaussianRealCovariance C (complexGaussianPartIndex i a)
              (complexGaussianPartIndex l d) *
            complexGaussianRealCovariance C (complexGaussianPartIndex j b)
              (complexGaussianPartIndex k c)) := by
  let f : (ι → ℂ) → ℝ := fun z ↦
    complexGaussianPart m i a z * complexGaussianPart m j b z *
      complexGaussianPart m k c z * complexGaussianPart m l d z
  have hcast (z : ι → ℂ) :
      (complexGaussianPart m i a z : ℂ) * complexGaussianPart m j b z *
          complexGaussianPart m k c z * complexGaussianPart m l d z =
        (f z : ℂ) := by
    simp only [f, Complex.ofReal_mul]
  change ∫ z, (complexGaussianPartCoeff false a * complexGaussianPartCoeff true b *
    complexGaussianPartCoeff false c * complexGaussianPartCoeff true d) *
      ((complexGaussianPart m i a z : ℂ) * complexGaussianPart m j b z *
        complexGaussianPart m k c z * complexGaussianPart m l d z)
      ∂properComplexGaussianMeasure m C = _
  simp_rw [hcast]
  rw [integral_const_mul]
  apply congrArg (fun x : ℂ ↦
    (complexGaussianPartCoeff false a * complexGaussianPartCoeff true b *
      complexGaussianPartCoeff false c * complexGaussianPartCoeff true d) * x)
  calc
    _ = ((∫ z, f z ∂properComplexGaussianMeasure m C : ℝ) : ℂ) := by
      exact _root_.integral_ofReal
    _ = _ := congrArg Complex.ofReal
      (integral_four_complexGaussianParts m hC i j k l a b c d)
    _ = _ := by
      simp only [Complex.ofReal_add, Complex.ofReal_mul]

/-- The fourth centered mixed moment of a proper complex Gaussian is the sum of its two
covariance pairings. Equivalently, for covariance `C`,

`E[(Zᵢ-mᵢ) * conj (Zⱼ-mⱼ) * (Zₖ-mₖ) * conj (Zₗ-mₗ)] =
  Cᵢⱼ * Cₖₗ + Cᵢₗ * Cₖⱼ`.

The identity includes singular covariance matrices. -/
theorem integral_mul_conj_mul_conj_sub_properComplexGaussianMeasure
    (m : ι → ℂ) [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℂ}
    (hC : C.PosSemidef) (i j k l : ι) :
    ∫ z, (z i - m i) * star (z j - m j) * (z k - m k) * star (z l - m l)
        ∂properComplexGaussianMeasure m C =
      C i j * C k l + C i l * C k j := by
  let T := complexGaussianFourthTerm m i j k l
  have hterm (a b c d : Bool) :
      Integrable (fun z ↦ T a b c d z) (properComplexGaussianMeasure m C) := by
    exact integrable_complexGaussianFourthTerm m C i j k l a b c d
  have hsumD (a b c : Bool) :
      Integrable (fun z ↦ ∑ d : Bool, T a b c d z) (properComplexGaussianMeasure m C) :=
    integrable_finsetSum _ (fun d _ ↦ hterm a b c d)
  have hsumC (a b : Bool) :
      Integrable (fun z ↦ ∑ c : Bool, ∑ d : Bool, T a b c d z)
        (properComplexGaussianMeasure m C) :=
    integrable_finsetSum _ (fun c _ ↦ hsumD a b c)
  have hsumB (a : Bool) :
      Integrable (fun z ↦ ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, T a b c d z)
        (properComplexGaussianMeasure m C) :=
    integrable_finsetSum _ (fun b _ ↦ hsumC a b)
  calc
    _ = ∫ z, ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        T a b c d z ∂properComplexGaussianMeasure m C := by
          congr 1
          funext z
          exact complexGaussianFourth_eq_sum_parts m i j k l z
    _ = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        ∫ z, T a b c d z ∂properComplexGaussianMeasure m C := by
          rw [integral_finsetSum _ (fun a _ ↦ hsumB a)]
          simp_rw [integral_finsetSum _ (fun b _ ↦ hsumC _ b)]
          simp_rw [integral_finsetSum _ (fun c _ ↦ hsumD _ _ c)]
          simp_rw [integral_finsetSum _ (fun d _ ↦ hterm _ _ _ d)]
    _ = C i j * C k l + C i l * C k j := by
          simp_rw [T, integral_complexGaussianFourthTerm m hC]
          simp_rw [Fintype.sum_bool]
          have hjk : C j k = star (C k j) := (hC.isHermitian.apply j k).symm
          simp only [complexGaussianPartCoeff, complexGaussianPartIndex,
            complexGaussianRealCovariance_inl_inl, complexGaussianRealCovariance_inl_inr,
            complexGaussianRealCovariance_inr_inl, complexGaussianRealCovariance_inr_inr,
            hjk, Bool.false_eq_true, ite_true, ite_false]
          apply Complex.ext
          · simp [Complex.mul_re, Complex.mul_im]
            ring
          · simp [Complex.mul_re, Complex.mul_im]
            ring

end TauCeti.Probability
