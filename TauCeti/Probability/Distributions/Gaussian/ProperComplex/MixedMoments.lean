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

private theorem complexGaussianPart_eq_coordinate (m : ι → ℂ) [Fintype ι]
    (i : ι) (a : Bool) (z : ι → ℂ) :
    complexGaussianPart m i a z =
      complexToRealEuclidean ι z (complexGaussianPartIndex i a) -
        complexToRealEuclidean ι m (complexGaussianPartIndex i a) := by
  cases a <;> simp [complexGaussianPart, complexGaussianPartIndex,
    complexToRealEuclidean_apply]

private def complexGaussianPartCoeff (conjugated : Bool) : Bool → ℂ :=
  fun
  | false => 1
  | true => if conjugated then -Complex.I else Complex.I

private def complexGaussianPairing (C : Matrix ι ι ℂ) (i j : ι) (x y : Bool) : ℂ :=
  ∑ a : Bool, ∑ b : Bool, complexGaussianPartCoeff x a * complexGaussianPartCoeff y b *
    (complexGaussianRealCovariance C (complexGaussianPartIndex i a)
      (complexGaussianPartIndex j b) : ℂ)

private theorem complexGaussianPairing_values (C : Matrix ι ι ℂ) (i j : ι) :
    complexGaussianPairing C i j false true = C i j ∧
    complexGaussianPairing C i j true false = star (C i j) ∧
    complexGaussianPairing C i j false false = 0 ∧
    complexGaussianPairing C i j true true = 0 := by
  simp only [complexGaussianPairing, Fintype.sum_bool, complexGaussianPartCoeff,
    complexGaussianPartIndex, complexGaussianRealCovariance_inl_inl,
    complexGaussianRealCovariance_inl_inr, complexGaussianRealCovariance_inr_inl,
    complexGaussianRealCovariance_inr_inr, Bool.false_eq_true, ite_true, ite_false]
  repeat' constructor
  all_goals
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]; ring

private theorem complexGaussianPairings_factor (C : Matrix ι ι ℂ) (i j k l : ι) :
    (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
      complexGaussianPartCoeff false a * complexGaussianPartCoeff true b *
        complexGaussianPartCoeff false c * complexGaussianPartCoeff true d *
          ((complexGaussianRealCovariance C (complexGaussianPartIndex i a)
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
              (complexGaussianPartIndex k c) : ℝ) : ℂ)) =
      complexGaussianPairing C i j false true * complexGaussianPairing C k l false true +
      complexGaussianPairing C i k false false * complexGaussianPairing C j l true true +
      complexGaussianPairing C i l false true * complexGaussianPairing C j k true false := by
  simp only [complexGaussianPairing, Fintype.sum_bool, Complex.ofReal_add, Complex.ofReal_mul]
  ring

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
  simpa only [complexGaussianPart_eq_coordinate] using integral_four_real_coordinates m hC
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
  ring

private theorem integrable_complexGaussianFourthTerm (m : ι → ℂ) (C : Matrix ι ι ℂ)
    [Fintype ι] [DecidableEq ι] (i j k l : ι) (a b c d : Bool) :
    Integrable (fun z ↦ complexGaussianFourthTerm m i j k l a b c d z)
      (properComplexGaussianMeasure m C) := by
  let indices : Fin 4 → ι ⊕ ι :=
    ![complexGaussianPartIndex i a, complexGaussianPartIndex j b,
      complexGaussianPartIndex k c, complexGaussianPartIndex l d]
  let L : Fin 4 → StrongDual ℝ (ι → ℂ) := fun q ↦
    (EuclideanSpace.proj (indices q)).comp (complexToRealEuclidean ι).toContinuousLinearMap
  have hint := IsGaussian.integrable_prod_dual (properComplexGaussianMeasure m C)
    (Finset.univ : Finset (Fin 4)) L (fun q ↦ -L q m)
  have hcast := Complex.ofRealCLM.integrable_comp hint
  simp only [complexGaussianFourthTerm, complexGaussianPart_eq_coordinate]
  simpa [complexGaussianFourthTerm, L, indices, Fin.prod_univ_succ,
    complexToRealEuclidean_apply, sub_eq_add_neg, Complex.ofReal_mul, mul_assoc] using
    hcast.const_mul
    (complexGaussianPartCoeff false a * complexGaussianPartCoeff true b *
      complexGaussianPartCoeff false c * complexGaussianPartCoeff true d)

/-- The fourth centered complex coordinate product is integrable, for any covariance matrix. -/
theorem integrable_mul_conj_mul_conj_sub_properComplexGaussianMeasure
    (m : ι → ℂ) (C : Matrix ι ι ℂ) [Fintype ι] [DecidableEq ι] (i j k l : ι) :
    Integrable (fun z ↦ (z i - m i) * star (z j - m j) *
      (z k - m k) * star (z l - m l)) (properComplexGaussianMeasure m C) := by
  simp_rw [complexGaussianFourth_eq_sum_parts]
  exact integrable_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun b _ ↦
    integrable_finsetSum _ (fun c _ ↦ integrable_finsetSum _ (fun d _ ↦
      integrable_complexGaussianFourthTerm m C i j k l a b c d))))

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
  simp only [complexGaussianFourthTerm]
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
          have hfactor := complexGaussianPairings_factor C i j k l
          simp only [Complex.ofReal_add, Complex.ofReal_mul] at hfactor
          rw [hfactor]
          simp only [(complexGaussianPairing_values C _ _).1,
            (complexGaussianPairing_values C _ _).2.1,
            (complexGaussianPairing_values C _ _).2.2.1,
            (complexGaussianPairing_values C _ _).2.2.2, zero_mul, add_zero]
          rw [(hC.isHermitian.apply j k).symm, star_star]

end TauCeti.Probability
