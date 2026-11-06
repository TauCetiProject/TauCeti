/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Correlation
public import TauCeti.Probability.Distributions.LKJ.Normalizer
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Normalization of determinant powers on correlation matrices

Positive-definite correlation matrices are parametrized by their partial correlations in the
open cube.  In these coordinates the determinant and the Jacobian are products of powers of
`1 - zᵢⱼ²`, so the determinant-power integral factors into Euler beta integrals.  This file
evaluates that integral as `lkjNormalizer p η`, providing the normalization identity used to
define the LKJ probability law.

## Main result

* `TauCeti.Probability.integral_rpow_det_correlationLebesgue` evaluates the determinant-power
  integral over the positive-definite correlation matrices.
* `TauCeti.Probability.integrableOn_rpow_det_correlationLebesgue` proves the corresponding
  integrability statement.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators

namespace TauCeti.Probability

private theorem image_centered_Ioo :
    (fun x : ℝ ↦ -1 + 2 * x) '' Ioo 0 1 = Ioo (-1) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor <;> linarith [hx.1, hx.2]
  · intro hy
    refine ⟨(y + 1) / 2, ?_, by ring⟩
    constructor <;> linarith [hy.1, hy.2]

/-- The beta integral in centered coordinates. -/
private theorem integral_one_sub_sq_rpow {a : ℝ} (ha : 0 < a) :
    ∫ z in Ioo (-1 : ℝ) 1, (1 - z ^ 2) ^ (a - 1) = beta (1 / 2) a := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Ioo (0 : ℝ) 1) (f := fun x : ℝ ↦ -1 + 2 * x) (f' := fun _ ↦ 2)
    measurableSet_Ioo
    (fun x _ ↦ by
      simpa [mul_comm] using
        (((hasDerivAt_id x).const_mul 2).const_add (-1)).hasDerivWithinAt)
    (fun x _ y _ hxy ↦ by
      have : x * 2 = y * 2 := by simpa using hxy
      linarith) (fun z : ℝ ↦ (1 - z ^ 2) ^ (a - 1))
  rw [image_centered_Ioo] at hchange
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) 1,
      |(2 : ℝ)| • (1 - (-1 + 2 * x) ^ 2) ^ (a - 1) =
        2 ^ (2 * a - 1) * (x ^ (a - 1) * (1 - x) ^ (a - 1)) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : 0 ≤ 1 - x := sub_nonneg.2 hx.2.le
    have hfour : (0 : ℝ) ≤ 4 := by norm_num
    have hpow : 2 * (4 : ℝ) ^ (a - 1) = 2 ^ (2 * a - 1) := by
      calc
        2 * (4 : ℝ) ^ (a - 1) =
            (2 : ℝ) ^ (1 : ℝ) * ((2 : ℝ) ^ (2 : ℝ)) ^ (a - 1) := by
              norm_num [Real.rpow_one, Real.rpow_two]
        _ = (2 : ℝ) ^ (1 + 2 * (a - 1)) := by
          rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
        _ = (2 : ℝ) ^ (2 * a - 1) := by congr 1; ring
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul]
    have harg : 1 - (-1 + 2 * x) ^ 2 = 4 * (x * (1 - x)) := by ring
    rw [harg, Real.mul_rpow hfour (mul_nonneg hx0 hx1), Real.mul_rpow hx0 hx1,
      ← mul_assoc, hpow]
  have hbeta :
      ∫ x in Ioo (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (a - 1) = beta a a := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow_mul_one_sub_rpow ha ha]
  rw [setIntegral_congr_fun measurableSet_Ioo hpoint, integral_const_mul, hbeta] at hchange
  rw [hchange, ProbabilityTheory.beta_one_half_left_eq_two_rpow_mul_beta_self ha]

private def strictLowerTriangleColumnEquiv (j : Fin p) :
    {ij : strictLowerTriangle p // ij.1.2 = j} ≃ {i : Fin p // j < i} where
  toFun ij := ⟨ij.1.1.1, by simpa [ij.2] using ij.1.2⟩
  invFun i := ⟨⟨(i.1, j), i.2⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨i, k⟩, hik⟩, hkj⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl hkj.symm
  right_inv := by
    rintro ⟨i, hji⟩
    rfl

private theorem prod_lkjBetaFactors (p : ℕ) (η : ℝ) :
    (∏ ij : strictLowerTriangle p,
      beta (1 / 2) (η + (((p - 1 - ij.1.2.1 - 1 : ℕ) : ℝ) / 2))) =
      lkjNormalizer p η := by
  let F : ℕ → ℝ := fun k ↦ beta (1 / 2) (η + (((k - 1 : ℕ) : ℝ) / 2)) ^ k
  calc
    _ = ∏ j : Fin p,
        beta (1 / 2) (η + (((p - 1 - j.1 - 1 : ℕ) : ℝ) / 2)) ^
          (p - 1 - j.1) := by
      rw [← Fintype.prod_fiberwise' (fun ij : strictLowerTriangle p ↦ ij.1.2)
        (fun j : Fin p ↦
          beta (1 / 2) (η + (((p - 1 - j.1 - 1 : ℕ) : ℝ) / 2)))]
      apply Finset.prod_congr rfl
      intro j _
      simp only [Finset.prod_const, Finset.card_univ]
      have hcard : Fintype.card {i : Fin p // j < i} = p - 1 - j.1 := by
        calc
          _ = Fintype.card (Finset.Ioi j) :=
            Fintype.card_congr (Equiv.subtypeEquivRight (by simp))
          _ = (Finset.Ioi j).card := Fintype.card_coe _
          _ = p - 1 - j.1 := Fin.card_Ioi j
      rw [← hcard, Fintype.card_congr (strictLowerTriangleColumnEquiv j)]
    _ = ∏ j : Fin p, F (p - 1 - j.1) := by rfl
    _ = ∏ k ∈ Finset.range p, F k := by
      calc
        _ = ∏ k ∈ Finset.range p, F (p - 1 - k) :=
          Fin.prod_univ_eq_prod_range (fun k ↦ F (p - 1 - k)) p
        _ = _ := Finset.prod_range_reflect F p
    _ = lkjNormalizer p η := by
      rw [lkjNormalizer_def]
      by_cases hp : p = 0
      · subst p
        simp
      · rw [Finset.prod_range_eq_mul_Ico F (Nat.pos_of_ne_zero hp)]
        simp only [F, pow_zero, one_mul]
        apply Finset.prod_congr rfl
        intro k hk
        rw [Nat.cast_sub (Finset.mem_Ico.mp hk).1]
        norm_num

private theorem integral_rpow_det_posDefCorrelationRegion (p : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫ x in posDefCorrelationRegion p,
      (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) =
        lkjNormalizer p η := by
  let cube : Set (strictLowerTriangle p → ℝ) := {z | ∀ ij, |z ij| < 1}
  let factor : strictLowerTriangle p → ℝ → ℝ := fun ij z ↦
    (1 - z ^ 2) ^
      (η + (((p - 1 - ij.1.2.1 - 1 : ℕ) : ℝ) / 2) - 1)
  have hcube_eq : cube = Set.univ.pi fun _ ↦ Ioo (-1 : ℝ) 1 := by
    ext z
    simp only [cube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const, mem_Ioo,
      abs_lt]
  have hopen : IsOpen cube := by
    rw [hcube_eq]
    exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo
  have hcube : MeasurableSet cube := by
    exact hopen.measurableSet
  have hderiv : ∀ z ∈ cube,
      HasFDerivWithinAt (correlationCoordinatesOfPartialCorrelation (p := p))
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z) cube z := by
    intro z hz
    exact ((contDiffOn_correlationCoordinatesOfPartialCorrelation.differentiableOn
      (by simp) z hz).differentiableAt (hopen.mem_nhds hz)).hasFDerivAt.hasFDerivWithinAt
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hcube hderiv
    (injOn_correlationCoordinatesOfPartialCorrelation (p := p))
    (fun x ↦ (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1))
  rw [image_correlationCoordinatesOfPartialCorrelation] at hchange
  have hpoint : ∀ z ∈ cube,
      |(fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).det| •
          (correlationMatrix p (correlationCoordinatesOfPartialCorrelation z) :
            Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) =
        ∏ ij, factor ij (z ij) := by
    intro z hz
    have hz' : ∀ ij, |z ij| < 1 := hz
    have hpos : ∀ ij, 0 < 1 - z ij ^ 2 := fun ij ↦
      sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 (hz' ij))
    have hnonneg : ∀ ij, 0 ≤ 1 - z ij ^ 2 := fun ij ↦ (hpos ij).le
    have hrpow :
        (Finset.univ.prod fun ij : strictLowerTriangle p ↦ 1 - z ij ^ 2) ^ (η - 1) =
          Finset.univ.prod fun ij : strictLowerTriangle p ↦
            (1 - z ij ^ 2) ^ (η - 1) := by
      simpa using (Real.finsetProd_rpow Finset.univ (fun ij ↦ 1 - z ij ^ 2)
        (fun ij _ ↦ hnonneg ij) (η - 1)).symm
    rw [abs_det_fderiv_correlationCoordinatesOfPartialCorrelation hz', smul_eq_mul,
      coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation
        (fun ij ↦ (hz' ij).le), det_partialCorrelationGram (fun ij ↦ (hz' ij).le),
      hrpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ij _
    rw [← Real.rpow_natCast, ← Real.rpow_div_two_eq_sqrt _ (hnonneg ij),
      ← Real.rpow_add (hpos ij)]
    congr 1
    have hindex : p - ij.1.2.1 - 2 = p - 1 - ij.1.2.1 - 1 := by
      omega
    rw [hindex]
    ring
  rw [setIntegral_congr_fun hcube hpoint] at hchange
  have hfactor (ij : strictLowerTriangle p) :
      ∫ z in Ioo (-1 : ℝ) 1, factor ij z =
        beta (1 / 2) (η + (((p - 1 - ij.1.2.1 - 1 : ℕ) : ℝ) / 2)) := by
    apply integral_one_sub_sq_rpow
    positivity
  have heval : ∫ z in cube, ∏ ij, factor ij (z ij) = lkjNormalizer p η := by
    rw [hcube_eq]
    change ∫ z, ∏ ij, factor ij (z ij) ∂
      volume.restrict (Set.univ.pi fun _ : strictLowerTriangle p ↦ Ioo (-1 : ℝ) 1) = _
    rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
    simp_rw [hfactor]
    exact prod_lkjBetaFactors p η
  exact hchange.trans heval

/-- The determinant power with parameter `η > 0` integrates over positive-definite correlation
matrices to the LKJ normalizing constant. -/
theorem integral_rpow_det_correlationLebesgue (p : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) ∂correlationLebesgue p =
        lkjNormalizer p η := by
  rw [← integral_indicator (measurableSet_posDefMatrix p)]
  calc
    _ = ∫ x : strictLowerTriangle p → ℝ,
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator
          (fun A ↦ (A : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1))
          (correlationMatrix p x) :=
      ((measurePreserving_correlationMatrix p).integral_comp
        (measurableEmbedding_correlationMatrix p) _).symm
    _ = ∫ x in posDefCorrelationRegion p,
        (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) := by
      rw [← integral_indicator (measurableSet_posDefCorrelationRegion p)]
      congr 1
      funext x
      by_cases hx : x ∈ posDefCorrelationRegion p
      · rw [indicator_of_mem hx, indicator_of_mem (mem_posDefCorrelationRegion.1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem]
        exact fun h ↦ hx (mem_posDefCorrelationRegion.2 h)
    _ = lkjNormalizer p η := integral_rpow_det_posDefCorrelationRegion p hη

/-- The determinant power with parameter `η > 0` is integrable on positive-definite correlation
matrices with respect to correlation Lebesgue measure. -/
theorem integrableOn_rpow_det_correlationLebesgue (p : ℕ) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1))
      {A | (A : Matrix (Fin p) (Fin p) ℝ).PosDef} (correlationLebesgue p) := by
  by_contra h
  have hzero := integral_undef h
  rw [integral_rpow_det_correlationLebesgue p hη] at hzero
  exact (lkjNormalizer_pos hη).ne' hzero

end TauCeti.Probability
