/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Bartlett

import TauCeti.Probability.Distributions.Wishart.Congruence

/-!
# The determinant of a Wishart matrix

The determinant of a nonsingular Wishart matrix of real degree `n` and scale `S` has the law
of `det S` times a product of independent chi-squared variables with degrees `n - i`, for
zero-based indices `i < p`. This identifies the determinant law without requiring integer
degrees and is the product representation used to compute its real-power moments.

The standard-scale result follows from the independent diagonal squares in Bartlett's
decomposition. Congruence by a square root of the scale supplies the determinant factor.
In dimension zero, the empty product and the determinant are both one.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Section 3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped MatrixOrder

namespace TauCeti.Probability

variable {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

/-- The determinant of a standard Wishart matrix is a product of independent chi-squared
variables. This includes the empty product in dimension zero. -/
theorem map_det_nonsingularWishartMeasure_one (hn : (p : ℝ) - 1 < n) :
    (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ).det) =
      (Measure.pi (fun i : Fin p ↦ chiSquaredMeasure (n - i.1))).map
        (fun x ↦ ∏ i, x i) := by
  rw [nonsingularWishartMeasure_one_eq_map_lowerTriangleGram hn,
    Measure.map_map (by fun_prop) (measurable_lowerTriangleGram p),
    ← map_diagonal_sq_pi_bartlettCoordinateMeasure hn,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, coe_lowerTriangleGram, Matrix.det_mul, Matrix.det_transpose,
    det_lowerTriangleMatrix, ← pow_two, Finset.prod_pow]

/-- The determinant of a Wishart matrix of scale `S` is `det S` times a product of independent
chi-squared variables of degrees `n, n - 1, …, n - p + 1`. -/
theorem map_det_nonsingularWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    (nonsingularWishartMeasure n S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ).det) =
      (Measure.pi (fun i : Fin p ↦ chiSquaredMeasure (n - i.1))).map
        (fun x ↦ S.det * ∏ i, x i) := by
  have hsqrt : (CFC.sqrt S).det ^ 2 = S.det := by
    simpa only [Matrix.det_mul, pow_two] using
      congrArg Matrix.det (CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg)
  rw [nonsingularWishartMeasure_eq_map_sqrt n hS,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ).det) ∘
      Matrix.symmetricCongruenceLinearMap (CFC.sqrt S) =
        (fun x ↦ S.det * x) ∘ (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ).det) := by
    funext A
    simp only [Function.comp_apply, Matrix.det_coe_symmetricCongruenceLinearMap_apply, hsqrt]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_det_nonsingularWishartMeasure_one hn, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A random Wishart matrix has the scaled chi-squared-product determinant law. -/
theorem hasLaw_det_nonsingularWishartMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : HasLaw A (nonsingularWishartMeasure n S) P)
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    HasLaw (fun ω ↦ (A ω : Matrix (Fin p) (Fin p) ℝ).det)
      ((Measure.pi (fun i : Fin p ↦ chiSquaredMeasure (n - i.1))).map
        (fun x ↦ S.det * ∏ i, x i)) P :=
  (⟨by fun_prop, map_det_nonsingularWishartMeasure hS hn⟩ :
    HasLaw _ _ (nonsingularWishartMeasure n S)).fun_comp hA

/-- A scaled product of independent chi-squared variables realizes the determinant law of a
Wishart matrix, including the empty product in dimension zero. -/
theorem hasLaw_prod_chiSquared_det_nonsingularWishartMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Fin p → Ω → ℝ} (hY : iIndepFun Y P)
    (hLaw : ∀ i, HasLaw (Y i) (chiSquaredMeasure (n - i.1)) P)
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    HasLaw (fun ω ↦ S.det * ∏ i, Y i ω)
      ((nonsingularWishartMeasure n S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ).det)) P := by
  rw [map_det_nonsingularWishartMeasure hS hn]
  exact (⟨by fun_prop, rfl⟩ : HasLaw (fun x : Fin p → ℝ ↦ S.det * ∏ i, x i)
    _ (Measure.pi (fun i : Fin p ↦ chiSquaredMeasure (n - i.1)))).fun_comp (hY.hasLaw_pi hLaw)

/-- For positive dimension, the `q`-th real power of the determinant is integrable under a
nonsingular Wishart law exactly above the sharp Bartlett threshold. -/
@[simp]
theorem integrable_rpow_det_nonsingularWishartMeasure_iff (hp : 0 < p) (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (q : ℝ) :
    Integrable
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ).det ^ q)
        (nonsingularWishartMeasure n S) ↔
      -((n - p + 1) / 2) < q := by
  have hk (i : Fin p) : 0 < n - i.1 := by
    have hi : (i.1 : ℝ) + 1 ≤ p := by exact_mod_cast i.2
    linarith
  have hdet : Measurable
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ).det) := by fun_prop
  let _ (i : Fin p) : IsProbabilityMeasure (chiSquaredMeasure (n - i.1)) :=
    isProbabilityMeasure_chiSquaredMeasure (hk i).le
  refine (integrable_map_measure (g := fun x : ℝ ↦ x ^ q) (by fun_prop)
    hdet.aemeasurable).symm.trans ?_
  rw [map_det_nonsingularWishartMeasure hS hn,
    integrable_map_measure (by fun_prop) (by fun_prop), Function.comp_def]
  have hpos : ∀ᵐ x ∂Measure.pi (fun i : Fin p ↦ chiSquaredMeasure (n - i.1)),
      ∀ i, 0 < x i := Filter.eventually_all.2 fun i ↦
    Measure.tendsto_eval_ae_ae.eventually (ae_pos_chiSquaredMeasure (hk i))
  have hae : (fun x : Fin p → ℝ ↦ (S.det * ∏ i, x i) ^ q) =ᵐ[
      Measure.pi (fun i : Fin p ↦ chiSquaredMeasure (n - i.1))]
      fun x ↦ S.det ^ q * ∏ i, x i ^ q := by
    filter_upwards [hpos] with x hx
    rw [Real.mul_rpow hS.det_pos.le (Finset.prod_nonneg fun i _ ↦ (hx i).le),
      ← Real.finsetProd_rpow _ _ fun i _ ↦ (hx i).le]
  rw [integrable_congr hae, integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos hS.det_pos q).ne')]
  rw [integrable_prod_rpow_pi_chiSquaredMeasure_iff hk]
  constructor
  · intro hall
    have hp1 : 1 ≤ p := hp
    have hlast := hall ⟨p - 1, Nat.sub_lt hp zero_lt_one⟩
    rw [Nat.cast_sub hp1, Nat.cast_one] at hlast
    linarith
  · intro hq i
    have hi : (i.1 : ℝ) + 1 ≤ p := by exact_mod_cast i.2
    linarith

/-- The real-power determinant moment of a nonsingular Wishart law on the stated domain. -/
theorem integral_rpow_det_nonsingularWishartMeasure (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (hq : -((n - p + 1) / 2) < q) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (A : Matrix (Fin p) (Fin p) ℝ).det ^ q ∂nonsingularWishartMeasure n S =
      2 ^ ((p : ℝ) * q) * S.det ^ q *
        multivariateGamma p (n / 2 + q) / multivariateGamma p (n / 2) := by
  have hk (i : Fin p) : 0 < n - i.1 := by
    have hi : (i.1 : ℝ) + 1 ≤ p := by exact_mod_cast i.2
    linarith
  have hdet : Measurable
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (A : Matrix (Fin p) (Fin p) ℝ).det) := by fun_prop
  have hrpow : Measurable (fun x : ℝ ↦ x ^ q) := by fun_prop
  rw [← integral_map (f := fun x : ℝ ↦ x ^ q)
      (hdet.aemeasurable) hrpow.aestronglyMeasurable,
    map_det_nonsingularWishartMeasure hS hn,
    integral_map (f := fun x : ℝ ↦ x ^ q) (by fun_prop) hrpow.aestronglyMeasurable]
  let _ (i : Fin p) : IsProbabilityMeasure (chiSquaredMeasure (n - i.1)) :=
    isProbabilityMeasure_chiSquaredMeasure (hk i).le
  have hpos : ∀ᵐ x ∂Measure.pi (fun i : Fin p ↦ chiSquaredMeasure (n - i.1)),
      ∀ i, 0 < x i := Filter.eventually_all.2 fun i ↦
    Measure.tendsto_eval_ae_ae.eventually (ae_pos_chiSquaredMeasure (hk i))
  rw [integral_congr_ae (hpos.mono fun x hx ↦ by
    rw [Real.mul_rpow hS.det_pos.le (Finset.prod_nonneg fun i _ ↦ (hx i).le),
      ← Real.finsetProd_rpow _ _ fun i _ ↦ (hx i).le])]
  rw [integral_const_mul,
    integral_fintype_prod_eq_prod (fun (_ : Fin p) (x : ℝ) ↦ x ^ q)]
  have hqi (i : Fin p) : -((n - i.1) / 2) < q := by
    have hi : (i.1 : ℝ) + 1 ≤ p := by exact_mod_cast i.2
    linarith
  simp_rw [integral_rpow_chiSquaredMeasure (hk _) (hqi _)]
  simp_rw [mul_div_assoc]
  rw [Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    multivariateGamma_div_multivariateGamma]
  have hprod : (∏ i : Fin p, Real.Gamma ((n - i.1) / 2 + q) / Real.Gamma ((n - i.1) / 2)) =
      ∏ i : Fin p, Real.Gamma (n / 2 + q - (i.1 : ℝ) / 2) / Real.Gamma (n / 2 - (i.1 : ℝ) / 2) :=
    Finset.prod_congr rfl fun i _ ↦ by ring_nf
  rw [hprod, mul_comm q]
  ring

/-- In dimension zero every real power of the determinant is the constant one under every valid
nonsingular Wishart law. -/
theorem integrable_rpow_det_nonsingularWishartMeasure_zero
    (S : Matrix (Fin 0) (Fin 0) ℝ) (hn : -1 < n) (q : ℝ) :
    Integrable
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) ↦
        (A : Matrix (Fin 0) (Fin 0) ℝ).det ^ q)
      (nonsingularWishartMeasure n S) := by
  simp [nonsingularWishartMeasure_zero hn S]

/-- In dimension zero every real-power determinant moment is one. -/
theorem integral_rpow_det_nonsingularWishartMeasure_zero
    (S : Matrix (Fin 0) (Fin 0) ℝ) (hn : -1 < n) (q : ℝ) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ),
        (A : Matrix (Fin 0) (Fin 0) ℝ).det ^ q ∂nonsingularWishartMeasure n S = 1 := by
  simp [nonsingularWishartMeasure_zero hn S]

end TauCeti.Probability
