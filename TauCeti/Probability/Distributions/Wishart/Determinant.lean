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

end TauCeti.Probability
