/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Matrix.EuclideanCLM
public import TauCeti.Analysis.CStarAlgebra.SquareFunction
public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten

import Mathlib.Analysis.InnerProductSpace.SingularValues
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
import TauCeti.Analysis.InnerProductSpace.Polar.Finite
import TauCeti.Analysis.InnerProductSpace.SingularValues
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# The Schatten `p`-gauge on matrix C⋆-algebras

For a finite type `n`, the **Schatten `p`-gauge** on `CStarMatrix n n ℂ` is
`matrixLpGauge p x = (tr(|x|^p)).re ^ (1 / p)` with `|x| = √(x⋆ x)`. Via
`CStarMatrix.toEuclideanCLM` and the right singular basis, `matrixLpGauge p x = (∑ᵢ σᵢ(x)^p)^(1/p)`
for `0 < p`. Star invariance holds for all `p`; faithfulness, complex homogeneity, operator-norm
comparison, and the two-sided ideal bounds hold for `0 < p`; for `1 ≤ p`, agreement with
`UnitarilyInvariantSeminorm.schatten` gives subadditivity and `matrixLpSeminorm`. At `p = 1`, we
prove trace-norm duality. We also expose the column stacking map `columnEuclideanLM`, its
modulus identification `operatorAbs_columnEuclideanLM`, the Schatten realizations, subadditivity,
homogeneity, and restriction bounds of `columnSquare` and `rowSquare`, and their trace-pairing
duality at `p = 1`.

## Main declarations

* `TauCeti.matrixLpGauge`, `TauCeti.matrixLpGauge_eq_singularValues_sum`,
  `TauCeti.matrixLpGauge_of_isStarProjection`
* `TauCeti.matrixLpGauge_eq_schatten`, `TauCeti.matrixLpGauge_one_eq_nuclear`,
  `TauCeti.matrixLpSeminorm`
* `TauCeti.matrixLpGauge_unitary_mul`, `TauCeti.matrixLpGauge_mul_unitary`,
  `TauCeti.matrixLpGauge_le_mul_of_singularValues_le`,
  `TauCeti.matrixLpGauge_le_mul_of_norm_apply_le`
* `TauCeti.norm_trace_mul_le_norm_mul_matrixLpGauge_one`,
  `TauCeti.exists_norm_le_one_and_trace_mul_eq_matrixLpGauge_one`
* `TauCeti.columnEuclideanLM`, `TauCeti.norm_columnSquare_apply_sq_eq`,
  `TauCeti.norm_rowSquare_apply_sq_eq`, `TauCeti.matrixLpGauge_columnSquare_eq_schatten`,
  `TauCeti.matrixLpGauge_rowSquare_eq_schatten`, `TauCeti.matrixLpGauge_columnSquare_add_le`,
  `TauCeti.matrixLpGauge_columnSquare_smul`, `TauCeti.matrixLpGauge_rowSquare_add_le`,
  `TauCeti.matrixLpGauge_rowSquare_smul`, `TauCeti.matrixLpGauge_columnSquare_comp_le`,
  `TauCeti.matrixLpGauge_rowSquare_comp_le`, `TauCeti.matrixLpGauge_two_columnSquare_sq`,
  `TauCeti.matrixLpGauge_two_rowSquare_sq`, `TauCeti.star_toEuclideanCLM_symm_rankOne_mul_self`,
  `TauCeti.matrixLpGauge_columnSquare_rankOne`
* `TauCeti.exists_mul_columnSquare_and_norm_columnSquare_le_one`,
  `TauCeti.norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare`,
  `TauCeti.norm_sum_trace_mul_le_norm_columnSquare_mul_matrixLpGauge_one_rowSquare`,
  `TauCeti.norm_rowSquare_le_of_forall_norm_sum_trace_mul_le`,
  `TauCeti.norm_columnSquare_le_of_forall_norm_sum_trace_mul_le`

## References

* R. Bhatia, *Matrix Analysis*, GTM 169, Springer, 1997, Section IV.2.
* G. Pisier and Q. Xu, *Non-commutative `Lᵖ`-spaces*, *Handbook of the Geometry of Banach Spaces*,
  Vol. 2, North-Holland, 2003, §1–2.
-/

public section

noncomputable section

open scoped BigOperators ComplexOrder NNReal ENNReal InnerProductSpace

namespace TauCeti

section Gauge

variable {n : Type*} [Fintype n]

/-- The Schatten `p`-gauge `(tr(|x|^p)).re ^ (1 / p)` of `x : CStarMatrix n n ℂ` with respect to
the unnormalized matrix trace, where `|x| = √(x⋆ x)`. -/
def matrixLpGauge (p : ℝ≥0) (x : CStarMatrix n n ℂ) : ℝ :=
  (Matrix.trace (CStarMatrix.ofMatrix.symm
    (CFC.nnrpow (CFC.sqrt (star x * x)) p))).re ^ (1 / (p : ℝ))

/-- Unfolding definition of `matrixLpGauge`. -/
theorem matrixLpGauge_def (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p x = (Matrix.trace (CStarMatrix.ofMatrix.symm
      (CFC.nnrpow (CFC.sqrt (star x * x)) p))).re ^ (1 / (p : ℝ)) := (rfl)

/-- For `0 < p`, `tr(|x|^p)` equals `∑ᵢ σᵢ(x)^p` for the singular values of `toEuclideanCLM x`. -/
theorem trace_nnrpow_sqrt_star_mul_self [DecidableEq n] {p : ℝ≥0} (hp : 0 < p)
    (x : CStarMatrix n n ℂ) :
    Matrix.trace (CStarMatrix.ofMatrix.symm (CFC.nnrpow (CFC.sqrt (star x * x)) p)) =
      ((((CStarMatrix.toEuclideanCLM x).toLinearMap.singularValues.sum
        fun _ s => s ^ (p : ℝ)) : ℝ) : ℂ) := by
  set T := CStarMatrix.toEuclideanCLM x
  set A := T.toLinearMap
  have hp2 : (0 : ℝ) < ((p / 2 : ℝ≥0) : ℝ) := by positivity
  have hf0 : (0 : ℝ) ^ ((p / 2 : ℝ≥0) : ℝ) = 0 := Real.zero_rpow hp2.ne'
  have hmap : CStarMatrix.toEuclideanCLM (CFC.nnrpow (CFC.sqrt (star x * x)) p) =
      cfc (fun t : ℝ => t ^ ((p / 2 : ℝ≥0) : ℝ)) (star T * T) := by
    rw [CFC.nnrpow_eq_pow, CFC.nnrpow_sqrt, CFC.nnrpow_eq_cfcₙ_real (star x * x) (p / 2),
      NonUnitalStarAlgHomClass.map_cfcₙ (CStarMatrix.toEuclideanCLM (n := n)) _ (star x * x)
        (Real.continuous_rpow_const hp2.le).continuousOn hf0 (StarAlgEquiv.isometry _).continuous
        (IsSelfAdjoint.star_mul_self x) ((IsSelfAdjoint.star_mul_self x).map _),
      cfcₙ_eq_cfc]
    simp [T, map_star]
  rw [← CStarMatrix.trace_toEuclideanCLM, hmap, LinearMap.trace_eq_sum_inner _ A.rightSingularBasis,
    ← A.sum_fin_singularValues (· ^ (p : ℝ)) (Real.zero_rpow (NNReal.coe_pos.mpr hp).ne'),
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have heig : (star T * T) (A.rightSingularBasis i) =
      ((A.singularValues i ^ 2 : ℝ) : ℂ) • A.rightSingularBasis i := by
    simpa [A, ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_toLinearMap] using A.adjoint_comp_self_rightSingularBasis i
  have hrpow : (A.singularValues i ^ 2) ^ ((p / 2 : ℝ≥0) : ℝ) = A.singularValues i ^ (p : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (A.singularValues_nonneg i), NNReal.coe_div,
      NNReal.coe_ofNat, mul_div_cancel₀ _ two_ne_zero]
  rw [ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.cfc_apply_of_apply_eq_smul (μ := A.singularValues i ^ 2) _ heig, hrpow]
  simp [Complex.real_smul]

/-- Taking the real part of `tr(|x|^p)` gives `∑ᵢ σᵢ(x)^p` for `0 < p`. -/
theorem re_trace_nnrpow_sqrt_star_mul_self [DecidableEq n] {p : ℝ≥0} (hp : 0 < p)
    (x : CStarMatrix n n ℂ) :
    (Matrix.trace (CStarMatrix.ofMatrix.symm (CFC.nnrpow (CFC.sqrt (star x * x)) p))).re =
      ((CStarMatrix.toEuclideanCLM x).toLinearMap.singularValues.sum fun _ s => s ^ (p : ℝ)) := by
  rw [trace_nnrpow_sqrt_star_mul_self hp x, Complex.ofReal_re]

/-- For every `p : ℝ≥0`, the real part of `tr(|x|^p)` is nonnegative. -/
theorem re_trace_nnrpow_sqrt_star_mul_self_nonneg (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    0 ≤ (Matrix.trace (CStarMatrix.ofMatrix.symm (CFC.nnrpow (CFC.sqrt (star x * x)) p))).re := by
  classical
  obtain rfl | hp := eq_zero_or_pos p
  · simp
  · rw [re_trace_nnrpow_sqrt_star_mul_self hp x]
    exact Finsupp.sum_nonneg fun i _ =>
      Real.rpow_nonneg ((CStarMatrix.toEuclideanCLM x).toLinearMap.singularValues_nonneg i) _

/-- The Schatten `p`-gauge is nonnegative. -/
theorem matrixLpGauge_nonneg (p : ℝ≥0) (x : CStarMatrix n n ℂ) : 0 ≤ matrixLpGauge p x :=
  Real.rpow_nonneg (re_trace_nnrpow_sqrt_star_mul_self_nonneg p x) _

/-- Raising `matrixLpGauge p x` to the power `p` recovers `(tr(|x|^p)).re` when `0 < p`. -/
theorem matrixLpGauge_rpow {p : ℝ≥0} (hp : 0 < p) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p x ^ (p : ℝ) =
      (Matrix.trace (CStarMatrix.ofMatrix.symm (CFC.nnrpow (CFC.sqrt (star x * x)) p))).re := by
  rw [matrixLpGauge_def, one_div,
    Real.rpow_inv_rpow (re_trace_nnrpow_sqrt_star_mul_self_nonneg p x) (NNReal.coe_pos.mpr hp).ne']

/-- At exponent `0`, `matrixLpGauge 0 x` evaluates to `1` through `1 / 0 = 0` and `r ^ 0 = 1`. -/
@[simp] theorem matrixLpGauge_zero_left (x : CStarMatrix n n ℂ) : matrixLpGauge 0 x = 1 := by
  simp [matrixLpGauge_def]

/-- At `p = 1`, `matrixLpGauge 1 x` is the real part of `tr(|x|)`. -/
theorem matrixLpGauge_one (x : CStarMatrix n n ℂ) :
    matrixLpGauge 1 x = (Matrix.trace (CStarMatrix.ofMatrix.symm (CFC.sqrt (star x * x)))).re := by
  simp [matrixLpGauge_def, CFC.nnrpow_one]

/-- For a positive element `0 ≤ x` of `CStarMatrix n n ℂ`, `matrixLpGauge 1 x = (tr x).re`. -/
theorem matrixLpGauge_one_of_nonneg {x : CStarMatrix n n ℂ} (hx : 0 ≤ x) :
    matrixLpGauge 1 x = (Matrix.trace (CStarMatrix.ofMatrix.symm x)).re := by
  rw [matrixLpGauge_one, hx.star_eq, CFC.sqrt_mul_self x hx]

/-- For `0 < p`, the Schatten `p`-gauge of a star projection `x` equals `(tr x).re ^ (1 / p)`. -/
theorem matrixLpGauge_of_isStarProjection {p : ℝ≥0} (hp : 0 < p) {x : CStarMatrix n n ℂ}
    (hx : IsStarProjection x) :
    matrixLpGauge p x = (Matrix.trace (CStarMatrix.ofMatrix.symm x)).re ^ (1 / (p : ℝ)) := by
  have hsqrt : CFC.sqrt (star x * x) = x := by
    rw [hx.isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_self x hx.nonneg
  have hnnrpow : CFC.nnrpow x p = x := by
    rw [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real x p]
    refine (cfcₙ_congr (f := fun t : ℝ => t ^ (p : ℝ)) (g := id) fun t ht => ?_).trans
      (cfcₙ_id' ℝ x hx.isSelfAdjoint)
    rcases hx.isIdempotentElem.quasispectrum_subset ℝ ht with rfl | rfl
    · exact Real.zero_rpow (NNReal.coe_pos.mpr hp).ne'
    · exact Real.one_rpow _
  rw [matrixLpGauge_def, hsqrt, hnnrpow]

/-- At `p = 2`, `matrixLpGauge 2 x ^ 2 = (tr(x⋆ x)).re`. -/
theorem matrixLpGauge_two_sq (x : CStarMatrix n n ℂ) :
    matrixLpGauge 2 x ^ 2 = (Matrix.trace (CStarMatrix.ofMatrix.symm (star x * x))).re := by
  have h := matrixLpGauge_rpow (p := 2) (by norm_num) x
  norm_num at h
  rw [h, CFC.nnrpow_one (star x * x) (star_mul_self_nonneg x)]

/-- **Singular-value formula for `matrixLpGauge`.** For `0 < p`, `matrixLpGauge p x` equals
`(∑ᵢ σᵢ(x)^p) ^ (1 / p)`, where `σᵢ(x)` are the singular values of `toEuclideanCLM x`. -/
theorem matrixLpGauge_eq_singularValues_sum [DecidableEq n] {p : ℝ≥0} (hp : 0 < p)
    (x : CStarMatrix n n ℂ) :
    matrixLpGauge p x = ((CStarMatrix.toEuclideanCLM x).toLinearMap.singularValues.sum
      fun _ s => s ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
  rw [matrixLpGauge_def, re_trace_nnrpow_sqrt_star_mul_self hp x]

/-- For `1 ≤ p`, `matrixLpGauge p` agrees with the Schatten `p`-seminorm on
`EuclideanSpace ℂ n`. -/
theorem matrixLpGauge_eq_schatten [DecidableEq n] (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))]
    (x : CStarMatrix n n ℂ) :
    matrixLpGauge p x =
      UnitarilyInvariantSeminorm.schatten ℂ (EuclideanSpace ℂ n) (EuclideanSpace ℂ n) p
        (CStarMatrix.toEuclideanCLM x).toLinearMap := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  rw [matrixLpGauge_eq_singularValues_sum (zero_lt_one.trans_le hp1),
    UnitarilyInvariantSeminorm.schatten_apply_of_ne_top (p : ℝ≥0∞) ENNReal.coe_ne_top]
  simp

/-- At `p = 1`, `matrixLpGauge 1` agrees with the nuclear seminorm on `EuclideanSpace ℂ n`. -/
theorem matrixLpGauge_one_eq_nuclear [DecidableEq n] (x : CStarMatrix n n ℂ) :
    matrixLpGauge 1 x =
      UnitarilyInvariantSeminorm.nuclear ℂ (EuclideanSpace ℂ n) (EuclideanSpace ℂ n)
        (CStarMatrix.toEuclideanCLM x).toLinearMap := by
  let : Fact (1 ≤ ((1 : ℝ≥0) : ℝ≥0∞)) := ⟨le_rfl⟩
  simpa using matrixLpGauge_eq_schatten 1 x

/-- For `0 < p`, the zero matrix has `matrixLpGauge p 0 = 0`. -/
@[simp] theorem matrixLpGauge_zero {p : ℝ≥0} (hp : 0 < p) :
    matrixLpGauge p (0 : CStarMatrix n n ℂ) = 0 := by
  simp [matrixLpGauge_def, Real.zero_rpow (inv_ne_zero (NNReal.coe_pos.mpr hp).ne')]

/-- For `0 < p`, `matrixLpGauge p x = 0` if and only if `x = 0`. -/
@[simp] theorem matrixLpGauge_eq_zero_iff {p : ℝ≥0} (hp : 0 < p) {x : CStarMatrix n n ℂ} :
    matrixLpGauge p x = 0 ↔ x = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ matrixLpGauge_zero hp⟩
  set A := (CStarMatrix.toEuclideanCLM x).toLinearMap
  have hsum : A.singularValues.sum (fun _ s => s ^ (p : ℝ)) = 0 := by
    rw [← re_trace_nnrpow_sqrt_star_mul_self hp x, ← matrixLpGauge_rpow hp x, h,
      Real.zero_rpow (NNReal.coe_pos.mpr hp).ne']
  have hsv : A.singularValues = 0 := Finsupp.ext fun i => by_contra fun hi => hi <|
    (Real.rpow_eq_zero (A.singularValues_nonneg i) (NNReal.coe_pos.mpr hp).ne').mp <|
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        Real.rpow_nonneg (A.singularValues_nonneg j) (p : ℝ)).mp hsum i
        (Finsupp.mem_support_iff.mpr hi)
  exact CStarMatrix.toEuclideanCLM.injective
    ((ContinuousLinearMap.coe_inj.mp (A.singularValues_eq_zero_iff.mp hsv)).trans (map_zero _).symm)

/-- The Schatten `p`-gauge is invariant under negation. -/
@[simp] theorem matrixLpGauge_neg (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p (-x) = matrixLpGauge p x := by simp [matrixLpGauge_def]

/-- The Schatten `p`-gauge is invariant under the C⋆-algebra involution `star`. -/
@[simp] theorem matrixLpGauge_star (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p (star x) = matrixLpGauge p x := by
  classical
  obtain rfl | hp := eq_zero_or_pos p
  · simp [matrixLpGauge_def]
  · rw [matrixLpGauge_eq_singularValues_sum hp, matrixLpGauge_eq_singularValues_sum hp,
      map_star, ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_toLinearMap,
      LinearMap.singularValues_adjoint]

/-- For `0 < p`, a pointwise singular-value bound `σᵢ(x) ≤ c * σᵢ(y)` (with `0 ≤ c`) lifts to
`matrixLpGauge p x ≤ c * matrixLpGauge p y`. -/
theorem matrixLpGauge_le_mul_of_singularValues_le [DecidableEq n] {p : ℝ≥0} (hp : 0 < p)
    {x y : CStarMatrix n n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hσ : ∀ i : ℕ, (CStarMatrix.toEuclideanCLM x).toLinearMap.singularValues i ≤
      c * (CStarMatrix.toEuclideanCLM y).toLinearMap.singularValues i) :
    matrixLpGauge p x ≤ c * matrixLpGauge p y := by
  rw [matrixLpGauge_eq_singularValues_sum hp, matrixLpGauge_eq_singularValues_sum hp]
  exact LinearMap.singularValues_rpow_sum_le_mul (NNReal.coe_pos.mpr hp) _ _ hc hσ

/-- For `0 < p`, a pointwise Euclidean operator bound `‖x ξ‖ ≤ c * ‖y ξ‖` (with `0 ≤ c`) lifts to
`matrixLpGauge p x ≤ c * matrixLpGauge p y`. -/
theorem matrixLpGauge_le_mul_of_norm_apply_le [DecidableEq n] {p : ℝ≥0} (hp : 0 < p)
    {x y : CStarMatrix n n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ξ : EuclideanSpace ℂ n,
      ‖CStarMatrix.toEuclideanCLM x ξ‖ ≤ c * ‖CStarMatrix.toEuclideanCLM y ξ‖) :
    matrixLpGauge p x ≤ c * matrixLpGauge p y :=
  matrixLpGauge_le_mul_of_singularValues_le hp hc fun i =>
    LinearMap.singularValues_le_mul_of_norm_apply_le h i

/-- For `1 ≤ p`, `matrixLpGauge p` is subadditive. -/
theorem matrixLpGauge_add_le {p : ℝ≥0} (hp : 1 ≤ p) (x y : CStarMatrix n n ℂ) :
    matrixLpGauge p (x + y) ≤ matrixLpGauge p x + matrixLpGauge p y := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  simp only [matrixLpGauge_eq_schatten p, map_add, ContinuousLinearMap.toLinearMap_add]
  exact map_add_le_add _ _ _

/-- For `0 < p`, `matrixLpGauge p` is absolutely homogeneous over `ℂ`. -/
theorem matrixLpGauge_smul {p : ℝ≥0} (hp : 0 < p) (c : ℂ) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p (c • x) = ‖c‖ * matrixLpGauge p x := by
  classical
  rw [matrixLpGauge_eq_singularValues_sum hp, matrixLpGauge_eq_singularValues_sum hp, map_smul,
    ContinuousLinearMap.toLinearMap_smul]
  exact LinearMap.singularValues_rpow_sum_eq_mul (NNReal.coe_pos.mpr hp) _ _ (norm_nonneg c)
    fun i => by rw [LinearMap.singularValues_smul, Finsupp.smul_apply, smul_eq_mul]

/-- If `0 ≤ y` and `y * y = star x * x`, then `matrixLpGauge p y = matrixLpGauge p x`. -/
theorem matrixLpGauge_eq_of_mul_self (p : ℝ≥0) {y x : CStarMatrix n n ℂ} (hy : 0 ≤ y)
    (hsq : y * y = star x * x) : matrixLpGauge p y = matrixLpGauge p x := by
  rw [matrixLpGauge_def, matrixLpGauge_def, hy.star_eq, hsq]

/-- The Schatten `p`-gauge of `√(star x * x)` equals `matrixLpGauge p x`. -/
@[simp] theorem matrixLpGauge_sqrt_star_mul_self (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p (CFC.sqrt (star x * x)) = matrixLpGauge p x :=
  matrixLpGauge_eq_of_mul_self p (CFC.sqrt_nonneg _)
    (CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg x))

/-- The Schatten `p`-gauge of `√(x * star x)` equals `matrixLpGauge p x`. -/
@[simp] theorem matrixLpGauge_sqrt_mul_star_self (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p (CFC.sqrt (x * star x)) = matrixLpGauge p x := by
  simpa only [star_star, matrixLpGauge_star] using matrixLpGauge_sqrt_star_mul_self p (star x)

/-- Left multiplication by a unitary matrix preserves `matrixLpGauge`. -/
theorem matrixLpGauge_unitary_mul [DecidableEq n] (p : ℝ≥0) {u : CStarMatrix n n ℂ}
    (hu : u ∈ unitary (CStarMatrix n n ℂ)) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p (u * x) = matrixLpGauge p x := by
  rw [matrixLpGauge_def, matrixLpGauge_def, star_mul, mul_assoc, ← mul_assoc (star u),
    Unitary.star_mul_self_of_mem hu, one_mul]

/-- Right multiplication by a unitary matrix preserves `matrixLpGauge`. -/
theorem matrixLpGauge_mul_unitary [DecidableEq n] (p : ℝ≥0) (x : CStarMatrix n n ℂ)
    {u : CStarMatrix n n ℂ} (hu : u ∈ unitary (CStarMatrix n n ℂ)) :
    matrixLpGauge p (x * u) = matrixLpGauge p x := by
  rw [← matrixLpGauge_star p (x * u), star_mul,
    matrixLpGauge_unitary_mul p (Unitary.star_mem hu), matrixLpGauge_star]

variable (n) in
/-- For `1 ≤ p`, `matrixLpGauge p` bundled as a `ℂ`-seminorm on `CStarMatrix n n ℂ`. -/
def matrixLpSeminorm (p : ℝ≥0) (hp : 1 ≤ p) : Seminorm ℂ (CStarMatrix n n ℂ) :=
  Seminorm.of (matrixLpGauge p) (matrixLpGauge_add_le hp)
    (matrixLpGauge_smul (zero_lt_one.trans_le hp))

@[simp] theorem matrixLpSeminorm_apply (p : ℝ≥0) (hp : 1 ≤ p) (x : CStarMatrix n n ℂ) :
    matrixLpSeminorm n p hp x = matrixLpGauge p x := (rfl)

/-- For `0 < p`, the operator norm is bounded by `matrixLpGauge p`. -/
theorem norm_le_matrixLpGauge {p : ℝ≥0} (hp : 0 < p) (x : CStarMatrix n n ℂ) :
    ‖x‖ ≤ matrixLpGauge p x := by
  classical
  have hp' : (0 : ℝ) < (p : ℝ) := NNReal.coe_pos.mpr hp
  set A := (CStarMatrix.toEuclideanCLM x).toLinearMap
  have hcoe : A.toContinuousLinearMap = CStarMatrix.toEuclideanCLM x :=
    DFunLike.coe_injective (LinearMap.coe_toContinuousLinearMap' A)
  rw [← CStarMatrix.norm_toEuclideanCLM, ← hcoe,
    A.norm_toContinuousLinearMap_eq_singularValues_zero, matrixLpGauge_eq_singularValues_sum hp]
  have hle : A.singularValues 0 ^ (p : ℝ) ≤ A.singularValues.sum (fun _ s => s ^ (p : ℝ)) := by
    by_cases h0 : 0 ∈ A.singularValues.support
    · exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (A.singularValues_nonneg i) _) h0
    · rw [Finsupp.notMem_support_iff.mp h0, Real.zero_rpow hp'.ne']
      exact Finsupp.sum_nonneg fun i _ => Real.rpow_nonneg (A.singularValues_nonneg i) _
  simpa only [one_div, Real.rpow_rpow_inv (A.singularValues_nonneg 0) hp'.ne'] using
    Real.rpow_le_rpow (Real.rpow_nonneg (A.singularValues_nonneg 0) _) hle
      (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))

/-- **Left ideal inequality.** For `0 < p`, `matrixLpGauge p (x * y) ≤ ‖x‖ * matrixLpGauge p y`. -/
theorem matrixLpGauge_mul_le_left {p : ℝ≥0} (hp : 0 < p) (x y : CStarMatrix n n ℂ) :
    matrixLpGauge p (x * y) ≤ ‖x‖ * matrixLpGauge p y := by
  classical
  refine matrixLpGauge_le_mul_of_singularValues_le hp (norm_nonneg x) fun i => ?_
  rw [map_mul, ContinuousLinearMap.toLinearMap_mul, Module.End.mul_eq_comp]
  simpa only [CStarMatrix.norm_toEuclideanCLM] using
    LinearMap.singularValues_comp_le (CStarMatrix.toEuclideanCLM x).toLinearMap
      (CStarMatrix.toEuclideanCLM y).toLinearMap (CStarMatrix.toEuclideanCLM x).le_opNorm i

/-- **Right ideal inequality.** For `0 < p`, `matrixLpGauge p (x * y) ≤ matrixLpGauge p x * ‖y‖`. -/
theorem matrixLpGauge_mul_le_right {p : ℝ≥0} (hp : 0 < p) (x y : CStarMatrix n n ℂ) :
    matrixLpGauge p (x * y) ≤ matrixLpGauge p x * ‖y‖ := by
  rw [← matrixLpGauge_star p (x * y), star_mul, ← matrixLpGauge_star p x, ← norm_star y, mul_comm]
  exact matrixLpGauge_mul_le_left hp (star y) (star x)

/-! ### Trace-norm duality at `p = 1` -/

/-- **Trace-norm Hölder inequality** (`(∞, 1)` endpoint): `‖tr(b x)‖ ≤ ‖b‖ * matrixLpGauge 1 x`. -/
theorem norm_trace_mul_le_norm_mul_matrixLpGauge_one (b x : CStarMatrix n n ℂ) :
    ‖Matrix.trace (CStarMatrix.ofMatrix.symm (b * x))‖ ≤ ‖b‖ * matrixLpGauge 1 x := by
  classical
  rw [← CStarMatrix.trace_toEuclideanCLM]
  set T := (CStarMatrix.toEuclideanCLM (b * x)).toLinearMap
  calc ‖LinearMap.trace ℂ (EuclideanSpace ℂ n) T‖
      ≤ T.kyFanSum (Module.finrank ℂ (EuclideanSpace ℂ n)) :=
        T.norm_trace_comp_linearIsometryEquiv_le_kyFanSum (.refl ℂ _)
    _ = matrixLpGauge 1 (b * x) := by
        rw [T.kyFanSum_eq_nuclear (Submodule.finrank_le _), matrixLpGauge_one_eq_nuclear]
    _ ≤ ‖b‖ * matrixLpGauge 1 x := matrixLpGauge_mul_le_left zero_lt_one b x

/-- Real-part form of trace-norm Hölder: `|(tr(b x)).re| ≤ ‖b‖ * matrixLpGauge 1 x`. -/
theorem abs_re_trace_mul_le_norm_mul_matrixLpGauge_one (b x : CStarMatrix n n ℂ) :
    |(Matrix.trace (CStarMatrix.ofMatrix.symm (b * x))).re| ≤ ‖b‖ * matrixLpGauge 1 x :=
  (Complex.abs_re_le_norm _).trans (norm_trace_mul_le_norm_mul_matrixLpGauge_one b x)

/-- **Trace-norm duality attainment**: there exists `u` (`‖u‖ ≤ 1`) with
`tr(u x) = matrixLpGauge 1 x`. -/
theorem exists_norm_le_one_and_trace_mul_eq_matrixLpGauge_one (x : CStarMatrix n n ℂ) :
    ∃ u : CStarMatrix n n ℂ, ‖u‖ ≤ 1 ∧
      Matrix.trace (CStarMatrix.ofMatrix.symm (u * x)) = (matrixLpGauge 1 x : ℂ) := by
  classical
  set A := (CStarMatrix.toEuclideanCLM x).toLinearMap
  obtain ⟨Q, hQ⟩ := A.exists_linearIsometryEquiv_trace_comp_eq_kyFanSum
  let Qclm := Q.toLinearIsometry.toContinuousLinearMap
  refine ⟨CStarMatrix.toEuclideanCLM.symm Qclm, ?_, ?_⟩
  · rw [← CStarMatrix.norm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]
    exact Qclm.opNorm_le_bound zero_le_one fun v => by simp [Qclm]
  · rw [← CStarMatrix.trace_toEuclideanCLM, map_mul, StarAlgEquiv.apply_symm_apply,
      ContinuousLinearMap.toLinearMap_mul, Module.End.mul_eq_comp, LinearMap.trace_comp_comm',
      matrixLpGauge_one_eq_nuclear, ← A.kyFanSum_eq_nuclear (Submodule.finrank_le _)]
    exact hQ

end Gauge

section ColumnRow

variable {ι m : Type*} [Fintype m] [DecidableEq m]

/-- Stacking a finite family of `m × m` C⋆-matrices into a column operator
`EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ m)`. -/
def columnEuclideanLM :
    (ι → CStarMatrix m m ℂ) →ₗ[ℂ]
      (EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 fun _ : ι => EuclideanSpace ℂ m) where
  toFun b := (WithLp.linearEquiv 2 ℂ (ι → EuclideanSpace ℂ m)).symm.toLinearMap.comp
    (LinearMap.pi fun k => (CStarMatrix.toEuclideanCLM (b k)).toLinearMap)
  map_add' _ _ := by ext v k; simp
  map_smul' _ _ := by ext v k; simp

/-- Applying `columnEuclideanLM b` to `v` and evaluating at coordinate `k` applies
`CStarMatrix.toEuclideanCLM (b k)` to `v`. -/
@[simp] theorem columnEuclideanLM_apply (b : ι → CStarMatrix m m ℂ) (v : EuclideanSpace ℂ m)
    (k : ι) : (columnEuclideanLM b v).ofLp k = CStarMatrix.toEuclideanCLM (b k) v := (rfl)

/-- Stacking the coordinate projections of an operator `T` into `PiLp` via `columnEuclideanLM`
recovers `T`. -/
theorem columnEuclideanLM_projₗ
    (T : EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 fun _ : ι => EuclideanSpace ℂ m) :
    columnEuclideanLM (fun k => CStarMatrix.toEuclideanCLM.symm
      ((PiLp.projₗ 2 (fun _ : ι => EuclideanSpace ℂ m) k).comp T).toContinuousLinearMap) = T := by
  ext v k
  simp

/-- The column Gram operator `(columnEuclideanLM b).adjoint ∘ₗ columnEuclideanLM b` agrees with
the Euclidean operator of `∑ k, star (b k) * b k`. -/
theorem adjoint_comp_columnEuclideanLM [Fintype ι] (b : ι → CStarMatrix m m ℂ) :
    (columnEuclideanLM b).adjoint ∘ₗ columnEuclideanLM b =
      (CStarMatrix.toEuclideanCLM (∑ k, star (b k) * b k)).toLinearMap :=
  LinearMap.ext fun _ => ext_inner_left ℂ fun _ => by
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, PiLp.inner_apply,
      columnEuclideanLM_apply, map_sum, ContinuousLinearMap.coe_coe, sum_apply, inner_sum, map_mul,
      map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]

/-- The operator modulus `|columnEuclideanLM b|` agrees with the Euclidean operator of
`columnSquare b`. -/
theorem operatorAbs_columnEuclideanLM [Fintype ι] (b : ι → CStarMatrix m m ℂ) :
    (columnEuclideanLM b).operatorAbs =
      (CStarMatrix.toEuclideanCLM (columnSquare b)).toLinearMap := by
  set T := CStarMatrix.toEuclideanCLM (columnSquare b)
  have hnonneg : 0 ≤ T := map_zero (CStarMatrix.toEuclideanCLM (n := m)) ▸
    OrderHomClass.mono CStarMatrix.toEuclideanCLM (columnSquare_nonneg b)
  have hsq : T * T = (columnEuclideanLM b).adjoint.toContinuousLinearMap ∘L
      (columnEuclideanLM b).toContinuousLinearMap := by
    rw [← map_mul, columnSquare_mul_self]
    apply ContinuousLinearMap.coe_inj.mp
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.coe_toContinuousLinearMap,
      LinearMap.coe_toContinuousLinearMap, adjoint_comp_columnEuclideanLM b]
  exact LinearMap.ext fun v => DFunLike.congr_fun
    ((LinearMap.toContinuousLinearMap_operatorAbs _).trans (CFC.sqrt_unique hsq hnonneg)) v

/-- Pointwise Euclidean norm of `columnSquare b`:
`‖toEuclideanCLM (columnSquare b) ξ‖ ^ 2 = ∑ k, ‖toEuclideanCLM (b k) ξ‖ ^ 2`. -/
theorem norm_columnSquare_apply_sq_eq [Fintype ι] (b : ι → CStarMatrix m m ℂ)
    (ξ : EuclideanSpace ℂ m) :
    ‖CStarMatrix.toEuclideanCLM (columnSquare b) ξ‖ ^ 2 =
      ∑ k, ‖CStarMatrix.toEuclideanCLM (b k) ξ‖ ^ 2 := by
  have h : CStarMatrix.toEuclideanCLM (columnSquare b) ξ = (columnEuclideanLM b).operatorAbs ξ := by
    rw [← ContinuousLinearMap.coe_coe, operatorAbs_columnEuclideanLM]
  rw [h, LinearMap.norm_operatorAbs_apply, PiLp.norm_sq_eq_of_L2]
  simp

/-- Pointwise Euclidean norm of `rowSquare x`:
`‖toEuclideanCLM (rowSquare x) ξ‖ ^ 2 = ∑ k, ‖toEuclideanCLM (star (x k)) ξ‖ ^ 2`. -/
theorem norm_rowSquare_apply_sq_eq [Fintype ι] (x : ι → CStarMatrix m m ℂ)
    (ξ : EuclideanSpace ℂ m) :
    ‖CStarMatrix.toEuclideanCLM (rowSquare x) ξ‖ ^ 2 =
      ∑ k, ‖CStarMatrix.toEuclideanCLM (star (x k)) ξ‖ ^ 2 := by
  rw [rowSquare_eq_columnSquare_star, norm_columnSquare_apply_sq_eq]

/-- For `1 ≤ p`, `matrixLpGauge p (columnSquare b)` equals the Schatten `p`-seminorm of the column
stacking operator `columnEuclideanLM b`. -/
theorem matrixLpGauge_columnSquare_eq_schatten [Fintype ι] (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))]
    (b : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (columnSquare b) = UnitarilyInvariantSeminorm.schatten ℂ
      (EuclideanSpace ℂ m) (PiLp 2 fun _ : ι => EuclideanSpace ℂ m) p (columnEuclideanLM b) := by
  rw [matrixLpGauge_eq_schatten p, ← operatorAbs_columnEuclideanLM,
    UnitarilyInvariantSeminorm.schatten_apply, UnitarilyInvariantSeminorm.schatten_apply]
  simp_rw [(columnEuclideanLM b).singularValues_operatorAbs]

/-- For `1 ≤ p`, `matrixLpGauge p (rowSquare c)` equals the Schatten `p`-seminorm of the adjoint
column stacking operator `(columnEuclideanLM (fun k => star (c k))).adjoint`. -/
theorem matrixLpGauge_rowSquare_eq_schatten [Fintype ι] (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))]
    (c : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (rowSquare c) = UnitarilyInvariantSeminorm.schatten ℂ
      (PiLp 2 fun _ : ι => EuclideanSpace ℂ m) (EuclideanSpace ℂ m) p
      (columnEuclideanLM (fun k => star (c k))).adjoint := by
  rw [rowSquare_eq_columnSquare_star, matrixLpGauge_columnSquare_eq_schatten,
    UnitarilyInvariantSeminorm.schatten_apply_adjoint]

omit [DecidableEq m] in
/-- Subadditivity of `b ↦ matrixLpGauge p (columnSquare b)` for `1 ≤ p`. -/
theorem matrixLpGauge_columnSquare_add_le [Fintype ι] {p : ℝ≥0} (hp : 1 ≤ p)
    (b₁ b₂ : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (columnSquare (b₁ + b₂)) ≤
      matrixLpGauge p (columnSquare b₁) + matrixLpGauge p (columnSquare b₂) := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  simp only [matrixLpGauge_columnSquare_eq_schatten p, map_add]; exact map_add_le_add _ _ _

omit [DecidableEq m] in
/-- Absolute homogeneity of `b ↦ matrixLpGauge p (columnSquare b)` for `0 < p`. -/
theorem matrixLpGauge_columnSquare_smul [Fintype ι] {p : ℝ≥0} (hp : 0 < p) (c : ℂ)
    (b : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (columnSquare (c • b)) = ‖c‖ * matrixLpGauge p (columnSquare b) := by
  rw [columnSquare_smul, ← Complex.coe_smul, matrixLpGauge_smul hp, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg c)]

omit [DecidableEq m] in
/-- Subadditivity of `c ↦ matrixLpGauge p (rowSquare c)` for `1 ≤ p`. -/
theorem matrixLpGauge_rowSquare_add_le [Fintype ι] {p : ℝ≥0} (hp : 1 ≤ p)
    (c₁ c₂ : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (rowSquare (c₁ + c₂)) ≤
      matrixLpGauge p (rowSquare c₁) + matrixLpGauge p (rowSquare c₂) := by
  simp only [rowSquare_eq_columnSquare_star, ← Pi.star_def, star_add]
  exact matrixLpGauge_columnSquare_add_le hp _ _

omit [DecidableEq m] in
/-- Absolute homogeneity of `c ↦ matrixLpGauge p (rowSquare c)` for `0 < p`. -/
theorem matrixLpGauge_rowSquare_smul [Fintype ι] {p : ℝ≥0} (hp : 0 < p) (z : ℂ)
    (c : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (rowSquare (z • c)) = ‖z‖ * matrixLpGauge p (rowSquare c) := by
  rw [rowSquare_smul, ← Complex.coe_smul, matrixLpGauge_smul hp, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg z)]

omit [DecidableEq m] in
/-- Restricting a family along an injection does not increase `matrixLpGauge p (columnSquare ·)`
for `0 < p`. -/
theorem matrixLpGauge_columnSquare_comp_le [Fintype ι] {κ : Type*} [Fintype κ] {f : κ → ι}
    (hf : Function.Injective f) {p : ℝ≥0} (hp : 0 < p) (b : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (columnSquare (b ∘ f)) ≤ matrixLpGauge p (columnSquare b) := by
  classical
  refine (matrixLpGauge_le_mul_of_norm_apply_le hp zero_le_one fun ξ => ?_).trans_eq (one_mul _)
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_columnSquare_apply_sq_eq, norm_columnSquare_apply_sq_eq]
  exact (Finset.sum_image (f := fun i => ‖CStarMatrix.toEuclideanCLM (b i) ξ‖ ^ 2)
    fun _ _ _ _ h => hf h).symm.trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _)

omit [DecidableEq m] in
/-- Restricting a family along an injection does not increase `matrixLpGauge p (rowSquare ·)` for
`0 < p`. -/
theorem matrixLpGauge_rowSquare_comp_le [Fintype ι] {κ : Type*} [Fintype κ] {f : κ → ι}
    (hf : Function.Injective f) {p : ℝ≥0} (hp : 0 < p) (c : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (rowSquare (c ∘ f)) ≤ matrixLpGauge p (rowSquare c) := by
  rw [rowSquare_eq_columnSquare_star, rowSquare_eq_columnSquare_star]
  exact matrixLpGauge_columnSquare_comp_le hf hp (fun i => star (c i))

omit [DecidableEq m] in
/-- At `p = 2`, the squared Schatten gauge of `columnSquare a` equals
`∑ k, matrixLpGauge 2 (a k) ^ 2`. -/
theorem matrixLpGauge_two_columnSquare_sq [Fintype ι] (a : ι → CStarMatrix m m ℂ) :
    matrixLpGauge 2 (columnSquare a) ^ 2 = ∑ k, matrixLpGauge 2 (a k) ^ 2 := by
  rw [matrixLpGauge_two_sq, (columnSquare_nonneg a).star_eq, columnSquare_mul_self]
  simp only [← CStarMatrix.traceLinearMap_apply (R := ℝ), map_sum, Complex.re_sum,
    matrixLpGauge_two_sq]

omit [DecidableEq m] in
/-- At `p = 2`, the squared Schatten gauge of `rowSquare a` equals
`∑ k, matrixLpGauge 2 (a k) ^ 2`. -/
theorem matrixLpGauge_two_rowSquare_sq [Fintype ι] (a : ι → CStarMatrix m m ℂ) :
    matrixLpGauge 2 (rowSquare a) ^ 2 = ∑ k, matrixLpGauge 2 (a k) ^ 2 := by
  simp only [rowSquare_eq_columnSquare_star, matrixLpGauge_two_columnSquare_sq, matrixLpGauge_star]

omit [DecidableEq m] in
/-- On a single-element index type,
`matrixLpGauge p (columnSquare a) = matrixLpGauge p (a default)`. -/
theorem matrixLpGauge_columnSquare_unique [Fintype ι] [Unique ι] (p : ℝ≥0)
    (a : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (columnSquare a) = matrixLpGauge p (a default) :=
  matrixLpGauge_eq_of_mul_self p (columnSquare_nonneg a) (by rw [columnSquare_mul_self]; simp)

omit [DecidableEq m] in
/-- On a single-element index type,
`matrixLpGauge p (rowSquare a) = matrixLpGauge p (a default)`. -/
theorem matrixLpGauge_rowSquare_unique [Fintype ι] [Unique ι] (p : ℝ≥0)
    (a : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (rowSquare a) = matrixLpGauge p (a default) := by
  rw [rowSquare_eq_columnSquare_star, matrixLpGauge_columnSquare_unique, matrixLpGauge_star]

/-- **Rank-one Gram identity** in `CStarMatrix`:
`star (rankOne ℂ η ξ) * rankOne ℂ η ξ = (‖η‖ ^ 2) • rankOne ℂ ξ ξ` under `toEuclideanCLM`. -/
theorem star_toEuclideanCLM_symm_rankOne_mul_self (η ξ : EuclideanSpace ℂ m) :
    star (CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ η ξ)) *
      CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ η ξ) =
      (‖η‖ ^ 2) • CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ ξ ξ) := by
  refine EquivLike.injective CStarMatrix.toEuclideanCLM ?_
  rw [map_mul, map_star, ← algebraMap_smul ℂ (‖η‖ ^ 2), map_smul]
  simp [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
    ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne]

/-- For `0 < p`, the Schatten `p`-gauge of `columnSquare` of a family of rank-one operators with
common unit source vector `ξ` is `√(∑ k, ‖η k‖ ^ 2)`. -/
theorem matrixLpGauge_columnSquare_rankOne [Fintype ι] {p : ℝ≥0} (hp : 0 < p)
    (η : ι → EuclideanSpace ℂ m) {ξ : EuclideanSpace ℂ m} (hξ : ‖ξ‖ = 1) :
    matrixLpGauge p (columnSquare fun k =>
      CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ (η k) ξ)) =
      √(∑ k, ‖η k‖ ^ 2) := by
  let P := CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ ξ ξ)
  let b := fun k => CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ (η k) ξ)
  set s : ℝ := √(∑ k, ‖η k‖ ^ 2)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self hξ).map CStarMatrix.toEuclideanCLM.symm
  have hcol : columnSquare b = s • P := columnSquare_eq_of_mul_self (by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← sq, Real.sq_sqrt (by positivity),
      hP.isIdempotentElem.eq, Finset.sum_smul]
    exact (Finset.sum_congr rfl fun k _ =>
      star_toEuclideanCLM_symm_rankOne_mul_self (η k) ξ).symm)
    (smul_nonneg hs_nonneg hP.nonneg)
  have htrP : Matrix.trace (CStarMatrix.ofMatrix.symm P) = 1 := by
    rw [← CStarMatrix.trace_toEuclideanCLM, StarAlgEquiv.apply_symm_apply,
      InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  have hP_gauge : matrixLpGauge p P = 1 := by
    rw [matrixLpGauge_of_isStarProjection hp hP, htrP, Complex.one_re, Real.one_rpow]
  rw [hcol, ← algebraMap_smul ℂ s P, Complex.coe_algebraMap, matrixLpGauge_smul hp,
    Complex.norm_real, Real.norm_of_nonneg hs_nonneg, hP_gauge, mul_one]

omit [DecidableEq m] in
/-- Polar decomposition through `columnSquare`: `b k = u k * columnSquare b` with
`‖columnSquare u‖ ≤ 1`. -/
theorem exists_mul_columnSquare_and_norm_columnSquare_le_one [Fintype ι]
    (b : ι → CStarMatrix m m ℂ) :
    ∃ u : ι → CStarMatrix m m ℂ, (∀ k, b k = u k * columnSquare b) ∧ ‖columnSquare u‖ ≤ 1 := by
  classical
  set A := columnEuclideanLM b
  let U := A.polarFactor
  let u : ι → CStarMatrix m m ℂ := fun k => CStarMatrix.toEuclideanCLM.symm
    ((PiLp.projₗ 2 (fun _ : ι => EuclideanSpace ℂ m) k).comp U).toContinuousLinearMap
  have hu_eq : columnEuclideanLM u = U := columnEuclideanLM_projₗ U
  have hu (k : ι) (v : EuclideanSpace ℂ m) :
      CStarMatrix.toEuclideanCLM (u k) v = (U v).ofLp k := by
    rw [← columnEuclideanLM_apply u v k, hu_eq]
  have hgram : CStarMatrix.toEuclideanCLM (∑ k, star (u k) * u k) =
      (U.adjoint ∘ₗ U).toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_inj.mp
    rw [LinearMap.coe_toContinuousLinearMap, ← hu_eq, adjoint_comp_columnEuclideanLM u]
  refine ⟨u, fun k => EquivLike.injective CStarMatrix.toEuclideanCLM <|
      ContinuousLinearMap.ext fun v => ?_, ?_⟩
  · have hpol := congrArg (fun w : PiLp 2 fun _ : ι => EuclideanSpace ℂ m => w.ofLp k)
      (A.polarFactor_operatorAbs_apply v)
    rw [operatorAbs_columnEuclideanLM, columnEuclideanLM_apply] at hpol
    rw [map_mul, mul_apply_eq_comp, hu]; exact hpol.symm
  · rw [norm_columnSquare, Real.sqrt_le_one, ← CStarMatrix.norm_toEuclideanCLM, hgram]
    exact (LinearMap.isStarProjection_toContinuousLinearMap_iff.mpr
      A.isPartialIsometry_polarFactor.isStarProjection_adjoint_comp_self).norm_le

omit [DecidableEq m] in
/-- **Column-row trace-pairing Hölder inequality**:
`‖∑ k, tr(x k * b k)‖ ≤ ‖rowSquare x‖ * matrixLpGauge 1 (columnSquare b)`. -/
theorem norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare [Fintype ι]
    (x b : ι → CStarMatrix m m ℂ) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k))‖ ≤
      ‖rowSquare x‖ * matrixLpGauge 1 (columnSquare b) := by
  obtain ⟨u, hbu, hu_norm⟩ := exists_mul_columnSquare_and_norm_columnSquare_le_one b
  have htr : ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k)) =
      Matrix.trace (CStarMatrix.ofMatrix.symm ((∑ k, x k * u k) * columnSquare b)) := by
    simp only [hbu, ← mul_assoc, ← CStarMatrix.traceLinearMap_apply (R := ℂ), Finset.sum_mul,
      map_sum]
  rw [htr]
  exact (norm_trace_mul_le_norm_mul_matrixLpGauge_one _ _).trans <|
    mul_le_mul_of_nonneg_right ((norm_sum_mul_le_norm_rowSquare_mul_norm_columnSquare x u).trans
      (mul_le_of_le_one_right (norm_nonneg _) hu_norm)) (matrixLpGauge_nonneg 1 _)

omit [DecidableEq m] in
/-- **Row-column trace-pairing Hölder inequality**:
`‖∑ k, tr(x k * c k)‖ ≤ ‖columnSquare x‖ * matrixLpGauge 1 (rowSquare c)`. -/
theorem norm_sum_trace_mul_le_norm_columnSquare_mul_matrixLpGauge_one_rowSquare [Fintype ι]
    (x c : ι → CStarMatrix m m ℂ) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * c k))‖ ≤
      ‖columnSquare x‖ * matrixLpGauge 1 (rowSquare c) := by
  simpa only [CStarMatrix.norm_sum_trace_star_mul_star, ← rowSquare_eq_columnSquare_star,
    ← columnSquare_eq_rowSquare_star] using
    norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare
      (fun k => star (x k)) (fun k => star (c k))

omit [DecidableEq m] in
/-- **Converse trace-pairing bound (row norm)**: if
`‖∑ k, tr(x k * b k)‖ ≤ C * matrixLpGauge 1 (columnSquare b)` for all `b`, then `‖rowSquare x‖ ≤ C`.
-/
theorem norm_rowSquare_le_of_forall_norm_sum_trace_mul_le [Fintype ι]
    {x : ι → CStarMatrix m m ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ b : ι → CStarMatrix m m ℂ,
      ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k))‖ ≤
        C * matrixLpGauge 1 (columnSquare b)) : ‖rowSquare x‖ ≤ C := by
  classical
  set R := CStarMatrix.toEuclideanCLM (rowSquare x)
  rw [← CStarMatrix.norm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun ξ hξ => ?_
  let η (k : ι) := CStarMatrix.toEuclideanCLM (star (x k)) ξ
  let b := fun k => CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ (η k) ξ)
  have hR_sq : ‖R ξ‖ ^ 2 = ∑ k, ‖η k‖ ^ 2 := norm_rowSquare_apply_sq_eq x ξ
  have hpair : ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k)) =
      ((‖R ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [hR_sq, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← CStarMatrix.trace_toEuclideanCLM]
    simp only [b, map_mul, StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.toLinearMap_mul,
      InnerProductSpace.trace_mul_rankOne]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    simp [η, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  have hbound := h b
  rw [hpair, matrixLpGauge_columnSquare_rankOne zero_lt_one η hξ, ← hR_sq,
    Real.sqrt_sq (norm_nonneg _), Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
    sq] at hbound
  exact (norm_nonneg (R ξ)).eq_or_lt.elim (fun h0 => by linarith) (le_of_mul_le_mul_right hbound)

omit [DecidableEq m] in
/-- **Converse trace-pairing bound (column norm)**: if
`‖∑ k, tr(x k * c k)‖ ≤ C * matrixLpGauge 1 (rowSquare c)` for all `c`, then `‖columnSquare x‖ ≤ C`.
-/
theorem norm_columnSquare_le_of_forall_norm_sum_trace_mul_le [Fintype ι]
    {x : ι → CStarMatrix m m ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : ι → CStarMatrix m m ℂ,
      ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * c k))‖ ≤
        C * matrixLpGauge 1 (rowSquare c)) : ‖columnSquare x‖ ≤ C := by
  rw [columnSquare_eq_rowSquare_star]
  refine norm_rowSquare_le_of_forall_norm_sum_trace_mul_le hC fun b => ?_
  simpa only [← CStarMatrix.norm_sum_trace_star_mul_star x (fun k => star (b k)), star_star,
    rowSquare_eq_columnSquare_star] using h (fun k => star (b k))

end ColumnRow

end TauCeti
