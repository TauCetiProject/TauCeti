/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten

import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison

/-!
# The Schatten `p`-gauge on matrix C⋆-algebras

For a finite index type `n`, `CStarMatrix n n ℂ` is the C⋆-algebra of `n × n` complex matrices
equipped with the `ℓ²` operator norm. Using the unnormalized matrix trace and the continuous
functional calculus, its noncommutative `Lᵖ` gauge (the **Schatten `p`-gauge**) is

`matrixLpGauge p x = (tr(|x|^p)).re ^ (1 / p)`, where `|x| = √(x⋆ x)`.

Through the isometric `⋆`-algebra equivalence `CStarMatrix.toEuclideanCLM` between
`CStarMatrix n n ℂ` and `EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n`, this file evaluates
`tr(|x|^p)` in the right singular basis of `x` to obtain the singular-value formula

`matrixLpGauge p x = (∑ᵢ σᵢ(x)^p) ^ (1 / p)` for `0 < p`.

For `1 ≤ p`, this identifies `matrixLpGauge p` with `TauCeti.UnitarilyInvariantSeminorm.schatten`,
from which `matrixLpGauge p` inherits the triangle inequality, homogeneity, star invariance, the
two-sided ideal bounds against the operator norm, and faithfulness. At the nuclear endpoint `p = 1`
we also record trace-norm duality: `|re tr(b x)| ≤ ‖b‖ · matrixLpGauge 1 x`, with equality attained
by a contraction `u` (`‖u‖ ≤ 1`).

## Main declarations

* `CStarMatrix.toEuclideanCLM`: the isometric `⋆`-algebra isomorphism between `CStarMatrix n n ℂ`
  and `EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n`.
* `TauCeti.matrixLpGauge`: the Schatten `p`-gauge `(tr(|x|^p)).re ^ (1 / p)` on
  `CStarMatrix n n ℂ`.
* `TauCeti.matrixLpGauge_eq_singularValues_sum`: the singular-value formula for `0 < p`.
* `TauCeti.matrixLpGauge_eq_schatten`, `TauCeti.matrixLpGauge_one_eq_nuclear`: agreement with the
  Schatten and nuclear seminorms on `EuclideanSpace ℂ n`.
* `TauCeti.matrixLpSeminorm`: `matrixLpGauge p` bundled as a `ℂ`-seminorm for `1 ≤ p`.
* `TauCeti.norm_trace_mul_le_norm_mul_matrixLpGauge_one`,
  `TauCeti.exists_norm_le_one_and_trace_mul_eq_matrixLpGauge_one`: trace-norm duality at `p = 1`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* G. Pisier and Q. Xu, *Non-commutative `Lᵖ`-spaces*, in *Handbook of the Geometry of Banach
  Spaces*, Vol. 2, North-Holland, 2003, §1–2.
-/

public section

noncomputable section

open scoped BigOperators ComplexOrder NNReal ENNReal InnerProductSpace

namespace CStarMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The natural `⋆`-algebra equivalence between `CStarMatrix n n ℂ` and continuous linear
endomorphisms of `EuclideanSpace ℂ n`, obtained by composing `ofMatrixStarAlgEquiv.symm` with
`Matrix.toEuclideanCLM`. -/
def toEuclideanCLM :
    CStarMatrix n n ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  ofMatrixStarAlgEquiv.symm.trans (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))

/-- `toEuclideanCLM` acts on an underlying matrix via `Matrix.toEuclideanCLM`. -/
theorem toEuclideanCLM_apply (x : CStarMatrix n n ℂ) :
    toEuclideanCLM x = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (ofMatrix.symm x) :=
  (rfl)

/-- `toEuclideanCLM` is isometric for the C⋆-algebra norm on `CStarMatrix n n ℂ` and the operator
norm on `EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n`. -/
@[simp]
theorem norm_toEuclideanCLM (x : CStarMatrix n n ℂ) :
    ‖toEuclideanCLM x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map toEuclideanCLM toEuclideanCLM.injective x

/-- The operator trace of `toEuclideanCLM x` equals the matrix trace of `x`. -/
@[simp]
theorem trace_toEuclideanCLM (x : CStarMatrix n n ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ n) (toEuclideanCLM x).toLinearMap =
      Matrix.trace (ofMatrix.symm x) := by
  let b := EuclideanSpace.basisFun n ℂ
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  congr 1
  exact (LinearMap.toMatrixOrthonormal b).apply_symm_apply (ofMatrix.symm x)

/-- `toEuclideanCLM` commutes with the real non-unital continuous functional calculus. -/
theorem toEuclideanCLM_cfcₙ (f : ℝ → ℝ) (x : CStarMatrix n n ℂ)
    (hf : ContinuousOn f (quasispectrum ℝ x) := by cfc_cont_tac)
    (hf₀ : f 0 = 0 := by cfc_zero_tac) (hx : IsSelfAdjoint x := by cfc_tac) :
    toEuclideanCLM (cfcₙ f x) = cfcₙ f (toEuclideanCLM x) :=
  ((toEuclideanCLM (n := n)).toNonUnitalStarAlgHom.restrictScalars ℝ).map_cfcₙ f x hf hf₀
    (NonUnitalStarAlgHom.isometry (toEuclideanCLM (n := n)) toEuclideanCLM.injective).continuous hx

end CStarMatrix

namespace TauCeti

section Gauge

variable {n : Type*} [Fintype n]

/-- The Schatten `p`-gauge `(tr(|x|^p)).re ^ (1 / p)` of a matrix `x : CStarMatrix n n ℂ` with
respect to the unnormalized matrix trace, where `|x| = √(x⋆ x)`. -/
def matrixLpGauge (p : ℝ≥0) (x : CStarMatrix n n ℂ) : ℝ :=
  (Matrix.trace (CStarMatrix.ofMatrix.symm
    (CFC.nnrpow (CFC.sqrt (star x * x)) p))).re ^ (1 / (p : ℝ))

/-- Unfolding definition of `matrixLpGauge`. -/
theorem matrixLpGauge_def (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p x =
      (Matrix.trace (CStarMatrix.ofMatrix.symm
        (CFC.nnrpow (CFC.sqrt (star x * x)) p))).re ^ (1 / (p : ℝ)) :=
  (rfl)

/-- For `0 < p`, the trace `tr(|x|^p)` is the sum `∑ᵢ σᵢ(x)^p` of the `p`-th powers of the
singular values of the Euclidean operator attached to `x`. -/
theorem trace_nnrpow_sqrt_star_mul_self [DecidableEq n] {p : ℝ≥0} (hp : 0 < p)
    (x : CStarMatrix n n ℂ) :
    Matrix.trace (CStarMatrix.ofMatrix.symm (CFC.nnrpow (CFC.sqrt (star x * x)) p)) =
      ((((CStarMatrix.toEuclideanCLM x).toLinearMap.singularValues.sum
        fun _ s => s ^ (p : ℝ)) : ℝ) : ℂ) := by
  set T := CStarMatrix.toEuclideanCLM x
  set A := T.toLinearMap
  have hp2 : (0 : ℝ) < ((p / 2 : ℝ≥0) : ℝ) := by positivity
  have hf0 : (0 : ℝ) ^ ((p / 2 : ℝ≥0) : ℝ) = 0 := Real.zero_rpow hp2.ne'
  have hfcont : Continuous (fun t : ℝ => t ^ ((p / 2 : ℝ≥0) : ℝ)) :=
    Real.continuous_rpow_const hp2.le
  have hmap : CStarMatrix.toEuclideanCLM (CFC.nnrpow (CFC.sqrt (star x * x)) p) =
      cfc (fun t : ℝ => t ^ ((p / 2 : ℝ≥0) : ℝ)) (star T * T) := by
    rw [CFC.nnrpow_eq_pow, CFC.nnrpow_sqrt, CFC.nnrpow_eq_cfcₙ_real (star x * x) (p / 2),
      CStarMatrix.toEuclideanCLM_cfcₙ _ (star x * x) hfcont.continuousOn hf0,
      map_mul, map_star, cfcₙ_eq_cfc]
  rw [← CStarMatrix.trace_toEuclideanCLM, hmap,
    LinearMap.trace_eq_sum_inner _ A.rightSingularBasis,
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
  · simp [show CStarMatrix.ofMatrix.symm (0 : CStarMatrix n n ℂ) = 0 from rfl]
  · rw [re_trace_nnrpow_sqrt_star_mul_self hp x]
    exact Finsupp.sum_nonneg fun i _ =>
      Real.rpow_nonneg ((CStarMatrix.toEuclideanCLM x).toLinearMap.singularValues_nonneg i) _

/-- The Schatten `p`-gauge is nonnegative. -/
theorem matrixLpGauge_nonneg (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    0 ≤ matrixLpGauge p x :=
  Real.rpow_nonneg (re_trace_nnrpow_sqrt_star_mul_self_nonneg p x) _

/-- Raising `matrixLpGauge p x` to the power `p` recovers `(tr(|x|^p)).re` when `0 < p`. -/
theorem matrixLpGauge_rpow {p : ℝ≥0} (hp : 0 < p) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p x ^ (p : ℝ) =
      (Matrix.trace (CStarMatrix.ofMatrix.symm (CFC.nnrpow (CFC.sqrt (star x * x)) p))).re := by
  rw [matrixLpGauge_def, ← Real.rpow_mul (re_trace_nnrpow_sqrt_star_mul_self_nonneg p x),
    one_div_mul_cancel (NNReal.coe_pos.mpr hp).ne', Real.rpow_one]

/-- At `p = 1`, `matrixLpGauge 1 x` is the real part of `tr(|x|)`. -/
theorem matrixLpGauge_one_eq_re_trace (x : CStarMatrix n n ℂ) :
    matrixLpGauge 1 x =
      (Matrix.trace (CStarMatrix.ofMatrix.symm (CFC.sqrt (star x * x)))).re := by
  simp [matrixLpGauge_def, CFC.nnrpow_one]

/-- For a positive element `0 ≤ x` of `CStarMatrix n n ℂ`, the trace norm `matrixLpGauge 1 x` is
simply `(tr x).re`. -/
theorem matrixLpGauge_one_of_nonneg {x : CStarMatrix n n ℂ} (hx : 0 ≤ x) :
    matrixLpGauge 1 x = (Matrix.trace (CStarMatrix.ofMatrix.symm x)).re := by
  rw [matrixLpGauge_one_eq_re_trace, hx.star_eq, CFC.sqrt_mul_self x hx]

/-- **Singular-value formula for `matrixLpGauge`.** For `0 < p`, `matrixLpGauge p x` equals
`(∑ᵢ σᵢ(x)^p) ^ (1 / p)`, where `σᵢ(x)` are the singular values of `toEuclideanCLM x`. -/
theorem matrixLpGauge_eq_singularValues_sum [DecidableEq n] {p : ℝ≥0} (hp : 0 < p)
    (x : CStarMatrix n n ℂ) :
    matrixLpGauge p x =
      ((CStarMatrix.toEuclideanCLM x).toLinearMap.singularValues.sum
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

/-- At `p = 1`, `matrixLpGauge 1` agrees with the nuclear (trace) seminorm on
`EuclideanSpace ℂ n`. -/
theorem matrixLpGauge_one_eq_nuclear [DecidableEq n] (x : CStarMatrix n n ℂ) :
    matrixLpGauge 1 x =
      UnitarilyInvariantSeminorm.nuclear ℂ (EuclideanSpace ℂ n) (EuclideanSpace ℂ n)
        (CStarMatrix.toEuclideanCLM x).toLinearMap := by
  let : Fact (1 ≤ ((1 : ℝ≥0) : ℝ≥0∞)) := ⟨le_rfl⟩
  simpa using matrixLpGauge_eq_schatten 1 x

/-- For `0 < p`, the zero matrix has `matrixLpGauge p 0 = 0`. -/
@[simp]
theorem matrixLpGauge_zero {p : ℝ≥0} (hp : 0 < p) :
    matrixLpGauge p (0 : CStarMatrix n n ℂ) = 0 := by
  simp [matrixLpGauge_def, show CStarMatrix.ofMatrix.symm (0 : CStarMatrix n n ℂ) = 0 from rfl,
    Real.zero_rpow (inv_ne_zero (NNReal.coe_pos.mpr hp).ne')]

/-- For `0 < p`, `matrixLpGauge p x = 0` if and only if `x = 0`. -/
@[simp]
theorem matrixLpGauge_eq_zero_iff {p : ℝ≥0} (hp : 0 < p) {x : CStarMatrix n n ℂ} :
    matrixLpGauge p x = 0 ↔ x = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ matrixLpGauge_zero hp⟩
  set A := (CStarMatrix.toEuclideanCLM x).toLinearMap
  have hfin : ∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ n)),
      A.singularValues i ^ (p : ℝ) = 0 := by
    rw [A.sum_fin_singularValues (· ^ (p : ℝ)) (Real.zero_rpow (NNReal.coe_pos.mpr hp).ne'),
      ← re_trace_nnrpow_sqrt_star_mul_self hp x, ← matrixLpGauge_rpow hp x, h,
      Real.zero_rpow (NNReal.coe_pos.mpr hp).ne']
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun (i : Fin _) _ =>
    Real.rpow_nonneg (A.singularValues_nonneg i) (p : ℝ)).mp hfin
  have hA : A = 0 := A.rightSingularBasis.toBasis.ext fun i => by
    have h0 := (Real.rpow_eq_zero (A.singularValues_nonneg i) (NNReal.coe_pos.mpr hp).ne').mp
      (hall i (Finset.mem_univ _))
    rw [OrthonormalBasis.coe_toBasis, LinearMap.zero_apply, ← norm_eq_zero,
      A.norm_apply_rightSingularBasis i, h0]
  exact CStarMatrix.toEuclideanCLM.injective
    ((ContinuousLinearMap.coe_inj.mp hA).trans (map_zero _).symm)

/-- The Schatten `p`-gauge is invariant under the C⋆-algebra involution `star`. -/
@[simp]
theorem matrixLpGauge_star (p : ℝ≥0) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p (star x) = matrixLpGauge p x := by
  classical
  obtain rfl | hp := eq_zero_or_pos p
  · simp [matrixLpGauge_def]
  · rw [matrixLpGauge_eq_singularValues_sum hp, matrixLpGauge_eq_singularValues_sum hp,
      map_star, ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_toLinearMap,
      LinearMap.singularValues_adjoint]

/-- For `1 ≤ p`, `matrixLpGauge p` is subadditive. -/
theorem matrixLpGauge_add_le {p : ℝ≥0} (hp : 1 ≤ p) (x y : CStarMatrix n n ℂ) :
    matrixLpGauge p (x + y) ≤ matrixLpGauge p x + matrixLpGauge p y := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  simp only [matrixLpGauge_eq_schatten p, map_add, ContinuousLinearMap.toLinearMap_add]
  exact map_add_le_add _ _ _

/-- For `1 ≤ p`, `matrixLpGauge p` is absolutely homogeneous over `ℂ`. -/
theorem matrixLpGauge_smul {p : ℝ≥0} (hp : 1 ≤ p) (c : ℂ) (x : CStarMatrix n n ℂ) :
    matrixLpGauge p (c • x) = ‖c‖ * matrixLpGauge p x := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  simp only [matrixLpGauge_eq_schatten p, map_smul, ContinuousLinearMap.toLinearMap_smul]
  exact (UnitarilyInvariantSeminorm.schatten ℂ (EuclideanSpace ℂ n) (EuclideanSpace ℂ n) p
    ).toSeminorm.smul' c _

variable (n) in
/-- For `1 ≤ p`, `matrixLpGauge p` bundled as a `ℂ`-seminorm on `CStarMatrix n n ℂ`. -/
def matrixLpSeminorm (p : ℝ≥0) (hp : 1 ≤ p) : Seminorm ℂ (CStarMatrix n n ℂ) :=
  Seminorm.of (matrixLpGauge p) (matrixLpGauge_add_le hp) (matrixLpGauge_smul hp)

@[simp]
theorem matrixLpSeminorm_apply (p : ℝ≥0) (hp : 1 ≤ p) (x : CStarMatrix n n ℂ) :
    matrixLpSeminorm n p hp x = matrixLpGauge p x :=
  (rfl)

/-- For `1 ≤ p`, the operator norm is bounded by `matrixLpGauge p`. -/
theorem norm_le_matrixLpGauge {p : ℝ≥0} (hp : 1 ≤ p) (x : CStarMatrix n n ℂ) :
    ‖x‖ ≤ matrixLpGauge p x := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  have hcoe : (CStarMatrix.toEuclideanCLM x).toLinearMap.toContinuousLinearMap =
      CStarMatrix.toEuclideanCLM x := by ext; rfl
  rw [← CStarMatrix.norm_toEuclideanCLM, ← hcoe, matrixLpGauge_eq_schatten p]
  simpa only [UnitarilyInvariantSeminorm.opNorm_apply] using
    UnitarilyInvariantSeminorm.opNorm_apply_le_schatten_apply (p : ℝ≥0∞)
      (CStarMatrix.toEuclideanCLM x).toLinearMap

/-- **Left ideal inequality.** For `1 ≤ p`, `matrixLpGauge p (x * y) ≤ ‖x‖ * matrixLpGauge p y`. -/
theorem matrixLpGauge_mul_le_left {p : ℝ≥0} (hp : 1 ≤ p) (x y : CStarMatrix n n ℂ) :
    matrixLpGauge p (x * y) ≤ ‖x‖ * matrixLpGauge p y := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  rw [matrixLpGauge_eq_schatten p, matrixLpGauge_eq_schatten p, map_mul,
    ContinuousLinearMap.toLinearMap_mul, ← CStarMatrix.norm_toEuclideanCLM]
  exact UnitarilyInvariantSeminorm.schatten_comp_le_left (p : ℝ≥0∞)
    _ _ (CStarMatrix.toEuclideanCLM x).le_opNorm

/-- **Right ideal inequality.** For `1 ≤ p`, `matrixLpGauge p (x * y) ≤ matrixLpGauge p x * ‖y‖`. -/
theorem matrixLpGauge_mul_le_right {p : ℝ≥0} (hp : 1 ≤ p) (x y : CStarMatrix n n ℂ) :
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
    _ ≤ ‖b‖ * matrixLpGauge 1 x := matrixLpGauge_mul_le_left le_rfl b x

/-- Real-part form of the `(∞, 1)` trace-norm Hölder inequality:
`|(tr(b x)).re| ≤ ‖b‖ * matrixLpGauge 1 x`. -/
theorem abs_re_trace_mul_le_norm_mul_matrixLpGauge_one (b x : CStarMatrix n n ℂ) :
    |(Matrix.trace (CStarMatrix.ofMatrix.symm (b * x))).re| ≤ ‖b‖ * matrixLpGauge 1 x :=
  (Complex.abs_re_le_norm _).trans (norm_trace_mul_le_norm_mul_matrixLpGauge_one b x)

/-- **Trace-norm duality attainment**: for every `x : CStarMatrix n n ℂ`, there exists a
contraction `u : CStarMatrix n n ℂ` (`‖u‖ ≤ 1`) with `tr(u x) = matrixLpGauge 1 x`. -/
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

end TauCeti
