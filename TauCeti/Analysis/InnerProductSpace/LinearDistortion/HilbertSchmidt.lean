/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import Mathlib.Analysis.MeanInequalities

/-!
# The Hilbert–Schmidt distortion of a linear map

Let `V` and `W` be oriented real inner product spaces of the same finite dimension `n`, and let
`A : V →ₗ[ℝ] W` be linear, with Hilbert–Schmidt (Frobenius) norm
`‖A‖_HS = (σ₁² + ⋯ + σₙ²)^{1/2}` (`TauCeti.UnitarilyInvariantSeminorm.frobenius`) and oriented
Jacobian `J(A)`. The **Hilbert–Schmidt distortion** is

    q_S(A) = ‖A‖_HSⁿ / (n^{n/2} J(A))   if J(A) > 0,     q_S(A) = 0   if A = 0 and J(A) ≤ 0,
    q_S(A) = ∞                           if A ≠ 0 and J(A) ≤ 0,

the normalisation of the distortion inequality by the Hilbert–Schmidt norm, as in
Martio–Rickman–Väisälä (2.23). It compares with the outer distortion `q_O(A)`
(`Orientation.outerDistortion`) by `q_S(A) ≤ q_O(A) ≤ n^{n/2} q_S(A)` (Martio–Rickman–Väisälä
(2.24)), since `‖A‖ ≤ ‖A‖_HS ≤ √n ‖A‖`. When `J(A) > 0` it is at least `1`: by the inequality of
arithmetic and geometric means on the `σᵢ²`, `J(A) = σ₁ ⋯ σₙ ≤ (‖A‖_HS / √n)ⁿ`. For example
`q_S(diag(2, 1)) = 5/4` while `q_O(diag(2, 1)) = 2`.

## Main declarations

* `Orientation.hilbertSchmidtDistortion`: `q_S(A)`.
* `Orientation.hilbertSchmidtDistortion_eq_ofReal_singularValues`: the singular-value formula
  `q_S(A) = (σ₁² + ⋯ + σₙ²)^{n/2} / (n^{n/2} σ₁ ⋯ σₙ)` when `J(A) > 0`.
* `Orientation.orientedJacobian_le_frobenius_div_sqrt_pow`: `J(A) ≤ (‖A‖_HS / √n)ⁿ`.
* `Orientation.one_le_hilbertSchmidtDistortion`: `q_S(A) ≥ 1` when `J(A) > 0`.
* `Orientation.hilbertSchmidtDistortion_le_outerDistortion`,
  `Orientation.outerDistortion_le_mul_hilbertSchmidtDistortion`: `q_S ≤ q_O ≤ n^{n/2} q_S`.
* `Orientation.hilbertSchmidtDistortion_smul`,
  `Orientation.hilbertSchmidtDistortion_linearIsometry_comp`,
  `Orientation.hilbertSchmidtDistortion_comp_linearIsometryEquiv`: the invariances of `q_O`.

## References

* O. Martio, S. Rickman and J. Väisälä, *Definitions for quasiregular mappings*, Ann. Acad. Sci.
  Fenn. Ser. A I 448 (1969), Section 2, (2.23)–(2.24).
-/

public section

noncomputable section

open Module TauCeti.UnitarilyInvariantSeminorm
open scoped ENNReal

namespace Orientation

variable {V W X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)] [Fact (finrank ℝ X = n)]

/-- The **Hilbert–Schmidt distortion** `q_S(A) ∈ [0, ∞]` of a linear map `A` between oriented
real inner product spaces of the same dimension `n`: `‖A‖_HSⁿ / (n^{n/2} J(A))` when the oriented
Jacobian `J(A)` is positive, where `‖A‖_HS` is the Frobenius norm, `0` for the zero map when
`J(A) ≤ 0`, and `∞` for a nonzero map with `J(A) ≤ 0`. -/
def hilbertSchmidtDistortion (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) : ℝ≥0∞ :=
  open Classical in
  if 0 < oV.orientedJacobian oW A then
    ENNReal.ofReal (frobenius ℝ V W A ^ n / (√(n : ℝ) ^ n * oV.orientedJacobian oW A))
  else if A = 0 then 0 else ⊤

variable (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
  (oX : Orientation ℝ X (Fin n))

omit [FiniteDimensional ℝ W] in
open Classical in
/-- The defining case split of the Hilbert–Schmidt distortion. -/
theorem hilbertSchmidtDistortion_def (A : V →ₗ[ℝ] W) :
    oV.hilbertSchmidtDistortion oW A =
      if 0 < oV.orientedJacobian oW A then
        ENNReal.ofReal (frobenius ℝ V W A ^ n / (√(n : ℝ) ^ n * oV.orientedJacobian oW A))
      else if A = 0 then 0 else ⊤ :=
  (rfl)

theorem hilbertSchmidtDistortion_of_pos {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    oV.hilbertSchmidtDistortion oW A =
      ENNReal.ofReal (frobenius ℝ V W A ^ n / (√(n : ℝ) ^ n * oV.orientedJacobian oW A)) := by
  simp [hilbertSchmidtDistortion_def, h]

omit [FiniteDimensional ℝ W] in
theorem hilbertSchmidtDistortion_of_nonpos {A : V →ₗ[ℝ] W} (h : oV.orientedJacobian oW A ≤ 0)
    (hA : A ≠ 0) : oV.hilbertSchmidtDistortion oW A = ⊤ := by
  simp [hilbertSchmidtDistortion_def, h.not_gt, hA]

omit [FiniteDimensional ℝ W] in
/-- In positive dimension the zero map has Hilbert–Schmidt distortion `0`. -/
@[simp]
theorem hilbertSchmidtDistortion_zero (hn : 0 < n) : oV.hilbertSchmidtDistortion oW 0 = 0 := by
  simp [hilbertSchmidtDistortion_def, oV.orientedJacobian_zero_of_pos oW hn]

/-! ### The Frobenius norm against the operator norm and the Jacobian -/

omit [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)] in
/-- The power `√n ^ n`, the normalising constant `n^{n/2}`, is positive (it is `1` for
`n = 0`). -/
theorem _root_.Real.sqrt_natCast_pow_self_pos (n : ℕ) : 0 < √(n : ℝ) ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact pow_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)) n

omit [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)] in
/-- The Frobenius norm is the square root of the sum of the squares of the singular values below
the dimension. -/
theorem _root_.LinearMap.frobenius_eq_sqrt_sum_range (A : V →ₗ[ℝ] W) :
    frobenius ℝ V W A = √(∑ i ∈ Finset.range (finrank ℝ V), A.singularValues i ^ 2) := by
  rw [← Real.sqrt_sq (apply_nonneg _ A), A.sq_frobenius_apply_eq_sum_sq_singularValues,
    Fin.sum_univ_eq_sum_range (fun i ↦ A.singularValues i ^ 2)]

omit [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)] in
/-- The operator norm is at most the Frobenius norm. -/
theorem _root_.LinearMap.norm_toContinuousLinearMap_le_frobenius (A : V →ₗ[ℝ] W) :
    ‖LinearMap.toContinuousLinearMap A‖ ≤ frobenius ℝ V W A := by
  simpa [opNorm_apply] using opNorm_apply_le_schatten_apply 2 A

omit [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)] in
/-- The Frobenius norm is at most `√(dim V)` times the operator norm. -/
theorem _root_.LinearMap.frobenius_le_sqrt_finrank_mul_norm (A : V →ₗ[ℝ] W) :
    frobenius ℝ V W A ≤ √(finrank ℝ V : ℝ) * ‖LinearMap.toContinuousLinearMap A‖ := by
  rw [A.frobenius_eq_sqrt_sum_range, A.norm_toContinuousLinearMap_eq_singularValues_zero,
    ← Real.sqrt_sq (A.singularValues_nonneg 0), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i ∈ Finset.range (finrank ℝ V), A.singularValues i ^ 2
      ≤ ∑ _i ∈ Finset.range (finrank ℝ V), A.singularValues 0 ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (A.singularValues_nonneg i)
          (A.singularValues_antitone (Nat.zero_le i)) 2
    _ = _ := by simp

/-- **Arithmetic and geometric means** for `n` nonnegative numbers, in the form used for the
Hilbert–Schmidt distortion: `σ₀ ⋯ σₙ₋₁ ≤ ((σ₀² + ⋯ + σₙ₋₁²)^{1/2} / √n)ⁿ`. -/
theorem _root_.Real.prod_range_le_sqrt_sum_sq_div_sqrt_pow (σ : ℕ → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (n : ℕ) :
    ∏ i ∈ Finset.range n, σ i ≤ (√(∑ i ∈ Finset.range n, σ i ^ 2) / √(n : ℝ)) ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hS : 0 ≤ ∑ i ∈ Finset.range n, σ i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- AM-GM for the squares `σᵢ²`, with unit weights.
  have hamgm := Real.geom_mean_le_arith_mean (Finset.range n) (fun _ ↦ (1 : ℝ))
    (fun i ↦ σ i ^ 2) (fun _ _ ↦ zero_le_one) (by simpa using hnR) (fun i _ ↦ sq_nonneg _)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    one_mul] at hamgm
  rw [Real.rpow_inv_le_iff_of_pos (Finset.prod_nonneg fun i _ ↦ sq_nonneg _)
    (div_nonneg hS hnR.le) hnR, Real.rpow_natCast, Finset.prod_pow] at hamgm
  have hrhs : (∑ i ∈ Finset.range n, σ i ^ 2) / n =
      (√(∑ i ∈ Finset.range n, σ i ^ 2) / √(n : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hS, Real.sq_sqrt hnR.le]
  rw [hrhs, ← pow_mul, mul_comm, pow_mul] at hamgm
  exact (pow_le_pow_iff_left₀ (Finset.prod_nonneg fun i _ ↦ hσ i)
    (pow_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) n) two_ne_zero).mp hamgm

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The oriented Jacobian is at most `(‖A‖_HS / √n)ⁿ`: the inequality of arithmetic and geometric
means for the squares of the singular values. -/
theorem orientedJacobian_le_frobenius_div_sqrt_pow (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A ≤ (frobenius ℝ V W A / √(n : ℝ)) ^ n := by
  refine (le_abs_self _).trans ?_
  rw [oV.abs_orientedJacobian oW A, A.normDet_eq_prod_singularValues, A.frobenius_eq_sqrt_sum_range,
    (Fact.out : finrank ℝ V = n)]
  exact Real.prod_range_le_sqrt_sum_sq_div_sqrt_pow _ A.singularValues_nonneg n

/-! ### Formula and lower bound -/

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The singular-value formula: when `J(A) > 0`,
`q_S(A) = (σ₁² + ⋯ + σₙ²)^{n/2} / (n^{n/2} σ₁ ⋯ σₙ)`. -/
theorem hilbertSchmidtDistortion_eq_ofReal_singularValues {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) :
    oV.hilbertSchmidtDistortion oW A =
      ENNReal.ofReal (√(∑ i ∈ Finset.range n, A.singularValues i ^ 2) ^ n /
        (√(n : ℝ) ^ n * ∏ i ∈ Finset.range n, A.singularValues i)) := by
  rw [oV.hilbertSchmidtDistortion_of_pos oW h, A.frobenius_eq_sqrt_sum_range,
    oV.orientedJacobian_eq_prod_singularValues_of_nonneg oW h.le, (Fact.out : finrank ℝ V = n)]

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- When `J(A) > 0`, the Hilbert–Schmidt distortion is at least `1`. -/
theorem one_le_hilbertSchmidtDistortion {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    1 ≤ oV.hilbertSchmidtDistortion oW A := by
  have hc := Real.sqrt_natCast_pow_self_pos n
  rw [oV.hilbertSchmidtDistortion_of_pos oW h, ENNReal.one_le_ofReal,
    one_le_div (mul_pos hc h), mul_comm, ← le_div_iff₀ hc, ← div_pow]
  exact oV.orientedJacobian_le_frobenius_div_sqrt_pow oW A

/-! ### Comparison with the outer distortion -/

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The Hilbert–Schmidt distortion is at most the outer distortion: `‖A‖_HS ≤ √n ‖A‖`. -/
theorem hilbertSchmidtDistortion_le_outerDistortion (A : V →ₗ[ℝ] W) :
    oV.hilbertSchmidtDistortion oW A ≤ oV.outerDistortion oW A := by
  by_cases h : 0 < oV.orientedJacobian oW A
  · rw [oV.hilbertSchmidtDistortion_of_pos oW h, oV.outerDistortion_of_pos oW h]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← div_div, div_le_div_iff_of_pos_right h,
      div_le_iff₀ (Real.sqrt_natCast_pow_self_pos n), ← mul_pow, mul_comm]
    refine pow_le_pow_left₀ (apply_nonneg _ A) ?_ n
    simpa [(Fact.out : finrank ℝ V = n)] using A.frobenius_le_sqrt_finrank_mul_norm
  · simp only [hilbertSchmidtDistortion_def, outerDistortion_def, h, ite_false, le_refl]

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The outer distortion is at most `n^{n/2}` times the Hilbert–Schmidt distortion:
`‖A‖ ≤ ‖A‖_HS`. -/
theorem outerDistortion_le_mul_hilbertSchmidtDistortion (A : V →ₗ[ℝ] W) :
    oV.outerDistortion oW A ≤
      ENNReal.ofReal (√(n : ℝ) ^ n) * oV.hilbertSchmidtDistortion oW A := by
  have hc := Real.sqrt_natCast_pow_self_pos n
  by_cases h : 0 < oV.orientedJacobian oW A
  · rw [oV.hilbertSchmidtDistortion_of_pos oW h, oV.outerDistortion_of_pos oW h,
      ← ENNReal.ofReal_mul hc.le, ← mul_div_assoc, mul_div_mul_left _ _ hc.ne']
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) A.norm_toContinuousLinearMap_le_frobenius n) h.le)
  by_cases hA : A = 0
  · subst hA
    simp [outerDistortion_def, hilbertSchmidtDistortion_def, h]
  rw [oV.outerDistortion_of_nonpos oW (not_lt.mp h) hA,
    oV.hilbertSchmidtDistortion_of_nonpos oW (not_lt.mp h) hA,
    ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']

/-! ### Invariance -/

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- Scaling by `c` with `cⁿ > 0` changes no Hilbert–Schmidt distortion. -/
theorem hilbertSchmidtDistortion_smul {c : ℝ} (hc : 0 < c ^ n) (A : V →ₗ[ℝ] W) :
    oV.hilbertSchmidtDistortion oW (c • A) = oV.hilbertSchmidtDistortion oW A := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : Subsingleton V := Module.finrank_zero_iff.mp (Fact.out : finrank ℝ V = 0)
    rw [Subsingleton.elim (c • A) A]
  have hc0 : c ≠ 0 := (pow_ne_zero_iff hn.ne').mp hc.ne'
  have hpow : |c| ^ n = c ^ n := by rw [pow_abs, abs_of_pos hc]
  have hzero : c • A = 0 ↔ A = 0 := smul_eq_zero_iff_right hc0
  rw [hilbertSchmidtDistortion_def, hilbertSchmidtDistortion_def, hzero]
  simp only [oV.orientedJacobian_smul oW, map_smul_eq_mul, Real.norm_eq_abs, mul_pow, hpow,
    mul_left_comm (√(n : ℝ) ^ n), mul_div_mul_left _ _ hc.ne', mul_pos_iff_of_pos_left hc]

/-- Postcomposing with a linear isometry of oriented Jacobian `1` (orientation-preserving) changes
no Hilbert–Schmidt distortion. -/
theorem hilbertSchmidtDistortion_linearIsometry_comp (U : W →ₗᵢ[ℝ] X)
    (hU : oW.orientedJacobian oX U.toLinearMap = 1) (A : V →ₗ[ℝ] W) :
    oV.hilbertSchmidtDistortion oX (U.toLinearMap ∘ₗ A) = oV.hilbertSchmidtDistortion oW A := by
  have hzero : U.toLinearMap ∘ₗ A = 0 ↔ A = 0 := by
    simp [LinearMap.ext_iff, map_eq_zero_iff U U.injective]
  have hF : frobenius ℝ V X (U.toLinearMap ∘ₗ A) = frobenius ℝ V W A := by
    simp only [frobenius_apply_eq_sqrt_sum_sq_singularValues,
      LinearMap.singularValues_linearIsometry_comp]
  rw [hilbertSchmidtDistortion_def, hilbertSchmidtDistortion_def,
    oV.orientedJacobian_comp_of_left_eq_one oW oX hU, hF, hzero]

/-- Precomposing with an isometric isomorphism of oriented Jacobian `1` (orientation-preserving)
changes no Hilbert–Schmidt distortion. -/
theorem hilbertSchmidtDistortion_comp_linearIsometryEquiv (U : X ≃ₗᵢ[ℝ] V)
    (hU : oX.orientedJacobian oV (U : X →ₗ[ℝ] V) = 1) (A : V →ₗ[ℝ] W) :
    oX.hilbertSchmidtDistortion oW (A ∘ₗ (U : X →ₗ[ℝ] V)) = oV.hilbertSchmidtDistortion oW A := by
  have hzero : A ∘ₗ (U : X →ₗ[ℝ] V) = 0 ↔ A = 0 := by
    simp [LinearMap.ext_iff, U.surjective.forall]
  have hF : frobenius ℝ X W (A ∘ₗ (U : X →ₗ[ℝ] V)) = frobenius ℝ V W A := by
    simp only [frobenius_apply_eq_sqrt_sum_sq_singularValues,
      LinearMap.singularValues_comp_linearIsometryEquiv]
  rw [hilbertSchmidtDistortion_def, hilbertSchmidtDistortion_def,
    oX.orientedJacobian_comp_of_right_eq_one oV oW hU, hF, hzero]

end Orientation
