/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
import TauCeti.Algebra.Module.LinearMap.Defs
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.Real.Sqrt

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
* `Orientation.hilbertSchmidtDistortion_eq_top_iff`,
  `Orientation.hilbertSchmidtDistortion_eq_zero_iff`: `q_S(A) = ∞` exactly for nonzero `A` with
  `J(A) ≤ 0`, and in positive dimension `q_S(A) = 0` exactly for `A = 0`.
* `Orientation.hilbertSchmidtDistortion_eq_ofReal_singularValues`: the singular-value formula
  `q_S(A) = (σ₁² + ⋯ + σₙ²)^{n/2} / (n^{n/2} σ₁ ⋯ σₙ)` when `J(A) > 0`.
* `Orientation.orientedJacobian_le_frobenius_div_sqrt_pow`: `J(A) ≤ (‖A‖_HS / √n)ⁿ`.
* `Orientation.one_le_hilbertSchmidtDistortion`: `q_S(A) ≥ 1` when `J(A) > 0`.
* `Orientation.hilbertSchmidtDistortion_le_outerDistortion`,
  `Orientation.outerDistortion_le_mul_hilbertSchmidtDistortion`: `q_S ≤ q_O ≤ n^{n/2} q_S`, with
  `Orientation.outerDistortion_lt_mul_hilbertSchmidtDistortion`: the upper bound is strict when
  `J(A) > 0` and `n ≥ 2`.
* `Orientation.hilbertSchmidtDistortion_eq_one_iff_outerDistortion_eq_one`: `q_S(A) = 1` iff
  `q_O(A) = 1`, the equality case of `q_S ≥ 1`; `Orientation.hilbertSchmidtDistortion_id`.
* `Orientation.hilbertSchmidtDistortion_smul`,
  `Orientation.hilbertSchmidtDistortion_linearIsometry_comp`,
  `Orientation.hilbertSchmidtDistortion_comp_linearIsometryEquiv`: the invariances of `q_S`
  under positive scaling (`cⁿ > 0`) and orientation-preserving isometries;
  `Orientation.hilbertSchmidtDistortion_neg_neg` (reversing both orientations) and
  `Orientation.hilbertSchmidtDistortion_smul_of_pow_neg` (`cⁿ < 0` makes `q_S` infinite for
  nonzero `A` with `J(A) ≥ 0`).

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

omit [FiniteDimensional ℝ W] in
/-- When `J(A) > 0`, the Hilbert–Schmidt distortion is finite. -/
theorem hilbertSchmidtDistortion_ne_top_of_pos {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) : oV.hilbertSchmidtDistortion oW A ≠ ⊤ := by
  simp [hilbertSchmidtDistortion_def, h]

omit [FiniteDimensional ℝ W] in
/-- The Hilbert–Schmidt distortion is infinite exactly for the nonzero maps with `J(A) ≤ 0`. -/
theorem hilbertSchmidtDistortion_eq_top_iff {A : V →ₗ[ℝ] W} :
    oV.hilbertSchmidtDistortion oW A = ⊤ ↔ A ≠ 0 ∧ oV.orientedJacobian oW A ≤ 0 := by
  rw [hilbertSchmidtDistortion_def]
  split_ifs with h hA
  · simp [h.not_ge]
  · simp [hA]
  · simp [hA, not_lt.mp h]

/-! ### The Frobenius norm against the operator norm and the Jacobian -/

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The oriented Jacobian is at most `(‖A‖_HS / √n)ⁿ`: the inequality of arithmetic and geometric
means for the squares of the singular values. -/
theorem orientedJacobian_le_frobenius_div_sqrt_pow (A : V →ₗ[ℝ] W) :
    oV.orientedJacobian oW A ≤ (frobenius ℝ V W A / √(n : ℝ)) ^ n := by
  refine (le_abs_self _).trans ?_
  have h := Real.prod_le_sqrt_sum_sq_div_sqrt_card_pow (Finset.range n) A.singularValues
    fun i _ ↦ A.singularValues_nonneg i
  rw [Finset.card_range] at h
  rwa [oV.abs_orientedJacobian oW A, A.normDet_eq_prod_singularValues,
    A.frobenius_apply_eq_sqrt_sum_range_sq_singularValues, (Fact.out : finrank ℝ V = n)]

/-! ### Formula and lower bound -/

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The singular-value formula: when `J(A) > 0`,
`q_S(A) = (σ₁² + ⋯ + σₙ²)^{n/2} / (n^{n/2} σ₁ ⋯ σₙ)`. -/
theorem hilbertSchmidtDistortion_eq_ofReal_singularValues {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) :
    oV.hilbertSchmidtDistortion oW A =
      ENNReal.ofReal (√(∑ i ∈ Finset.range n, A.singularValues i ^ 2) ^ n /
        (√(n : ℝ) ^ n * ∏ i ∈ Finset.range n, A.singularValues i)) := by
  rw [oV.hilbertSchmidtDistortion_of_pos oW h,
    A.frobenius_apply_eq_sqrt_sum_range_sq_singularValues,
    oV.orientedJacobian_eq_prod_singularValues_of_nonneg oW h.le, (Fact.out : finrank ℝ V = n)]

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- When `J(A) > 0`, the Hilbert–Schmidt distortion is at least `1`. -/
theorem one_le_hilbertSchmidtDistortion {A : V →ₗ[ℝ] W} (h : 0 < oV.orientedJacobian oW A) :
    1 ≤ oV.hilbertSchmidtDistortion oW A := by
  have hc := Real.sqrt_natCast_pow_self_pos n
  rw [oV.hilbertSchmidtDistortion_of_pos oW h, ENNReal.one_le_ofReal, one_le_div (mul_pos hc h)]
  calc √(n : ℝ) ^ n * oV.orientedJacobian oW A
      ≤ √(n : ℝ) ^ n * (frobenius ℝ V W A / √(n : ℝ)) ^ n := by
        gcongr
        exact oV.orientedJacobian_le_frobenius_div_sqrt_pow oW A
    _ = frobenius ℝ V W A ^ n := by rw [div_pow, mul_div_cancel₀ _ hc.ne']

/-! ### Comparison with the outer distortion -/

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The Hilbert–Schmidt distortion is at most the outer distortion: `‖A‖_HS ≤ √n ‖A‖`. -/
theorem hilbertSchmidtDistortion_le_outerDistortion (A : V →ₗ[ℝ] W) :
    oV.hilbertSchmidtDistortion oW A ≤ oV.outerDistortion oW A := by
  by_cases h : 0 < oV.orientedJacobian oW A
  · rw [oV.hilbertSchmidtDistortion_of_pos oW h, oV.outerDistortion_of_pos oW h]
    have hc := Real.sqrt_natCast_pow_self_pos n
    refine ENNReal.ofReal_le_ofReal ?_
    calc frobenius ℝ V W A ^ n / (√(n : ℝ) ^ n * oV.orientedJacobian oW A)
        ≤ (√(n : ℝ) * ‖LinearMap.toContinuousLinearMap A‖) ^ n /
            (√(n : ℝ) ^ n * oV.orientedJacobian oW A) := by
          gcongr
          simpa [(Fact.out : finrank ℝ V = n)] using
            A.frobenius_le_sqrt_finrank_mul_norm_toContinuousLinearMap
      _ = ‖LinearMap.toContinuousLinearMap A‖ ^ n / oV.orientedJacobian oW A := by
          rw [mul_pow, mul_div_mul_left _ _ hc.ne']
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

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- In positive dimension the Hilbert–Schmidt distortion vanishes exactly at the zero map. -/
theorem hilbertSchmidtDistortion_eq_zero_iff (hn : 0 < n) {A : V →ₗ[ℝ] W} :
    oV.hilbertSchmidtDistortion oW A = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ (oV.outerDistortion_eq_zero_iff oW hn).mp ?_,
    fun h ↦ h ▸ oV.hilbertSchmidtDistortion_zero oW hn⟩
  simpa [h] using oV.outerDistortion_le_mul_hilbertSchmidtDistortion oW A

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

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ X] in
/-- Postcomposing with a linear isometry of oriented Jacobian `1` (orientation-preserving) changes
no Hilbert–Schmidt distortion. -/
theorem hilbertSchmidtDistortion_linearIsometry_comp (U : W →ₗᵢ[ℝ] X)
    (hU : oW.orientedJacobian oX U.toLinearMap = 1) (A : V →ₗ[ℝ] W) :
    oV.hilbertSchmidtDistortion oX (U.toLinearMap ∘ₗ A) = oV.hilbertSchmidtDistortion oW A := by
  rw [hilbertSchmidtDistortion_def, hilbertSchmidtDistortion_def,
    oV.orientedJacobian_comp_of_left_eq_one oW oX hU, LinearMap.frobenius_linearIsometry_comp,
    LinearMap.comp_eq_zero_iff_of_injective U.injective]

omit [FiniteDimensional ℝ W] in
/-- Precomposing with an isometric isomorphism of oriented Jacobian `1` (orientation-preserving)
changes no Hilbert–Schmidt distortion. -/
theorem hilbertSchmidtDistortion_comp_linearIsometryEquiv (U : X ≃ₗᵢ[ℝ] V)
    (hU : oX.orientedJacobian oV (U : X →ₗ[ℝ] V) = 1) (A : V →ₗ[ℝ] W) :
    oX.hilbertSchmidtDistortion oW (A ∘ₗ (U : X →ₗ[ℝ] V)) = oV.hilbertSchmidtDistortion oW A := by
  rw [hilbertSchmidtDistortion_def, hilbertSchmidtDistortion_def,
    oX.orientedJacobian_comp_of_right_eq_one oV oW hU, LinearMap.frobenius_comp_linearIsometryEquiv,
    LinearMap.comp_eq_zero_iff_of_surjective (f := (U : X →ₗ[ℝ] V)) U.surjective]

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- **Equality case of `q_S ≥ 1`.** The Hilbert–Schmidt distortion is `1` exactly when the outer
distortion is `1`: by the equality case of the inequality of arithmetic and geometric means, all
the singular values agree. -/
theorem hilbertSchmidtDistortion_eq_one_iff_outerDistortion_eq_one {A : V →ₗ[ℝ] W} :
    oV.hilbertSchmidtDistortion oW A = 1 ↔ oV.outerDistortion oW A = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hJ : 0 < oV.orientedJacobian oW A := by
      by_contra hJ
      by_cases hA : A = 0
      · subst hA
        simp [hilbertSchmidtDistortion_def, hJ] at h
      · simp [oV.hilbertSchmidtDistortion_of_nonpos oW (not_lt.mp hJ) hA] at h
    have hc := Real.sqrt_natCast_pow_self_pos n
    rw [oV.hilbertSchmidtDistortion_of_pos oW hJ, ENNReal.ofReal_eq_one,
      div_eq_one_iff_eq (mul_pos hc hJ).ne'] at h
    have hJ' : oV.orientedJacobian oW A = (frobenius ℝ V W A / √(n : ℝ)) ^ n := by
      rw [div_pow, h, mul_div_cancel_left₀ _ hc.ne']
    rw [oV.orientedJacobian_eq_prod_singularValues_of_nonneg oW hJ.le,
      A.frobenius_apply_eq_sqrt_sum_range_sq_singularValues, (Fact.out : finrank ℝ V = n)] at hJ'
    rcases n.eq_zero_or_pos with rfl | hn
    · rw [oV.outerDistortion_of_pos oW hJ, oV.orientedJacobian_eq_one_of_fin_zero oW hJ]
      simp
    have hall := (Real.prod_eq_sqrt_sum_sq_div_sqrt_card_pow_iff (Finset.range n)
      A.singularValues fun i _ ↦ A.singularValues_nonneg i).mp (by rwa [Finset.card_range])
    have hP : ∏ i ∈ Finset.range n, A.singularValues i = A.singularValues 0 ^ n := by
      rw [Finset.prod_congr rfl fun i hi ↦ hall i hi 0 (Finset.mem_range.mpr hn),
        Finset.prod_const, Finset.card_range]
    have hpos : 0 < A.singularValues 0 ^ n := by
      rw [← hP, ← oV.orientedJacobian_eq_prod_singularValues_of_nonneg oW hJ.le]
      exact hJ
    rw [oV.outerDistortion_eq_ofReal_prod_singularValues oW hJ, hP, div_self hpos.ne',
      ENNReal.ofReal_one]
  · have hJ := oV.orientedJacobian_pos_of_outerDistortion_ne_zero_of_ne_top oW (A := A)
      (by simp [h]) (by simp [h])
    exact le_antisymm (h ▸ oV.hilbertSchmidtDistortion_le_outerDistortion oW A)
      (oV.one_le_hilbertSchmidtDistortion oW hJ)

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- For `J(A) > 0` in dimension `n ≥ 2` the bound `q_O(A) ≤ n^{n/2} q_S(A)` is strict: the
second singular value is positive, so `‖A‖ = σ₁ < (σ₁² + ⋯ + σₙ²)^{1/2} = ‖A‖_HS`. -/
theorem outerDistortion_lt_mul_hilbertSchmidtDistortion (hn : 2 ≤ n) {A : V →ₗ[ℝ] W}
    (h : 0 < oV.orientedJacobian oW A) :
    oV.outerDistortion oW A <
      ENNReal.ofReal (√(n : ℝ) ^ n) * oV.hilbertSchmidtDistortion oW A := by
  have hc := Real.sqrt_natCast_pow_self_pos n
  have hℓ := oV.minimalStretch_pos_of_orientedJacobian_ne_zero oW (by omega) h.ne'
  rw [A.minimalStretch_def, (Fact.out : finrank ℝ V = n)] at hℓ
  have hlt := A.norm_toContinuousLinearMap_lt_frobenius
    (hℓ.trans_le (A.singularValues_antitone (by omega)))
  rw [oV.hilbertSchmidtDistortion_of_pos oW h, oV.outerDistortion_of_pos oW h,
    ← ENNReal.ofReal_mul hc.le, ← mul_div_assoc, mul_div_mul_left _ _ hc.ne',
    ENNReal.ofReal_lt_ofReal_iff (div_pos (pow_pos ((norm_nonneg _).trans_lt hlt) n) h)]
  exact div_lt_div_of_pos_right (pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega)) h

omit [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- The identity has Hilbert–Schmidt distortion `1`. -/
@[simp]
theorem hilbertSchmidtDistortion_id :
    oV.hilbertSchmidtDistortion oV LinearMap.id = 1 :=
  (oV.hilbertSchmidtDistortion_eq_one_iff_outerDistortion_eq_one oV).mpr oV.outerDistortion_id

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- Reversing both orientations changes no Hilbert–Schmidt distortion. -/
@[simp]
theorem hilbertSchmidtDistortion_neg_neg (A : V →ₗ[ℝ] W) :
    (-oV).hilbertSchmidtDistortion (-oW) A = oV.hilbertSchmidtDistortion oW A := by
  simp [hilbertSchmidtDistortion_def]

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ X] [Fact (finrank ℝ X = n)] in
/-- Scaling a nonzero map with `J(A) ≥ 0` by `c` with `cⁿ < 0` (a negative scalar in odd
dimension) makes the Hilbert–Schmidt distortion infinite. -/
theorem hilbertSchmidtDistortion_smul_of_pow_neg {c : ℝ} (hc : c ^ n < 0) {A : V →ₗ[ℝ] W}
    (h : 0 ≤ oV.orientedJacobian oW A) (hA : A ≠ 0) :
    oV.hilbertSchmidtDistortion oW (c • A) = ⊤ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; norm_num at hc)
  have hc0 : c ≠ 0 := (pow_ne_zero_iff hn.ne').mp hc.ne
  refine oV.hilbertSchmidtDistortion_of_nonpos oW ?_ (smul_ne_zero hc0 hA)
  rw [oV.orientedJacobian_smul oW]
  exact mul_nonpos_of_nonpos_of_nonneg hc.le h

end Orientation
