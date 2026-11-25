/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The norm of the Dirac fundamental matrix

In the Euclidean operator norm of `EuclideanSpace ℂ (Fin 2)`, the Dirac coefficient satisfies
`‖-Ω(z - Q_q(s))‖ ≤ |z| + |q(s)|` (`TauCeti.norm_toEuclideanCLM_diracCoeff_le`), so the
fundamental matrix satisfies `‖M_q(t, z)‖ ≤ exp(t|z| + ∫₀ᵗ |q|)` for `t ≥ 0`
(`TauCeti.norm_toEuclideanCLM_diracFundamentalMatrix_le`).

The bound is attained for a constant potential `q = c` at `z = 0`. There the coefficient is the
constant matrix `K = Ω Q_c = [[Re c, -Im c], [-Im c, -Re c]]`, with `K² = |c|²`, and
`M_c(t, 0) = cosh(t|c|) + (sinh(t|c|)/|c|) K` for `c ≠ 0`
(`TauCeti.diracFundamentalMatrix_const_zero`). An eigenvector of `K` for the eigenvalue `|c|` is
multiplied by `e^{t|c|}`, so `‖M_c(t, 0)‖ = e^{t|c|}`
(`TauCeti.norm_toEuclideanCLM_diracFundamentalMatrix_const_zero`).

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open MeasureTheory Set Matrix

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- **The norm bound.** If `q` is integrable on `[0, t]`, then in the Euclidean operator norm
`‖M_q(t, z)‖ ≤ exp(t|z| + ∫₀ᵗ |q|)`. -/
theorem norm_toEuclideanCLM_diracFundamentalMatrix_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) :
    ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q t z)‖ ≤
      Real.exp (t * ‖z‖ + ∫ s in (0 : ℝ)..t, ‖q s‖) := by
  have hqi : IntervalIntegrable (fun s ↦ ‖q s‖) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 hq.norm
  have hP := integrableOn_toEuclideanCLM_diracCoeff hq z
  rw [toEuclideanCLM_diracFundamentalMatrix]
  refine (norm_propagator_le_of_norm_le ((intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 hP)
    (intervalIntegrable_const.add hqi) (m := fun s ↦ ‖z‖ + ‖q s‖)
    (Filter.Eventually.of_forall fun s _ ↦ norm_toEuclideanCLM_diracCoeff_le q z s)).trans_eq ?_
  have hint : 0 ≤ ∫ s in (0 : ℝ)..t, ‖q s‖ :=
    intervalIntegral.integral_nonneg ht fun _ _ ↦ norm_nonneg _
  rw [intervalIntegral.integral_add intervalIntegrable_const hqi, intervalIntegral.integral_const,
    smul_eq_mul, sub_zero, abs_of_nonneg (by positivity)]

/-- The Dirac coefficient of a constant potential `c` at `z = 0`:
`Ω Q_c = [[Re c, -Im c], [-Im c, -Re c]]`. -/
theorem diracCoeff_const_zero (c : ℂ) (s : ℝ) :
    diracCoeff (fun _ ↦ c) 0 s = !![(c.re : ℂ), -(c.im : ℂ); -(c.im : ℂ), -(c.re : ℂ)] := by
  simp [diracCoeff_def]

/-- `(Ω Q_c)² = |c|²`. -/
private theorem diracCoeff_const_zero_mul_self (c : ℂ) :
    (!![(c.re : ℂ), -(c.im : ℂ); -(c.im : ℂ), -(c.re : ℂ)] *
      !![(c.re : ℂ), -(c.im : ℂ); -(c.im : ℂ), -(c.re : ℂ)]) = ((‖c‖ ^ 2 : ℝ) : ℂ) • 1 := by
  have h : ((‖c‖ ^ 2 : ℝ) : ℂ) = (c.re : ℂ) ^ 2 + (c.im : ℂ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    push_cast
    ring
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **A constant potential at `z = 0`.** For a constant `c ≠ 0`,
`M_c(t, 0) = cosh(t|c|) + (sinh(t|c|)/|c|) Ω Q_c`, with
`Ω Q_c = [[Re c, -Im c], [-Im c, -Re c]]`. -/
theorem diracFundamentalMatrix_const_zero {c : ℂ} (hc : c ≠ 0) (t : ℝ) :
    diracFundamentalMatrix (fun _ ↦ c) t 0 =
      (Real.cosh (t * ‖c‖) : ℂ) • 1 + ((Real.sinh (t * ‖c‖) / ‖c‖ : ℝ) : ℂ) •
        !![(c.re : ℂ), -(c.im : ℂ); -(c.im : ℂ), -(c.re : ℂ)] := by
  set K : Matrix (Fin 2) (Fin 2) ℂ := !![(c.re : ℂ), -(c.im : ℂ); -(c.im : ℂ), -(c.re : ℂ)]
  set a : ℝ := ‖c‖
  have ha : a ≠ 0 := norm_ne_zero_iff.2 hc
  set L := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) K
  have hLL : L * L = ((a ^ 2 : ℝ) : ℂ) • 1 := by
    rw [← map_mul, diracCoeff_const_zero_mul_self, map_smul, map_one]
  have hP : (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff (fun _ ↦ c) 0 s)) =
      fun _ ↦ L := by
    ext1 s
    rw [diracCoeff_const_zero]
  have hX : propagator (fun _ ↦ L) t 0 =
      (Real.cosh (t * a) : ℂ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) +
        ((Real.sinh (t * a) / a : ℝ) : ℂ) • L := by
    refine propagator_eq_of_hasDerivAt (a := min 0 t) (b := max 0 t)
      (X := fun r : ℝ ↦ (Real.cosh (r * a) : ℂ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] _) +
        ((Real.sinh (r * a) / a : ℝ) : ℂ) • L) continuousOn_const.integrableOn_Icc
      ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
      (fun r _ ↦ ?_) (by simp)
    have hc' : HasDerivAt (fun r : ℝ ↦ (Real.cosh (r * a) : ℂ)) ((Real.sinh (r * a) * a : ℝ)) r :=
      (((hasDerivAt_id r).mul_const a).cosh.congr_deriv (by simp)).ofReal_comp
    have hs' : HasDerivAt (fun r : ℝ ↦ ((Real.sinh (r * a) / a : ℝ) : ℂ))
        ((Real.cosh (r * a) : ℝ)) r :=
      ((((hasDerivAt_id r).mul_const a).sinh.div_const a).congr_deriv
        (by field_simp; simp [mul_comm])).ofReal_comp
    refine ((hc'.smul_const _).add (hs'.smul_const _)).congr_deriv ?_
    simp only [← ContinuousLinearMap.mul_def, mul_add, mul_smul_comm, mul_one, hLL, smul_smul]
    rw [add_comm]
    congr 1
    rw [← Complex.ofReal_mul]
    congr 2
    field_simp
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  rw [toEuclideanCLM_diracFundamentalMatrix, hP, hX]
  simp [L]

/-- An eigenvector of `Ω Q_c` for the eigenvalue `|c|`, when `c ≠ 0`. -/
private theorem exists_mulVec_eq_norm_smul {c : ℂ} (hc : c ≠ 0) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      !![(c.re : ℂ), -(c.im : ℂ); -(c.im : ℂ), -(c.re : ℂ)] *ᵥ v = (‖c‖ : ℂ) • v := by
  set K : Matrix (Fin 2) (Fin 2) ℂ := !![(c.re : ℂ), -(c.im : ℂ); -(c.im : ℂ), -(c.re : ℂ)]
  -- The columns of `|c| + K` lie in the `|c|`-eigenspace, since `K² = |c|²`; one is nonzero,
  -- since `|c| + K` has trace `2|c| ≠ 0`.
  have hK : K * ((‖c‖ : ℂ) • 1 + K) = (‖c‖ : ℂ) • ((‖c‖ : ℂ) • 1 + K) := by
    rw [Matrix.mul_add, diracCoeff_const_zero_mul_self, Matrix.mul_smul, Matrix.mul_one,
      smul_add, smul_smul, add_comm]
    push_cast
    ring_nf
  obtain ⟨j, hj⟩ : ∃ j, ((‖c‖ : ℂ) • 1 + K) *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra! h
    have h0 := congrFun (h 0) 0
    have h1 := congrFun (h 1) 1
    simp only [Complex.coe_smul, Fin.isValue, mulVec_single, MulOpposite.op_one, col_add,
      col_smul, col_of, Pi.add_apply, Pi.smul_apply, col_apply, one_apply_eq, Complex.real_smul,
      mul_one, cons_val', cons_val_zero, cons_val_fin_one, smul_add, one_smul, Pi.zero_apply,
      cons_val_one, smul_neg, K] at h0 h1
    exact hc (norm_eq_zero.1 (by exact_mod_cast (by linear_combination (h0 + h1) / 2 :
      (‖c‖ : ℂ) = 0)))
  refine ⟨_, hj, ?_⟩
  rw [mulVec_mulVec, hK, smul_mulVec]

/-- **The norm bound is attained.** For a constant potential `c` and `t ≥ 0`, the Euclidean
operator norm of `M_c(t, 0)` is `e^{t|c|} = exp(t|0| + ∫₀ᵗ |c|)`. -/
theorem norm_toEuclideanCLM_diracFundamentalMatrix_const_zero (c : ℂ) (ht : 0 ≤ t) :
    ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix (fun _ ↦ c) t 0)‖ =
      Real.exp (t * ‖c‖) := by
  refine le_antisymm ((norm_toEuclideanCLM_diracFundamentalMatrix_le
    continuousOn_const.integrableOn_Icc ht 0).trans_eq (by simp)) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : (fun _ : ℝ ↦ (0 : ℂ)) = 0 := rfl
    simp [h0, diracFundamentalMatrix_zero_potential, ← Matrix.one_fin_two]
  obtain ⟨v, hv, hKv⟩ := exists_mulVec_eq_norm_smul hc
  have hMv : diracFundamentalMatrix (fun _ ↦ c) t 0 *ᵥ v = (Real.exp (t * ‖c‖) : ℂ) • v := by
    rw [diracFundamentalMatrix_const_zero hc, add_mulVec, smul_mulVec, smul_mulVec, hKv,
      one_mulVec, smul_smul, ← add_smul, ← Real.cosh_add_sinh]
    congr 1
    have ha : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hc
    push_cast
    field_simp
  have hvn : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 2))‖ :=
    norm_pos_iff.2 fun h ↦ hv (by simpa using congrArg WithLp.ofLp h)
  have hle := (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
    (diracFundamentalMatrix (fun _ ↦ c) t 0)).le_opNorm (WithLp.toLp 2 v)
  rw [toEuclideanCLM_toLp, hMv, WithLp.toLp_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le] at hle
  exact le_of_mul_le_mul_right hle hvn

end TauCeti
