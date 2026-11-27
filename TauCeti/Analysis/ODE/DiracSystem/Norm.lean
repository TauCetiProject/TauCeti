/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic
import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# The norm of the Dirac fundamental matrix

In the Euclidean operator norm of `EuclideanSpace ℂ (Fin 2)`, the Dirac coefficient satisfies
`‖-Ω(z - Q_q(s))‖ ≤ |z| + |q(s)|` (`TauCeti.norm_toEuclideanCLM_diracCoeff_le`), so the
fundamental matrix satisfies `‖M_q(t, z)‖ ≤ exp(t|z| + ∫₀ᵗ |q|)` for `t ≥ 0`
(`TauCeti.norm_toEuclideanCLM_diracFundamentalMatrix_le`). Hence every entry of `M_q(t, z)` is
bounded by the same exponential (`TauCeti.norm_diracFundamentalMatrix_apply_le`).

The bound is attained for a constant potential `q = c` at `z = 0`. There the coefficient is the
constant matrix `K = Ω Q_c = [[Re c, -Im c], [-Im c, -Re c]]`, with `K² = |c|²`, and
`M_c(t, 0) = cosh(t|c|) + (sinh(t|c|)/|c|) K` (`TauCeti.diracFundamentalMatrix_const_zero`, from
`TauCeti.propagator_const_eq_cosh_add_sinh`). An eigenvector of `K` for the eigenvalue `|c|` is
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

/-- **The norm bound.** If `q` is integrable on `[0, t]` and `t ≥ 0`, then in the Euclidean
operator norm `‖M_q(t, z)‖ ≤ exp(t|z| + ∫₀ᵗ |q|)`. -/
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
  rw [intervalIntegral.integral_add intervalIntegrable_const hqi]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [abs_of_nonneg (add_nonneg (by positivity) hint)]

open scoped Matrix.Norms.L2Operator in
/-- **Entries of the fundamental matrix.** If `q` is integrable on `[0, t]` and `t ≥ 0`, every
entry of `M_q(t, z)` has modulus at most `exp(t|z| + ∫₀ᵗ |q|)`. -/
theorem norm_diracFundamentalMatrix_apply_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) (i j : Fin 2) :
    ‖diracFundamentalMatrix q t z i j‖ ≤ Real.exp (t * ‖z‖ + ∫ s in (0 : ℝ)..t, ‖q s‖) :=
  ((norm_apply_le_l2_opNorm _ i j).trans_eq (cstar_norm_def _)).trans
    (norm_toEuclideanCLM_diracFundamentalMatrix_le hq ht z)

/-- **A constant potential at `z = 0`.** For a constant `c`,
`M_c(t, 0) = cosh(t|c|) + (sinh(t|c|)/|c|) Ω Q_c`, with
`Ω Q_c = [[Re c, -Im c], [-Im c, -Re c]]`; for `c = 0` both sides are `1`. -/
theorem diracFundamentalMatrix_const_zero (c : ℂ) (t : ℝ) :
    diracFundamentalMatrix (fun _ ↦ c) t 0 =
      (Real.cosh (t * ‖c‖) : ℂ) • 1 + ((Real.sinh (t * ‖c‖) / ‖c‖ : ℝ) : ℂ) •
        !![(c.re : ℂ), -(c.im : ℂ); -(c.im : ℂ), -(c.re : ℂ)] := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [← Pi.zero_def, diracFundamentalMatrix_zero_potential, ← Matrix.one_fin_two]
  have hP : (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff (fun _ ↦ c) 0 s)) =
      fun _ ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff (fun _ ↦ c) 0 0) := by
    simp only [diracCoeff_const_zero]
  have hKK : toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff (fun _ ↦ c) 0 0) *
      toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff (fun _ ↦ c) 0 0) = (‖c‖ : ℂ) ^ 2 • 1 := by
    rw [← map_mul, diracCoeff_zero_mul_self, map_smul, map_one]
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  rw [toEuclideanCLM_diracFundamentalMatrix, hP,
    propagator_const_eq_cosh_add_sinh (norm_ne_zero_iff.2 hc) hKK, diracCoeff_const_zero]
  simp only [map_add, map_smul, map_one, sub_zero]
  norm_cast

/-- An eigenvector of `Ω Q_c` for the eigenvalue `|c|`. -/
private theorem exists_mulVec_eq_norm_smul (c : ℂ) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ diracCoeff (fun _ ↦ c) 0 0 *ᵥ v = (‖c‖ : ℂ) • v := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨Pi.single 0 1, by simp, by ext i; fin_cases i <;> simp [diracCoeff_const_zero]⟩
  -- The columns of `|c| + Ω Q_c` lie in the `|c|`-eigenspace, since `(Ω Q_c)² = |c|²`; one is
  -- nonzero, since `|c| + Ω Q_c` has trace `2|c| ≠ 0`.
  have hK : diracCoeff (fun _ ↦ c) 0 0 * ((‖c‖ : ℂ) • 1 + diracCoeff (fun _ ↦ c) 0 0) =
      (‖c‖ : ℂ) • ((‖c‖ : ℂ) • 1 + diracCoeff (fun _ ↦ c) 0 0) := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, diracCoeff_zero_mul_self]
    module
  obtain ⟨j, hj⟩ : ∃ j, ((‖c‖ : ℂ) • 1 + diracCoeff (fun _ ↦ c) 0 0) *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra! h
    -- The diagonal entries of `|c| + Ω Q_c` are `|c| + Re c` and `|c| - Re c`.
    have h0 : (‖c‖ : ℂ) + c.re = 0 := by
      simpa [diracCoeff_const_zero, mulVec_single] using congrFun (h 0) 0
    have h1 : (‖c‖ : ℂ) + -c.re = 0 := by
      simpa [diracCoeff_const_zero, mulVec_single] using congrFun (h 1) 1
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
  obtain ⟨v, hv, hKv⟩ := exists_mulVec_eq_norm_smul c
  -- `v` is multiplied by `cosh(t|c|) + (sinh(t|c|)/|c|) |c| = e^{t|c|}`.
  have hMv : diracFundamentalMatrix (fun _ ↦ c) t 0 *ᵥ v = (Real.exp (t * ‖c‖) : ℂ) • v := by
    have h : Real.sinh (t * ‖c‖) / ‖c‖ * ‖c‖ = Real.sinh (t * ‖c‖) :=
      div_mul_cancel_of_imp fun h ↦ by simp [h]
    rw [diracFundamentalMatrix_const_zero, ← diracCoeff_const_zero c 0]
    simp only [add_mulVec, smul_mulVec, hKv, one_mulVec, smul_smul, ← add_smul,
      ← Complex.ofReal_mul, h, ← Complex.ofReal_add, Real.cosh_add_sinh]
  have hvn : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 2))‖ :=
    norm_pos_iff.2 fun h ↦ hv (by simpa using congrArg WithLp.ofLp h)
  have hle := (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
    (diracFundamentalMatrix (fun _ ↦ c) t 0)).le_opNorm (WithLp.toLp 2 v)
  simp only [toEuclideanCLM_toLp, hMv, WithLp.toLp_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, Real.abs_exp] at hle
  exact le_of_mul_le_mul_right hle hvn

end TauCeti
