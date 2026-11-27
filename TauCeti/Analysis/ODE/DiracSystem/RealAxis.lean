/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Basic
public import TauCeti.Analysis.ODE.Propagator.SymmetricPart
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.ODE.DiracSystem.ZeroFree

/-!
# The Hermite–Biehler functions of a Dirac system on the real axis

For a real spectral parameter `x`, the Dirac coefficient `-Ω(x - Q_q(s)) = -xΩ + ΩQ_q(s)` is the
sum of the skew-adjoint matrix `-xΩ`, which does not change lengths, and the symmetric matrix
`ΩQ_q(s)` of norm `|q(s)|`. So `|⟪v, -Ω(x - Q_q(s)) v⟫| ≤ |q(s)| ‖v‖²` for the real inner product
of `ℂ²` (`TauCeti.abs_re_inner_toEuclideanCLM_diracCoeff_ofReal_le`). By the propagator bounds
from the symmetric part of the coefficient (`TauCeti.norm_propagator_apply_le_of_abs_inner_le`),
`M_q(t, x)` multiplies norms by factors between `e^{-A(t)}` and `e^{A(t)}`, where
`A(t) = |∫₀ᵗ |q||` (`TauCeti.norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply_le`,
`TauCeti.exp_neg_mul_norm_le_norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply`).

On the real axis, `|E(t, x)|` and `|E~(t, x)|` equal the norms of the two columns of `M_q(t, x)`
(`TauCeti.norm_diracHermiteBiehler_ofReal`, `TauCeti.norm_diracHermiteBiehlerDirichlet_ofReal`).
Thus whenever `q` is integrable between `0` and `t`,

`e^{-A(t)} ≤ |E(t, x)|, |E~(t, x)| ≤ e^{A(t)}`

(`TauCeti.norm_diracHermiteBiehler_ofReal_le`,
`TauCeti.exp_neg_le_norm_diracHermiteBiehler_ofReal`,
`TauCeti.norm_diracHermiteBiehlerDirichlet_ofReal_le`,
`TauCeti.exp_neg_le_norm_diracHermiteBiehlerDirichlet_ofReal`). In particular `E(t, ·)` and
`E~(t, ·)` have no zeros on `ℝ`. Between any two times `s, t` in an interval containing `0`
on which `q` is integrable, either modulus grows by at most `exp |∫ₛᵗ |q||`
(`TauCeti.norm_diracFundamentalMatrix_sub_I_mul_le_mul_exp_abs_integral`).

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open MeasureTheory Set Matrix Complex
open scoped RealInnerProductSpace

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- For a real spectral parameter `x`, the Dirac coefficient changes lengths at rate at most
`|q(s)|`: `|Re ⟪v, -Ω(x - Q_q(s)) v⟫| ≤ |q(s)| ‖v‖²` in `ℂ²`. -/
theorem abs_re_inner_toEuclideanCLM_diracCoeff_ofReal_le (q : ℝ → ℂ) (x s : ℝ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    |(inner ℂ v (toEuclideanCLM (𝕜 := ℂ) (diracCoeff q x s) v)).re| ≤ ‖q s‖ * ‖v‖ ^ 2 := by
  have hskew : (inner ℂ v (toEuclideanCLM (𝕜 := ℂ) ((x : ℂ) • !![(0 : ℂ), -1; 1, 0]) v)).re =
      0 := by
    rw [map_smul, smul_apply, inner_smul_right, re_ofReal_mul]
    refine mul_eq_zero_of_right _ ?_
    simp [PiLp.inner_apply, Fin.sum_univ_two, mulVec, dotProduct, mul_comm]
  rw [diracCoeff_eq_smul_add, map_add, add_apply, inner_add_right, Complex.add_re, hskew,
    zero_add]
  refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
  rw [norm_toEuclideanCLM_diracCoeff_zero_apply]
  exact le_of_eq (by ring)

/-- For real frequency, both norm bounds on `M_q(t, x) v` follow from the symmetric-part
propagator estimates with `m(s) = |q(s)|`. -/
private theorem diracFundamentalMatrix_ofReal_apply_bounds (hq : IntegrableOn q (uIcc 0 t))
    (x : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    Real.exp (-|∫ s in (0 : ℝ)..t, ‖q s‖|) * ‖v‖ ≤
        ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ ∧
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ ≤
        Real.exp |∫ s in (0 : ℝ)..t, ‖q s‖| * ‖v‖ := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) := InnerProductSpace.complexToReal
  have hP := integrableOn_toEuclideanCLM_diracCoeff hq x
  rw [toEuclideanCLM_diracFundamentalMatrix]
  refine ⟨exp_neg_mul_norm_le_norm_propagator_apply_of_abs_inner_le hP hq.norm ?_ v,
    norm_propagator_apply_le_of_abs_inner_le hP hq.norm ?_ v⟩ <;>
  exact .of_forall fun s w ↦ (real_inner_eq_re_inner ℂ w _).symm ▸
    abs_re_inner_toEuclideanCLM_diracCoeff_ofReal_le q x s w

/-- For a real spectral parameter `x`, the fundamental matrix increases vector norms by at most
`exp |∫₀ᵗ |q||` whenever `q` is integrable between `0` and `t`. -/
theorem norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply_le
    (hq : IntegrableOn q (uIcc 0 t)) (x : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ ≤
      Real.exp |∫ s in (0 : ℝ)..t, ‖q s‖| * ‖v‖ :=
  (diracFundamentalMatrix_ofReal_apply_bounds hq x v).2

/-- For a real spectral parameter `x`, the norm of `M_q(t, x) v` is at least
`exp (-|∫₀ᵗ |q||) ‖v‖` whenever `q` is integrable between `0` and `t`. -/
theorem exp_neg_mul_norm_le_norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply
    (hq : IntegrableOn q (uIcc 0 t)) (x : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    Real.exp (-|∫ s in (0 : ℝ)..t, ‖q s‖|) * ‖v‖ ≤
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ :=
  (diracFundamentalMatrix_ofReal_apply_bounds hq x v).1

/-- On the real axis, `|M₀ⱼ - i M₁ⱼ|` is the Euclidean norm of the column `M_q(t, x) e_j`.
The diagonal Christoffel–Darboux identity gives equal moduli for `M₀ⱼ ± i M₁ⱼ`,
so the parallelogram law gives the column norm. -/
private theorem norm_diracFundamentalMatrix_ofReal_sub_I_mul (hq : IntegrableOn q (uIcc 0 t))
    (x : ℝ) (j : Fin 2) :
    ‖diracFundamentalMatrix q t x 0 j - I * diracFundamentalMatrix q t x 1 j‖ =
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single j 1)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toEuclideanCLM_single_sq, Fin.sum_univ_two]
  have h := norm_sub_I_mul_sq_sub_norm_add_I_mul_sq_diracFundamentalMatrix hq x j
  simp only [ofReal_im, mul_zero, zero_mul, sub_eq_zero] at h
  have hp := parallelogram_law_with_norm ℂ (diracFundamentalMatrix q t x 0 j)
    (I * diracFundamentalMatrix q t x 1 j)
  rw [norm_mul, norm_I, one_mul, ← h] at hp
  linarith

/-- On the real axis either Hermite–Biehler column combination grows by a factor of at most
`exp |∫ₛᵗ |q||` between two times in a closed interval containing `0` on which `q` is integrable.
The times may be taken in either order. -/
theorem norm_diracFundamentalMatrix_sub_I_mul_le_mul_exp_abs_integral
    {a b s : ℝ} (hq : IntegrableOn q (Icc a b)) (h0 : 0 ∈ Icc a b) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : ℝ) (j : Fin 2) :
    ‖diracFundamentalMatrix q t x 0 j - I * diracFundamentalMatrix q t x 1 j‖ ≤
      ‖diracFundamentalMatrix q s x 0 j - I * diracFundamentalMatrix q s x 1 j‖ *
        Real.exp |∫ r in s..t, ‖q r‖| := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) := InnerProductSpace.complexToReal
  rw [norm_diracFundamentalMatrix_ofReal_sub_I_mul (hq.mono_set (uIcc_subset_Icc h0 ht)),
    norm_diracFundamentalMatrix_ofReal_sub_I_mul (hq.mono_set (uIcc_subset_Icc h0 hs)),
    toEuclideanCLM_diracFundamentalMatrix, toEuclideanCLM_diracFundamentalMatrix, mul_comm]
  have hP := integrableOn_toEuclideanCLM_diracCoeff hq x
  have hst := uIcc_subset_Icc hs ht
  rw [← propagator_comp_propagator hP hs h0 ht, ContinuousLinearMap.comp_apply]
  exact norm_propagator_apply_le_of_abs_inner_le (hP.mono_set hst) (hq.mono_set hst).norm
    (.of_forall fun r w ↦ (real_inner_eq_re_inner ℂ w _).symm ▸
      abs_re_inner_toEuclideanCLM_diracCoeff_ofReal_le q x r w) _

/-- On the real axis, `|E(t, x)|` is the Euclidean norm of the first column of `M_q(t, x)`,
when `q` is integrable between `0` and `t`. -/
theorem norm_diracHermiteBiehler_ofReal (hq : IntegrableOn q (uIcc 0 t)) (x : ℝ) :
    ‖diracHermiteBiehler q t x‖ =
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single 0 1)‖ := by
  rw [diracHermiteBiehler_def]
  exact norm_diracFundamentalMatrix_ofReal_sub_I_mul hq x 0

/-- On the real axis, `|E~(t, x)|` is the Euclidean norm of the second column of `M_q(t, x)`,
when `q` is integrable between `0` and `t`. -/
theorem norm_diracHermiteBiehlerDirichlet_ofReal (hq : IntegrableOn q (uIcc 0 t)) (x : ℝ) :
    ‖diracHermiteBiehlerDirichlet q t x‖ =
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single 1 1)‖ := by
  rw [diracHermiteBiehlerDirichlet_def]
  exact norm_diracFundamentalMatrix_ofReal_sub_I_mul hq x 1

/-- **Upper bound for `E` on `ℝ`.** If `q` is integrable between `0` and `t`, then
`|E(t, x)| ≤ exp |∫₀ᵗ |q||`. -/
theorem norm_diracHermiteBiehler_ofReal_le (hq : IntegrableOn q (uIcc 0 t)) (x : ℝ) :
    ‖diracHermiteBiehler q t x‖ ≤ Real.exp |∫ s in (0 : ℝ)..t, ‖q s‖| := by
  rw [norm_diracHermiteBiehler_ofReal hq]
  simpa using norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply_le hq x
    (EuclideanSpace.single 0 1)

/-- **Lower bound for `E` on `ℝ`.** If `q` is integrable between `0` and `t`, then
`exp (-|∫₀ᵗ |q||) ≤ |E(t, x)|`. -/
theorem exp_neg_le_norm_diracHermiteBiehler_ofReal (hq : IntegrableOn q (uIcc 0 t)) (x : ℝ) :
    Real.exp (-|∫ s in (0 : ℝ)..t, ‖q s‖|) ≤ ‖diracHermiteBiehler q t x‖ := by
  rw [norm_diracHermiteBiehler_ofReal hq]
  simpa using exp_neg_mul_norm_le_norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply hq x
    (EuclideanSpace.single 0 1)

/-- **Upper bound for `E~` on `ℝ`.** If `q` is integrable between `0` and `t`, then
`|E~(t, x)| ≤ exp |∫₀ᵗ |q||`. -/
theorem norm_diracHermiteBiehlerDirichlet_ofReal_le (hq : IntegrableOn q (uIcc 0 t)) (x : ℝ) :
    ‖diracHermiteBiehlerDirichlet q t x‖ ≤ Real.exp |∫ s in (0 : ℝ)..t, ‖q s‖| := by
  rw [norm_diracHermiteBiehlerDirichlet_ofReal hq]
  simpa using norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply_le hq x
    (EuclideanSpace.single 1 1)

/-- **Lower bound for `E~` on `ℝ`.** If `q` is integrable between `0` and `t`, then
`exp (-|∫₀ᵗ |q||) ≤ |E~(t, x)|`. -/
theorem exp_neg_le_norm_diracHermiteBiehlerDirichlet_ofReal
    (hq : IntegrableOn q (uIcc 0 t)) (x : ℝ) :
    Real.exp (-|∫ s in (0 : ℝ)..t, ‖q s‖|) ≤ ‖diracHermiteBiehlerDirichlet q t x‖ := by
  rw [norm_diracHermiteBiehlerDirichlet_ofReal hq]
  simpa using exp_neg_mul_norm_le_norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply hq x
    (EuclideanSpace.single 1 1)

end TauCeti
