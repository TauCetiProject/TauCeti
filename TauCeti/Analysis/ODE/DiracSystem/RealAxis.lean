/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Basic
public import TauCeti.Analysis.ODE.DiracSystem.Symmetry
public import TauCeti.Analysis.ODE.Propagator.SymmetricPart
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# The Hermite–Biehler functions of a Dirac system on the real axis

For a real spectral parameter `x`, the Dirac coefficient `-Ω(x - Q_q(s)) = -xΩ + ΩQ_q(s)` is the
sum of the skew-adjoint matrix `-xΩ`, which does not change lengths, and the symmetric matrix
`ΩQ_q(s)` of norm `|q(s)|`. So `|⟪v, -Ω(x - Q_q(s)) v⟫| ≤ |q(s)| ‖v‖²` for the real inner product
of `ℂ²` (`TauCeti.abs_re_inner_toEuclideanCLM_diracCoeff_ofReal_le`). By the propagator bounds
from the symmetric part of the coefficient (`TauCeti.norm_propagator_apply_le_of_abs_inner_le`),
`M_q(t, x)` multiplies norms by factors between `e^{-∫₀ᵗ |q|}` and `e^{∫₀ᵗ |q|}`
(`TauCeti.norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply_le`,
`TauCeti.exp_neg_mul_norm_le_norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply`).

For `t ≥ 0` the entries `A, B, C, D` of `M_q(t, x)` are real
(`TauCeti.conj_diracFundamentalMatrix_ofReal`), so `|E(t, x)|² = A² + C²` and
`|E~(t, x)|² = B² + D²` are the squared norms of the columns
(`TauCeti.norm_diracHermiteBiehler_ofReal`, `TauCeti.norm_diracHermiteBiehlerDirichlet_ofReal`).
Hence, on `ℝ`,

`e^{-∫₀ᵗ |q|} ≤ |E(t, x)|, |E~(t, x)| ≤ e^{∫₀ᵗ |q|}`

(`TauCeti.norm_diracHermiteBiehler_ofReal_le`,
`TauCeti.exp_neg_le_norm_diracHermiteBiehler_ofReal`,
`TauCeti.norm_diracHermiteBiehlerDirichlet_ofReal_le`,
`TauCeti.exp_neg_le_norm_diracHermiteBiehlerDirichlet_ofReal`). In particular `E(t, ·)` and
`E~(t, ·)` have no zeros on `ℝ`.

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

/-- For a real spectral parameter `x` and `t ≥ 0`, both bounds on `‖M_q(t, x) v‖`, from the
propagator bounds from the symmetric part of the coefficient. -/
private theorem diracFundamentalMatrix_ofReal_apply_bounds (hq : IntegrableOn q (Icc 0 t))
    (ht : 0 ≤ t) (x : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    Real.exp (-∫ s in (0 : ℝ)..t, ‖q s‖) * ‖v‖ ≤
        ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ ∧
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ ≤
        Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖) * ‖v‖ := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) := InnerProductSpace.complexToReal
  have hP := integrableOn_toEuclideanCLM_diracCoeff hq x
  have hm := hq.norm
  rw [← uIcc_of_le ht] at hP hm
  rw [toEuclideanCLM_diracFundamentalMatrix,
    ← abs_of_nonneg (intervalIntegral.integral_nonneg ht fun _ _ ↦ norm_nonneg _)]
  refine ⟨exp_neg_mul_norm_le_norm_propagator_apply_of_abs_inner_le hP hm ?_ v,
    norm_propagator_apply_le_of_abs_inner_le hP hm ?_ v⟩ <;>
  exact .of_forall fun s w ↦ (real_inner_eq_re_inner ℂ w _).symm ▸
    abs_re_inner_toEuclideanCLM_diracCoeff_ofReal_le q x s w

/-- For a real spectral parameter `x` and `t ≥ 0`, each vector `M_q(t, x) v` has norm at most
`e^{∫₀ᵗ |q|} ‖v‖`. -/
theorem norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply_le (hq : IntegrableOn q (Icc 0 t))
    (ht : 0 ≤ t) (x : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ ≤
      Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖) * ‖v‖ :=
  (diracFundamentalMatrix_ofReal_apply_bounds hq ht x v).2

/-- For a real spectral parameter `x` and `t ≥ 0`, each vector `M_q(t, x) v` has norm at least
`e^{-∫₀ᵗ |q|} ‖v‖`. -/
theorem exp_neg_mul_norm_le_norm_toEuclideanCLM_diracFundamentalMatrix_ofReal_apply
    (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (x : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    Real.exp (-∫ s in (0 : ℝ)..t, ‖q s‖) * ‖v‖ ≤
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ :=
  (diracFundamentalMatrix_ofReal_apply_bounds hq ht x v).1

/-- On the real axis, for `t ≥ 0`, `|M₀ⱼ - i M₁ⱼ|` is the norm of the column `M_q(t, x) e_j`,
since the entries of `M_q(t, x)` are real there. -/
private theorem norm_diracFundamentalMatrix_ofReal_sub_I_mul (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) (j : Fin 2) :
    ‖diracFundamentalMatrix q t x 0 j - I * diracFundamentalMatrix q t x 1 j‖ =
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single j 1)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toEuclideanCLM_single_sq, Fin.sum_univ_two,
    ← conj_eq_iff_re.1 (conj_diracFundamentalMatrix_ofReal hq ht x 0 j),
    ← conj_eq_iff_re.1 (conj_diracFundamentalMatrix_ofReal hq ht x 1 j), sub_eq_add_neg,
    mul_comm I, ← neg_mul, ← ofReal_neg]
  simp only [Complex.sq_norm, normSq_add_mul_I, normSq_ofReal]
  ring

/-- On the real axis, for `t ≥ 0`, both bounds hold for each column `M_q(t, x) e_j`. -/
private theorem diracFundamentalMatrix_ofReal_single_bounds (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) (j : Fin 2) :
    Real.exp (-∫ s in (0 : ℝ)..t, ‖q s‖) ≤
        ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single j 1)‖ ∧
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single j 1)‖ ≤
        Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  simpa using diracFundamentalMatrix_ofReal_apply_bounds
    (hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc) ht x
    (EuclideanSpace.single j 1)

/-- On the real axis, for `t ≥ 0`, `|E(t, x)|` is the norm of the first column `(A, C)` of
`M_q(t, x)`, since `A` and `C` are real there. -/
theorem norm_diracHermiteBiehler_ofReal (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    (x : ℝ) :
    ‖diracHermiteBiehler q t x‖ =
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single 0 1)‖ := by
  rw [diracHermiteBiehler_def]
  exact norm_diracFundamentalMatrix_ofReal_sub_I_mul hq ht x 0

/-- On the real axis, for `t ≥ 0`, `|E~(t, x)|` is the norm of the second column `(B, D)` of
`M_q(t, x)`, since `B` and `D` are real there. -/
theorem norm_diracHermiteBiehlerDirichlet_ofReal (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) :
    ‖diracHermiteBiehlerDirichlet q t x‖ =
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single 1 1)‖ := by
  rw [diracHermiteBiehlerDirichlet_def]
  exact norm_diracFundamentalMatrix_ofReal_sub_I_mul hq ht x 1

/-- **Upper bound for `E` on `ℝ`.** For `q` locally integrable on `[0, ∞)`, `t ≥ 0` and real `x`,
`|E(t, x)| ≤ e^{∫₀ᵗ |q|}`. -/
theorem norm_diracHermiteBiehler_ofReal_le (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    (x : ℝ) : ‖diracHermiteBiehler q t x‖ ≤ Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  rw [norm_diracHermiteBiehler_ofReal hq ht]
  exact (diracFundamentalMatrix_ofReal_single_bounds hq ht x 0).2

/-- **Lower bound for `E` on `ℝ`.** For `q` locally integrable on `[0, ∞)`, `t ≥ 0` and real `x`,
`e^{-∫₀ᵗ |q|} ≤ |E(t, x)|`; in particular `E(t, x) ≠ 0`. -/
theorem exp_neg_le_norm_diracHermiteBiehler_ofReal (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) : Real.exp (-∫ s in (0 : ℝ)..t, ‖q s‖) ≤ ‖diracHermiteBiehler q t x‖ := by
  rw [norm_diracHermiteBiehler_ofReal hq ht]
  exact (diracFundamentalMatrix_ofReal_single_bounds hq ht x 0).1

/-- **Upper bound for `E~` on `ℝ`.** For `q` locally integrable on `[0, ∞)`, `t ≥ 0` and real
`x`, `|E~(t, x)| ≤ e^{∫₀ᵗ |q|}`. -/
theorem norm_diracHermiteBiehlerDirichlet_ofReal_le (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) :
    ‖diracHermiteBiehlerDirichlet q t x‖ ≤ Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  rw [norm_diracHermiteBiehlerDirichlet_ofReal hq ht]
  exact (diracFundamentalMatrix_ofReal_single_bounds hq ht x 1).2

/-- **Lower bound for `E~` on `ℝ`.** For `q` locally integrable on `[0, ∞)`, `t ≥ 0` and real
`x`, `e^{-∫₀ᵗ |q|} ≤ |E~(t, x)|`; in particular `E~(t, x) ≠ 0`. -/
theorem exp_neg_le_norm_diracHermiteBiehlerDirichlet_ofReal (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) :
    Real.exp (-∫ s in (0 : ℝ)..t, ‖q s‖) ≤ ‖diracHermiteBiehlerDirichlet q t x‖ := by
  rw [norm_diracHermiteBiehlerDirichlet_ofReal hq ht]
  exact (diracFundamentalMatrix_ofReal_single_bounds hq ht x 1).1

end TauCeti
