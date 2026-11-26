/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler
public import TauCeti.Analysis.ODE.DiracSystem.Symmetry
public import TauCeti.Analysis.ODE.Propagator.Dissipative

/-!
# The Hermite–Biehler functions of a Dirac system on the real axis

For a real spectral parameter `x`, the Dirac coefficient `-Ω(x - Q_q(s)) = -xΩ + ΩQ_q(s)` is the
sum of the skew-adjoint matrix `-xΩ`, which does not change lengths, and the symmetric matrix
`ΩQ_q(s)` of norm `|q(s)|`. So `|⟪v, -Ω(x - Q_q(s)) v⟫| ≤ |q(s)| ‖v‖²` for the real inner product
of `ℂ²` (`TauCeti.abs_re_inner_diracCoeff_ofReal_le`). By the propagator bounds from the
symmetric part of the coefficient (`TauCeti.norm_propagator_apply_le_of_abs_inner_le`), `M_q(t, x)`
multiplies norms by factors between `e^{-∫₀ᵗ |q|}` and `e^{∫₀ᵗ |q|}`
(`TauCeti.norm_diracFundamentalMatrix_ofReal_apply_le`,
`TauCeti.exp_neg_mul_norm_le_norm_diracFundamentalMatrix_ofReal_apply`).

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
theorem abs_re_inner_diracCoeff_ofReal_le (q : ℝ → ℂ) (x s : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    |(inner ℂ v (toEuclideanCLM (𝕜 := ℂ) (diracCoeff q x s) v)).re| ≤ ‖q s‖ * ‖v‖ ^ 2 := by
  have hskew : (inner ℂ v (toEuclideanCLM (𝕜 := ℂ) ((x : ℂ) • !![(0 : ℂ), -1; 1, 0]) v)).re =
      0 := by
    simp only [map_smul, smul_apply, inner_smul_right, PiLp.inner_apply,
      Fin.sum_univ_two, ofLp_toEuclideanCLM, mulVec, dotProduct]
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, zero_mul,
      cons_val_one, neg_mul, one_mul, zero_add, RCLike.inner_apply, add_zero, mul_re, ofReal_re,
      add_re, neg_re, conj_re, conj_im, mul_neg, sub_neg_eq_add, neg_add_rev, ofReal_im, add_im,
      neg_im, mul_im, neg_neg, sub_zero, mul_eq_zero]
    exact Or.inr (by ring)
  rw [diracCoeff_eq_smul_add, map_add, add_apply, inner_add_right, Complex.add_re, hskew,
    zero_add]
  refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
  rw [norm_toEuclideanCLM_diracCoeff_zero_apply]
  ring_nf
  rfl

/-- For a real spectral parameter `x` and `t ≥ 0`, each column `M_q(t, x) e_j` of the fundamental
matrix has norm at most `e^{∫₀ᵗ |q|}`. -/
theorem norm_diracFundamentalMatrix_ofReal_apply_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (x : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ ≤
      Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖) * ‖v‖ := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) := InnerProductSpace.complexToReal
  have hu : uIcc 0 t = Icc 0 t := uIcc_of_le ht
  have h := norm_propagator_apply_le_of_abs_inner_le
    (P := fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q x s)) (m := fun s ↦ ‖q s‖)
    (s := 0) (t := t) (by rw [hu]; exact integrableOn_toEuclideanCLM_diracCoeff hq x)
    (by rw [hu]; exact hq.norm) (.of_forall fun _ ↦ norm_nonneg _)
    (.of_forall fun s w ↦ abs_re_inner_diracCoeff_ofReal_le q x s w) v
  rw [toEuclideanCLM_diracFundamentalMatrix]
  rwa [abs_of_nonneg (intervalIntegral.integral_nonneg ht fun _ _ ↦ norm_nonneg _)] at h

/-- For a real spectral parameter `x` and `t ≥ 0`, each vector `M_q(t, x) v` has norm at least
`e^{-∫₀ᵗ |q|} ‖v‖`. -/
theorem exp_neg_mul_norm_le_norm_diracFundamentalMatrix_ofReal_apply
    (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (x : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    Real.exp (-∫ s in (0 : ℝ)..t, ‖q s‖) * ‖v‖ ≤
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) v‖ := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) := InnerProductSpace.complexToReal
  have hu : uIcc 0 t = Icc 0 t := uIcc_of_le ht
  have h := exp_neg_mul_norm_le_norm_propagator_apply_of_abs_inner_le
    (P := fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q x s)) (m := fun s ↦ ‖q s‖)
    (s := 0) (t := t) (by rw [hu]; exact integrableOn_toEuclideanCLM_diracCoeff hq x)
    (by rw [hu]; exact hq.norm) (.of_forall fun _ ↦ norm_nonneg _)
    (.of_forall fun s w ↦ abs_re_inner_diracCoeff_ofReal_le q x s w) v
  rw [toEuclideanCLM_diracFundamentalMatrix]
  rwa [abs_of_nonneg (intervalIntegral.integral_nonneg ht fun _ _ ↦ norm_nonneg _)] at h

/-- `|a - ic|² = |a|² + |c|²` for real `a`, `c`. -/
private theorem norm_sub_I_mul_sq {a c : ℂ} (ha : a.im = 0) (hc : c.im = 0) :
    ‖a - I * c‖ ^ 2 = ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, I_re, I_im,
    ha, hc]
  ring

/-- The `j`-th column of a `2 × 2` matrix, as a vector of `ℂ²`, has squared norm
`|M₀ⱼ|² + |M₁ⱼ|²`. -/
private theorem norm_toEuclideanCLM_single_sq (M : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    ‖toEuclideanCLM (𝕜 := ℂ) M (EuclideanSpace.single j 1)‖ ^ 2 = ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp

/-- On the real axis, for `t ≥ 0`, `|E(t, x)|` is the norm of the first column `(A, C)` of
`M_q(t, x)`, since `A` and `C` are real there. -/
theorem norm_diracHermiteBiehler_ofReal (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    (x : ℝ) :
    ‖diracHermiteBiehler q t x‖ =
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single 0 1)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toEuclideanCLM_single_sq, diracHermiteBiehler_def,
    norm_sub_I_mul_sq (Complex.conj_eq_iff_im.1 (conj_diracFundamentalMatrix_ofReal hq ht x 0 0))
      (Complex.conj_eq_iff_im.1 (conj_diracFundamentalMatrix_ofReal hq ht x 1 0))]

/-- On the real axis, for `t ≥ 0`, `|E~(t, x)|` is the norm of the second column `(B, D)` of
`M_q(t, x)`, since `B` and `D` are real there. -/
theorem norm_diracHermiteBiehlerDirichlet_ofReal (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) :
    ‖diracHermiteBiehlerDirichlet q t x‖ =
      ‖toEuclideanCLM (𝕜 := ℂ) (diracFundamentalMatrix q t x) (EuclideanSpace.single 1 1)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toEuclideanCLM_single_sq, diracHermiteBiehlerDirichlet_def,
    norm_sub_I_mul_sq (Complex.conj_eq_iff_im.1 (conj_diracFundamentalMatrix_ofReal hq ht x 0 1))
      (Complex.conj_eq_iff_im.1 (conj_diracFundamentalMatrix_ofReal hq ht x 1 1))]

/-- **Upper bound for `E` on `ℝ`.** For `q` locally integrable on `[0, ∞)`, `t ≥ 0` and real `x`,
`|E(t, x)| ≤ e^{∫₀ᵗ |q|}`. -/
theorem norm_diracHermiteBiehler_ofReal_le (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    (x : ℝ) : ‖diracHermiteBiehler q t x‖ ≤ Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  have hqt : IntegrableOn q (Icc 0 t) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  rw [norm_diracHermiteBiehler_ofReal hq ht]
  simpa using norm_diracFundamentalMatrix_ofReal_apply_le hqt ht x (EuclideanSpace.single 0 1)

/-- **Lower bound for `E` on `ℝ`.** For `q` locally integrable on `[0, ∞)`, `t ≥ 0` and real `x`,
`e^{-∫₀ᵗ |q|} ≤ |E(t, x)|`; in particular `E(t, x) ≠ 0`. -/
theorem exp_neg_le_norm_diracHermiteBiehler_ofReal (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) : Real.exp (-∫ s in (0 : ℝ)..t, ‖q s‖) ≤ ‖diracHermiteBiehler q t x‖ := by
  have hqt : IntegrableOn q (Icc 0 t) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  rw [norm_diracHermiteBiehler_ofReal hq ht]
  simpa using exp_neg_mul_norm_le_norm_diracFundamentalMatrix_ofReal_apply hqt ht x
    (EuclideanSpace.single 0 1)

/-- **Upper bound for `E~` on `ℝ`.** For `q` locally integrable on `[0, ∞)`, `t ≥ 0` and real
`x`, `|E~(t, x)| ≤ e^{∫₀ᵗ |q|}`. -/
theorem norm_diracHermiteBiehlerDirichlet_ofReal_le (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) :
    ‖diracHermiteBiehlerDirichlet q t x‖ ≤ Real.exp (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  have hqt : IntegrableOn q (Icc 0 t) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  rw [norm_diracHermiteBiehlerDirichlet_ofReal hq ht]
  simpa using norm_diracFundamentalMatrix_ofReal_apply_le hqt ht x (EuclideanSpace.single 1 1)

/-- **Lower bound for `E~` on `ℝ`.** For `q` locally integrable on `[0, ∞)`, `t ≥ 0` and real
`x`, `e^{-∫₀ᵗ |q|} ≤ |E~(t, x)|`; in particular `E~(t, x) ≠ 0`. -/
theorem exp_neg_le_norm_diracHermiteBiehlerDirichlet_ofReal (hq : LocallyIntegrableOn q (Ici 0))
    (ht : 0 ≤ t) (x : ℝ) :
    Real.exp (-∫ s in (0 : ℝ)..t, ‖q s‖) ≤ ‖diracHermiteBiehlerDirichlet q t x‖ := by
  have hqt : IntegrableOn q (Icc 0 t) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  rw [norm_diracHermiteBiehlerDirichlet_ofReal hq ht]
  simpa using exp_neg_mul_norm_le_norm_diracFundamentalMatrix_ofReal_apply hqt ht x
    (EuclideanSpace.single 1 1)

end TauCeti
