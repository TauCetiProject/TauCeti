/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic

/-!
# The Hermite–Biehler functions of a Dirac system

Let `M_q(t, z) = [[A, B], [C, D]]` be the fundamental matrix of the Dirac system with potential
`q = f + ig` (`TauCeti.diracFundamentalMatrix`). Its **Hermite–Biehler functions** are

`E(t, z) = A(t, z) - i C(t, z)` and `E~(t, z) = B(t, z) - i D(t, z)`

(`TauCeti.diracHermiteBiehler`, `TauCeti.diracHermiteBiehlerDirichlet`; `E~` is the E-tilde of the
literature), built from the Neumann column `(A, C)` and the Dirichlet column `(B, D)` of `M`
(Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, §2).

* `E(0, ·) = 1` and `E~(0, ·) = -i` (`TauCeti.diracHermiteBiehler_zero`,
  `TauCeti.diracHermiteBiehlerDirichlet_zero`).
* `E(t, ·)` and `E~(t, ·)` are entire when `q` is integrable between `0` and `t`
  (`TauCeti.differentiable_diracHermiteBiehler`,
  `TauCeti.differentiable_diracHermiteBiehlerDirichlet`).
* The integral equations `E(t, z) = 1 + ∫₀ᵗ (-izE(s, z) + q(s)(A(s, z) + iC(s, z))) ds` and
  `E~(t, z) = -i + ∫₀ᵗ (-iz E~(s, z) + q(s)(B(s, z) + iD(s, z))) ds`
  (`TauCeti.diracHermiteBiehler_eq_one_add_integral`,
  `TauCeti.diracHermiteBiehlerDirichlet_eq_neg_I_add_integral`). The second factor `A + iC` is the
  reflection `E#(z) = conj E(conj z)` once `A` and `C` are known to be real entire functions.
* For the zero potential, `E(t, z) = e^{-itz}` and `E~(t, z) = -i e^{-itz}`
  (`TauCeti.diracHermiteBiehler_zero_potential`,
  `TauCeti.diracHermiteBiehlerDirichlet_zero_potential`).

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286,
  §3.1.
-/

public section

open MeasureTheory Set Matrix Complex
open scoped Matrix

namespace TauCeti

/-- The **Hermite–Biehler function** `E(t, z) = A(t, z) - i C(t, z)` of the Dirac system with
potential `q`, from the Neumann column `(A, C)` of the fundamental matrix `M_q(t, z)`. -/
noncomputable def diracHermiteBiehler (q : ℝ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  diracFundamentalMatrix q t z 0 0 - I * diracFundamentalMatrix q t z 1 0

/-- The **Dirichlet Hermite–Biehler function** `E~(t, z) = B(t, z) - i D(t, z)` of the Dirac system
with potential `q`, from the Dirichlet column `(B, D)` of the fundamental matrix `M_q(t, z)`. -/
noncomputable def diracHermiteBiehlerDirichlet (q : ℝ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  diracFundamentalMatrix q t z 0 1 - I * diracFundamentalMatrix q t z 1 1

/-- `E(t, z) = A(t, z) - i C(t, z)`, from the Neumann column of the fundamental matrix. -/
theorem diracHermiteBiehler_def (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    diracHermiteBiehler q t z =
      diracFundamentalMatrix q t z 0 0 - I * diracFundamentalMatrix q t z 1 0 :=
  (rfl)

/-- `E~(t, z) = B(t, z) - i D(t, z)`, from the Dirichlet column of the fundamental matrix. -/
theorem diracHermiteBiehlerDirichlet_def (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    diracHermiteBiehlerDirichlet q t z =
      diracFundamentalMatrix q t z 0 1 - I * diracFundamentalMatrix q t z 1 1 :=
  (rfl)

/-- At time `0`, `E = 1`. -/
@[simp]
theorem diracHermiteBiehler_zero (q : ℝ → ℂ) (z : ℂ) : diracHermiteBiehler q 0 z = 1 := by
  simp [diracHermiteBiehler_def]

/-- At time `0`, `E~ = -i`. -/
@[simp]
theorem diracHermiteBiehlerDirichlet_zero (q : ℝ → ℂ) (z : ℂ) :
    diracHermiteBiehlerDirichlet q 0 z = -I := by
  simp [diracHermiteBiehlerDirichlet_def]

variable {q : ℝ → ℂ} {t : ℝ}

/-- `E(t, ·)` is entire when `q` is integrable between `0` and `t`. -/
theorem differentiable_diracHermiteBiehler (hq : IntegrableOn q (uIcc 0 t)) :
    Differentiable ℂ (diracHermiteBiehler q t) :=
  (differentiable_diracFundamentalMatrix_apply hq 0 0).sub
    ((differentiable_diracFundamentalMatrix_apply hq 1 0).const_mul I)

/-- `E~(t, ·)` is entire when `q` is integrable between `0` and `t`. -/
theorem differentiable_diracHermiteBiehlerDirichlet (hq : IntegrableOn q (uIcc 0 t)) :
    Differentiable ℂ (diracHermiteBiehlerDirichlet q t) :=
  (differentiable_diracFundamentalMatrix_apply hq 0 1).sub
    ((differentiable_diracFundamentalMatrix_apply hq 1 1).const_mul I)

/-- The functional `x ↦ x₀ - i x₁` and the Dirac equation it satisfies: the value at
`-Ω (z - Q_q(s)) x` is `-iz (x₀ - i x₁) + q(s) (x₀ + i x₁)`. -/
private theorem hermiteBiehler_diracCoeff (z : ℂ) (s : ℝ) (x : Fin 2 → ℂ) :
    (diracCoeff q z s *ᵥ x) 0 - I * (diracCoeff q z s *ᵥ x) 1 =
      -I * z * (x 0 - I * x 1) + q s * (x 0 + I * x 1) := by
  have hq := Complex.re_add_im (q s)
  have h0 : (diracCoeff q z s *ᵥ x) 0 = (q s).re * x 0 + (-z - (q s).im) * x 1 := by
    simp [diracCoeff_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (diracCoeff q z s *ᵥ x) 1 = (z - (q s).im) * x 0 - (q s).re * x 1 := by
    simp [diracCoeff_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]
  rw [h0, h1]
  linear_combination (-(z + (q s).im) * x 1) * I_sq + (x 0 + I * x 1) * hq

/-- The integral equation of `x ↦ x₀ - i x₁` along a column of the fundamental matrix. -/
private theorem hermiteBiehler_column_eq_add_integral (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ)
    (j : Fin 2) :
    diracFundamentalMatrix q t z 0 j - I * diracFundamentalMatrix q t z 1 j =
      ((Pi.single j (1 : ℂ) : Fin 2 → ℂ) 0 - I * (Pi.single j (1 : ℂ) : Fin 2 → ℂ) 1) +
        ∫ s in (0 : ℝ)..t, (-I * z * (diracFundamentalMatrix q s z 0 j -
            I * diracFundamentalMatrix q s z 1 j) +
          q s * (diracFundamentalMatrix q s z 0 j + I * diracFundamentalMatrix q s z 1 j)) := by
  set v : Fin 2 → ℂ := Pi.single j 1
  -- The functional `x ↦ x₀ - i x₁`.
  let ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0 - I • ContinuousLinearMap.proj 1
  have hℓ (x : Fin 2 → ℂ) : ℓ x = x 0 - I * x 1 := by simp [ℓ]
  have key := congrArg ℓ
    (diracFundamentalMatrix_mulVec_eq_add_integral hq left_mem_uIcc right_mem_uIcc z v)
  rw [map_add, ← ℓ.intervalIntegral_comp_comm
    (intervalIntegrable_diracCoeff_mulVec_diracFundamentalMatrix_mulVec hq z v)] at key
  simpa only [hℓ, hermiteBiehler_diracCoeff, v, Matrix.mulVec_single_one, Matrix.col_apply]
    using key

/-- **The integral equation of `E`.** If `q` is integrable between `0` and `t`, then
`E(t, z) = 1 + ∫₀ᵗ (-iz E(s, z) + q(s) (A(s, z) + i C(s, z))) ds`. -/
theorem diracHermiteBiehler_eq_one_add_integral (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ) :
    diracHermiteBiehler q t z =
      1 + ∫ s in (0 : ℝ)..t, (-I * z * diracHermiteBiehler q s z +
        q s * (diracFundamentalMatrix q s z 0 0 + I * diracFundamentalMatrix q s z 1 0)) := by
  simpa [diracHermiteBiehler_def] using hermiteBiehler_column_eq_add_integral hq z 0

/-- **The integral equation of `E~`.** If `q` is integrable between `0` and `t`, then
`E~(t, z) = -i + ∫₀ᵗ (-iz E~(s, z) + q(s) (B(s, z) + i D(s, z))) ds`. -/
theorem diracHermiteBiehlerDirichlet_eq_neg_I_add_integral (hq : IntegrableOn q (uIcc 0 t))
    (z : ℂ) :
    diracHermiteBiehlerDirichlet q t z =
      -I + ∫ s in (0 : ℝ)..t, (-I * z * diracHermiteBiehlerDirichlet q s z +
        q s * (diracFundamentalMatrix q s z 0 1 + I * diracFundamentalMatrix q s z 1 1)) := by
  simpa [diracHermiteBiehlerDirichlet_def, sub_eq_add_neg] using
    hermiteBiehler_column_eq_add_integral hq z 1

/-- **The free case.** For the zero potential, `E(t, z) = e^{-itz}`. -/
theorem diracHermiteBiehler_zero_potential (t : ℝ) (z : ℂ) :
    diracHermiteBiehler 0 t z = exp (-I * (t * z)) := by
  rw [show -I * (t * z) = -(t * z) * I by ring, ← cos_sub_sin_I]
  simp [diracHermiteBiehler_def, diracFundamentalMatrix_zero_potential, mul_comm]

/-- **The free case.** For the zero potential, `E~(t, z) = -i e^{-itz}`. -/
theorem diracHermiteBiehlerDirichlet_zero_potential (t : ℝ) (z : ℂ) :
    diracHermiteBiehlerDirichlet 0 t z = -I * exp (-I * (t * z)) := by
  have h : diracHermiteBiehlerDirichlet 0 t z = -sin (t * z) - I * cos (t * z) := by
    simp [diracHermiteBiehlerDirichlet_def, diracFundamentalMatrix_zero_potential]
  rw [h, show -I * (t * z) = -(t * z) * I by ring, ← cos_sub_sin_I]
  linear_combination (-sin (t * z)) * I_sq

end TauCeti
