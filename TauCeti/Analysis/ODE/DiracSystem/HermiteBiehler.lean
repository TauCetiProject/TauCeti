/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Hermite–Biehler functions of a Dirac system

Let `M_q(t, z) = [[A, B], [C, D]]` be the fundamental matrix of the Dirac system with potential
`q = f + ig` (`TauCeti.diracFundamentalMatrix`). Its **Hermite–Biehler functions** are

`E(t, z) = A(t, z) - i C(t, z)` and `Ẽ(t, z) = B(t, z) - i D(t, z)`

(`TauCeti.diracHermiteBiehler`, `TauCeti.diracHermiteBiehlerDirichlet`), built from the Neumann
column `(A, C)` and the Dirichlet column `(B, D)` of `M` (Poltoratski, *Pointwise convergence of
the non-linear Fourier transform*, §2).

* `E(0, ·) = 1` and `Ẽ(0, ·) = -i` (`TauCeti.diracHermiteBiehler_zero`,
  `TauCeti.diracHermiteBiehlerDirichlet_zero`).
* `E(t, ·)` and `Ẽ(t, ·)` are entire when `q` is integrable between `0` and `t`
  (`TauCeti.differentiable_diracHermiteBiehler`,
  `TauCeti.differentiable_diracHermiteBiehlerDirichlet`).
* The integral equations `E(t, z) = 1 + ∫₀ᵗ (-izE(s, z) + q(s)(A(s, z) + iC(s, z))) ds` and
  `Ẽ(t, z) = -i + ∫₀ᵗ (-izẼ(s, z) + q(s)(B(s, z) + iD(s, z))) ds`
  (`TauCeti.diracHermiteBiehler_eq_one_add_integral`,
  `TauCeti.diracHermiteBiehlerDirichlet_eq_neg_I_add_integral`). The second factor `A + iC` is the
  reflection `E#(z) = conj E(conj z)` once `A` and `C` are known to be real entire functions.
* For the zero potential, `E(t, z) = e^{-itz}` and `Ẽ(t, z) = -i e^{-itz}`
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

/-- The **Dirichlet Hermite–Biehler function** `Ẽ(t, z) = B(t, z) - i D(t, z)` of the Dirac system
with potential `q`, from the Dirichlet column `(B, D)` of the fundamental matrix `M_q(t, z)`. -/
noncomputable def diracHermiteBiehlerDirichlet (q : ℝ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  diracFundamentalMatrix q t z 0 1 - I * diracFundamentalMatrix q t z 1 1

/-- At time `0`, `E = 1`. -/
@[simp]
theorem diracHermiteBiehler_zero (q : ℝ → ℂ) (z : ℂ) : diracHermiteBiehler q 0 z = 1 := by
  simp [diracHermiteBiehler]

/-- At time `0`, `Ẽ = -i`. -/
@[simp]
theorem diracHermiteBiehlerDirichlet_zero (q : ℝ → ℂ) (z : ℂ) :
    diracHermiteBiehlerDirichlet q 0 z = -I := by
  simp [diracHermiteBiehlerDirichlet]

variable {q : ℝ → ℂ} {t : ℝ}

/-- `E(t, ·)` is entire when `q` is integrable between `0` and `t`. -/
theorem differentiable_diracHermiteBiehler (hq : IntegrableOn q (uIcc 0 t)) :
    Differentiable ℂ (diracHermiteBiehler q t) :=
  (differentiable_diracFundamentalMatrix_apply hq 0 0).sub
    ((differentiable_diracFundamentalMatrix_apply hq 1 0).const_mul I)

/-- `Ẽ(t, ·)` is entire when `q` is integrable between `0` and `t`. -/
theorem differentiable_diracHermiteBiehlerDirichlet (hq : IntegrableOn q (uIcc 0 t)) :
    Differentiable ℂ (diracHermiteBiehlerDirichlet q t) :=
  (differentiable_diracFundamentalMatrix_apply hq 0 1).sub
    ((differentiable_diracFundamentalMatrix_apply hq 1 1).const_mul I)

/-- The column `j` of the fundamental matrix, as the propagator applied to a basis vector. -/
private theorem diracFundamentalMatrix_apply_eq_propagator (q : ℝ → ℂ) (s : ℝ) (z : ℂ)
    (i j : Fin 2) :
    diracFundamentalMatrix q s z i j =
      propagator (fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z r)) s 0
        (EuclideanSpace.single j 1) i := by
  rw [← toEuclideanCLM_diracFundamentalMatrix]
  rw [ofLp_toEuclideanCLM]
  simp [Matrix.mulVec_single]

/-- The functional `x ↦ x₀ - i x₁` on the columns of the fundamental matrix, and the Dirac
equation it satisfies: for a column `x` of `M_q(s, z)`, the value at `-Ω (z - Q_q(s)) x` is
`-iz (x₀ - i x₁) + q(s) (x₀ + i x₁)`. -/
private theorem hermiteBiehler_diracCoeff (z : ℂ) (s : ℝ) (x : EuclideanSpace ℂ (Fin 2)) :
    (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s) x) 0 -
        I * (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s) x) 1 =
      -I * z * (x 0 - I * x 1) + q s * (x 0 + I * x 1) := by
  rw [ofLp_toEuclideanCLM]
  conv_rhs => rw [← Complex.re_add_im (q s)]
  simp only [diracCoeff_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring_nf
  rw [I_sq]
  ring

/-- The integral equation of `x ↦ x₀ - i x₁` along a column of the fundamental matrix. -/
private theorem hermiteBiehler_column_eq_add_integral (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ)
    (j : Fin 2) :
    diracFundamentalMatrix q t z 0 j - I * diracFundamentalMatrix q t z 1 j =
      ((EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) 0 -
          I * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) 1) +
        ∫ s in (0 : ℝ)..t, (-I * z * (diracFundamentalMatrix q s z 0 j -
            I * diracFundamentalMatrix q s z 1 j) +
          q s * (diracFundamentalMatrix q s z 0 j + I * diracFundamentalMatrix q s z 1 j)) := by
  set P := fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z r)
  set e : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single j 1
  have hP : IntegrableOn P (Icc (0 ⊓ t) (0 ⊔ t)) := integrableOn_toEuclideanCLM_diracCoeff hq z
  -- The functional `x ↦ x₀ - i x₁`.
  let ℓ : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ :=
    EuclideanSpace.proj (0 : Fin 2) - I • EuclideanSpace.proj (1 : Fin 2)
  have hℓ (x : EuclideanSpace ℂ (Fin 2)) : ℓ x = x 0 - I * x 1 := rfl
  have hint : IntervalIntegrable (fun u ↦ P u (propagator P u 0 e)) volume 0 t := by
    have h := MeasureTheory.IntegrableOn.intervalIntegrable_clm_comp hP
      (continuousOn_propagator_left hP left_mem_uIcc) left_mem_uIcc right_mem_uIcc
    exact ⟨(ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin 2)) e).integrable_comp h.1,
      (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin 2)) e).integrable_comp h.2⟩
  have key := congrArg ℓ (propagator_apply_eq_add_integral hP left_mem_uIcc right_mem_uIcc e)
  rw [map_add, ← ℓ.intervalIntegral_comp_comm hint] at key
  simp only [hℓ] at key
  simp only [diracFundamentalMatrix_apply_eq_propagator q _ z _ j]
  rw [key]
  congr 1
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  exact hermiteBiehler_diracCoeff z s _

/-- **The integral equation of `E`.** If `q` is integrable between `0` and `t`, then
`E(t, z) = 1 + ∫₀ᵗ (-iz E(s, z) + q(s) (A(s, z) + i C(s, z))) ds`. -/
theorem diracHermiteBiehler_eq_one_add_integral (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ) :
    diracHermiteBiehler q t z =
      1 + ∫ s in (0 : ℝ)..t, (-I * z * diracHermiteBiehler q s z +
        q s * (diracFundamentalMatrix q s z 0 0 + I * diracFundamentalMatrix q s z 1 0)) := by
  simpa [diracHermiteBiehler] using hermiteBiehler_column_eq_add_integral hq z 0

/-- **The integral equation of `Ẽ`.** If `q` is integrable between `0` and `t`, then
`Ẽ(t, z) = -i + ∫₀ᵗ (-iz Ẽ(s, z) + q(s) (B(s, z) + i D(s, z))) ds`. -/
theorem diracHermiteBiehlerDirichlet_eq_neg_I_add_integral (hq : IntegrableOn q (uIcc 0 t))
    (z : ℂ) :
    diracHermiteBiehlerDirichlet q t z =
      -I + ∫ s in (0 : ℝ)..t, (-I * z * diracHermiteBiehlerDirichlet q s z +
        q s * (diracFundamentalMatrix q s z 0 1 + I * diracFundamentalMatrix q s z 1 1)) := by
  simpa [diracHermiteBiehlerDirichlet, sub_eq_add_neg] using
    hermiteBiehler_column_eq_add_integral hq z 1

/-- `e^{-iw} = cos w - i sin w`. -/
private theorem exp_neg_I_mul (w : ℂ) : exp (-I * w) = cos w - I * sin w := by
  rw [show -I * w = -w * I by ring, exp_mul_I, cos_neg, sin_neg]
  ring

/-- **The free case.** For the zero potential, `E(t, z) = e^{-itz}`. -/
theorem diracHermiteBiehler_zero_potential (t : ℝ) (z : ℂ) :
    diracHermiteBiehler 0 t z = exp (-I * (t * z)) := by
  rw [diracHermiteBiehler, diracFundamentalMatrix_zero_potential, exp_neg_I_mul]
  simp

/-- **The free case.** For the zero potential, `Ẽ(t, z) = -i e^{-itz}`. -/
theorem diracHermiteBiehlerDirichlet_zero_potential (t : ℝ) (z : ℂ) :
    diracHermiteBiehlerDirichlet 0 t z = -I * exp (-I * (t * z)) := by
  simp only [diracHermiteBiehlerDirichlet, diracFundamentalMatrix_zero_potential, exp_neg_I_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring_nf
  rw [I_sq]
  ring

end TauCeti
