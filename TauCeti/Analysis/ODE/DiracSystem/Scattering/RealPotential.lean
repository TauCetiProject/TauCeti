/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Scattering
import TauCeti.Analysis.ODE.DiracSystem.RealPotential
import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Reflection
import TauCeti.Analysis.ODE.DiracSystem.Norm
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The scattering functions of real and constant potentials

For a potential `q : ℝ → ℂ` and its scattering functions `a = (G_q)₂₂`, `b = (G_q)₂₁`
(`TauCeti.diracScatteringA`, `TauCeti.diracScatteringB`):

## Main results

* `TauCeti.diracScatteringA_conj_potential`, `TauCeti.diracScatteringB_conj_potential`: for any
  potential `q`, `a_{conj q}(t, -conj z) = conj a_q(t, z)` and
  `b_{conj q}(t, -conj z) = conj b_q(t, z)`;
* `TauCeti.diracScatteringA_neg_conj`, `TauCeti.diracScatteringB_neg_conj`: hence, for a real
  potential, `a(t, -conj z) = conj a(t, z)` and `b(t, -conj z) = conj b(t, z)`;
* `TauCeti.im_diracScatteringA_I_mul`, `TauCeti.im_diracScatteringB_I_mul`: hence `a(t, iy)` and
  `b(t, iy)` are real;
* `TauCeti.diracScatteringA_spectralParam_zero_of_im_eq_zero`,
  `TauCeti.diracScatteringB_spectralParam_zero_of_im_eq_zero`: at `z = 0`, for a real potential,
  `a(t, 0) = cosh F(t)` and `b(t, 0) = sinh F(t)` with `F(t) = ∫₀ᵗ Re q`;
* `TauCeti.diracScatteringMatrix_const_zero`: for a constant potential `q = c` the scattering
  matrix at `z = 0` is `cosh(t|c|) + (sinh(t|c|) / |c|) [[0, conj c], [c, 0]]`, so
  `a(t, 0) = cosh(t|c|)` and `b(t, 0) = (c / |c|) sinh(t|c|)`
  (`TauCeti.diracScatteringA_const_zero`, `TauCeti.diracScatteringB_const_zero`).

## Implementation notes

The conjugate-potential symmetries come from the dictionary `a = e^{itz} (E + i E~) / 2`,
`b = e^{itz} (E - i E~) / 2` with the Hermite–Biehler functions and from their conjugate-potential
symmetries (`TauCeti.diracHermiteBiehler_neg_conj_of_eqOn_conj`,
`TauCeti.diracHermiteBiehlerDirichlet_neg_conj_of_eqOn_conj`), applied to the truncation
`1_{[0, t]} q` (`TauCeti.diracScatteringMatrix_indicator`). The constant potential is read off
from the fundamental matrix `TauCeti.diracFundamentalMatrix_const_zero` through
`TauCeti.diracScatteringMatrix_eq_mul_diracFundamentalMatrix_mul`.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §5.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate
open scoped Matrix Interval

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- The conjugate-potential symmetries of `a` and `b`, proved together. -/
private theorem diracScattering_conj_potential (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) :
    diracScatteringA (fun s ↦ conj (q s)) t (-conj z) = conj (diracScatteringA q t z) ∧
      diracScatteringB (fun s ↦ conj (q s)) t (-conj z) = conj (diracScatteringB q t z) := by
  set q₀ := (Icc 0 t).indicator q
  have hq₀ : LocallyIntegrableOn q₀ (Ici 0) :=
    ((integrable_indicator_iff measurableSet_Icc).2 hq).locallyIntegrable.locallyIntegrableOn _
  have hq₀t : IntegrableOn q₀ (uIcc 0 t) := hq₀.integrableOn_uIcc_of_Ici ht
  have hc : (Icc 0 t).indicator (fun s ↦ conj (q s)) = fun s ↦ conj (q₀ s) :=
    indicator_comp_of_zero (f := q) (map_zero (starRingEnd ℂ))
  have hqc : IntegrableOn (fun s ↦ conj (q₀ s)) (uIcc 0 t) :=
    conjCLE.toContinuousLinearMap.integrable_comp hq₀t
  have hA (p : ℝ → ℂ) (w : ℂ) :
      diracScatteringA p t w = diracScatteringA ((Icc 0 t).indicator p) t w := by
    rw [diracScatteringA_def, diracScatteringA_def, diracScatteringMatrix_indicator ht]
  have hB (p : ℝ → ℂ) (w : ℂ) :
      diracScatteringB p t w = diracScatteringB ((Icc 0 t).indicator p) t w := by
    rw [diracScatteringB_def, diracScatteringB_def, diracScatteringMatrix_indicator ht]
  have hAq : diracScatteringA q t z = diracScatteringA q₀ t z := hA q z
  have hBq : diracScatteringB q t z = diracScatteringB q₀ t z := hB q z
  have hexp : exp (I * (t * -conj z)) = conj (exp (I * (t * z))) := by
    rw [← exp_conj]; congr 1; simp
  rw [hA _ (-conj z), hB _ (-conj z), hAq, hBq, hc, diracScatteringA_eq hqc,
    diracScatteringA_eq hq₀t, diracScatteringB_eq hqc, diracScatteringB_eq hq₀t,
    diracHermiteBiehler_neg_conj_of_eqOn_conj hq₀ (fun _ _ ↦ rfl) ht,
    diracHermiteBiehlerDirichlet_neg_conj_of_eqOn_conj hq₀ (fun _ _ ↦ rfl) ht, hexp]
  constructor <;> simp [map_ofNat]

/-- **The conjugate potential.** If `q` is integrable on `[0, t]` with `t ≥ 0`, then
`a_{conj q}(t, -conj z) = conj a_q(t, z)`. -/
theorem diracScatteringA_conj_potential (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringA (fun s ↦ conj (q s)) t (-conj z) = conj (diracScatteringA q t z) :=
  (diracScattering_conj_potential hq ht z).1

/-- **The conjugate potential.** If `q` is integrable on `[0, t]` with `t ≥ 0`, then
`b_{conj q}(t, -conj z) = conj b_q(t, z)`. -/
theorem diracScatteringB_conj_potential (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringB (fun s ↦ conj (q s)) t (-conj z) = conj (diracScatteringB q t z) :=
  (diracScattering_conj_potential hq ht z).2

/-- A potential real on `[0, t]`, `t ≥ 0`, has the scattering matrix of its conjugate. -/
private theorem diracScatteringMatrix_conj_of_im_eq_zero (hre : ∀ s ∈ Icc 0 t, (q s).im = 0)
    (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringMatrix (fun s ↦ conj (q s)) t z = diracScatteringMatrix q t z :=
  diracScatteringMatrix_congr_ae (ae_of_all _ fun u hu ↦
    conj_eq_iff_im.2 (hre u (Ioc_subset_Icc_self (uIoc_of_le ht ▸ hu)))) z

/-- **Real potentials.** If `q` is integrable and real on `[0, t]` with `t ≥ 0`, then
`a(t, -conj z) = conj a(t, z)`. -/
theorem diracScatteringA_neg_conj (hq : IntegrableOn q (Icc 0 t))
    (hre : ∀ s ∈ Icc 0 t, (q s).im = 0) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringA q t (-conj z) = conj (diracScatteringA q t z) := by
  rw [diracScatteringA_def, ← diracScatteringMatrix_conj_of_im_eq_zero hre ht,
    ← diracScatteringA_def, diracScatteringA_conj_potential hq ht]

/-- **Real potentials.** If `q` is integrable and real on `[0, t]` with `t ≥ 0`, then
`b(t, -conj z) = conj b(t, z)`. -/
theorem diracScatteringB_neg_conj (hq : IntegrableOn q (Icc 0 t))
    (hre : ∀ s ∈ Icc 0 t, (q s).im = 0) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringB q t (-conj z) = conj (diracScatteringB q t z) := by
  rw [diracScatteringB_def, ← diracScatteringMatrix_conj_of_im_eq_zero hre ht,
    ← diracScatteringB_def, diracScatteringB_conj_potential hq ht]

/-- **Real potentials on the imaginary axis.** If `q` is integrable and real on `[0, t]` with
`t ≥ 0`, then `a(t, iy)` is real. -/
theorem im_diracScatteringA_I_mul (hq : IntegrableOn q (Icc 0 t))
    (hre : ∀ s ∈ Icc 0 t, (q s).im = 0) (ht : 0 ≤ t) (y : ℝ) :
    (diracScatteringA q t (I * y)).im = 0 := by
  have h := diracScatteringA_neg_conj hq hre ht (I * y)
  rw [map_mul, conj_I, conj_ofReal, neg_mul, neg_neg] at h
  exact conj_eq_iff_im.1 h.symm

/-- **Real potentials on the imaginary axis.** If `q` is integrable and real on `[0, t]` with
`t ≥ 0`, then `b(t, iy)` is real. -/
theorem im_diracScatteringB_I_mul (hq : IntegrableOn q (Icc 0 t))
    (hre : ∀ s ∈ Icc 0 t, (q s).im = 0) (ht : 0 ≤ t) (y : ℝ) :
    (diracScatteringB q t (I * y)).im = 0 := by
  have h := diracScatteringB_neg_conj hq hre ht (I * y)
  rw [map_mul, conj_I, conj_ofReal, neg_mul, neg_neg] at h
  exact conj_eq_iff_im.1 h.symm

/-- **Real potentials at `z = 0`.** If `q` is integrable and real between `0` and `t`, then
`a(t, 0) = cosh F(t)` with `F(t) = ∫₀ᵗ Re q`. -/
theorem diracScatteringA_spectralParam_zero_of_im_eq_zero (hq : IntegrableOn q (uIcc 0 t))
    (hre : ∀ s ∈ uIcc 0 t, (q s).im = 0) :
    diracScatteringA q t 0 = Real.cosh (∫ s in (0 : ℝ)..t, (q s).re) := by
  rw [diracScatteringA_eq hq, diracHermiteBiehler_def, diracHermiteBiehlerDirichlet_def,
    diracFundamentalMatrix_spectralParam_zero_of_im_eq_zero hq hre, Real.cosh_eq]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    mul_zero, exp_zero, one_mul, sub_zero, zero_sub]
  generalize (∫ s in (0 : ℝ)..t, (q s).re) = F
  push_cast
  linear_combination -exp (-(F : ℂ)) * I_sq / 2

/-- **Real potentials at `z = 0`.** If `q` is integrable and real between `0` and `t`, then
`b(t, 0) = sinh F(t)` with `F(t) = ∫₀ᵗ Re q`. -/
theorem diracScatteringB_spectralParam_zero_of_im_eq_zero (hq : IntegrableOn q (uIcc 0 t))
    (hre : ∀ s ∈ uIcc 0 t, (q s).im = 0) :
    diracScatteringB q t 0 = Real.sinh (∫ s in (0 : ℝ)..t, (q s).re) := by
  rw [diracScatteringB_eq hq, diracHermiteBiehler_def, diracHermiteBiehlerDirichlet_def,
    diracFundamentalMatrix_spectralParam_zero_of_im_eq_zero hq hre, Real.sinh_eq]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    mul_zero, exp_zero, one_mul, sub_zero, zero_sub]
  generalize (∫ s in (0 : ℝ)..t, (q s).re) = F
  push_cast
  linear_combination exp (-(F : ℂ)) * I_sq / 2

/-- **Constant potentials at `z = 0`.** For the constant potential `q = c`, the scattering matrix
at `z = 0` is `G(t, 0) = cosh(t|c|) + (sinh(t|c|) / |c|) [[0, conj c], [c, 0]]`. -/
theorem diracScatteringMatrix_const_zero (c : ℂ) (t : ℝ) :
    diracScatteringMatrix (fun _ ↦ c) t 0 =
      (Real.cosh (t * ‖c‖) : ℂ) • 1 + (Real.sinh (t * ‖c‖) / ‖c‖ : ℂ) • !![0, conj c; c, 0] := by
  rw [diracScatteringMatrix_eq_mul_diracFundamentalMatrix_mul continuousOn_const.integrableOn_uIcc,
    diracFundamentalMatrix_const_zero c t, ofReal_div]
  generalize (Real.cosh (t * ‖c‖) : ℂ) = C
  generalize (Real.sinh (t * ‖c‖) : ℂ) / ‖c‖ = S
  have hc : (c.re : ℂ) + c.im * I = c := re_add_im c
  have hcc : (c.re : ℂ) - c.im * I = conj c := by apply Complex.ext <;> simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_zero, exp_zero, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
      head_cons, one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, Matrix.symm_of, zero_add,
      Matrix.empty_mul, coe_rowEquiv, row_of, smul_of, smul_cons, smul_eq_mul, mul_neg,
      Matrix.smul_empty, one_div, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, of_apply,
      cons_val', vecMul, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_ite,
      mul_one, cons_val_fin_one, Fin.sum_univ_two, cons_val_zero, one_mul, cons_val_one, neg_mul,
      ↓reduceIte, one_ne_zero, zero_ne_one, neg_neg]
  · linear_combination (S * c.re - C) / 2 * I_sq
  · linear_combination (C - S * c.re) / 2 * I_sq + S * hcc
  · linear_combination (C - S * c.re) / 2 * I_sq + S * hc
  · linear_combination (S * c.re - C) / 2 * I_sq

/-- **Constant potentials at `z = 0`.** For the constant potential `q = c`, `a(t, 0) = cosh(t|c|)`.
-/
theorem diracScatteringA_const_zero (c : ℂ) (t : ℝ) :
    diracScatteringA (fun _ ↦ c) t 0 = Real.cosh (t * ‖c‖) := by
  rw [diracScatteringA_def, diracScatteringMatrix_const_zero]
  simp

/-- **Constant potentials at `z = 0`.** For the constant potential `q = c`,
`b(t, 0) = (c / |c|) sinh(t|c|)`. -/
theorem diracScatteringB_const_zero (c : ℂ) (t : ℝ) :
    diracScatteringB (fun _ ↦ c) t 0 = c / ‖c‖ * Real.sinh (t * ‖c‖) := by
  rw [diracScatteringB_def, diracScatteringMatrix_const_zero]
  simp [div_mul_comm]

end TauCeti
