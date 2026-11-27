/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Scattering
import TauCeti.Analysis.ODE.DiracSystem.RealPotential
import TauCeti.Analysis.ODE.DiracSystem.Symmetry

/-!
# The scattering functions of real and constant potentials

For a potential `q : ℝ → ℂ` and its scattering functions `a = (G_q)₂₂`, `b = (G_q)₂₁`
(`TauCeti.diracScatteringA`, `TauCeti.diracScatteringB`):

## Main results

* `TauCeti.diracScatteringA_neg_conj`, `TauCeti.diracScatteringB_neg_conj`: for a real potential,
  `a(t, -conj z) = conj a(t, z)` and `b(t, -conj z) = conj b(t, z)`;
* `TauCeti.im_diracScatteringA_I_mul`, `TauCeti.im_diracScatteringB_I_mul`: hence `a(t, iy)` and
  `b(t, iy)` are real;
* `TauCeti.diracScatteringA_zero_of_im_eq_zero`, `TauCeti.diracScatteringB_zero_of_im_eq_zero`:
  at `z = 0`, `a(t, 0) = cosh F(t)` and `b(t, 0) = sinh F(t)` with `F(t) = ∫₀ᵗ Re q`;
* `TauCeti.diracScatteringMatrix_const_zero`: for a constant potential `q = c` the scattering
  matrix at `z = 0` is `cosh(t|c|) + (sinh(t|c|) / |c|) [[0, conj c], [c, 0]]`, so
  `a(t, 0) = cosh(t|c|)` and `b(t, 0) = (c / |c|) sinh(t|c|)`
  (`TauCeti.diracScatteringA_const_zero`, `TauCeti.diracScatteringB_const_zero`).

## Implementation notes

The symmetries come from the dictionary `a = e^{itz} (E + i E~) / 2`, `b = e^{itz} (E - i E~) / 2`
with the Hermite–Biehler functions and from the reflection and parity symmetries of the
fundamental matrix (`TauCeti.diracFundamentalMatrix_conj`,
`TauCeti.diracFundamentalMatrix_neg_of_im_eq_zero`), applied to the truncation `1_{[0, t]} q`. The
constant potential is the propagator of a constant coefficient whose square is `|c|²`.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §5.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate
open scoped Matrix Interval

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- For a real potential locally integrable on `[0, ∞)` and `t ≥ 0`, the Hermite–Biehler
functions satisfy `E(t, -conj z) = conj E(t, z)` and `E~(t, -conj z) = -conj E~(t, z)`. -/
private theorem diracHermiteBiehler_neg_conj_of_locallyIntegrableOn
    (hq : LocallyIntegrableOn q (Ici 0)) (hre : ∀ s ∈ Ici 0, (q s).im = 0) (ht : 0 ≤ t)
    (z : ℂ) :
    diracHermiteBiehler q t (-conj z) = conj (diracHermiteBiehler q t z) ∧
      diracHermiteBiehlerDirichlet q t (-conj z) =
        -conj (diracHermiteBiehlerDirichlet q t z) := by
  rw [diracHermiteBiehler_def, diracHermiteBiehler_def, diracHermiteBiehlerDirichlet_def,
    diracHermiteBiehlerDirichlet_def, diracFundamentalMatrix_neg_of_im_eq_zero hq hre ht,
    diracFundamentalMatrix_conj hq ht]
  constructor
  · simp
  · simp only [map_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, map_sub, map_mul, conj_I]
    ring

/-- The truncation `1_{[0, t]} q` of a potential integrable and real on `[0, t]` is locally
integrable and real on `[0, ∞)`, and has the same scattering matrix up to time `t ≥ 0`. -/
private theorem diracScattering_indicator_props (hq : IntegrableOn q (Icc 0 t))
    (hre : ∀ s ∈ Icc 0 t, (q s).im = 0) (ht : 0 ≤ t) :
    LocallyIntegrableOn ((Icc 0 t).indicator q) (Ici 0) ∧
      (∀ s ∈ Ici 0, ((Icc 0 t).indicator q s).im = 0) ∧
      ∀ z, diracScatteringMatrix ((Icc 0 t).indicator q) t z = diracScatteringMatrix q t z := by
  refine ⟨((integrable_indicator_iff measurableSet_Icc).2 hq).locallyIntegrable.locallyIntegrableOn
    _, fun s _ ↦ ?_, fun z ↦ diracScatteringMatrix_congr_ae (ae_of_all _ fun u hu ↦
      indicator_of_mem (Ioc_subset_Icc_self (uIoc_of_le ht ▸ hu)) q) z⟩
  by_cases hs : s ∈ Icc 0 t
  · rw [indicator_of_mem hs]; exact hre s hs
  · rw [indicator_of_notMem hs]; simp

/-- **Real potentials.** If `q` is integrable and real on `[0, t]` with `t ≥ 0`, then
`a(t, -conj z) = conj a(t, z)` and `b(t, -conj z) = conj b(t, z)`. -/
private theorem diracScattering_neg_conj (hq : IntegrableOn q (Icc 0 t))
    (hre : ∀ s ∈ Icc 0 t, (q s).im = 0) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringA q t (-conj z) = conj (diracScatteringA q t z) ∧
      diracScatteringB q t (-conj z) = conj (diracScatteringB q t z) := by
  obtain ⟨hql, hrel, hG⟩ := diracScattering_indicator_props hq hre ht
  have hqt : IntegrableOn ((Icc 0 t).indicator q) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact hql.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  have hA (w : ℂ) : diracScatteringA q t w = diracScatteringA ((Icc 0 t).indicator q) t w := by
    rw [diracScatteringA_def, diracScatteringA_def, hG]
  have hB (w : ℂ) : diracScatteringB q t w = diracScatteringB ((Icc 0 t).indicator q) t w := by
    rw [diracScatteringB_def, diracScatteringB_def, hG]
  obtain ⟨hE, hE'⟩ := diracHermiteBiehler_neg_conj_of_locallyIntegrableOn hql hrel ht z
  have hexp : exp (I * (t * -conj z)) = conj (exp (I * (t * z))) := by
    rw [← exp_conj]; congr 1; simp
  rw [hA, hA, hB, hB, diracScatteringA_eq hqt, diracScatteringA_eq hqt, diracScatteringB_eq hqt,
    diracScatteringB_eq hqt, hE, hE', hexp]
  constructor <;> simp [map_ofNat]

/-- **Real potentials.** If `q` is integrable and real on `[0, t]` with `t ≥ 0`, then
`a(t, -conj z) = conj a(t, z)`. -/
theorem diracScatteringA_neg_conj (hq : IntegrableOn q (Icc 0 t))
    (hre : ∀ s ∈ Icc 0 t, (q s).im = 0) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringA q t (-conj z) = conj (diracScatteringA q t z) :=
  (diracScattering_neg_conj hq hre ht z).1

/-- **Real potentials.** If `q` is integrable and real on `[0, t]` with `t ≥ 0`, then
`b(t, -conj z) = conj b(t, z)`. -/
theorem diracScatteringB_neg_conj (hq : IntegrableOn q (Icc 0 t))
    (hre : ∀ s ∈ Icc 0 t, (q s).im = 0) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringB q t (-conj z) = conj (diracScatteringB q t z) :=
  (diracScattering_neg_conj hq hre ht z).2

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
theorem diracScatteringA_zero_of_im_eq_zero (hq : IntegrableOn q (uIcc 0 t))
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
theorem diracScatteringB_zero_of_im_eq_zero (hq : IntegrableOn q (uIcc 0 t))
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
  rcases eq_or_ne c 0 with rfl | hc
  · rw [show (fun _ : ℝ ↦ (0 : ℂ)) = 0 from rfl, diracScatteringMatrix_zero_potential]
    simp
  set T := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  have hcoeff : (fun s ↦ T (diracScatteringCoeff (fun _ ↦ c) 0 s)) =
      fun _ ↦ T !![0, conj c; c, 0] := by
    ext1 s
    simp [diracScatteringCoeff_def]
  have hsq : T !![0, conj c; c, 0] * T !![0, conj c; c, 0] = ((‖c‖ : ℝ) : ℂ) ^ 2 • 1 := by
    rw [← map_mul, ← map_one T, ← map_smul]
    congr 1
    rw [← ofReal_pow, ← normSq_eq_norm_sq, ← mul_conj]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  apply EquivLike.injective T
  rw [toEuclideanCLM_diracScatteringMatrix, hcoeff,
    propagator_const_eq_cosh_add_sinh (norm_ne_zero_iff.2 hc) hsq, sub_zero, map_add, map_smul,
    map_smul, map_one]
  simp only [RCLike.ofReal_eq_complex_ofReal]

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
  simp
  ring

end TauCeti
