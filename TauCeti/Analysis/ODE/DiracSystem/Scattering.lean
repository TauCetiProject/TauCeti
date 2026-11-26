/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.ODE.DiracSystem.Symmetry
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The scattering matrix of the Dirac system

For a potential `q : ℝ → ℂ` and a spectral parameter `z ∈ ℂ`, the scattering matrix `G_q(t, z)`
(`TauCeti.diracScatteringMatrix`) is the matrix in the standard basis of the propagator `N(t, 0)`
on `EuclideanSpace ℂ (Fin 2)` of the coefficient
`[[0, e^{-2itz} conj q(t)], [e^{2itz} q(t), 0]]` (`TauCeti.diracScatteringCoeff`). The scattering
functions are its lower entries `a = (G_q)₂₂` and `b = (G_q)₂₁` (`TauCeti.diracScatteringA`,
`TauCeti.diracScatteringB`).

## Main results

* `TauCeti.diracScatteringMatrix_eq_mul_diracFundamentalMatrix_mul`: the scattering matrix is the
  gauge transform `G_q(t, z) = D(t) V M_q(t, z) V⁻¹` of the Dirac fundamental matrix, with
  `D(t) = diag(e^{-itz}, e^{itz})` and `V = [[1, i], [1, -i]]`;
* `TauCeti.diracScatteringA_eq`, `TauCeti.diracScatteringB_eq`: hence the dictionary
  `a = e^{itz} (E + i E~) / 2` and `b = e^{itz} (E - i E~) / 2` with the Hermite–Biehler functions
  `E = A - i C` and `E~ = B - i D`, and conversely `E = e^{-itz} (a + b)` and
  `E~ = -i e^{-itz} (a - b)` (`TauCeti.diracHermiteBiehler_eq_exp_mul_diracScatteringA_add`,
  `TauCeti.diracHermiteBiehlerDirichlet_eq_neg_I_mul_exp_mul_diracScatteringA_sub`); in
  particular `a(t, ·)` and `b(t, ·)` are entire (`TauCeti.differentiable_diracScatteringA`,
  `TauCeti.differentiable_diracScatteringB`);
* `TauCeti.diracScatteringMatrix_eq_conj`: the structure `G_q = [[a#, b#], [b, a]]` with
  `h#(z) = conj h(conj z)`, from the reflection symmetry of the fundamental matrix;
* `TauCeti.det_diracScatteringMatrix`,
  `TauCeti.diracScatteringA_mul_conj_sub_diracScatteringB_mul_conj`: `det G_q = a a# - b b# = 1`,
  so that `|a(t, x)|² - |b(t, x)|² = 1` on the real axis and `G_q(t, x) ∈ SU(1, 1)`
  (`TauCeti.norm_diracScatteringA_sq_sub_norm_diracScatteringB_sq`);
* `TauCeti.diracScatteringA_eq_one_add_integral`, `TauCeti.diracScatteringB_eq_integral`: the
  Volterra form `a(t, z) = 1 + ∫₀ᵗ q(s) e^{2isz} b#(s, z) ds` and
  `b(t, z) = ∫₀ᵗ q(s) e^{2isz} a#(s, z) ds`;
* `TauCeti.diracScatteringMatrix_congr_ae`, `TauCeti.diracScatteringMatrix_eq_of_ae_eq_zero`:
  locality, `G_q(t, ·)` depends only on `q` almost everywhere on `[0, t]`, and
  `G_q(t, ·) = G_q(T, ·)` when `q = 0` on `(T, t]`;
* `TauCeti.diracScatteringMatrix_zero_potential`: in the free case `G = 1`, `a = 1` and `b = 0`.

## Implementation notes

The gauge transform is proved by differentiating `D(r) V M_q(r, z) V⁻¹`: the fundamental matrix is
absolutely continuous in `r` with derivative `P_M(r) M_q(r, z)` almost everywhere, where `P_M` is
the Dirac coefficient, and `D' V + D V P_M = P_G D V` for the scattering coefficient `P_G`. The
fundamental theorem of calculus for absolutely continuous curves then shows that
`D V M_q V⁻¹` solves the integral equation of the propagator of `P_G`.

The reflection formulas are proved for potentials integrable on `[0, t]` by passing to the
truncation `1_{[0, t]} q`, which is locally integrable on `[0, ∞)` and has the same scattering
matrix up to time `t`.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §5.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate
open scoped Matrix Interval

namespace TauCeti

/-- The coefficient `[[0, e^{-2itz} conj q(t)], [e^{2itz} q(t), 0]]` of the scattering system of
the potential `q` at the spectral parameter `z`. -/
noncomputable def diracScatteringCoeff (q : ℝ → ℂ) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, exp (-2 * I * (t * z)) * conj (q t); exp (2 * I * (t * z)) * q t, 0]

/-- The entries of the scattering coefficient. -/
theorem diracScatteringCoeff_def (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    diracScatteringCoeff q z t =
      !![0, exp (-2 * I * (t * z)) * conj (q t); exp (2 * I * (t * z)) * q t, 0] :=
  (rfl)

/-- The scattering matrix `G_q(t, z)` of the potential `q`: the matrix in the standard basis of the
propagator `N(t, 0)` of the coefficient `[[0, e^{-2isz} conj q(s)], [e^{2isz} q(s), 0]]` acting on
`EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def diracScatteringMatrix (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm
    (propagator (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff q z s)) t 0)

/-- The scattering function `a(t, z)`, the lower right entry of the scattering matrix
`G_q(t, z)`. -/
noncomputable def diracScatteringA (q : ℝ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  diracScatteringMatrix q t z 1 1

/-- The scattering function `b(t, z)`, the lower left entry of the scattering matrix
`G_q(t, z)`. -/
noncomputable def diracScatteringB (q : ℝ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  diracScatteringMatrix q t z 1 0

/-- The scattering matrix acts on `EuclideanSpace ℂ (Fin 2)` as the propagator `N(t, 0)` of the
scattering coefficient. -/
@[simp]
theorem toEuclideanCLM_diracScatteringMatrix (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringMatrix q t z) =
      propagator (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff q z s))
        t 0 := by
  simp [diracScatteringMatrix]

/-- The scattering matrix at time `0` is the identity. -/
@[simp]
theorem diracScatteringMatrix_zero (q : ℝ → ℂ) (z : ℂ) : diracScatteringMatrix q 0 z = 1 := by
  simp [diracScatteringMatrix]

/-- `a(t, z)` is the lower right entry of `G_q(t, z)`. -/
theorem diracScatteringA_def (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    diracScatteringA q t z = diracScatteringMatrix q t z 1 1 :=
  (rfl)

/-- `b(t, z)` is the lower left entry of `G_q(t, z)`. -/
theorem diracScatteringB_def (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    diracScatteringB q t z = diracScatteringMatrix q t z 1 0 :=
  (rfl)

/-- At time `0`, `a = 1`. -/
@[simp]
theorem diracScatteringA_zero (q : ℝ → ℂ) (z : ℂ) : diracScatteringA q 0 z = 1 := by
  simp [diracScatteringA_def]

/-- At time `0`, `b = 0`. -/
@[simp]
theorem diracScatteringB_zero (q : ℝ → ℂ) (z : ℂ) : diracScatteringB q 0 z = 0 := by
  simp [diracScatteringB_def]

/-- The scattering coefficient is trace-free. -/
@[simp]
theorem trace_diracScatteringCoeff (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    (diracScatteringCoeff q z t).trace = 0 := by
  simp [diracScatteringCoeff_def, Matrix.trace_fin_two]

/-- The gauge `diag(e^{-irz}, e^{irz})`. -/
private noncomputable def gauge (z : ℂ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![exp (-I * (r * z)), 0; 0, exp (I * (r * z))]

/-- The derivative of the gauge in `r`. -/
private noncomputable def gaugeDeriv (z : ℂ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-I * z * exp (-I * (r * z)), 0; 0, I * z * exp (I * (r * z))]

/-- The change of basis `x ↦ (x₀ + i x₁, x₀ - i x₁)`. -/
private def chg : Matrix (Fin 2) (Fin 2) ℂ := !![1, I; 1, -I]

/-- The inverse of `chg`. -/
private noncomputable def chgInv : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; -I / 2, I / 2]

/-- `chgInv` is the inverse of `chg`. -/
private theorem chg_mul_chgInv : chg * chgInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chg, chgInv, Matrix.mul_apply] <;> ring_nf <;>
    simp [I_sq] <;> ring

/-- The gauge is the identity at time `0`. -/
private theorem gauge_zero (z : ℂ) : gauge z 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gauge]

/-- The key identity `D' V + D V P_M = P_G D V` between the gauge `D`, the change of basis `V`,
the Dirac coefficient `P_M` and the scattering coefficient `P_G`. -/
private theorem gaugeDeriv_mul_add (q : ℝ → ℂ) (z : ℂ) (r : ℝ) :
    gaugeDeriv z r * chg + gauge z r * chg * diracCoeff q z r =
      diracScatteringCoeff q z r * gauge z r * chg := by
  obtain ⟨f, g, hfg⟩ : ∃ f g : ℝ, q r = f + g * I := ⟨_, _, (re_add_im _).symm⟩
  have h2 : exp (2 * I * (r * z)) = exp (I * (r * z)) * exp (I * (r * z)) := by
    rw [← exp_add]; ring_nf
  have h2' : exp (-2 * I * (r * z)) = exp (-I * (r * z)) * exp (-I * (r * z)) := by
    rw [← exp_add]; ring_nf
  have hee' : exp (I * (r * z)) * exp (-I * (r * z)) = 1 := by
    rw [← exp_add]; simp
  simp only [gauge, gaugeDeriv, chg, diracScatteringCoeff_def, diracCoeff_def, h2, h2', hfg]
  generalize exp (I * (r * z)) = e at *
  generalize exp (-I * (r * z)) = e' at *
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, conj_ofReal]
  · linear_combination (-(e' * (f - g * I))) * hee'
  · linear_combination (e' * (g + I * f)) * hee' + (-z * e' - e' ^ 2 * e * g) * I_sq
  · linear_combination (-(e * (f + g * I))) * hee'
  · linear_combination (e * (g - I * f)) * hee' + (-z * e - e ^ 2 * e' * g) * I_sq

variable {q : ℝ → ℂ} {a b t : ℝ}

/-- The scattering coefficient as an operator on `EuclideanSpace ℂ (Fin 2)`: a combination of the
two off-diagonal matrix units. -/
private theorem toEuclideanCLM_diracScatteringCoeff (q : ℝ → ℂ) (z : ℂ) (s : ℝ) :
    toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff q z s) =
      (exp (-2 * I * (s * z)) * conj (q s)) • toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; 0, 0] +
        (exp (2 * I * (s * z)) * q s) • toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 0; 1, 0] := by
  simp only [← map_smul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diracScatteringCoeff_def]

/-- The scattering coefficient, as an operator on `EuclideanSpace ℂ (Fin 2)`, is integrable on
every compact interval on which the potential is integrable. -/
theorem integrableOn_toEuclideanCLM_diracScatteringCoeff (hq : IntegrableOn q (Icc a b)) (z : ℂ) :
    IntegrableOn (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff q z s))
      (Icc a b) := by
  simp_rw [toEuclideanCLM_diracScatteringCoeff]
  have hc (w : ℂ) : ContinuousOn (fun s : ℝ ↦ exp (w * (s * z))) (Icc a b) := by
    fun_prop
  have hconj : IntegrableOn (fun s ↦ conj (q s)) (Icc a b) :=
    (Complex.conjCLE.toContinuousLinearMap).integrable_comp hq
  exact ((hconj.continuousOn_mul (hc _) isCompact_Icc).smul_const _).add
    ((hq.continuousOn_mul (hc _) isCompact_Icc).smul_const _)

/-- The gauge as an operator on `EuclideanSpace ℂ (Fin 2)`. -/
private theorem toEuclideanCLM_gauge (z : ℂ) (r : ℝ) :
    toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (gauge z r) =
      exp (-I * (r * z)) • toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![1, 0; 0, 0] +
        exp (I * (r * z)) • toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 0; 0, 1] := by
  simp only [← map_smul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gauge]

/-- The gauge has derivative `gaugeDeriv`. -/
private theorem hasDerivAt_toEuclideanCLM_gauge (z : ℂ) (r : ℝ) :
    HasDerivAt (fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (gauge z r))
      (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (gaugeDeriv z r)) r := by
  have he (w : ℂ) : HasDerivAt (fun r : ℝ ↦ exp (w * (r * z))) (w * z * exp (w * (r * z))) r := by
    have := (((hasDerivAt_id (r : ℂ)).mul_const z).const_mul w).cexp.comp_ofReal
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  simp_rw [toEuclideanCLM_gauge]
  refine (((he (-I)).smul_const _).add ((he I).smul_const _)).congr_deriv ?_
  simp only [← map_smul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gaugeDeriv]

/-- The gauge is continuously differentiable. -/
private theorem contDiff_toEuclideanCLM_gauge (z : ℂ) :
    ContDiff ℝ 1 (fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (gauge z r)) := by
  have hof : ContDiff ℝ 1 (fun r : ℝ ↦ (r : ℂ)) := ofRealCLM.contDiff
  simp_rw [toEuclideanCLM_gauge]
  fun_prop

/-- **The scattering matrix from the fundamental matrix.** If `q` is integrable between `0` and
`t`, then `G_q(t, z) = D(t) V M_q(t, z) V⁻¹` with `D(t) = diag(e^{-itz}, e^{itz})` and
`V = [[1, i], [1, -i]]`. -/
theorem diracScatteringMatrix_eq_mul_diracFundamentalMatrix_mul (hq : IntegrableOn q (uIcc 0 t))
    (z : ℂ) :
    diracScatteringMatrix q t z =
      !![exp (-I * (t * z)), 0; 0, exp (I * (t * z))] * !![1, I; 1, -I] *
        diracFundamentalMatrix q t z * !![1 / 2, 1 / 2; -I / 2, I / 2] := by
  -- The three explicit matrices are, by definition, `gauge z t`, `chg` and `chgInv`.
  change _ = gauge z t * chg * diracFundamentalMatrix q t z * chgInv
  set T := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  set PG : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun s ↦ T (diracScatteringCoeff q z s)
  set PM : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun s ↦ T (diracCoeff q z s)
  set Z : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun r ↦ T (gauge z r) * T chg * propagator PM r 0 * T chgInv
  have hPM : IntegrableOn PM (uIcc 0 t) := integrableOn_toEuclideanCLM_diracCoeff hq z
  have hPG : IntegrableOn PG (uIcc 0 t) := integrableOn_toEuclideanCLM_diracScatteringCoeff hq z
  have h0 : (0 : ℝ) ∈ uIcc 0 t := left_mem_uIcc
  -- `Z(r) = D(r) V M_q(r, z) V⁻¹` is absolutely continuous, with `Z(0) = 1` and `Z' = P_G Z`
  -- almost everywhere, so it solves the integral equation of the propagator of `P_G`.
  have hZac : AbsolutelyContinuousOnInterval Z 0 t :=
    (((((contDiff_toEuclideanCLM_gauge z).contDiffOn).absolutelyContinuousOnInterval.fun_mul'
      contDiffOn_const.absolutelyContinuousOnInterval).fun_mul'
        ((absolutelyContinuousOnInterval_propagator_left hPM h0).mono
          (uIcc_of_le inf_le_sup).ge)).fun_mul' contDiffOn_const.absolutelyContinuousOnInterval)
  have hkey (r : ℝ) : T (gaugeDeriv z r) * T chg + T (gauge z r) * T chg * PM r =
      PG r * T (gauge z r) * T chg := by
    simp only [PM, PG, ← map_mul, ← map_add, gaugeDeriv_mul_add]
  have hZd : ∀ᵐ r, r ∈ Ioo (0 ⊓ t) (0 ⊔ t) → HasDerivAt Z (PG r * Z r) r := by
    filter_upwards [ae_hasDerivAt_propagator_left hPM h0] with r hr hmem
    refine ((((hasDerivAt_toEuclideanCLM_gauge z r).mul_const (T chg)).mul
      (hr hmem)).mul_const (T chgInv)).congr_deriv ?_
    simp only [Z, ← ContinuousLinearMap.mul_def]
    calc T (gaugeDeriv z r) * T chg * propagator PM r 0 * T chgInv +
          T (gauge z r) * T chg * (PM r * propagator PM r 0) * T chgInv
        = (T (gaugeDeriv z r) * T chg + T (gauge z r) * T chg * PM r) *
            propagator PM r 0 * T chgInv := by noncomm_ring
      _ = PG r * (T (gauge z r) * T chg * propagator PM r 0 * T chgInv) := by
        rw [hkey]; noncomm_ring
  have hZ0 : Z 0 = 1 := by
    simp only [Z, gauge_zero, propagator_self, map_one, one_mul, mul_one, ← map_mul,
      chg_mul_chgInv]
  have hZeq : ∀ r ∈ uIcc 0 t, Z r = 1 + ∫ u in (0 : ℝ)..r, PG u ∘L Z u := fun r hr ↦ by
    have hsub : uIcc 0 r ⊆ uIcc 0 t := uIcc_subset_uIcc h0 hr
    have hder : ∀ᵐ u, u ∈ uIoc 0 r → HasDerivAt Z (PG u ∘L Z u) u := by
      filter_upwards [hZd, Measure.ae_ne volume (0 ⊓ t), Measure.ae_ne volume (0 ⊔ t)]
        with u hu h1 h2 hmem
      have hu' : u ∈ uIcc 0 t := hsub (uIoc_subset_uIcc hmem)
      exact hu ⟨lt_of_le_of_ne hu'.1 (Ne.symm h1), lt_of_le_of_ne hu'.2 h2⟩
    rw [(hZac.mono hsub).integral_eq_sub_of_ae_hasDerivAt hder, hZ0, add_sub_cancel]
  rw [diracScatteringMatrix, propagator_eq_of_forall_mem_Icc hPG h0 right_mem_uIcc
    hZac.continuousOn' hZeq]
  have hN : propagator PM t 0 = T (diracFundamentalMatrix q t z) :=
    (toEuclideanCLM_diracFundamentalMatrix q t z).symm
  simp only [Z, hN, ← map_mul, T, StarAlgEquiv.symm_apply_apply]

/-- **The dictionary with the Hermite–Biehler functions.** If `q` is integrable between `0` and
`t`, then `a(t, z) = e^{itz} (E(t, z) + i E~(t, z)) / 2`. -/
theorem diracScatteringA_eq (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ) :
    diracScatteringA q t z =
      exp (I * (t * z)) * (diracHermiteBiehler q t z + I * diracHermiteBiehlerDirichlet q t z) /
        2 := by
  rw [diracScatteringA_def, diracScatteringMatrix_eq_mul_diracFundamentalMatrix_mul hq,
    diracHermiteBiehler_def,
    diracHermiteBiehlerDirichlet_def]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

/-- **The dictionary with the Hermite–Biehler functions.** If `q` is integrable between `0` and
`t`, then `b(t, z) = e^{itz} (E(t, z) - i E~(t, z)) / 2`. -/
theorem diracScatteringB_eq (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ) :
    diracScatteringB q t z =
      exp (I * (t * z)) * (diracHermiteBiehler q t z - I * diracHermiteBiehlerDirichlet q t z) /
        2 := by
  rw [diracScatteringB_def, diracScatteringMatrix_eq_mul_diracFundamentalMatrix_mul hq,
    diracHermiteBiehler_def,
    diracHermiteBiehlerDirichlet_def]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

/-- **The inverse dictionary.** If `q` is integrable between `0` and `t`, then
`E(t, z) = e^{-itz} (a(t, z) + b(t, z))`. -/
theorem diracHermiteBiehler_eq_exp_mul_diracScatteringA_add (hq : IntegrableOn q (uIcc 0 t))
    (z : ℂ) :
    diracHermiteBiehler q t z =
      exp (-I * (t * z)) * (diracScatteringA q t z + diracScatteringB q t z) := by
  rw [diracScatteringA_eq hq, diracScatteringB_eq hq]
  have h : exp (-I * (t * z)) * exp (I * (t * z)) = 1 := by rw [← exp_add]; simp
  linear_combination (-diracHermiteBiehler q t z) * h

/-- **The inverse dictionary.** If `q` is integrable between `0` and `t`, then
`E~(t, z) = -i e^{-itz} (a(t, z) - b(t, z))`. -/
theorem diracHermiteBiehlerDirichlet_eq_neg_I_mul_exp_mul_diracScatteringA_sub
    (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ) :
    diracHermiteBiehlerDirichlet q t z =
      -I * exp (-I * (t * z)) * (diracScatteringA q t z - diracScatteringB q t z) := by
  rw [diracScatteringA_eq hq, diracScatteringB_eq hq]
  have h : exp (-I * (t * z)) * exp (I * (t * z)) = 1 := by rw [← exp_add]; simp
  linear_combination (-diracHermiteBiehlerDirichlet q t z) * h +
    (diracHermiteBiehlerDirichlet q t z * exp (-I * (t * z)) * exp (I * (t * z))) * I_sq

/-- `a(t, ·)` is entire when `q` is integrable between `0` and `t`. -/
theorem differentiable_diracScatteringA (hq : IntegrableOn q (uIcc 0 t)) :
    Differentiable ℂ (diracScatteringA q t) := by
  have hE := differentiable_diracHermiteBiehler hq
  have hE' := differentiable_diracHermiteBiehlerDirichlet hq
  simp_rw [funext (diracScatteringA_eq hq)]
  fun_prop

/-- `b(t, ·)` is entire when `q` is integrable between `0` and `t`. -/
theorem differentiable_diracScatteringB (hq : IntegrableOn q (uIcc 0 t)) :
    Differentiable ℂ (diracScatteringB q t) := by
  have hE := differentiable_diracHermiteBiehler hq
  have hE' := differentiable_diracHermiteBiehlerDirichlet hq
  simp_rw [funext (diracScatteringB_eq hq)]
  fun_prop

/-- **Locality.** The scattering matrix `G_q(t, z)` depends only on `q` almost everywhere between
`0` and `t`. -/
theorem diracScatteringMatrix_congr_ae {q' : ℝ → ℂ} (h : ∀ᵐ u, u ∈ Ι 0 t → q u = q' u) (z : ℂ) :
    diracScatteringMatrix q t z = diracScatteringMatrix q' t z := by
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  simp only [toEuclideanCLM_diracScatteringMatrix]
  refine propagator_congr_ae ?_
  filter_upwards [h] with u hu hmem
  simp [diracScatteringCoeff_def, hu hmem]

/-- The scattering matrix of `q` up to time `t ≥ 0` is that of the truncation `1_{[0, t]} q`,
which is locally integrable on `[0, ∞)` when `q` is integrable on `[0, t]`. -/
private theorem diracScatteringMatrix_indicator (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringMatrix ((Icc 0 t).indicator q) t z = diracScatteringMatrix q t z :=
  diracScatteringMatrix_congr_ae (ae_of_all _ fun _ hu ↦ indicator_of_mem
    (Ioc_subset_Icc_self (uIoc_of_le ht ▸ hu)) q) z

/-- The reflection formulas for the top row, for a potential locally integrable on `[0, ∞)`. -/
private theorem diracScatteringMatrix_apply_zero_of_locallyIntegrableOn
    (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringMatrix q t z 0 0 = conj (diracScatteringA q t (conj z)) ∧
      diracScatteringMatrix q t z 0 1 = conj (diracScatteringB q t (conj z)) := by
  have hqt : IntegrableOn q (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  rw [diracScatteringA_def, diracScatteringB_def,
    diracScatteringMatrix_eq_mul_diracFundamentalMatrix_mul hqt,
    diracScatteringMatrix_eq_mul_diracFundamentalMatrix_mul hqt, diracFundamentalMatrix_conj hq ht]
  constructor <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, ← exp_conj, map_ofNat]

/-- The reflection formulas for the top row, for a potential integrable on `[0, t]`. -/
private theorem diracScatteringMatrix_apply_zero (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) :
    diracScatteringMatrix q t z 0 0 = conj (diracScatteringA q t (conj z)) ∧
      diracScatteringMatrix q t z 0 1 = conj (diracScatteringB q t (conj z)) := by
  have hq' : LocallyIntegrableOn ((Icc 0 t).indicator q) (Ici 0) :=
    ((integrable_indicator_iff measurableSet_Icc).2 hq).locallyIntegrable.locallyIntegrableOn _
  simpa only [diracScatteringA_def, diracScatteringB_def, diracScatteringMatrix_indicator ht] using
    diracScatteringMatrix_apply_zero_of_locallyIntegrableOn hq' ht z

/-- The upper left entry of the scattering matrix is `a#(t, z) = conj a(t, conj z)`, for `q`
integrable on `[0, t]` with `t ≥ 0`. -/
theorem diracScatteringMatrix_apply_zero_zero (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) : diracScatteringMatrix q t z 0 0 = conj (diracScatteringA q t (conj z)) :=
  (diracScatteringMatrix_apply_zero hq ht z).1

/-- The upper right entry of the scattering matrix is `b#(t, z) = conj b(t, conj z)`, for `q`
integrable on `[0, t]` with `t ≥ 0`. -/
theorem diracScatteringMatrix_apply_zero_one (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) : diracScatteringMatrix q t z 0 1 = conj (diracScatteringB q t (conj z)) :=
  (diracScatteringMatrix_apply_zero hq ht z).2

/-- **The structure of the scattering matrix.** For `q` integrable on `[0, t]` with `t ≥ 0`,
`G_q(t, z) = [[a#, b#], [b, a]]`, where `h#(z) = conj h(conj z)`. -/
theorem diracScatteringMatrix_eq_conj (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) :
    diracScatteringMatrix q t z =
      !![conj (diracScatteringA q t (conj z)), conj (diracScatteringB q t (conj z));
        diracScatteringB q t z, diracScatteringA q t z] := by
  rw [← diracScatteringMatrix_apply_zero_zero hq ht, ← diracScatteringMatrix_apply_zero_one hq ht,
    diracScatteringA_def, diracScatteringB_def]
  exact eta_fin_two _

/-- **Liouville's formula for the scattering matrix.** The scattering coefficient is trace-free,
so `det G_q(t, z) = 1` whenever `q` is integrable between `0` and `t`. -/
@[simp]
theorem det_diracScatteringMatrix (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ) :
    (diracScatteringMatrix q t z).det = 1 := by
  rw [← det_toEuclideanCLM, toEuclideanCLM_diracScatteringMatrix, ContinuousLinearMap.det,
    det_propagator (integrableOn_toEuclideanCLM_diracScatteringCoeff hq z) left_mem_uIcc
      right_mem_uIcc]
  simp

/-- **The determinant identity** `a a# - b b# = 1`: for `q` integrable on `[0, t]` with `t ≥ 0`,
`a(t, z) conj a(t, conj z) - b(t, z) conj b(t, conj z) = 1`. -/
theorem diracScatteringA_mul_conj_sub_diracScatteringB_mul_conj (hq : IntegrableOn q (Icc 0 t))
    (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringA q t z * conj (diracScatteringA q t (conj z)) -
      diracScatteringB q t z * conj (diracScatteringB q t (conj z)) = 1 := by
  have h := det_diracScatteringMatrix (uIcc_of_le ht ▸ hq) z
  rw [diracScatteringMatrix_eq_conj hq ht, det_fin_two_of] at h
  linear_combination h

/-- **`G_q(t, x) ∈ SU(1, 1)` on the real axis.** For `q` integrable on `[0, t]` with `t ≥ 0` and
`x : ℝ`, `|a(t, x)|² - |b(t, x)|² = 1`. -/
theorem norm_diracScatteringA_sq_sub_norm_diracScatteringB_sq (hq : IntegrableOn q (Icc 0 t))
    (ht : 0 ≤ t) (x : ℝ) :
    ‖diracScatteringA q t x‖ ^ 2 - ‖diracScatteringB q t x‖ ^ 2 = 1 := by
  have h := diracScatteringA_mul_conj_sub_diracScatteringB_mul_conj hq ht x
  rw [conj_ofReal, mul_conj, mul_conj, normSq_eq_norm_sq, normSq_eq_norm_sq] at h
  exact_mod_cast h

/-- **The integral equation of the scattering matrix**, entrywise. If `q` is integrable between
`0` and `t`, then `G_q(t, z) = 1 + ∫₀ᵗ P(s) G_q(s, z) ds` with `P` the scattering coefficient. -/
theorem diracScatteringMatrix_apply_eq_add_integral (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ)
    (i j : Fin 2) :
    diracScatteringMatrix q t z i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
      ∫ s in (0 : ℝ)..t, (diracScatteringCoeff q z s * diracScatteringMatrix q s z) i j := by
  set T := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  set P : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun s ↦ T (diracScatteringCoeff q z s)
  have hP : IntegrableOn P (uIcc 0 t) := integrableOn_toEuclideanCLM_diracScatteringCoeff hq z
  -- The entry functional `X ↦ (X e_j)_i` on operators.
  let L : (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) →L[ℂ] ℂ :=
    (EuclideanSpace.proj i).comp
      (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace.single j 1))
  have hL (A : Matrix (Fin 2) (Fin 2) ℂ) : L (T A) = A i j := by
    simp [L, T]
  have hI : IntervalIntegrable (fun u ↦ P u ∘L propagator P u 0) volume 0 t :=
    hP.intervalIntegrable_clm_comp (continuousOn_propagator_left hP left_mem_uIcc)
      left_mem_uIcc right_mem_uIcc
  have key := congrArg L (propagator_eq_one_add_integral hP left_mem_uIcc right_mem_uIcc)
  rw [map_add, ← L.intervalIntegral_comp_comm hI, ← map_one T, hL] at key
  rw [← hL (diracScatteringMatrix q t z), toEuclideanCLM_diracScatteringMatrix, key]
  refine congrArg _ (intervalIntegral.integral_congr fun s _ ↦ ?_)
  rw [← hL (diracScatteringCoeff q z s * diracScatteringMatrix q s z), map_mul,
    toEuclideanCLM_diracScatteringMatrix, ContinuousLinearMap.mul_def]

/-- **The Volterra form of `b`.** For `q` integrable on `[0, t]` with `t ≥ 0`,
`b(t, z) = ∫₀ᵗ q(s) e^{2isz} a#(s, z) ds`, where `a#(s, z) = conj a(s, conj z)`. -/
theorem diracScatteringB_eq_integral (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (z : ℂ) :
    diracScatteringB q t z =
      ∫ s in (0 : ℝ)..t, q s * exp (2 * I * (s * z)) * conj (diracScatteringA q s (conj z)) := by
  rw [diracScatteringB_def, diracScatteringMatrix_apply_eq_add_integral (uIcc_of_le ht ▸ hq)]
  simp only [one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le ht] at hs
  have hqs : IntegrableOn q (Icc 0 s) := hq.mono_set (Icc_subset_Icc_right hs.2)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ← diracScatteringMatrix_apply_zero_zero hqs hs.1]
  simp only [diracScatteringCoeff_def, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, zero_mul, add_zero]
  ring

/-- **The Volterra form of `a`.** For `q` integrable on `[0, t]` with `t ≥ 0`,
`a(t, z) = 1 + ∫₀ᵗ q(s) e^{2isz} b#(s, z) ds`, where `b#(s, z) = conj b(s, conj z)`. -/
theorem diracScatteringA_eq_one_add_integral (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (z : ℂ) :
    diracScatteringA q t z =
      1 + ∫ s in (0 : ℝ)..t,
        q s * exp (2 * I * (s * z)) * conj (diracScatteringB q s (conj z)) := by
  rw [diracScatteringA_def, diracScatteringMatrix_apply_eq_add_integral (uIcc_of_le ht ▸ hq),
    one_apply_eq]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le ht] at hs
  have hqs : IntegrableOn q (Icc 0 s) := hq.mono_set (Icc_subset_Icc_right hs.2)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ← diracScatteringMatrix_apply_zero_one hqs hs.1]
  simp only [diracScatteringCoeff_def, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, zero_mul, add_zero]
  ring

/-- **Locality after the support.** If `q` is integrable on `[0, t]` and vanishes almost
everywhere on `(T, t]` for some `T ∈ [0, t]`, then `G_q(t, z) = G_q(T, z)`. -/
theorem diracScatteringMatrix_eq_of_ae_eq_zero (hq : IntegrableOn q (Icc 0 t)) {T : ℝ}
    (hT : T ∈ Icc 0 t) (h : ∀ᵐ u, u ∈ Ioc T t → q u = 0) (z : ℂ) :
    diracScatteringMatrix q t z = diracScatteringMatrix q T z := by
  set P : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff q z s)
  have hP : IntegrableOn P (Icc 0 t) := integrableOn_toEuclideanCLM_diracScatteringCoeff hq z
  have h0 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, hT.1.trans hT.2⟩
  have ht : t ∈ Icc 0 t := ⟨h0.2, le_rfl⟩
  have hone : propagator P t T = 1 := by
    rw [propagator_congr_ae (Q := 0), propagator_zero]
    filter_upwards [h] with u hu hmem
    rw [uIoc_of_le hT.2] at hmem
    simp [P, diracScatteringCoeff_def, hu hmem, ← Matrix.ext_iff, Fin.forall_fin_two]
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  simp only [toEuclideanCLM_diracScatteringMatrix]
  rw [← propagator_comp_propagator hP hT h0 ht, hone]
  rfl

/-- **The free case.** For the zero potential the scattering matrix is the identity. -/
@[simp]
theorem diracScatteringMatrix_zero_potential (t : ℝ) (z : ℂ) :
    diracScatteringMatrix 0 t z = 1 := by
  have hP : (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff 0 z s)) = 0 := by
    ext1 s
    simp [diracScatteringCoeff_def, ← Matrix.ext_iff, Fin.forall_fin_two]
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  rw [toEuclideanCLM_diracScatteringMatrix, hP, propagator_zero, map_one]

/-- **The free case.** For the zero potential, `a = 1`. -/
@[simp]
theorem diracScatteringA_zero_potential (t : ℝ) (z : ℂ) : diracScatteringA 0 t z = 1 := by
  simp [diracScatteringA_def]

/-- **The free case.** For the zero potential, `b = 0`. -/
@[simp]
theorem diracScatteringB_zero_potential (t : ℝ) (z : ℂ) : diracScatteringB 0 t z = 0 := by
  simp [diracScatteringB_def]

end TauCeti
